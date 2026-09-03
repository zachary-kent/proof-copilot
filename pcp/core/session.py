"""pet-server pool, sandboxing, timeouts (PLAN.md 6).

The physical ceiling here is Rocq, not the rate window.  A pet-server with Iris
loaded costs 1-2 GB RSS and executes tactics serially, and ``petanque/start``
re-elaborates the file prefix, so spawning is minutes rather than milliseconds.
Workers therefore multiplex as *immutable state ids* over a few shared pet-server
processes -- petanque states make that nearly free -- rather than each owning a
process.

Everything here is defensive: per-call wall clock, an RSS cap, kill-and-restart on
divergence, and state-hash loop detection so an agent applying a no-op tactic in a
cycle is caught mechanically instead of burning its budget.
"""

from __future__ import annotations

import atexit
import contextlib
import logging
import math
import os
import shutil
import signal
import socket
import subprocess
import tempfile
import threading
import time
from collections import OrderedDict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterator

log = logging.getLogger("pcp.session")

DEFAULT_STEP_TIMEOUT = 30.0
DEFAULT_START_TIMEOUT = 600.0
DEFAULT_RSS_CAP_MB = 8192

#: Hard, OS-enforced address-space ceiling for a `pet` process, in MB.
#:
#: `rss_cap_mb` is a *soft* cap: `ensure_healthy` only looks between calls, so a
#: single runaway tactic is unbounded -- Rocq's `Timeout` bounds time, not memory.
#: One orphaned session reached **372 GB** on a 1 TB box before anyone noticed. This
#: is the backstop that makes that impossible: the allocation fails inside the call
#: and the session dies, instead of the machine.
#:
#: Set well above the soft cap so the graceful path (restart between calls) is what
#: normally fires, and generously in absolute terms because a real Iris development
#: legitimately needs several GB.
DEFAULT_MEM_LIMIT_MB = int(os.environ.get("PCP_PET_MEM_LIMIT_MB") or 24576)


class PetServerError(RuntimeError):
    pass


class StepTimeout(PetServerError):
    pass


def _free_port() -> int:
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return int(s.getsockname()[1])


def pet_server_binary() -> str | None:
    """The socket-mode petanque server, when this coq-lsp ships one."""
    return os.environ.get("PCP_PET_SERVER") or shutil.which("pet-server")


def pet_binary() -> str | None:
    """The stdio-mode petanque binary.  coq-lsp 0.2.5 ships `pet` only."""
    return os.environ.get("PCP_PET") or shutil.which("pet")


def rocq_binary() -> str | None:
    return os.environ.get("PCP_COQC") or shutil.which("coqc") or shutil.which("rocq")


def toolchain_available() -> bool:
    return pet_server_binary() is not None or pet_binary() is not None


# --------------------------------------------------------------------------- server

@dataclass
class ServerConfig:
    workspace: Path
    port: int = 0
    rss_cap_mb: int = DEFAULT_RSS_CAP_MB
    #: Hard address-space limit applied to the process itself (see the constant).
    mem_limit_mb: int = DEFAULT_MEM_LIMIT_MB
    start_timeout: float = DEFAULT_START_TIMEOUT
    step_timeout: float = DEFAULT_STEP_TIMEOUT
    env: dict[str, str] = field(default_factory=dict)


def _limit_child(mem_limit_mb: int):
    """A `preexec_fn` that caps the child's address space and ties it to our life."""

    def apply() -> None:  # pragma: no cover -- runs post-fork in the child
        import resource

        limit = mem_limit_mb * 1024 * 1024
        with contextlib.suppress(Exception):
            resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
        # Die when the parent does. An orphaned petanque holds its whole Rocq heap
        # forever; one outlived the run that started it by hours.
        with contextlib.suppress(Exception):
            import ctypes

            ctypes.CDLL("libc.so.6", use_errno=True).prctl(1, signal.SIGKILL)  # PR_SET_PDEATHSIG

    return apply


_WRAPPER_DIRS: dict[int, Path] = {}


def _pet_wrapper_dir(mem_limit_mb: int) -> Path:
    """A directory holding a `pet` that limits itself and then becomes the real one."""
    cached = _WRAPPER_DIRS.get(mem_limit_mb)
    if cached is not None and (cached / "pet").exists():
        return cached
    real = pet_binary()
    if real is None:
        raise PetServerError("no `pet` binary on PATH to wrap")
    real = str(Path(real).resolve())
    root = Path(tempfile.gettempdir()) / f"pcp-pet-{mem_limit_mb}"
    root.mkdir(parents=True, exist_ok=True)
    wrapper = root / "pet"
    # `setpriv --pdeathsig KILL` makes the kernel reap petanque when whatever spawned
    # it dies. Without it an orphan keeps its entire Rocq heap: one survived the run
    # that started it by hours and was found holding 372 GB. Optional -- if setpriv
    # is missing the limit still applies, which is the part that bounds the damage.
    launch = f'exec setpriv --pdeathsig KILL "{real}" "$@"' if shutil.which("setpriv") \
        else f'exec "{real}" "$@"'
    wrapper.write_text(
        "#!/bin/sh\n"
        "# Written by pcp: bound petanque's address space and lifetime, then hand over.\n"
        f"ulimit -v {mem_limit_mb * 1024} 2>/dev/null || true\n"
        f"{launch}\n",
        encoding="utf-8",
    )
    wrapper.chmod(0o755)
    _WRAPPER_DIRS[mem_limit_mb] = root
    return root


class PetServer:
    """One ``pet-server`` process plus its pytanque client."""

    def __init__(self, cfg: ServerConfig) -> None:
        self.cfg = cfg
        self.port = cfg.port or _free_port()
        self.proc: subprocess.Popen | None = None
        self.client: Any = None
        self.lock = threading.RLock()
        self.calls = 0
        self.started_at = 0.0

    # -- lifecycle ---------------------------------------------------------
    def start(self) -> None:
        if pet_server_binary() is not None:
            self._start_socket()
        elif pet_binary() is not None:
            self._start_stdio()
        else:
            raise PetServerError(
                "no petanque binary found (looked for `pet-server` and `pet`). "
                "Run ./scripts/setup-toolchain.sh, then `. ./env.sh`."
            )
        self.started_at = time.time()

    def _start_socket(self) -> None:
        from pytanque import Pytanque  # imported lazily: pcp-orch must not need it

        binary = pet_server_binary()
        assert binary is not None
        env = {**os.environ, **self.cfg.env}
        self.proc = subprocess.Popen(
            [binary, "--port", str(self.port)],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            env=env,
            cwd=str(self.cfg.workspace),
            start_new_session=True,
            preexec_fn=_limit_child(self.cfg.mem_limit_mb),
        )
        deadline = time.time() + 30.0
        last: Exception | None = None
        while time.time() < deadline:
            if self.proc is not None and self.proc.poll() is not None:
                raise PetServerError(f"pet-server exited during startup: {self._drain()[-2000:]}")
            try:
                client = Pytanque("127.0.0.1", self.port)
                client.connect()
                client.set_workspace(False, str(self.cfg.workspace))
                self.client = client
                return
            except Exception as exc:  # noqa: BLE001 -- retry until the socket is up
                last = exc
                time.sleep(0.2)
        raise PetServerError(f"could not connect to pet-server on :{self.port}: {last}")

    def _start_stdio(self) -> None:
        """Drive `pet` over stdio.  pytanque owns the subprocess in this mode.

        It spawns a bare ``["pet"]`` resolved from ``PATH`` with no limits and no
        hook to add any, so the ceiling is imposed by putting a wrapper of that name
        earlier on ``PATH``. Shadowing the binary is normally a thing to avoid, but
        here the wrapper is a two-line ``exec`` whose only effect is a resource
        limit -- it cannot change what `pet` computes, only stop it from taking the
        machine down.
        """
        from pytanque import Pytanque, PytanqueMode

        os.environ["PATH"] = f"{_pet_wrapper_dir(self.cfg.mem_limit_mb)}{os.pathsep}{os.environ.get('PATH', '')}"
        client = Pytanque(mode=PytanqueMode.STDIO)
        client.connect()
        client.set_workspace(False, str(self.cfg.workspace))
        self.client = client
        self.proc = getattr(client, "process", None)

    def _drain(self) -> str:
        if self.proc is None or self.proc.stdout is None:
            return ""
        with contextlib.suppress(Exception):
            return self.proc.stdout.read(65536).decode("utf-8", "replace")
        return ""

    def stop(self) -> None:
        with contextlib.suppress(Exception):
            if self.client is not None:
                self.client.close()
        self.client = None
        if self.proc is not None and self.proc.poll() is None:
            self.proc.terminate()
            try:
                self.proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self.proc.kill()
        self.proc = None

    def restart(self) -> None:
        log.warning("restarting pet-server on :%d after divergence", self.port)
        self.stop()
        self.port = _free_port()
        self.start()

    # -- health ------------------------------------------------------------
    def rss_mb(self) -> int:
        if self.proc is None:
            return 0
        try:
            with open(f"/proc/{self.proc.pid}/statm") as fh:
                pages = int(fh.read().split()[1])
            return pages * os.sysconf("SC_PAGE_SIZE") // (1024 * 1024)
        except (OSError, ValueError, IndexError):
            return 0

    def healthy(self) -> bool:
        if self.proc is None or self.proc.poll() is not None or self.client is None:
            return False
        return self.rss_mb() <= self.cfg.rss_cap_mb

    def ensure_healthy(self) -> None:
        if not self.healthy():
            self.restart()


# ----------------------------------------------------------------------------- pool

class SessionPool:
    """A handful of pet-servers, shared by many logical sessions.

    Acquire is blocking and fair.  Callers hold a server only for the duration of one
    petanque call, because petanque states are immutable: a logical session is a
    state id, not a process.
    """

    def __init__(self, workspace: Path | str, size: int = 2, **cfg: Any) -> None:
        self.workspace = Path(workspace).resolve()
        self.size = max(1, size)
        self.cfg_extra = cfg
        self._servers: list[PetServer] = []
        self._sem = threading.Semaphore(self.size)
        self._lock = threading.Lock()
        self._closed = False
        #: server -> files it has already elaborated.  coq-lsp caches a checked
        #: document, so the *second* `start` on a file costs 0.3 s against 22 s for
        #: the first: routing a file back to the server that already knows it is
        #: worth far more than any parallelism.
        self._affinity: dict[int, set[str]] = {}
        atexit.register(self.close)

    def _spawn(self) -> PetServer:
        server = PetServer(ServerConfig(workspace=self.workspace, **self.cfg_extra))
        server.start()
        return server

    @contextlib.contextmanager
    def acquire(self, file: str | None = None) -> Iterator[PetServer]:
        if self._closed:
            raise PetServerError("pool is closed")
        self._sem.acquire()
        server: PetServer | None = None
        try:
            with self._lock:
                server = self._pick_free(file)
                if server is None:
                    server = self._spawn()
                    server.lock.acquire()
                    self._servers.append(server)
                if file is not None:
                    self._affinity.setdefault(id(server), set()).add(str(file))
            server.ensure_healthy()
            yield server
        finally:
            if server is not None:
                with contextlib.suppress(RuntimeError):
                    server.lock.release()
            self._sem.release()

    def _pick_free(self, file: str | None) -> PetServer | None:
        """Prefer a free server that has already elaborated ``file``."""
        warm = [
            s for s in self._servers
            if file is not None and str(file) in self._affinity.get(id(s), set())
        ]
        for candidate in warm + [s for s in self._servers if s not in warm]:
            if candidate.lock.acquire(blocking=False):
                return candidate
        return None

    def close(self) -> None:
        if self._closed:
            return
        self._closed = True
        for server in self._servers:
            with contextlib.suppress(Exception):
                server.stop()
        self._servers.clear()


# -------------------------------------------------------------------------- session

@dataclass
class StepResult:
    ok: bool
    state: Any = None
    state_hash: int | None = None
    error: str | None = None
    #: Messages Rocq emitted for this step -- the channel `iDump` rides on.
    messages: list[str] = field(default_factory=list)
    elapsed_ms: int = 0
    proof_finished: bool = False
    #: Set when the step produced a state we have already been in.
    loop_of: int | None = None
    typeclass_debug: str | None = None


class ProofSession:
    """A logical proof session: a root state plus the states reachable from it.

    The session owns no process.  It borrows one from the pool per call, which is
    what lets a handful of pet-servers carry dozens of workers.
    """

    def __init__(
        self,
        pool: SessionPool,
        file: str | Path,
        thm: str,
        *,
        pre_commands: str | None = None,
        step_timeout: float = DEFAULT_STEP_TIMEOUT,
        lru_size: int = 512,
        stub_prefix: bool = False,
    ) -> None:
        self.pool = pool
        self.source_file = str(Path(file).resolve())
        #: Opening a statements-only copy makes the cost of `start` flat in file
        #: size (22 s -> 2.5 s on seqlockWf).  Sound for the same reason the gate's
        #: `stub_prefix` is: `Qed` proofs are opaque, so the proof state at ``thm``
        #: depends on the *statements* before it and never on their bodies.
        self.file = _stubbed_copy(self.source_file, keep=thm) if stub_prefix else self.source_file
        self.thm = thm
        self.pre_commands = pre_commands
        self.step_timeout = step_timeout
        self.root: Any = None
        self.current: Any = None
        self.history: list[tuple[str, Any]] = []
        self._states: OrderedDict[int, Any] = OrderedDict()
        self._lru_size = lru_size
        self._seen_hashes: dict[int, int] = {}  # state hash -> step index

    # -- start -------------------------------------------------------------
    def start(self) -> Any:
        with self.pool.acquire(file=self.file) as server:
            self.root = server.client.start(
                file=self.file,
                thm=self.thm,
                pre_commands=self.pre_commands,
                timeout=self.pool.cfg_extra.get("start_timeout", DEFAULT_START_TIMEOUT),
            )
        self.current = self.root
        self._remember(self.root)
        return self.root

    def _remember(self, state: Any) -> None:
        self._states[state.st] = state
        self._states.move_to_end(state.st)
        while len(self._states) > self._lru_size:
            self._states.popitem(last=False)

    def state(self, state_id: int | None = None) -> Any:
        if state_id is None:
            return self.current
        st = self._states.get(state_id)
        if st is None:
            raise PetServerError(f"state {state_id} is no longer in the LRU table")
        return st

    # -- stepping ----------------------------------------------------------
    def run(
        self,
        tactic: str,
        *,
        from_state: Any | None = None,
        commit: bool = True,
        timeout: float | None = None,
    ) -> StepResult:
        """Run one tactic.  ``commit=False`` is speculative: the session does not move."""
        base = from_state if from_state is not None else self.current
        if base is None:
            raise PetServerError("session not started")
        started = time.perf_counter()
        limit = _coq_timeout(timeout or self.step_timeout)
        with self.pool.acquire() as server:
            try:
                # pytanque turns this into Rocq's own `Timeout n tac.` wrapper, which
                # is exactly the containment PLAN.md 6 asks for -- Iris typeclass
                # resolution can loop, and the wrapper bounds it inside Rocq rather
                # than leaving us to kill a process.  It must be a literal integer.
                state = server.client.run(base, tactic, timeout=limit)
            except Exception as exc:  # noqa: BLE001 -- petanque raises many shapes
                elapsed = int((time.perf_counter() - started) * 1000)
                msg = _error_text(exc)
                result = StepResult(ok=False, error=msg, elapsed_ms=elapsed)
                if _is_timeout(msg):
                    result.typeclass_debug = self._typeclass_debug(server, base, tactic)
                return result
            elapsed = int((time.perf_counter() - started) * 1000)
            try:
                h = server.client.state_hash(state)
            except Exception:  # noqa: BLE001 -- hashing is best-effort
                h = state.hash

        result = StepResult(
            ok=True,
            state=state,
            state_hash=h,
            messages=[m for _, m in getattr(state, "feedback", [])],
            elapsed_ms=elapsed,
            proof_finished=bool(getattr(state, "proof_finished", False)),
        )
        if h is not None and h in self._seen_hashes:
            result.loop_of = self._seen_hashes[h]
        if commit:
            self.current = state
            self.history.append((tactic, state))
            self._remember(state)
            if h is not None:
                self._seen_hashes.setdefault(h, len(self.history) - 1)
        return result

    def try_many(self, tactics: list[str], *, from_state: Any | None = None) -> list[StepResult]:
        """Speculative fan-out from one state (PLAN.md 7, ``proof_try``).

        Very high value per token: N candidate tactics, one report of which survive,
        no commitment and no goal dumps for the ones that do not.
        """
        base = from_state if from_state is not None else self.current
        return [self.run(t, from_state=base, commit=False) for t in tactics]

    def _typeclass_debug(self, server: PetServer, base: Any, tactic: str) -> str | None:
        """On a timeout, capture ``Set Typeclasses Debug`` output.

        Typeclass resolution in Iris can loop, and that trace is itself a good
        diagnostic to hand the agent -- better than "timed out".
        """
        with contextlib.suppress(Exception):
            probe = server.client.run(base, "Set Typeclasses Debug.", timeout=10)  # noqa: E501
            with contextlib.suppress(Exception):
                server.client.run(probe, tactic, timeout=_coq_timeout(min(10.0, self.step_timeout)))
            return "\n".join(m for _, m in getattr(probe, "feedback", []))[:8000] or None
        return None

    # -- inspection --------------------------------------------------------
    def goals(self, state: Any | None = None) -> list[Any]:
        st = state if state is not None else self.current
        with self.pool.acquire() as server:
            return server.client.goals(st)

    def premises(self, state: Any | None = None) -> Any:
        st = state if state is not None else self.current
        with self.pool.acquire() as server:
            return server.client.premises(st)

    def ast(self, text: str, state: Any | None = None) -> Any:
        st = state if state is not None else self.current
        with self.pool.acquire() as server:
            return server.client.ast(st, text)

    def state_equal(self, a: Any, b: Any) -> bool:
        from pytanque import InspectPhysical

        with self.pool.acquire() as server:
            try:
                return bool(server.client.state_equal(a, b, InspectPhysical()))
            except Exception:  # noqa: BLE001 -- fall back to hashes
                return server.client.state_hash(a) == server.client.state_hash(b)

    def query(self, command: str, state: Any | None = None) -> list[str]:
        """Run a *query* command (``Search``, ``Print``, ``About``) for its messages."""
        result = self.run(command, from_state=state, commit=False)
        if not result.ok:
            return []
        return result.messages

    # -- replay ------------------------------------------------------------
    def replay(self, tactics: list[str]) -> list[StepResult]:
        """Deterministic replay: a trace is (root state, tactic list) (PLAN.md 6)."""
        if self.root is None:
            self.start()
        self.current = self.root
        self.history.clear()
        self._seen_hashes.clear()
        out = []
        for tactic in tactics:
            res = self.run(tactic)
            out.append(res)
            if not res.ok:
                break
        return out


def _stubbed_copy(path: str, *, keep: str) -> str:
    """Write a statements-only twin of ``path`` beside it, and return its path.

    Kept in the same directory so the project's `-Q`/`-R` flags and the coq-lsp
    workspace apply unchanged; given a distinct name so nothing `Require`s it.
    """
    from pcp.orch.assemble import stub_proof_bodies

    src = Path(path)
    text = src.read_text(encoding="utf-8")
    stubbed, _names = stub_proof_bodies(text, keep={keep})
    twin = src.with_name(f"{src.stem}__pcpfast.v")
    if not twin.exists() or twin.read_text(encoding="utf-8") != stubbed:
        twin.write_text(stubbed, encoding="utf-8")
    return str(twin)


def _coq_timeout(seconds: float | None) -> int | None:
    """Rocq's `Timeout` vernacular takes an integer number of seconds."""
    if seconds is None:
        return None
    return max(1, math.ceil(seconds))


def _error_text(exc: Exception) -> str:
    message = getattr(exc, "message", None)
    if isinstance(message, str) and message:
        return message
    return f"{type(exc).__name__}: {exc}"


def _is_timeout(msg: str) -> bool:
    lowered = msg.lower()
    return "timeout" in lowered or "timed out" in lowered
