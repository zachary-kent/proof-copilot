"""One ``pet`` process and the only place pytanque is spoken (PLAN.md 6, 14; ARCHITECTURE.md 6).

The physical facts this adapter is built on (verified against coq-lsp 0.2.5 ``pet``):

* petanque **state ids are per process**, allocated 1, 2, 3, ... -- two processes hand
  out the *same* ids for *different* states, and a process given a foreign id answers
  with its own state of that id without complaint.  So every :class:`StateHandle`
  carries the process id and the process *generation*, and :meth:`PetProcess.call`
  refuses a handle from another process or an earlier generation *before* anything is
  sent (the v1 "state sent to the wrong process" class, ARCHITECTURE.md 8);
* pytanque's stdio mode has **no timeout at all** for ``start``/``goals``/``hash`` and
  only Rocq's ``Timeout`` for ``run``; so every call here runs under a Python-side wall
  clock that kills the whole process group on expiry (the v1 "hangs with no deadline"
  class);
* ``Timeout n`` is a Rocq vernacular control that takes an **integer** and is a syntax
  error before a bullet or a brace (``Timeout 5 -`` -> ``Syntax error``);
* one orphaned ``pet`` once held 372 GB, so the address space is capped with
  ``ulimit -v`` in a wrapper script -- and **never** with ``PR_SET_PDEATHSIG``, which
  is bound to the spawning *thread* and killed ``pet`` whenever an anyio worker thread
  exited (the v1 critical bug).  Lifetime is tied by :func:`atexit` + :meth:`close`
  (the MCP server adds its own parent watch).
"""

from __future__ import annotations

import atexit
import contextlib
import itertools
import math
import os
import socket
import subprocess
import tempfile
import threading
import time
import weakref
from collections import deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from pcp.config import env as penv
from pcp.errors import StateError, ToolchainError
from pcp.rocq.lexer import first_word, split_sentences
from pcp.util.io import atomic_write_text
from pcp.util.proc import kill_tree

DEFAULT_STEP_TIMEOUT = 30.0
DEFAULT_START_TIMEOUT = 600.0
DEFAULT_CALL_TIMEOUT = 120.0
DEFAULT_RSS_CAP_MB = 8192
#: Slack added to the Rocq-side ``Timeout`` so Rocq's graceful ``Timeout!`` error fires
#: before the watchdog has to kill the process.
TIMEOUT_GRACE_S = 15.0
#: Wire code petanque uses for a Rocq-level error (``Coq: ...``).
_COQ_ERROR_CODE = -32003


class TacticError(Exception):
    """A Rocq-level failure of one ``run`` -- a *result*, not a broken process.

    The session turns it into ``StepResult(ok=False)``.  Anything else that goes wrong
    in a call is a :class:`StateError`, so a dead process is never reported to a worker
    as "your tactic is wrong".
    """

    def __init__(self, message: str, *, code: int | None = None) -> None:
        super().__init__(message)
        self.message = message
        self.code = code

    @property
    def timed_out(self) -> bool:
        low = self.message.lower()
        return "timeout!" in low or "timed out" in low


@dataclass(frozen=True)
class HypView:
    names: tuple[str, ...]
    ty: str


@dataclass(frozen=True)
class GoalView:
    """One petanque goal: the printed IPM conclusion and the structured Coq context."""

    ty: str
    hyps: tuple[HypView, ...] = ()


@dataclass(frozen=True)
class StateHandle:
    """A petanque state bound to the process and generation that created it."""

    process: int
    generation: int
    st: int
    proof_finished: bool = False
    #: petanque's ``state/hash`` route value -- the one hash space pcp uses.  (The
    #: ``State.hash`` field is a *different* number for the same state.)
    state_hash: int | None = None
    #: Rocq feedback texts of the command that produced this state (the ``iDump`` channel).
    messages: tuple[str, ...] = ()
    raw: Any = field(default=None, repr=False, compare=False)

    def describe(self) -> str:
        return f"state {self.st} (petanque #{self.process}, generation {self.generation})"


# ------------------------------------------------------------------ Timeout wrapping


def coq_timeout(seconds: float | None) -> int | None:
    """Rocq's ``Timeout`` takes an integer number of seconds: ceil, never 0."""
    if seconds is None:
        return None
    return max(1, math.ceil(seconds))


def wrap_timeout(cmd: str, seconds: int) -> tuple[str, int]:
    """Prefix every bounded sentence of ``cmd`` with ``Timeout <seconds>``.

    The rule, verified against Rocq 9.1: a sentence gets the wrapper when it ends in
    ``.`` and is neither a bullet (``-``, ``+``, ``*``) nor a brace (``{``, ``}``,
    ``2: {``) -- ``Timeout`` before those is a syntax error, and they are focus
    operations that cannot loop.  A sentence that already starts with ``Timeout`` is
    left alone.  Goal selectors (``all: tac.``, ``2: tac.``) are fine after ``Timeout``.
    Returns the rewritten text and how many sentences were wrapped, so the caller can
    size the Python-side wall clock (``seconds`` per wrapped sentence).
    """
    sentences = split_sentences(cmd)
    if not sentences:
        return cmd, 0
    out: list[str] = []
    wrapped = 0
    for sent in sentences:
        code = sent.code.strip()
        if not code:
            continue
        if sent.is_bullet or sent.is_brace or not code.endswith(".") or first_word(code) == "Timeout":
            out.append(code)
            continue
        out.append(f"Timeout {seconds} {code}")
        wrapped += 1
    return " ".join(out), wrapped


# ------------------------------------------------------------------- wrapper script


def pet_wrapper(binary: str, mem_limit_mb: int) -> Path:
    """A ``pet`` (or ``pet-server``) wrapper that caps its address space, then execs.

    Written atomically (temp file + rename) into a per-uid, mode-0700 directory, so a
    concurrent process never execs a truncated or world-writable script, however many
    cold processes race to write it.  ``exec`` means the pid we hold *is* ``pet``,
    which is what :func:`kill_tree` needs.  No ``setpriv --pdeathsig``: see the module
    docstring.
    """
    real = str(Path(binary).resolve())
    root = Path(tempfile.gettempdir()) / f"pcp-pet-{os.getuid()}-{mem_limit_mb}"
    root.mkdir(mode=0o700, parents=True, exist_ok=True)
    wrapper = root / Path(real).name
    text = (
        "#!/bin/sh\n"
        "# Written by pcp: bound petanque's address space, then hand over.\n"
        f"ulimit -v {mem_limit_mb * 1024} 2>/dev/null || true\n"
        f'exec "{real}" "$@"\n'
    )
    current = wrapper.read_text(encoding="utf-8") if wrapper.exists() else None
    if current != text or not os.access(wrapper, os.X_OK):
        atomic_write_text(wrapper, text, mode=0o755)
    return wrapper


def _free_port() -> int:
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return int(s.getsockname()[1])


# ------------------------------------------------------------------------ process

_LIVE: weakref.WeakSet[PetProcess] = weakref.WeakSet()
_ids = itertools.count(1)


def _close_all() -> None:
    for proc in list(_LIVE):
        with contextlib.suppress(Exception):
            proc.close()


atexit.register(_close_all)


class PetProcess:
    """One ``pet`` process plus its pytanque client, spoken to under one lock.

    ``generation`` is bumped on every restart; handles from an earlier generation are
    refused.  ``files`` records which files this process has elaborated (coq-lsp caches
    the checked document: a second ``start`` costs 0.05 s against seconds cold), which is
    what the pool's file affinity is built on.
    """

    def __init__(
        self,
        workspace: str | Path,
        *,
        env: dict[str, str] | None = None,
        mem_limit_mb: int | None = None,
        rss_cap_mb: int = DEFAULT_RSS_CAP_MB,
        start_timeout: float = DEFAULT_START_TIMEOUT,
        step_timeout: float = DEFAULT_STEP_TIMEOUT,
        call_timeout: float = DEFAULT_CALL_TIMEOUT,
        mode: str | None = None,
    ) -> None:
        self.id = next(_ids)
        self.workspace = Path(workspace).resolve()
        self.env = dict(os.environ if env is None else env)
        self.mem_limit_mb = mem_limit_mb if mem_limit_mb is not None else penv.pet_mem_limit_mb()
        self.rss_cap_mb = rss_cap_mb
        if self.mem_limit_mb <= self.rss_cap_mb:
            raise ToolchainError(
                f"petanque hard memory limit ({self.mem_limit_mb} MB) must exceed the soft RSS cap "
                f"({self.rss_cap_mb} MB) so the graceful restart fires first"
            )
        self.start_timeout = start_timeout
        self.step_timeout = step_timeout
        self.call_timeout = call_timeout
        self.mode = mode or ("socket" if penv.pet_server_binary() else "stdio")
        self.generation = 0
        self.lock = threading.RLock()
        self.files: set[str] = set()
        self.started_at = 0.0
        self.calls = 0
        self._proc: subprocess.Popen[bytes] | None = None
        self._client: Any = None
        self._port = 0
        self._dead_reason: str | None = None
        self._watchdog_fired: str | None = None
        self._tail: deque[str] = deque(maxlen=200)

    # -- lifecycle -------------------------------------------------------------
    def spawn(self) -> None:
        """Start the process (idempotent while it is alive)."""
        with self.lock:
            if self.alive():
                return
            self._dead_reason = None
            self._watchdog_fired = None
            if self.mode == "socket":
                self._spawn_socket()
            else:
                self._spawn_stdio()
            self.started_at = time.time()
            _LIVE.add(self)
            self.call("set_workspace", False, str(self.workspace), timeout=self.call_timeout)

    def _spawn_stdio(self) -> None:
        pytanque = _pytanque()
        binary = penv.pet_binary()
        if binary is None:
            raise ToolchainError("no `pet` binary on PATH or in the pinned switch (run `pcp setup`; see `pcp doctor`)")
        wrapper = pet_wrapper(binary, self.mem_limit_mb)
        self._proc = subprocess.Popen(
            [str(wrapper)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            cwd=str(self.workspace),
            env=self.env,
            start_new_session=True,
        )
        self._drain(self._proc.stderr)
        client = pytanque.Pytanque(mode=pytanque.PytanqueMode.STDIO)
        client.process = self._proc
        self._client = client

    def _spawn_socket(self) -> None:
        pytanque = _pytanque()
        binary = penv.pet_server_binary()
        if binary is None:
            raise ToolchainError("no `pet-server` binary on PATH")
        wrapper = pet_wrapper(binary, self.mem_limit_mb)
        self._port = _free_port()
        self._proc = subprocess.Popen(
            [str(wrapper), "--port", str(self._port)],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            cwd=str(self.workspace),
            env=self.env,
            start_new_session=True,
        )
        self._drain(self._proc.stdout)
        deadline = time.monotonic() + 30.0
        last: Exception | None = None
        while time.monotonic() < deadline:
            if self._proc.poll() is not None:
                raise ToolchainError(f"pet-server exited during startup: {self.stderr_tail()[-2000:]}")
            try:
                client = pytanque.Pytanque("127.0.0.1", self._port)
                client.connect()
                self._client = client
                return
            except OSError as exc:
                last = exc
                time.sleep(0.2)
        self._kill()
        raise ToolchainError(f"could not connect to pet-server on :{self._port}: {last}")

    def _drain(self, stream: Any) -> None:
        """Keep a bounded tail of the child's log so a pipe can never fill and block it."""

        def pump() -> None:
            with contextlib.suppress(Exception):
                for line in iter(stream.readline, b""):
                    self._tail.append(line.decode("utf-8", "replace").rstrip())
            with contextlib.suppress(Exception):
                stream.close()

        threading.Thread(target=pump, name=f"pet-{self.id}-log", daemon=True).start()

    def stderr_tail(self) -> str:
        return "\n".join(self._tail)

    def alive(self) -> bool:
        """Running and not condemned (a watchdog kill counts as dead the moment it is decided)."""
        if self._dead_reason or self._proc is None or self._client is None:
            return False
        return self._proc.poll() is None

    @property
    def pid(self) -> int | None:
        return self._proc.pid if self._proc is not None else None

    def stop(self) -> None:
        """Terminate the process and close every pipe.  Idempotent.

        The kill happens *before* the lock is taken: a call blocked in ``readline``
        holds the lock, and waiting for it would defer ``close`` -- and with it
        ``atexit`` and the MCP parent watch -- until that call's own watchdog fired
        (up to ``start_timeout``).  Killing first makes the blocked call return EOF
        at once, and the blocked caller is told the process was closed, never that
        its tactic failed.
        """
        proc = self._proc
        if proc is not None:
            self._dead_reason = self._dead_reason or "closed"
            if proc.poll() is None:
                kill_tree(proc.pid)
        with self.lock:
            proc, self._proc, self._client = self._proc, None, None
            if proc is None:
                return
            if proc.poll() is None:
                kill_tree(proc.pid)
            for stream in (proc.stdin, proc.stdout):
                with contextlib.suppress(Exception):
                    if stream is not None:
                        stream.close()
            with contextlib.suppress(Exception):
                proc.wait(timeout=5)
            _LIVE.discard(self)

    close = stop

    def restart(self, reason: str = "restart") -> int:
        """Stop, bump the generation, start again.  Every earlier handle is now refused."""
        with self.lock:
            self.stop()
            self.generation += 1
            self.files.clear()
            self._dead_reason = None
            self.spawn()
            return self.generation

    def _kill(self, reason: str | None = None) -> None:
        if reason:
            self._dead_reason = reason  # before the kill: the blocked caller wakes up as soon as it lands
        proc = self._proc
        if proc is not None and proc.poll() is None:
            kill_tree(proc.pid)

    # -- health ----------------------------------------------------------------
    def rss_mb(self) -> int:
        if self._proc is None:
            return 0
        try:
            with open(f"/proc/{self._proc.pid}/statm", encoding="ascii") as fh:
                pages = int(fh.read().split()[1])
            return pages * os.sysconf("SC_PAGE_SIZE") // (1024 * 1024)
        except (OSError, ValueError, IndexError):
            return 0

    def healthy(self) -> bool:
        return self.alive() and self.rss_mb() <= self.rss_cap_mb

    @property
    def dead_reason(self) -> str | None:
        if self.alive():
            return None
        if self._dead_reason:
            return self._dead_reason
        if self._proc is not None:
            return f"exited with code {self._proc.poll()}"
        return "not started"

    # -- the one choke point ---------------------------------------------------
    def check_handle(self, handle: StateHandle) -> None:
        """Refuse a handle this process cannot own, before anything is sent."""
        if handle.process != self.id:
            raise StateError(
                f"{handle.describe()} was created by petanque process #{handle.process}, not #{self.id}; "
                "states never cross processes -- call proof_open again"
            )
        if handle.generation != self.generation:
            raise StateError(
                f"{handle.describe()} belongs to a petanque process that was restarted "
                f"(now generation {self.generation}); its states are gone -- call proof_open again"
            )

    def call(self, fn: str, *args: Any, timeout: float | None = None, **kwargs: Any) -> Any:
        """Invoke pytanque method ``fn`` under the lock and a Python-side wall clock.

        On expiry the watchdog kills the process group (a blocked ``readline`` then
        returns EOF), marks the process dead, and the caller gets a :class:`StateError`
        naming the call and the budget.  Rocq-level failures become :class:`TacticError`;
        every other exception becomes :class:`StateError`.
        """
        limit = self.call_timeout if timeout is None else timeout
        with self.lock:
            if not self.alive():
                raise StateError(f"petanque process #{self.id} is not running ({self.dead_reason}); call proof_open again")
            for arg in args:
                if isinstance(arg, StateHandle):
                    self.check_handle(arg)
            raw_args = [a.raw if isinstance(a, StateHandle) else a for a in args]
            client = self._client
            generation = self.generation
            self._watchdog_fired = None
            timer = threading.Timer(limit, self._on_timeout, args=(generation, fn, limit))
            timer.daemon = True
            timer.start()
            self.calls += 1
            try:
                return getattr(client, fn)(*raw_args, **kwargs)
            except Exception as exc:  # noqa: BLE001 -- translated below, never swallowed
                raise self._translate(exc, fn) from None
            finally:
                timer.cancel()

    def _on_timeout(self, generation: int, fn: str, limit: float) -> None:
        if generation != self.generation:
            return
        self._watchdog_fired = (
            f"petanque call `{fn}` exceeded its {limit:g} s wall clock; the process was killed and "
            "every state it held is gone -- call proof_open again"
        )
        self._kill(self._watchdog_fired)

    def _translate(self, exc: Exception, fn: str) -> Exception:
        if self._watchdog_fired:
            return StateError(self._watchdog_fired)
        code = getattr(exc, "code", None)
        message = getattr(exc, "message", None)
        text = message if isinstance(message, str) and message else f"{type(exc).__name__}: {exc}"
        if code == _COQ_ERROR_CODE and fn == "run":
            return TacticError(text, code=code)
        if not self.alive():
            if self._dead_reason == "closed":
                return StateError(f"petanque process #{self.id} was closed during `{fn}`; call proof_open again")
            self._dead_reason = self._dead_reason or f"died during `{fn}`: {text[:200]}"
            tail = self.stderr_tail()[-1000:]
            suffix = f"\n{tail}" if tail else ""
            return StateError(f"petanque process #{self.id} died during `{fn}`: {text[:300]}{suffix} -- call proof_open again")
        return StateError(f"petanque `{fn}` failed: {text[:500]}")

    # -- typed calls -----------------------------------------------------------
    def _handle(self, raw: Any, *, state_hash: int | None) -> StateHandle:
        return StateHandle(
            process=self.id,
            generation=self.generation,
            st=int(raw.st),
            proof_finished=bool(getattr(raw, "proof_finished", False)),
            state_hash=state_hash,
            messages=tuple(text for _, text in getattr(raw, "feedback", []) or []),
            raw=raw,
        )

    def start(
        self, file: str | Path, thm: str, pre_commands: str | None = None, *, timeout: float | None = None
    ) -> StateHandle:
        """``petanque/start``: elaborate the file prefix and open ``thm``."""
        path = str(Path(file).resolve())
        with self.lock:
            budget = self.start_timeout if timeout is None else timeout
            try:
                raw = self.call("start", path, thm, pre_commands, timeout=budget)
            except TacticError as exc:  # start has no tactic: a Rocq error here is an open failure
                raise StateError(f"petanque could not open {thm} in {path}: {exc.message}") from None
            self.files.add(path)
            h = self.call("state_hash", raw, timeout=self.call_timeout)
            return self._handle(raw, state_hash=int(h))

    def run(self, state: StateHandle, cmd: str, *, timeout: float | None = None, with_hash: bool = True) -> StateHandle:
        """``petanque/run`` with the Rocq ``Timeout`` wrapper (:func:`wrap_timeout`).

        Raises :class:`TacticError` for a Rocq-level failure (including ``Timeout!``).
        """
        seconds = coq_timeout(self.step_timeout if timeout is None else timeout) or 1
        wrapped, n = wrap_timeout(cmd, seconds)
        wall = seconds * max(1, n) + TIMEOUT_GRACE_S
        with self.lock:
            raw = self.call("run", state, wrapped, timeout=wall)
            h = int(self.call("state_hash", raw, timeout=self.call_timeout)) if with_hash else None
            return self._handle(raw, state_hash=h)

    def goals(self, state: StateHandle, *, timeout: float | None = None) -> list[GoalView]:
        raw = self.call("goals", state, timeout=timeout) or []
        return [
            GoalView(ty=g.ty, hyps=tuple(HypView(names=tuple(h.names), ty=h.ty) for h in (g.hyps or [])))
            for g in raw
        ]

    def premises(self, state: StateHandle, *, timeout: float | None = None) -> Any:
        return self.call("premises", state, timeout=timeout)

    def ast(self, state: StateHandle, text: str, *, timeout: float | None = None) -> Any:
        return self.call("ast", state, text, timeout=timeout)

    def state_hash(self, state: StateHandle, *, timeout: float | None = None) -> int:
        return int(self.call("state_hash", state, timeout=timeout))

    def state_equal(self, a: StateHandle, b: StateHandle, *, timeout: float | None = None) -> bool:
        pytanque = _pytanque()
        return bool(self.call("state_equal", a, b, pytanque.client.InspectPhysical, timeout=timeout))

    def __repr__(self) -> str:
        return f"<PetProcess #{self.id} gen={self.generation} pid={self.pid} {self.mode}>"


def _pytanque() -> Any:
    """pytanque, imported lazily: pcp-orch must never need it (ARCHITECTURE.md 1)."""
    try:
        import pytanque
        import pytanque.client  # noqa: F401 -- makes `pytanque.client` an attribute
    except ImportError as exc:  # pragma: no cover -- environment-specific
        raise ToolchainError(f"pytanque is not installed: {exc}") from None
    return pytanque

