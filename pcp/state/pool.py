"""A bounded pool of ``pet`` processes with **pinned** sessions (PLAN.md 6; ARCHITECTURE.md 6).

A pet with Iris loaded costs 1-2 GB and executes tactics serially, so there are a
handful of processes and many logical sessions over them.  Petanque ids are per
process, so a session that borrowed *any* free process per call would silently run
tactics against another lemma's state.  Instead a session is bound at ``open`` to the
process that elaborates its file (file affinity: coq-lsp caches the checked document,
22 s -> 0.3 s) and every later call goes to that process -- never to another one.

Health is checked only *between* calls; a restart bumps the process generation and
marks every session bound to it as lost, so the next call on such a session fails with
a clear ``StateError`` instead of a stale id being reused.

A process also goes stale when a project library it loaded is rebuilt: it keeps the
old ``.vo`` (``pcp.rocq.deps``, session 5, issue 37).  New sessions never land on a
stale process; when the pool is full, the least-loaded stale one is restarted, and its
sessions are told why.
"""

from __future__ import annotations

import contextlib
import threading
import weakref
from collections.abc import Iterator
from pathlib import Path
from typing import Any

from pcp.errors import StateError
from pcp.rocq import deps
from pcp.state.petanque import DEFAULT_STEP_TIMEOUT, PetProcess
from pcp.state.session import ProofSession

DEFAULT_ACQUIRE_TIMEOUT = 600.0


class SessionPool:
    """At most ``size`` processes, spawned lazily; sessions pinned by file affinity."""

    def __init__(
        self,
        workspace: str | Path,
        size: int = 2,
        *,
        acquire_timeout: float = DEFAULT_ACQUIRE_TIMEOUT,
        **cfg: Any,
    ) -> None:
        self.workspace = Path(workspace).resolve()
        self.size = max(1, int(size))
        self.acquire_timeout = acquire_timeout
        self.cfg = dict(cfg)
        self._lock = threading.Lock()
        self._processes: list[PetProcess] = []
        self._sessions: dict[int, list[weakref.ReferenceType[ProofSession]]] = {}
        #: Every session opened here, so ``close`` releases their twins.
        self._opened: weakref.WeakSet[ProofSession] = weakref.WeakSet()
        #: Per process id: the project ``.vo`` files its sessions loaded, with the mtime
        #: each had when it was loaded.
        self._libraries: dict[int, dict[Path, float | None]] = {}
        self._closed = False
        #: Per process id: why it was last restarted for stale libraries, until the open
        #: that caused it has picked the reason up (``ProofSession.refreshed``).
        self._refreshed: dict[int, str] = {}

    # -- processes -------------------------------------------------------------
    @property
    def processes(self) -> list[PetProcess]:
        return list(self._processes)

    def _spawn(self) -> PetProcess:
        proc = PetProcess(self.workspace, **self.cfg)
        proc.spawn()
        self._processes.append(proc)
        self._sessions[proc.id] = []
        return proc

    def process_for(self, file: str | Path) -> PetProcess:
        """The process a session on ``file`` should be pinned to.

        A process that has already elaborated ``file`` wins outright; otherwise a new
        process while the pool has room; otherwise the least-loaded one.
        """
        if self._closed:
            raise StateError("the petanque pool is closed")
        key = str(Path(file).resolve())
        with self._lock:
            stale = {p.id: changed for p in self._processes if (changed := self._changed(p.id))}
            fresh = [p for p in self._processes if p.id not in stale]
            warm = [p for p in fresh if key in p.files and p.alive()]
            if warm:
                return min(warm, key=self._load)
            if len(self._processes) < self.size:
                return self._spawn()
            if fresh:
                return min(fresh, key=self._load)
            victim = min(self._processes, key=self._load)
        self.refresh(victim, stale[victim.id])
        return victim

    def _changed(self, pid: int) -> list[Path]:
        """The libraries process ``pid`` loaded that changed on disk since."""
        return [path for path, when in self._libraries.get(pid, {}).items() if deps.mtime(path) != when]

    def changed_libraries(self, session: ProofSession) -> list[Path]:
        """The libraries ``session``'s file loads that were rebuilt after its process loaded them."""
        process = session.process
        if process is None:
            return []
        seen = self._libraries.get(process.id, {})
        mine = getattr(session, "libraries", None) or []
        return [path for path in mine if path in seen and deps.mtime(path) != seen[path]]

    def refresh(self, process: PetProcess, changed: list[Path]) -> None:
        """Restart ``process`` because libraries it loaded were rebuilt; its sessions are lost, saying so."""
        names = ", ".join(p.name for p in changed[:3]) + (f" and {len(changed) - 3} more" if len(changed) > 3 else "")
        reason = f"{names} changed on disk after this petanque process loaded {'it' if len(changed) == 1 else 'them'}"
        with process.lock:
            process.restart(reason)
            self._libraries[process.id] = {}
            for ref in self._sessions.get(process.id, []):
                session = ref()
                if session is not None and session.started:
                    session.mark_lost(f"petanque restarted ({reason})")
            self._sessions[process.id] = [r for r in self._sessions.get(process.id, []) if (x := r()) is not None and not x.started]
            self._refreshed[process.id] = reason

    def note_libraries(self, session: ProofSession, file: str | Path) -> None:
        """Record the project libraries ``file`` loads against ``session``'s process."""
        process = session.process
        if process is None:
            return
        try:
            files = deps.library_files(file)
        except Exception:  # noqa: BLE001 -- staleness tracking never costs the open
            return
        session.libraries = files  # type: ignore[attr-defined]
        with self._lock:
            table = self._libraries.setdefault(process.id, {})
            for path in files:
                table.setdefault(path, deps.mtime(path))

    def _load(self, proc: PetProcess) -> int:
        return sum(1 for ref in self._sessions.get(proc.id, []) if ref() is not None)

    @contextlib.contextmanager
    def acquire(self, process: PetProcess, timeout: float | None = None) -> Iterator[PetProcess]:
        """Hold ``process`` for one call.  Bounded: never blocks forever.

        Two threads cannot interleave calls on one ``pet`` (its protocol is strictly
        request/response); the wait is bounded so a wedged call elsewhere surfaces as an
        error instead of deadlocking the whole server.
        """
        if self._closed:
            raise StateError("the petanque pool is closed")
        limit = self.acquire_timeout if timeout is None else timeout
        if not process.lock.acquire(timeout=limit):
            raise StateError(
                f"petanque process #{process.id} is busy: another call has not returned within {limit:g} s"
            )
        try:
            self.ensure_healthy(process)
            yield process
        finally:
            process.lock.release()

    def ensure_healthy(self, process: PetProcess) -> bool:
        """Restart ``process`` if it is dead or over its soft RSS cap; returns True if it did.

        Only ever called between calls (under the process lock).  Every session bound
        to the process is marked lost with the reason, so no stale id is ever sent.
        """
        with process.lock:
            if process.healthy():
                return False
            reason = process.dead_reason or f"RSS {process.rss_mb()} MB exceeded the {process.rss_cap_mb} MB cap"
            process.restart(reason)
            self._libraries[process.id] = {}
            # A session that has not started holds no state ids, so it cannot go
            # stale: it is the open that triggered this restart (after a killed
            # `start`, the next open lands on the dead process) and stays registered.
            keep = []
            for ref in self._sessions.get(process.id, []):
                session = ref()
                if session is None:
                    continue
                if session.started:
                    session.mark_lost(f"petanque restarted ({reason})")
                else:
                    keep.append(ref)
            self._sessions[process.id] = keep
            return True

    # -- sessions --------------------------------------------------------------
    def open(
        self,
        file: str | Path,
        thm: str,
        *,
        pre_commands: str | None = None,
        stub_prefix: bool = False,
        step_timeout: float | None = None,
        lru_size: int = 512,
        start: bool = False,
    ) -> ProofSession:
        """A session for ``thm`` in ``file``, pinned to a process by file affinity.

        ``stub_prefix`` opens the statements-only twin (``pcp.rocq.assemble.stubbed_twin``),
        so affinity is computed on the twin's path -- that is the file petanque sees.
        The twin is removed when the last session using it closes (``ProofSession.close``
        or this pool's ``close``).
        ``start`` runs ``petanque/start`` immediately.
        """
        session = ProofSession(
            self,
            None,
            file,
            thm,
            pre_commands=pre_commands,
            step_timeout=self.cfg.get("step_timeout", DEFAULT_STEP_TIMEOUT) if step_timeout is None else step_timeout,
            lru_size=lru_size,
            stub_prefix=stub_prefix,
        )
        try:
            process = self.process_for(session.file)
        except BaseException:
            session.close()
            raise
        self._opened.add(session)
        session.bind(process)
        self.register(session)
        session.refreshed = self._refreshed.pop(process.id, None)  # type: ignore[attr-defined]
        self.note_libraries(session, file)
        if start:
            session.start()
        return session

    def register(self, session: ProofSession) -> None:
        """Track ``session`` so a restart of its process can mark it lost."""
        if session.process is None:
            return
        with self._lock:
            refs = self._sessions.setdefault(session.process.id, [])
            refs[:] = [r for r in refs if r() is not None]
            refs.append(weakref.ref(session))

    # -- lifecycle -------------------------------------------------------------
    def close(self) -> None:
        """Stop every process and close every session (removing their twins).
        Idempotent; safe from ``atexit``."""
        with self._lock:
            if self._closed:
                return
            self._closed = True
            procs, self._processes = self._processes, []
            opened = list(self._opened)
        for session in opened:
            with contextlib.suppress(Exception):
                session.close()
        for proc in procs:
            with contextlib.suppress(Exception):
                proc.close()

    def __enter__(self) -> SessionPool:
        return self

    def __exit__(self, *exc: object) -> None:
        self.close()
