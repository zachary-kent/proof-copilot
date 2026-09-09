"""Supervision: the run outlives its process (PLAN.md 8.11 "it never wedges", 11).

"Having to restart a long run is very costly."  The graph already survives a crash
(:mod:`pcp.orch.prove.resume`); what did not survive was the *run*: an orchestrator
killed at 2 a.m. -- an OOM, a Python exception nobody caught, a laptop lid -- left the
window idle until someone typed ``pcp prove`` again.  ``pcp prove --supervise`` puts
a small, dumb loop between the operator and the run:

* the CLI re-execs itself **detached** (its own session, stdin from ``/dev/null``,
  output to ``supervisor.log``) and returns at once with the pid to watch;
* the detached supervisor runs the ordinary ``pcp prove`` as a child, once per try,
  and reads the child's **outcome file** -- written by the child on a normal return,
  integrated or not -- to tell "finished" from "died": exit codes cannot (a traceback
  and "ran but did not integrate" are both ``1``);
* a child that died is restarted after a backoff (10 s, 60 s, then 5 min), at most
  ``--max-restarts`` times; the graph resumes, the run lock (an ``flock``, released by
  the kernel with the dead process) is re-taken, and every restart is a graph event;
* Ctrl-C or SIGTERM to the supervisor kills the child's whole process group -- the
  workers, their ``coqc``, their MCP servers -- and leaves the graph resumable.

The supervisor is deliberately not clever: it does not read the graph to decide, it
does not retry usage errors (the child says ``finished`` for those too), and it
never holds the run lock itself.
"""

from __future__ import annotations

import asyncio
import contextlib
import os
import shlex
import signal
import time
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from pcp.util.io import ensure_dir, json_dump, json_load
from pcp.util.proc import run_async

__all__ = [
    "DEFAULT_MAX_RESTARTS",
    "EXIT_TERMINATED",
    "LOG_FILE",
    "OUTCOME_FILE",
    "PID_FILE",
    "RESTART_BACKOFF_S",
    "Supervisor",
    "read_outcome",
    "state_dir",
    "strip_flags",
    "write_outcome",
]

DEFAULT_MAX_RESTARTS = 20
RESTART_BACKOFF_S: tuple[float, ...] = (10.0, 60.0, 300.0)
LOG_FILE = "supervisor.log"
PID_FILE = "supervisor.pid"
OUTCOME_FILE = "outcome.json"
#: The conventional "terminated by SIGTERM" status.
EXIT_TERMINATED = 143


def state_dir(*, record_root: Path | None, run_id: str | None, workroot: Path) -> Path:
    """Where the supervisor keeps its log, pid file and the child's outcome:
    ``<record>/<run-id>/`` when recording (next to the attempts it supervised), else
    the workroot."""
    if record_root is not None and run_id:
        return Path(record_root) / run_id
    return Path(workroot)


def strip_flags(argv: Sequence[str], *, flags: Sequence[str] = (), valued: Sequence[str] = ()) -> list[str]:
    """``argv`` without the given boolean ``flags`` and without the ``valued`` options
    and their arguments (``--opt value`` and ``--opt=value`` alike)."""
    drop = set(flags)
    drop_valued = set(valued)
    out: list[str] = []
    skip = False
    for arg in argv:
        if skip:
            skip = False
            continue
        name, has_eq, _ = arg.partition("=")
        if arg in drop or (has_eq and name in drop):
            continue
        if arg in drop_valued:
            skip = True
            continue
        if has_eq and name in drop_valued:
            continue
        out.append(arg)
    return out


def write_outcome(path: str | Path, **fields: Any) -> Path:
    """The child's word that it *returned* (``pcp prove`` writes this on every normal
    exit, integrated or not, usage error included).  Atomic: a half-written outcome
    would read as a crash and cost a restart."""
    return json_dump(Path(path), {"finished": True, "at": time.time(), **fields})


def read_outcome(path: str | Path) -> dict[str, Any] | None:
    p = Path(path)
    if not p.exists():
        return None
    try:
        data = json_load(p)
    except (ValueError, OSError):
        return None
    return data if isinstance(data, dict) and data.get("finished") else None


@dataclass
class Supervisor:
    """The loop (module docstring).  ``argv`` is the complete child command, already
    carrying ``--outcome-file <state>/outcome.json``."""

    argv: Sequence[str]
    state: Path
    graph: Path | None = None
    max_restarts: int = DEFAULT_MAX_RESTARTS
    backoff_s: Sequence[float] = RESTART_BACKOFF_S
    cwd: Path | None = None
    env: Mapping[str, str] | None = None

    @property
    def log(self) -> Path:
        return self.state / LOG_FILE

    @property
    def pid_file(self) -> Path:
        return self.state / PID_FILE

    @property
    def outcome(self) -> Path:
        return self.state / OUTCOME_FILE

    def run(self) -> int:
        return asyncio.run(self._run())

    # -- the loop ------------------------------------------------------------
    async def _run(self) -> int:
        ensure_dir(self.state)
        loop = asyncio.get_running_loop()
        stop = asyncio.Event()
        child: asyncio.Future[Any] | None = None

        def on_signal(signum: int) -> None:
            self._note(f"received {signal.Signals(signum).name}; terminating the child's process group")
            stop.set()
            if child is not None and not child.done():
                child.cancel()

        installed: list[signal.Signals] = []
        for sig in (signal.SIGTERM, signal.SIGINT):
            with contextlib.suppress(NotImplementedError, RuntimeError, ValueError):
                loop.add_signal_handler(sig, on_signal, sig)
                installed.append(sig)
        self._write_pid(child_pid=None)
        restarts = 0
        try:
            while True:
                with contextlib.suppress(OSError):
                    self.outcome.unlink()
                self._note(f"start #{restarts + 1}: {shlex.join(str(a) for a in self.argv)}")
                child = asyncio.ensure_future(
                    run_async(
                        list(self.argv), cwd=self.cwd, env=self.env, timeout=None,
                        on_chunk=self._chunk, on_spawn=lambda pid: self._write_pid(child_pid=pid),
                    )
                )
                try:
                    streamed = await child
                except asyncio.CancelledError:
                    self._note("the child's process group was killed; the graph is resumable -- re-run the same command")
                    return EXIT_TERMINATED
                if streamed.spawn_error:
                    self._note(f"cannot start the run at all: {streamed.spawn_error}")
                    return 2
                outcome = read_outcome(self.outcome)
                if outcome is not None:
                    code = int(outcome.get("exit_code", streamed.returncode if streamed.returncode is not None else 0))
                    self._note(f"finished: exit {code}" + (f" ({outcome.get('error')})" if outcome.get("error") else ""))
                    return code
                reason = _exit_reason(streamed.returncode)
                if restarts >= self.max_restarts:
                    self._note(f"the run {reason} and the restart budget ({self.max_restarts}) is spent; giving up. The graph is resumable.")
                    return 1
                restarts += 1
                delay = float(self.backoff_s[min(restarts - 1, len(self.backoff_s) - 1)]) if self.backoff_s else 0.0
                self._event("run.restarted", n=restarts, reason=reason, delay_s=delay, max_restarts=self.max_restarts)
                self._note(f"the run {reason}; restart {restarts}/{self.max_restarts} in {delay:.0f} s")
                if await _stopped(stop, delay):
                    self._note("terminated while waiting to restart; the graph is resumable")
                    return EXIT_TERMINATED
        finally:
            for sig in installed:
                with contextlib.suppress(Exception):
                    loop.remove_signal_handler(sig)
            with contextlib.suppress(OSError):
                self.pid_file.unlink()

    # -- bookkeeping -----------------------------------------------------------
    def _write_pid(self, *, child_pid: int | None) -> None:
        with contextlib.suppress(OSError):
            json_dump(self.pid_file, {"pid": os.getpid(), "child_pid": child_pid, "started_at": time.time(), "argv": [str(a) for a in self.argv]})

    def _chunk(self, chunk: bytes) -> None:
        with contextlib.suppress(OSError), open(self.log, "ab") as fh:
            fh.write(chunk)

    def _note(self, line: str) -> None:
        stamp = time.strftime("%Y-%m-%d %H:%M:%S")
        with contextlib.suppress(OSError), open(self.log, "a", encoding="utf-8") as fh:
            fh.write(f"[supervisor {stamp}] {line}\n")

    def _event(self, kind: str, **payload: Any) -> None:
        """A graph event, when there is a graph to write it to.  The supervisor never
        creates one (a child that died before ``build_graph`` has none) and a graph
        that cannot be opened never stops the loop."""
        if self.graph is None or not Path(self.graph).exists():
            return
        try:
            from pcp.orch.graph import Graph

            with Graph(self.graph) as g:
                g.emit(kind, None, **payload)
        except Exception as exc:  # noqa: BLE001 -- see the docstring
            self._note(f"could not record {kind} in the graph: {type(exc).__name__}: {exc}")


async def _stopped(stop: asyncio.Event, delay: float) -> bool:
    """Wait ``delay`` seconds unless ``stop`` is set first; ``True`` when it was."""
    if delay <= 0:
        return stop.is_set()
    try:
        await asyncio.wait_for(stop.wait(), timeout=delay)
    except TimeoutError:
        return False
    return True


def _exit_reason(rc: int | None) -> str:
    if rc is None:
        return "ended without an exit status"
    if rc < 0:
        try:
            return f"was killed by {signal.Signals(-rc).name}"
        except ValueError:
            return f"was killed by signal {-rc}"
    return f"exited with status {rc} without finishing"
