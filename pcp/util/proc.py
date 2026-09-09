"""Subprocess execution with the guarantees the rest of the tree relies on.

* every child runs in its **own session** (``start_new_session=True``), so a timeout
  kills the whole process tree -- ``coqc`` under ``pcp check`` under ``claude`` included --
  instead of orphaning it;
* every child is **reaped**;
* output is captured **incrementally**, so a process killed at its deadline still
  yields everything it wrote (the only witness a hung worker leaves behind);
* the result says whether it timed out, what it returned, and how long it took.

Nothing else in the tree calls ``subprocess`` directly except ``pcp.state.petanque``,
which owns a long-lived ``pet`` process and uses :func:`kill_tree` from here.
"""

from __future__ import annotations

import asyncio
import contextlib
import os
import signal
import subprocess
import time
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class Completed:
    argv: list[str]
    returncode: int | None
    stdout: str
    stderr: str
    timed_out: bool = False
    elapsed_s: float = 0.0
    #: Set when the binary could not be executed at all.
    spawn_error: str = ""

    @property
    def ok(self) -> bool:
        return self.returncode == 0 and not self.timed_out and not self.spawn_error

    @property
    def output(self) -> str:
        return self.stdout + ("\n" + self.stderr if self.stderr else "")


def kill_tree(pid: int, *, grace_s: float = 2.0) -> None:
    """Terminate, then kill, the process group rooted at ``pid``.

    Children spawned with ``start_new_session=True`` are group leaders, so the group id
    is the pid.  Falls back to the single process if the group is already gone.
    """
    for sig, wait in ((signal.SIGTERM, grace_s), (signal.SIGKILL, 0.0)):
        try:
            os.killpg(pid, sig)
        except ProcessLookupError:
            return
        except PermissionError:
            with contextlib.suppress(ProcessLookupError, PermissionError):
                os.kill(pid, sig)
        if wait:
            deadline = time.monotonic() + wait
            while time.monotonic() < deadline:
                try:
                    os.killpg(pid, 0)
                except ProcessLookupError:
                    return
                time.sleep(0.05)


def _env(env: Mapping[str, str] | None, extra: Mapping[str, str] | None) -> dict[str, str] | None:
    if env is None and extra is None:
        return None
    base = dict(os.environ if env is None else env)
    if extra:
        base.update(extra)
    return base


def run(
    argv: Sequence[str],
    *,
    cwd: str | Path | None = None,
    timeout: float | None = None,
    stdin: str | bytes | None = None,
    env: Mapping[str, str] | None = None,
    extra_env: Mapping[str, str] | None = None,
    merge_stderr: bool = False,
) -> Completed:
    """Run ``argv`` to completion (blocking).  Never raises for an ordinary failure."""
    argv = [str(a) for a in argv]
    started = time.perf_counter()
    data = stdin.encode("utf-8") if isinstance(stdin, str) else stdin
    try:
        proc = subprocess.Popen(
            argv,
            cwd=str(cwd) if cwd is not None else None,
            stdin=subprocess.PIPE if data is not None else subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT if merge_stderr else subprocess.PIPE,
            env=_env(env, extra_env),
            start_new_session=True,
        )
    except (FileNotFoundError, PermissionError, OSError) as exc:
        return Completed(argv, None, "", "", spawn_error=f"{argv[0]}: {exc}", elapsed_s=time.perf_counter() - started)
    try:
        out, err = proc.communicate(input=data, timeout=timeout)
        timed_out = False
    except subprocess.TimeoutExpired:
        kill_tree(proc.pid)
        out, err = proc.communicate()
        timed_out = True
    return Completed(
        argv,
        proc.returncode,
        (out or b"").decode("utf-8", "replace"),
        (err or b"").decode("utf-8", "replace"),
        timed_out=timed_out,
        elapsed_s=time.perf_counter() - started,
    )


@dataclass
class Streamed:
    """What :func:`run_async` returns: like :class:`Completed`, but the buffer is live."""

    argv: list[str]
    returncode: int | None = None
    buffer: bytearray = field(default_factory=bytearray)
    timed_out: bool = False
    elapsed_s: float = 0.0
    spawn_error: str = ""
    #: The child's pid (its process-group id too: every child leads its own session).
    pid: int | None = None

    @property
    def text(self) -> str:
        return bytes(self.buffer).decode("utf-8", "replace")

    @property
    def ok(self) -> bool:
        return self.returncode == 0 and not self.timed_out and not self.spawn_error


async def run_async(
    argv: Sequence[str],
    *,
    cwd: str | Path | None = None,
    timeout: float | None = None,
    stdin: str | bytes | None = None,
    env: Mapping[str, str] | None = None,
    extra_env: Mapping[str, str] | None = None,
    on_chunk=None,
    on_spawn=None,
) -> Streamed:
    """Run ``argv`` with incremental capture of merged stdout/stderr.

    On timeout the whole process group is killed and whatever was captured is
    returned with ``timed_out=True``.  ``on_chunk(bytes)`` is called for each chunk;
    ``on_spawn(pid)`` once the child exists (a supervisor records it so a signal to
    the supervisor can name the group it is about to kill).
    """
    argv = [str(a) for a in argv]
    result = Streamed(argv)
    started = time.perf_counter()
    data = stdin.encode("utf-8") if isinstance(stdin, str) else stdin
    try:
        proc = await asyncio.create_subprocess_exec(
            *argv,
            cwd=str(cwd) if cwd is not None else None,
            stdin=asyncio.subprocess.PIPE if data is not None else asyncio.subprocess.DEVNULL,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.STDOUT,
            env=_env(env, extra_env),
            start_new_session=True,
        )
    except (FileNotFoundError, PermissionError, OSError) as exc:
        result.spawn_error = f"{argv[0]}: {exc}"
        result.elapsed_s = time.perf_counter() - started
        return result
    result.pid = proc.pid
    if on_spawn is not None:
        on_spawn(proc.pid)

    async def pump() -> None:
        if data is not None and proc.stdin is not None:
            proc.stdin.write(data)
            with contextlib.suppress(BrokenPipeError, ConnectionResetError):
                await proc.stdin.drain()
            proc.stdin.close()
        assert proc.stdout is not None
        while True:
            chunk = await proc.stdout.read(65536)
            if not chunk:
                break
            result.buffer.extend(chunk)
            if on_chunk is not None:
                on_chunk(chunk)
        await proc.wait()

    try:
        await asyncio.wait_for(pump(), timeout=timeout)
        result.returncode = proc.returncode
    except TimeoutError:
        result.timed_out = True
        await asyncio.to_thread(kill_tree, proc.pid)
        with contextlib.suppress(Exception):
            await asyncio.wait_for(proc.wait(), timeout=5)
        result.returncode = proc.returncode
    except asyncio.CancelledError:
        await asyncio.to_thread(kill_tree, proc.pid)
        with contextlib.suppress(Exception):
            await asyncio.wait_for(proc.wait(), timeout=5)
        raise
    result.elapsed_s = time.perf_counter() - started
    return result


def spawn_detached(
    argv: Sequence[str],
    *,
    log: str | Path,
    cwd: str | Path | None = None,
    env: Mapping[str, str] | None = None,
) -> int:
    """Start ``argv`` in its own session, stdin from ``/dev/null``, stdout and stderr
    appended to ``log``, and return its pid **without waiting**.

    The one deliberate exception to "every child is reaped": the child is meant to
    outlive this process (the run supervisor, PLAN.md 8.11 "it never wedges"), so it
    is reparented to init when we exit and init reaps it.  ``start_new_session`` is
    the ``setsid``: the terminal's hangup and Ctrl-C never reach it.
    """
    argv = [str(a) for a in argv]
    log_path = Path(log)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with open(log_path, "ab") as fh:
        proc = subprocess.Popen(  # noqa: S603 -- the one place a child is not waited for
            argv,
            cwd=str(cwd) if cwd is not None else None,
            stdin=subprocess.DEVNULL,
            stdout=fh,
            stderr=subprocess.STDOUT,
            env=_env(env, None),
            start_new_session=True,
            close_fds=True,
        )
    return proc.pid
