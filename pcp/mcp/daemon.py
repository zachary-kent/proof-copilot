"""The MCP tools without MCP: one long-lived daemon per workspace on a Unix socket.

The plugin's tools (``proof_open``, ``proof_step``, ...) only appear after a client
restart, and a proof session lives only as long as the process holding its ``pet``, so
a one-shot ``pcp`` command cannot step a proof.  ``pcp tools`` fills the gap: a daemon
serves :func:`pcp.mcp.server.tool_functions` -- the very functions the MCP server
registers, so the two surfaces cannot drift -- and a client prints one call's JSON.

Why each piece is the way it is:

* **One daemon per workspace**, found by path: ``<workspace>/.pcp/tools/`` (mode 0700,
  so only the owner can reach the socket) holds ``sock``, ``lock`` and ``pid``; the log
  is ``<workspace>/.pcp/tools.log``.  A socket path past the kernel's ~108-byte limit
  moves to a per-user 0700 directory under the temp dir, keyed by the workspace.
* **The lock, not the socket, says "a daemon is alive"**: the daemon holds an
  exclusive ``flock`` for its whole life, so two clients auto-starting at once yield one
  daemon, and a socket file left by a killed daemon is stale by construction and is
  replaced.
* **Threaded**: ``PcpServer`` is thread-safe (a table lock plus one lock per session),
  so a slow ``proof_trace`` does not block ``status`` or ``stop``.
* **Never orphans ``pet``**: ``stop``, SIGTERM/SIGINT/SIGHUP and the idle timeout (no
  call in flight for ``idle_s``; default 2 h) all end in ``PcpServer.close``.

Wire format: one JSON object per line each way.  Requests are ``{"op": "call", "tool":
..., "args": {...}}``, ``{"op": "ping"}`` and ``{"op": "stop"}``; replies are ``{"ok":
true, ...}`` or ``{"ok": false, "error": ...}``.
"""

from __future__ import annotations

import contextlib
import errno
import fcntl
import hashlib
import importlib
import inspect
import json
import logging
import os
import signal
import socket
import socketserver
import threading
import time
from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from pcp.errors import PcpError, StateError
from pcp.util.paths import tmpdir

_log = logging.getLogger("pcp.tools")

DEFAULT_IDLE_S = 2 * 3600.0
DEFAULT_START_TIMEOUT_S = 60.0
DEFAULT_FACTORY = "pcp.mcp.daemon:pcp_tools"
#: ``sockaddr_un.sun_path`` is 108 bytes on Linux (104 on macOS), NUL included.
_MAX_SOCKET_PATH = 100


class DaemonRunning(PcpError):
    """Another daemon already holds this workspace's lock."""


@dataclass(frozen=True)
class DaemonPaths:
    workspace: Path
    dir: Path
    socket: Path
    lock: Path
    pid: Path
    log: Path


def paths_for(workspace: str | Path) -> DaemonPaths:
    ws = Path(workspace).resolve()
    state = ws / ".pcp" / "tools"
    sock = state / "sock"
    if len(os.fsencode(str(sock))) > _MAX_SOCKET_PATH:
        key = hashlib.sha256(os.fsencode(str(ws))).hexdigest()[:16]
        sock = tmpdir() / f"pcp-tools-{os.getuid()}" / f"{key}.sock"
    return DaemonPaths(ws, state, sock, state / "lock", state / "pid", ws / ".pcp" / "tools.log")


def _private_dir(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)
    os.chmod(path, 0o700)


# ------------------------------------------------------------------ tool sets


@dataclass
class ToolSet:
    """What a daemon serves: named functions returning JSON strings, and how to stop them."""

    tools: dict[str, Callable[..., str]]
    close: Callable[[], None] = lambda: None
    describe: Callable[[], dict[str, Any]] = field(default=lambda: {})


def pcp_tools(workspace: Path) -> ToolSet:
    """The real tool set: ``tool_functions(PcpServer(workspace))``."""
    from pcp.mcp.server import PcpServer, tool_functions

    server = PcpServer(workspace)
    return ToolSet(tool_functions(server), close=server.close, describe=lambda: {"sessions": server.sessions})


def load_factory(spec: str) -> Callable[[Path], ToolSet]:
    """``module:function`` -> the function (tests serve fake tools this way)."""
    module, _, name = spec.partition(":")
    return getattr(importlib.import_module(module), name or "make")


def _signature(name: str, fn: Callable[..., Any]) -> str:
    # Annotations are strings under `from __future__ import annotations`; unquote them.
    params = []
    for p in inspect.signature(fn).parameters.values():
        text = p.name if p.annotation is inspect.Parameter.empty else f"{p.name}: {p.annotation}"
        params.append(text if p.default is inspect.Parameter.empty else f"{text} = {p.default!r}")
    return f"{name}({', '.join(params)})"


def tool_signatures(tools: dict[str, Callable[..., str]]) -> list[dict[str, str]]:
    return [
        {"name": name, "signature": _signature(name, fn),
         "summary": (inspect.getdoc(fn) or "").split("\n", 1)[0]}
        for name, fn in tools.items()
    ]


# --------------------------------------------------------------------- daemon


class _Handler(socketserver.StreamRequestHandler):
    server: _Server

    def handle(self) -> None:
        line = self.rfile.readline()
        if not line:
            return
        try:
            request = json.loads(line)
            if not isinstance(request, dict):
                raise ValueError("the request must be a JSON object")
            reply = self.server.daemon.answer(request)
        except ValueError as exc:
            reply = {"ok": False, "error": f"bad request: {exc}"}
        with contextlib.suppress(OSError):
            self.wfile.write((json.dumps(reply, ensure_ascii=False, default=str) + "\n").encode())
            self.wfile.flush()


class _Server(socketserver.ThreadingMixIn, socketserver.UnixStreamServer):
    daemon_threads = True
    daemon: ToolDaemon


class ToolDaemon:
    """Serve one :class:`ToolSet` on the workspace socket until stopped or idle."""

    def __init__(self, paths: DaemonPaths, tools: ToolSet, *, idle_s: float = DEFAULT_IDLE_S) -> None:
        self.paths = paths
        self.toolset = tools
        self.idle_s = idle_s
        self.started = time.time()
        self._last = time.monotonic()
        self._in_flight = 0
        self._state = threading.Lock()
        self._lock_fd: int | None = None
        self._server: _Server | None = None
        self._stopping = threading.Event()

    # -- lifecycle ---------------------------------------------------------
    def acquire(self) -> None:
        """Take the workspace lock.  Raises DaemonRunning when another daemon holds it."""
        if self._lock_fd is not None:
            return
        _private_dir(self.paths.dir)
        fd = os.open(self.paths.lock, os.O_RDWR | os.O_CREAT, 0o600)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as exc:
            os.close(fd)
            if exc.errno in (errno.EAGAIN, errno.EACCES):
                raise DaemonRunning(f"a pcp tools daemon already serves {self.paths.workspace}") from exc
            raise
        self._lock_fd = fd

    def listen(self) -> None:
        """Replace any stale socket and listen: from here on a ping means "ready"."""
        self.acquire()
        _private_dir(self.paths.socket.parent)
        # We hold the lock, so whatever socket file is there belongs to a dead daemon.
        with contextlib.suppress(FileNotFoundError):
            self.paths.socket.unlink()
        server = _Server(str(self.paths.socket), _Handler, bind_and_activate=False)
        server.daemon = self
        old = os.umask(0o177)
        try:
            server.server_bind()
        finally:
            os.umask(old)
        server.server_activate()
        self._server = server
        self.paths.pid.write_text(f"{os.getpid()}\n", encoding="utf-8")

    def serve(self) -> None:
        """Listen (unless already listening) and serve until stop/idle/signal; always cleans up."""
        try:
            if self._server is None:
                self.listen()
            assert self._server is not None
            threading.Thread(target=self._idle_watch, name="pcp-tools-idle", daemon=True).start()
            _log.info("pcp tools: serving %s on %s (pid %d)", self.paths.workspace, self.paths.socket, os.getpid())
            if not self._stopping.is_set():  # a signal during start-up
                self._server.serve_forever(poll_interval=0.2)
        finally:
            self.close()

    def stop(self) -> None:
        """Ask ``serve`` to return.  Safe from any thread, a signal handler included."""
        if self._stopping.is_set():
            return
        self._stopping.set()
        if self._server is not None:
            threading.Thread(target=self._server.shutdown, name="pcp-tools-stop", daemon=True).start()

    def install_signal_handlers(self) -> None:
        for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
            signal.signal(sig, lambda *_: self.stop())

    def close(self) -> None:
        """Release the socket, the pid file, the tool set and the lock.  Idempotent."""
        if self._server is not None:
            self._server.server_close()
            self._server = None
        for path in (self.paths.socket, self.paths.pid):
            with contextlib.suppress(FileNotFoundError):
                path.unlink()
        try:
            self.toolset.close()  # stops every pet: the reason stop/idle exist at all
        except Exception:  # noqa: BLE001 -- the lock must still be released
            _log.exception("pcp tools: closing the tool set failed")
        if self._lock_fd is not None:
            os.close(self._lock_fd)
            self._lock_fd = None
        _log.info("pcp tools: stopped")

    def _idle_watch(self) -> None:
        if self.idle_s <= 0:
            return
        tick = min(30.0, max(0.05, self.idle_s / 4))
        while not self._stopping.wait(tick):
            with self._state:
                idle = self._in_flight == 0 and time.monotonic() - self._last >= self.idle_s
            if idle:
                _log.info("pcp tools: idle for %.0fs, stopping", self.idle_s)
                self.stop()
                return

    # -- requests ----------------------------------------------------------
    def answer(self, request: dict[str, Any]) -> dict[str, Any]:
        op = request.get("op")
        if op == "ping":
            return {"ok": True, **self.status()}
        if op == "stop":
            self.stop()
            return {"ok": True, "stopping": True}
        if op != "call":
            return {"ok": False, "error": f"unknown op {op!r} (call | ping | stop)"}
        with self._state:
            self._in_flight += 1
        try:
            return self._call(str(request.get("tool", "")), request.get("args") or {})
        finally:
            with self._state:
                self._in_flight -= 1
                self._last = time.monotonic()

    def _call(self, tool: str, args: Any) -> dict[str, Any]:
        fn = self.toolset.tools.get(tool)
        if fn is None:
            return {"ok": False, "error": f"no tool {tool!r}; available: {', '.join(self.toolset.tools)}"}
        if not isinstance(args, dict):
            return {"ok": False, "error": "the arguments must be a JSON object"}
        try:
            inspect.signature(fn).bind(**args)
        except TypeError as exc:
            return {"ok": False, "error": f"{tool}: {exc}; signature: {_signature(tool, fn)}"}
        try:
            text = fn(**args)
        except Exception as exc:  # noqa: BLE001 -- one bad call never kills the daemon
            _log.exception("pcp tools: %s failed", tool)
            return {"ok": False, "error": f"{type(exc).__name__}: {exc}"}
        try:
            return {"ok": True, "result": json.loads(text)}
        except (TypeError, ValueError):
            return {"ok": True, "result": text}

    def status(self) -> dict[str, Any]:
        with self._state:
            idle = 0.0 if self._in_flight else time.monotonic() - self._last
            busy = self._in_flight
        try:
            extra = self.toolset.describe()
        except Exception:  # noqa: BLE001
            extra = {}
        return {
            "pid": os.getpid(), "workspace": str(self.paths.workspace), "socket": str(self.paths.socket),
            "uptime_s": round(time.time() - self.started, 1), "idle_s": round(idle, 1), "in_flight": busy,
            "idle_timeout_s": self.idle_s, **extra,
        }


# --------------------------------------------------------------------- client


def request(paths: DaemonPaths, payload: dict[str, Any], *, timeout: float | None = None) -> dict[str, Any]:
    """One round trip.  Raises ``ConnectionError``/``FileNotFoundError`` if nothing listens."""
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as s:
        s.settimeout(timeout)
        s.connect(str(paths.socket))
        s.sendall((json.dumps(payload, ensure_ascii=False) + "\n").encode())
        with s.makefile("rb") as fh:
            line = fh.readline()
    if not line:
        raise StateError("the pcp tools daemon closed the connection without answering (it died? see "
                         f"{paths.log})")
    reply: dict[str, Any] = json.loads(line)
    return reply


def ping(paths: DaemonPaths, *, timeout: float = 5.0) -> dict[str, Any] | None:
    """The daemon's status, or ``None`` when no live daemon answers (a stale socket included)."""
    try:
        return request(paths, {"op": "ping"}, timeout=timeout)
    except (OSError, ValueError, StateError):
        return None


def lock_held(paths: DaemonPaths) -> bool:
    """Is a daemon alive (starting, serving or shutting down) for this workspace?"""
    try:
        fd = os.open(paths.lock, os.O_RDWR)
    except FileNotFoundError:
        return False
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        return True
    finally:
        os.close(fd)
    return False


def daemon_argv(paths: DaemonPaths, *, idle_s: float, factory: str | None = None) -> list[str]:
    import sys

    argv = [sys.executable, "-m", "pcp.cli.main", "tools", "serve", "--workspace", str(paths.workspace),
            "--idle-timeout", str(idle_s)]
    if factory:
        argv += ["--factory", factory]
    return argv


def ensure_daemon(
    paths: DaemonPaths,
    *,
    idle_s: float = DEFAULT_IDLE_S,
    factory: str | None = None,
    env: dict[str, str] | None = None,
    timeout: float = DEFAULT_START_TIMEOUT_S,
) -> dict[str, Any]:
    """The running daemon's status, starting one (detached, logging to ``paths.log``) if needed."""
    status = ping(paths)
    if status is not None:
        return status
    pid: int | None = None
    if not lock_held(paths):
        from pcp.util.proc import spawn_detached

        _private_dir(paths.dir)
        pid = spawn_detached(daemon_argv(paths, idle_s=idle_s, factory=factory), log=paths.log,
                             cwd=str(paths.workspace), env=env)
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        status = ping(paths, timeout=2.0)
        if status is not None:
            return status
        if pid is not None and _exited(pid) and not lock_held(paths):
            break
        time.sleep(0.1)
    raise StateError(f"the pcp tools daemon did not come up for {paths.workspace}; last log lines:\n{log_tail(paths)}")


def _exited(pid: int) -> bool:
    try:
        done, _ = os.waitpid(pid, os.WNOHANG)
    except ChildProcessError:
        return True
    return done == pid


def log_tail(paths: DaemonPaths, lines: int = 20) -> str:
    try:
        text = paths.log.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return "(no log)"
    return "\n".join(text.splitlines()[-lines:])


def stop_daemon(paths: DaemonPaths, *, timeout: float = 60.0) -> bool:
    """Stop the daemon and wait until its process is gone; ``False`` if none ran.

    The lock is released only after the tool set closed (every pet stopped), and the
    process exits right after; waiting for both makes "stopped" mean it.
    """
    deadline = time.monotonic() + timeout
    status = ping(paths)
    pid = int(status["pid"]) if status and "pid" in status else None
    asked = False
    while time.monotonic() < deadline:
        if not asked:
            try:
                asked = bool(request(paths, {"op": "stop"}, timeout=10.0).get("ok"))
            except (OSError, ValueError, StateError):
                if not lock_held(paths):
                    with contextlib.suppress(FileNotFoundError):
                        paths.socket.unlink()  # a dead daemon's leftover
                    return False
                # Held but not answering: still starting, or already shutting down.
        if asked and not lock_held(paths) and (pid is None or pid == os.getpid() or not process_alive(pid)):
            return True
        time.sleep(0.1)
    raise StateError(f"the pcp tools daemon for {paths.workspace} did not stop within {timeout:.0f}s")


def process_alive(pid: int) -> bool:
    """Running (a zombie waiting to be reaped counts as gone)."""
    try:
        with open(f"/proc/{pid}/stat", encoding="ascii", errors="replace") as fh:
            return fh.read().rsplit(")", 1)[-1].split()[0] != "Z"
    except FileNotFoundError:
        return False
    except OSError:
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return False
        return True
