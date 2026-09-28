"""``pcp tools``: the per-workspace tool daemon and its client (pcp.mcp.daemon, issue 5/7)."""

from __future__ import annotations

import json
import os
import shutil
import socket
import stat
import subprocess
import sys
import threading
import time
from pathlib import Path

import pytest
from conftest import ROOT, SCRATCH, needs_petanque

from pcp.cli.cmd_tools import parse_call_args
from pcp.errors import UsageError
from pcp.mcp import daemon
from pcp.mcp.daemon import DaemonRunning, ToolDaemon, ToolSet, paths_for, ping, request, stop_daemon

FAKE = '''
import json, os
from pcp.mcp.daemon import ToolSet

def make(workspace):
    state = {"n": 0}

    def bump(by: int = 1) -> str:
        """Add to a counter that lives as long as the daemon."""
        state["n"] += by
        return json.dumps({"n": state["n"], "pid": os.getpid()})

    def boom() -> str:
        """Always raises."""
        raise RuntimeError("kaboom")

    def closer():
        (workspace / "closed").write_text("yes")

    return ToolSet({"bump": bump, "boom": boom}, close=closer)
'''


def _fake_tools(closed: list[str]) -> ToolSet:
    state = {"n": 0}

    def bump(by: int = 1) -> str:
        state["n"] += by
        return json.dumps({"n": state["n"]})

    def slow(seconds: float = 0.5) -> str:
        time.sleep(seconds)
        return json.dumps({"slept": seconds})

    return ToolSet({"bump": bump, "slow": slow}, close=lambda: closed.append("closed"),
                   describe=lambda: {"sessions": ["s1"]})


def _serve_in_thread(d: ToolDaemon) -> threading.Thread:
    d.listen()
    t = threading.Thread(target=d.serve, daemon=True)
    t.start()
    return t


def test_round_trip_call_ping_stop_and_cleanup(tmp_path: Path) -> None:
    paths = paths_for(tmp_path)
    closed: list[str] = []
    d = ToolDaemon(paths, _fake_tools(closed), idle_s=0)
    t = _serve_in_thread(d)
    assert stat.S_IMODE(paths.dir.stat().st_mode) == 0o700
    assert stat.S_IMODE(paths.socket.stat().st_mode) & 0o077 == 0
    assert request(paths, {"op": "call", "tool": "bump", "args": {"by": 2}}) == {"ok": True, "result": {"n": 2}}
    assert request(paths, {"op": "call", "tool": "bump", "args": {}})["result"] == {"n": 3}, "state persists"
    bad = request(paths, {"op": "call", "tool": "bump", "args": {"nope": 1}})
    assert bad["ok"] is False and "signature: bump(by: int = 1)" in bad["error"]
    assert "available: bump, slow" in request(paths, {"op": "call", "tool": "zap"})["error"]
    status = ping(paths)
    assert status is not None and status["pid"] == os.getpid() and status["sessions"] == ["s1"]
    assert stop_daemon(paths) is True
    t.join(5)
    assert not t.is_alive() and closed == ["closed"], "stop closes the tool set (and so every pet)"
    assert not paths.socket.exists() and not paths.pid.exists()
    assert ping(paths) is None and stop_daemon(paths) is False


def test_a_second_daemon_is_refused_while_the_first_holds_the_lock(tmp_path: Path) -> None:
    paths = paths_for(tmp_path)
    first = ToolDaemon(paths, _fake_tools([]), idle_s=0)
    t = _serve_in_thread(first)
    with pytest.raises(DaemonRunning):
        ToolDaemon(paths, _fake_tools([])).acquire()
    assert ping(paths) is not None, "the refused daemon did not unlink the live socket"
    stop_daemon(paths)
    t.join(5)


def test_a_stale_socket_from_a_dead_daemon_is_detected_and_replaced(tmp_path: Path) -> None:
    paths = paths_for(tmp_path)
    paths.dir.mkdir(parents=True)
    dead = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    dead.bind(str(paths.socket))
    dead.close()  # the file stays, nobody listens: what a SIGKILLed daemon leaves
    assert paths.socket.exists() and ping(paths) is None
    d = ToolDaemon(paths, _fake_tools([]), idle_s=0)
    t = _serve_in_thread(d)
    assert request(paths, {"op": "call", "tool": "bump"})["result"] == {"n": 1}
    stop_daemon(paths)
    t.join(5)


def test_the_idle_timeout_stops_the_daemon_but_never_mid_call(tmp_path: Path) -> None:
    paths = paths_for(tmp_path)
    closed: list[str] = []
    d = ToolDaemon(paths, _fake_tools(closed), idle_s=0.4)
    t = _serve_in_thread(d)
    # A call longer than the idle timeout completes: in-flight time is not idle time.
    assert request(paths, {"op": "call", "tool": "slow", "args": {"seconds": 1.0}})["result"] == {"slept": 1.0}
    t.join(10)
    assert not t.is_alive() and closed == ["closed"] and not paths.socket.exists()


def test_a_long_workspace_path_moves_the_socket_to_a_private_temp_dir(tmp_path: Path) -> None:
    deep = tmp_path / ("x" * 60) / ("y" * 60)
    deep.mkdir(parents=True)
    paths = paths_for(deep)
    assert not str(paths.socket).startswith(str(deep)) and len(str(paths.socket)) < 100
    assert paths.lock.parent == deep / ".pcp" / "tools" and paths.log == deep / ".pcp" / "tools.log"
    t = _serve_in_thread(ToolDaemon(paths, _fake_tools([]), idle_s=0))
    assert stat.S_IMODE(paths.socket.parent.stat().st_mode) == 0o700
    assert request(paths, {"op": "call", "tool": "bump"})["ok"]
    stop_daemon(paths)
    t.join(5)


def test_call_arguments_merge_json_and_key_value_pairs() -> None:
    args = parse_call_args('{"session": "s1"}', ["tactic=iIntros \"H\".", "budget=500", "script=[\"a\", \"b\"]"])
    assert args == {"session": "s1", "tactic": 'iIntros "H".', "budget": 500, "script": ["a", "b"]}
    with pytest.raises(UsageError):
        parse_call_args("[1]", None)
    with pytest.raises(UsageError):
        parse_call_args(None, ["novalue"])


def _pcp(*argv: str, cwd: Path, env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run([sys.executable, "-m", "pcp.cli.main", *argv], cwd=str(cwd), env=env,
                          capture_output=True, text=True, timeout=120, check=False)


def test_cli_call_autostarts_a_detached_daemon_that_outlives_the_client(tmp_path: Path) -> None:
    ws = tmp_path / "ws"
    (ws / "sub").mkdir(parents=True)
    (ws / "_CoqProject").write_text("-Q . T\n")
    mod = tmp_path / "mods"
    mod.mkdir()
    (mod / "pcp_fake_tools.py").write_text(FAKE)
    env = {**os.environ, "PYTHONPATH": os.pathsep.join([str(mod), str(ROOT)])}
    factory = ["--factory", "pcp_fake_tools:make"]
    # From a subdirectory: the workspace is the nearest _CoqProject's directory.
    first = _pcp("tools", "call", "bump", '{"by": 5}', *factory, cwd=ws / "sub", env=env)
    assert first.returncode == 0, first.stderr
    out1 = json.loads(first.stdout)
    assert out1["n"] == 5 and out1["pid"] != os.getpid()
    paths = paths_for(ws)
    try:
        second = _pcp("tools", "call", "bump", "--arg", "by=2", "--compact", *factory, cwd=ws, env=env)
        out2 = json.loads(second.stdout)
        assert out2 == {"n": 7, "pid": out1["pid"]}, "the same daemon answered, with its state"
        assert "\n" not in second.stdout.strip()
        boom = _pcp("tools", "call", "boom", *factory, cwd=ws, env=env)
        assert boom.returncode == 1 and "RuntimeError: kaboom" in boom.stderr
        status = _pcp("tools", "status", cwd=ws, env=env)
        assert status.returncode == 0 and json.loads(status.stdout)["pid"] == out1["pid"]
        assert paths.log.is_file()
    finally:
        stopped = _pcp("tools", "stop", cwd=ws, env=env)
    assert stopped.returncode == 0 and "stopped the daemon" in stopped.stderr
    assert (ws / "closed").read_text() == "yes" and not daemon.lock_held(paths)
    assert not daemon.process_alive(out1["pid"]), "stop waits for the daemon process to exit"
    none = _pcp("tools", "call", "bump", "--no-start", *factory, cwd=ws, env=env)
    assert none.returncode == 2 and "no pcp tools daemon" in none.stderr


# ---------------------------------------------------------------------- live


@needs_petanque
def test_live_proof_open_and_step_through_the_cli(tmp_path: Path) -> None:
    ws = tmp_path / "ws"
    ws.mkdir()
    for name in ("Basic.v", "_CoqProject"):
        shutil.copy(SCRATCH / name, ws / name)
    env = dict(os.environ)
    try:
        opened = _pcp("tools", "call", "proof_open", '{"file": "Basic.v", "lemma": "sep_comm"}', cwd=ws, env=env)
        assert opened.returncode == 0, opened.stderr
        sid = json.loads(opened.stdout)["session"]
        stepped = _pcp("tools", "call", "proof_step", "--arg", f"session={sid}", "--arg", 'tactic=iIntros "[HP HQ]".',
                       cwd=ws, env=env)
        out = json.loads(stepped.stdout)
        assert out["ok"] is True and {e["hyp"] for e in out["ledger"]} >= {"HP", "HQ"}, out
        status = json.loads(_pcp("tools", "status", cwd=ws, env=env).stdout)
        assert status["sessions"] == [sid]
    finally:
        _pcp("tools", "stop", cwd=ws, env=env)
    paths = paths_for(ws)
    assert not daemon.lock_held(paths)
