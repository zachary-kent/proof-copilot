"""The shared helpers: subprocesses that die with their tree, atomic files, slugs, locks."""

from __future__ import annotations

import asyncio
import os
import sys
import time
from pathlib import Path

import pytest

from pcp.errors import LockedError
from pcp.util.io import atomic_write_text, json_dump, json_load, slug
from pcp.util.locks import RunLock
from pcp.util.proc import run, run_async

SPAWN_AND_SLEEP = """
import os, subprocess, sys, time
child = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(100)"])
open(sys.argv[1], "w").write(str(child.pid))
sys.stdout.write("started\\n"); sys.stdout.flush()
time.sleep(100)
"""


def _alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    return True


def test_run_captures_and_reports_exit_code(tmp_path: Path) -> None:
    done = run([sys.executable, "-c", "import sys; print('out'); print('err', file=sys.stderr); sys.exit(3)"])
    assert done.returncode == 3 and not done.ok
    assert done.stdout.strip() == "out" and done.stderr.strip() == "err"


def test_run_missing_binary_is_a_result_not_an_exception() -> None:
    done = run(["/nonexistent/binary-xyz"])
    assert done.spawn_error and not done.ok and done.returncode is None


def test_run_timeout_kills_the_whole_process_tree(tmp_path: Path) -> None:
    pidfile = tmp_path / "child.pid"
    done = run([sys.executable, "-c", SPAWN_AND_SLEEP, str(pidfile)], timeout=2)
    assert done.timed_out
    assert "started" in done.stdout
    child = int(pidfile.read_text())
    deadline = time.time() + 5
    while _alive(child) and time.time() < deadline:
        time.sleep(0.1)
    assert not _alive(child), "the grandchild survived the timeout"


def test_run_async_streams_and_kills_tree(tmp_path: Path) -> None:
    pidfile = tmp_path / "child.pid"
    chunks: list[bytes] = []
    streamed = asyncio.run(run_async([sys.executable, "-c", SPAWN_AND_SLEEP, str(pidfile)], timeout=2, on_chunk=chunks.append))
    assert streamed.timed_out and "started" in streamed.text and chunks
    child = int(pidfile.read_text())
    deadline = time.time() + 5
    while _alive(child) and time.time() < deadline:
        time.sleep(0.1)
    assert not _alive(child)


def test_run_async_stdin_and_exit_code() -> None:
    streamed = asyncio.run(run_async([sys.executable, "-c", "import sys; print(sys.stdin.read().upper()); sys.exit(4)"], stdin="hi"))
    assert streamed.returncode == 4 and streamed.text.strip() == "HI"


def test_atomic_write_and_json_round_trip(tmp_path: Path) -> None:
    p = tmp_path / "d" / "f.json"
    json_dump(p, {"a": [1, 2], "p": Path("/x")})
    assert json_load(p) == {"a": [1, 2], "p": "/x"}
    atomic_write_text(p, "x", mode=0o755)
    assert p.read_text() == "x" and os.access(p, os.X_OK)
    assert not [q for q in p.parent.iterdir() if q.name.startswith(".f.json.")]


def test_slug_is_collision_free() -> None:
    assert slug("foo_bar") == "foo_bar"
    assert slug("foo.bar") != slug("foo_bar")
    assert slug("a" * 100) != slug("a" * 101)
    assert len(slug("a" * 300)) <= 64
    assert slug("γ_spec")  # unicode does not crash


def test_run_lock_excludes_a_second_holder(tmp_path: Path) -> None:
    lock = tmp_path / "g.lock"
    with RunLock(lock), pytest.raises(LockedError, match="another pcp run holds"):
        RunLock(lock).acquire()
    with RunLock(lock):
        pass
