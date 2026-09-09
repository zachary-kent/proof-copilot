"""The process layer against a real ``pet`` (ARCHITECTURE.md 6).

Every test here is a v1 failure class: hangs with no deadline, a restart reusing stale
ids, a session's state sent to another process, two threads interleaving one pet's
protocol.  The shared ``pool`` fixture keeps the wall clock down; the tests that need
their own processes build small pools on the scratch corpus.
"""

from __future__ import annotations

import threading
import time

import pytest
from conftest import needs_petanque

from pcp.errors import StateError
from pcp.state.petanque import PetProcess, TacticError
from pcp.state.pool import SessionPool

pytestmark = needs_petanque


def test_process_starts_and_runs_a_tactic(pool, scratch_dir) -> None:
    session = pool.open(scratch_dir / "Basic.v", "sep_comm")
    root = session.start()
    proc = session.process
    assert proc is not None and proc.alive() and root.process == proc.id and root.generation == proc.generation
    assert root.state_hash is not None and str(session.file) in proc.files
    goals = proc.goals(root)
    assert goals and goals[0].ty == "P ∗ Q -∗ Q ∗ P" and any(h.names == ("P", "Q") for h in goals[0].hyps)
    with pool.acquire(proc) as held:
        after = held.run(root, 'iIntros "[HP HQ]".')
        assert after.st != root.st and not after.proof_finished
        assert held.state_hash(after) == after.state_hash
        with pytest.raises(TacticError) as exc:
            held.run(after, "exact I.")
        assert exc.value.message.startswith("Coq:") and not exc.value.timed_out
        with pytest.raises(TacticError) as slow:
            held.run(after, "repeat (let x := eval vm_compute in (Nat.pow 2 22) in idtac).", timeout=1)
        assert slow.value.timed_out
    assert proc.alive()


def test_rocq_timeout_reaches_the_session_with_a_typeclass_trace(pool, scratch_dir) -> None:
    session = pool.open(scratch_dir / "Basic.v", "sep_comm")
    session.start()
    session.run('iIntros "[HP HQ]".')
    result = session.run("repeat (let x := eval vm_compute in (Nat.pow 2 22) in idtac).", timeout=1)
    assert not result.ok and result.timed_out and "Timeout" in (result.error or "")
    assert session.process is not None and session.process.alive() and not session.lost


def test_python_side_wall_clock_kills_a_hung_call(scratch_dir) -> None:
    """pytanque's stdio mode has no timeout at all: the watchdog must kill and report."""
    proc = PetProcess(scratch_dir, mode="stdio", call_timeout=60.0)
    proc.spawn()
    try:
        root = proc.start(scratch_dir / "Basic.v", "sep_comm")
        client = proc._client

        original = client.goals

        def hang(*args, **kwargs):
            client.process.stdout.readline()  # blocks until the process dies: nothing is ever written
            return original(*args, **kwargs)

        client.goals = hang  # a call that never comes back
        started = time.monotonic()
        with pytest.raises(StateError, match="wall clock"):
            proc.call("goals", root, timeout=1.0)
        assert time.monotonic() - started < 10
        client.goals = original
        assert not proc.alive() and "wall clock" in (proc.dead_reason or "")
        with pytest.raises(StateError, match="not running"):
            proc.goals(root)
    finally:
        proc.close()


def test_restart_invalidates_every_handle_with_a_clear_message(scratch_dir) -> None:
    pool = SessionPool(scratch_dir, size=1)
    try:
        session = pool.open(scratch_dir / "Basic.v", "sep_comm")
        root = session.start()
        proc = session.process
        assert proc is not None
        old_generation = proc.generation
        proc.restart("test")
        assert proc.generation == old_generation + 1 and proc.alive()
        with pytest.raises(StateError, match="restarted.*proof_open again"):
            proc.goals(root)
        assert session.lost is False  # not yet observed by the pool ...
        # ... but a health pass that finds the process dead marks its sessions lost.
        proc._kill("simulated crash")
        proc._proc.wait(timeout=5)
        with pytest.raises(StateError, match="was lost when petanque restarted.*proof_open again"):
            session.run("idtac.")
        assert session.lost and "simulated crash" in (session.lost_reason or "")
        assert proc.alive(), "the pool restarted the process between calls"
        fresh = pool.open(scratch_dir / "Basic.v", "sep_comm")
        assert fresh.process is proc and fresh.start().generation == proc.generation
    finally:
        pool.close()


def test_pool_pins_sessions_to_the_process_that_elaborated_their_file(scratch_dir) -> None:
    pool = SessionPool(scratch_dir, size=2)
    try:
        s1 = pool.open(scratch_dir / "Basic.v", "sep_comm")
        s2 = pool.open(scratch_dir / "Blame.v", "leftover_spatial")
        assert s1.process is not None and s2.process is not None and s1.process is not s2.process
        s1.start()
        s2.start()
        p1, p2 = s1.process, s2.process
        calls_before = p2.calls
        r = s1.run('iIntros "[HP HQ]".')
        assert r.ok and r.state is not None and r.state.process == p1.id
        assert p2.calls == calls_before, "a step on session 1 must never reach process 2"
        # A third session on Basic.v goes to the warm process, never to a cold one.
        s3 = pool.open(scratch_dir / "Basic.v", "persist_dup")
        assert s3.process is p1
        # And a handle from p1 is refused by p2 before anything is sent.
        with pytest.raises(StateError, match="never cross processes"):
            p2.goals(r.state)
        assert len(pool.processes) == 2
    finally:
        pool.close()


def test_threads_stepping_one_session_serialise_without_error(pool, scratch_dir) -> None:
    session = pool.open(scratch_dir / "Basic.v", "destruct_nested")
    session.start()
    errors: list[BaseException] = []
    seen: list[int] = []

    def worker() -> None:
        try:
            for _ in range(3):
                r = session.run("idtac.")
                assert r.ok, r.error
                seen.append(r.state.st)  # type: ignore[union-attr]
        except BaseException as exc:  # noqa: BLE001 -- collected for the assertion
            errors.append(exc)

    threads = [threading.Thread(target=worker) for _ in range(8)]
    for t in threads:
        t.start()
    for t in threads:
        t.join(timeout=120)
    assert not errors, errors[:3]
    assert len(session.history) == 24 and len(seen) == 24
    assert session.process is not None and session.process.alive()


def test_bounded_acquire_raises_instead_of_blocking_forever(pool, scratch_dir) -> None:
    session = pool.open(scratch_dir / "Basic.v", "sep_comm")
    session.start()
    proc = session.process
    assert proc is not None
    holder = threading.Event()
    release = threading.Event()

    def hold() -> None:
        with proc.lock:
            holder.set()
            release.wait(10)

    t = threading.Thread(target=hold)
    t.start()
    holder.wait(5)
    try:
        with pytest.raises(StateError, match="busy"), pool.acquire(proc, timeout=0.2):
            pass
    finally:
        release.set()
        t.join()
