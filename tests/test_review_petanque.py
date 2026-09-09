"""Wave-3 adversarial review of the process layer, against a real ``pet``.

Reproduced before the fix: ``close()`` waiting behind a blocked call for that call's
whole watchdog budget (a parent-watch or ``atexit`` close during a hung ``start``
kept ``pet`` alive for up to ten minutes).  The others pin guarantees the review
attacked and could not break: huge feedback over stdio, sessions on two processes
under threads, the anonymous-hypothesis shift on a live trace, and the shelved-goal
diagnosis end to end.
"""

from __future__ import annotations

import os
import shutil
import signal
import subprocess
import sys
import threading
import time
from pathlib import Path

import pytest
from conftest import needs_petanque, needs_rocq

from pcp.errors import StateError
from pcp.rocq.project import compile_text, coq_project_flags
from pcp.state.explain import explain
from pcp.state.ledger.diff import attach
from pcp.state.ledger.query import unused_at_qed
from pcp.state.petanque import PetProcess
from pcp.state.pool import SessionPool
from pcp.state.trace import Tracer

pytestmark = needs_petanque


def test_close_while_a_call_is_blocked_returns_promptly_and_the_caller_is_told(scratch_dir: Path) -> None:
    proc = PetProcess(scratch_dir, mode="stdio", call_timeout=120.0)
    proc.spawn()
    pid = proc.pid
    root = proc.start(scratch_dir / "Basic.v", "sep_comm")
    client = proc._client
    original = client.goals

    def hang(*args, **kwargs):
        client.process.stdout.readline()  # nothing is ever written: blocks until the process dies
        return original(*args, **kwargs)

    client.goals = hang
    errors: list[BaseException] = []

    def blocked() -> None:
        try:
            proc.call("goals", root, timeout=60.0)
        except BaseException as exc:  # noqa: BLE001 -- collected for the assertion
            errors.append(exc)

    t = threading.Thread(target=blocked)
    t.start()
    time.sleep(0.5)
    started = time.monotonic()
    proc.close()
    assert time.monotonic() - started < 10, "close() must kill, not wait for the blocked call's watchdog"
    t.join(10)
    assert not t.is_alive() and errors and isinstance(errors[0], StateError)
    assert "closed" in str(errors[0]) and "proof_open again" in str(errors[0])
    assert not proc.alive() and pid is not None and not Path(f"/proc/{pid}").exists()


def _alive(pid: int) -> bool:
    try:
        return "State:\tZ" not in Path(f"/proc/{pid}/status").read_text()
    except OSError:
        return False


def test_pet_exits_when_its_parent_is_killed_without_pdeathsig(scratch_dir: Path) -> None:
    """No `PR_SET_PDEATHSIG` (per-thread: the v1 critical bug); the stdin pipe is the tie.

    A parent killed with SIGKILL runs no `atexit` and no parent watch, and `pet` must
    still go away -- it reads EOF on its stdin the moment the parent's fds close.
    """
    code = (
        "import time; from pcp.state.petanque import PetProcess; "
        f"p = PetProcess({str(scratch_dir)!r}); p.spawn(); print(p.pid, flush=True); time.sleep(120)"
    )
    env = {**os.environ, "PYTHONPATH": str(Path(__file__).resolve().parents[1])}
    child = subprocess.Popen([sys.executable, "-c", code], stdout=subprocess.PIPE, text=True, env=env)
    try:
        assert child.stdout is not None
        pet_pid = int(child.stdout.readline().strip())
        assert _alive(pet_pid)
        os.kill(child.pid, signal.SIGKILL)
        child.wait(timeout=10)
        deadline = time.monotonic() + 15
        while time.monotonic() < deadline and _alive(pet_pid):
            time.sleep(0.2)
        assert not _alive(pet_pid), "pet must exit on stdin EOF when its parent dies"
    finally:
        if child.poll() is None:
            child.kill()


def test_huge_search_feedback_does_not_wedge_the_process(pool, scratch_dir: Path) -> None:
    session = pool.open(scratch_dir / "Basic.v", "load_twice", start=True)
    assert session.run('iIntros "Hl".').ok
    result = session.run('Search "_".', commit=False, timeout=120.0)
    assert result.ok, result.error
    assert len(result.messages) > 5000 and sum(len(m) for m in result.messages) > 1_000_000
    assert session.run("wp_load.").ok and session.process is not None and session.process.alive()


def test_two_sessions_on_two_processes_under_threads_never_cross(scratch_dir: Path) -> None:
    pool = SessionPool(scratch_dir, size=2)
    try:
        s1 = pool.open(scratch_dir / "Basic.v", "destruct_nested", start=True)
        s2 = pool.open(scratch_dir / "Blame.v", "premature_consumption", start=True)
        assert s1.process is not None and s2.process is not None and s1.process is not s2.process
        bad: list[object] = []

        def hammer(session, n: int) -> None:
            try:
                for i in range(n):
                    r = session.run("idtac.", commit=i % 2 == 0)
                    if not r.ok or r.state is None or r.state.process != session.process.id:
                        bad.append((session.thm, r.error, r.state))
                    if not session.goals(r.state):
                        bad.append((session.thm, "no goals"))
            except BaseException as exc:  # noqa: BLE001 -- collected for the assertion
                bad.append((session.thm, repr(exc)))

        threads = [threading.Thread(target=hammer, args=(s, 6)) for s in (s1, s2, s1, s2)]
        for t in threads:
            t.start()
        for t in threads:
            t.join(180)
        assert not bad, bad[:3]
        assert len(s1.history) == 6 and len(s2.history) == 6
        with pytest.raises(StateError, match="never cross processes"):
            s2.goals(s1.current)
    finally:
        pool.close()


def test_anonymous_shift_on_a_live_trace_is_a_rename_not_an_update(pool, scratch_dir: Path) -> None:
    session = pool.open(scratch_dir / "Basic.v", "sep_comm")
    tracer = attach(Tracer(session))
    tracer.start()
    assert tracer.step('iIntros "[? ?]".').ok
    step = tracer.step('iAssert P with "[$]" as "HP".')
    assert step.ok and [h.id for h in step.goals[0].spatial] == ["_1", "HP"]
    events = tracer.trace.events_at(2)
    assert {e.kind for e in events} == {"Rename"}, [e.render() for e in events]
    assert {(e.sources[0], e.hyp) for e in events} == {("_2", "_1"), ("_1", "HP")}


def test_an_opened_invariant_is_a_use_on_a_live_trace(pool, scratch_dir: Path) -> None:
    session = pool.open(scratch_dir / "Basic.v", "inv_open")
    tracer = attach(Tracer(session))
    tracer.start()
    for tactic in ('iIntros "#Hinv".', 'iInv "Hinv" as "HP" "Hclose".', 'iMod ("Hclose" with "HP") as "_".', "done."):
        assert tracer.step(tactic).ok
    assert tracer.trace.finished and unused_at_qed(tracer.trace) == []
    use = next(e for e in tracer.trace.events_at(2) if e.hyp == "Hinv")
    assert use.kind == "Frame" and use.klass == "intuitionistic" and use.targets == ["HP", "Hclose"]


@needs_rocq
def test_a_shelved_existential_gets_the_unshelve_diagnosis(tmp_path: Path, scratch_dir: Path) -> None:
    shutil.copy(scratch_dir / "_CoqProject", tmp_path / "_CoqProject")
    text = (
        "From iris.proofmode Require Import proofmode.\n"
        "From iris.heap_lang Require Import lang proofmode notation.\n"
        'Set Default Proof Using "Type".\n'
        "Section s.\n  Context `{!heapGS Σ}.\n"
        "  Lemma ev2 (Φ : nat → iProp Σ) : (∀ n, Φ n) -∗ ∃ n, Φ n.\n"
        '  Proof. iIntros "H". iExists _. iApply "H". Qed.\n'
        "End s.\n"
    )
    result = compile_text(text, filename="Ev.v", root=tmp_path, flags=coq_project_flags(tmp_path), timeout=300)
    assert not result.ok and "incomplete proof" in result.output
    out = explain(assembly_text=text, assembled_path_name="Ev.v", compile_output_or_result=result, root=tmp_path,
                  target="ev2", verbose=True, budget_seconds=120)
    assert "shelved" in out and "Unshelve" in out and "bullet" not in out, out
    assert not list(tmp_path.glob("*__pcp*")), "the replay twins must be removed"
