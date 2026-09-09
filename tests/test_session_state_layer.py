"""Sessions, traces and the oracle on real Iris proofs (eval/corpus/scratch)."""

from __future__ import annotations

from pathlib import Path

import pytest
from conftest import needs_petanque

from pcp.errors import StateError
from pcp.state.ipm.oracle import annotate, query_hyp
from pcp.state.ipm.parse import goals_from_petanque
from pcp.state.pool import SessionPool
from pcp.state.trace import Trace, Tracer

pytestmark = needs_petanque


def test_a_real_trace_parses_both_contexts_and_the_mask_field(pool, scratch_dir: Path) -> None:
    tracer = Tracer(pool.open(scratch_dir / "Basic.v", "inv_open"))
    tracer.start()
    trace = tracer.run_script(
        ['iIntros "#Hinv".', 'iInv "Hinv" as "HP" "Hclose".', 'iMod ("Hclose" with "HP") as "_".', "done."]
    )
    assert trace.finished, trace.error
    after_intro = trace.steps[1].goals[0]
    assert [h.id for h in after_intro.intuitionistic] == ["Hinv"] and after_intro.intuitionistic[0].persistent is True
    opened = trace.steps[2].goals[0]
    assert opened.modality.fupd and opened.modality.mask and "↑N" in opened.modality.mask
    assert [h.id for h in opened.spatial] == ["HP", "Hclose"]
    assert trace.steps[2].parent_goal == "g0" and trace.steps[0].tactic == "<start>"
    assert trace.file == str(scratch_dir / "Basic.v") and trace.petanque_file is None
    assert all(s.state_hash is not None for s in trace.steps)


def test_state_hash_detects_a_loop_on_the_committed_path_including_the_root(pool, scratch_dir: Path) -> None:
    session = pool.open(scratch_dir / "Basic.v", "sep_comm")
    session.start()
    back_to_root = session.run("idtac.")
    assert back_to_root.ok and back_to_root.loop_of == 0, "a loop back to the root must be flagged"
    intro = session.run('iIntros "[HP HQ]".')
    assert intro.ok and intro.loop_of is None
    repeat = session.run("idtac.")
    assert repeat.ok and repeat.loop_of == 2
    spec = session.run("idtac.", commit=False)
    assert spec.loop_of == 2 and len(session.history) == 3
    tracer = Tracer(pool.open(scratch_dir / "Basic.v", "sep_comm"))
    tracer.start()
    assert tracer.step("idtac.").loop_of == 0


def test_speculative_fan_out_does_not_move_the_session(pool, scratch_dir: Path) -> None:
    session = pool.open(scratch_dir / "Basic.v", "sep_comm")
    session.start()
    before = session.current.st  # type: ignore[union-attr]
    results = session.try_many(['iIntros "[HP HQ]".', "reflexivity.", "exact I."])
    assert [r.ok for r in results] == [True, False, False]
    assert session.current.st == before and session.history == []  # type: ignore[union-attr]
    assert results[0].state is not None and results[0].state.st != before
    assert results[1].error and "Coq:" in results[1].error


def test_query_returns_search_messages(pool, scratch_dir: Path) -> None:
    session = pool.open(scratch_dir / "Basic.v", "sep_comm")
    session.start()
    lines = session.query("Search bi_sep.")
    assert lines and any("sep" in line for line in lines)
    assert session.query("Search this_does_not_exist_xyz.") == []
    assert session.history == []


def test_replay_is_deterministic(pool, scratch_dir: Path) -> None:
    script = ['iIntros "[HP [HQ HR]]".', "iFrame."]
    hashes = []
    for _ in range(2):
        tracer = Tracer(pool.open(scratch_dir / "Basic.v", "destruct_nested"))
        tracer.start()
        trace = tracer.run_script(script)
        assert trace.finished
        hashes.append([s.state_hash for s in trace.steps])
    assert hashes[0] == hashes[1]
    session = pool.open(scratch_dir / "Basic.v", "destruct_nested")
    first = [r.state_hash for r in session.replay(script)]
    second = [r.state_hash for r in session.replay(script)]
    assert first == second == hashes[0][1:]


def test_failed_step_records_pre_failure_goals_and_the_session_stays_put(pool, scratch_dir: Path) -> None:
    tracer = Tracer(pool.open(scratch_dir / "Basic.v", "sep_comm"))
    tracer.start()
    trace = tracer.run_script(['iIntros "[HP HQ]".', 'iDestruct "HP" as "[H1 H2]".', "iFrame."])
    assert trace.failed_at == 2 and trace.error and not trace.finished
    failed = trace.steps[2]
    assert failed.state_id == -1 and not failed.ok and [h.id for h in failed.goals[0].spatial] == ["HP", "HQ"]
    assert len(trace.steps) == 3 and trace.tactics[-1] == 'iDestruct "HP" as "[H1 H2]".'
    assert tracer.step("iFrame.").ok and trace.finished


def test_stubbed_twin_gives_identical_goals(scratch_dir: Path, tmp_path: Path) -> None:
    work = tmp_path / "w"
    work.mkdir()
    (work / "_CoqProject").write_text((scratch_dir / "_CoqProject").read_text(encoding="utf-8"), encoding="utf-8")
    target = work / "Basic.v"
    target.write_text((scratch_dir / "Basic.v").read_text(encoding="utf-8"), encoding="utf-8")
    pool = SessionPool(work, size=1)
    try:
        rendered = {}
        for label, stub in (("plain", False), ("stubbed", True)):
            session = pool.open(target, "load_twice", stub_prefix=stub)
            state = session.start()
            goal = goals_from_petanque(session.goals(state))[0]
            rendered[label] = (goal.goal, [(h.id, h.prop) for h in goal.ipm_hyps])
            if stub:
                assert session.file.endswith("Basic__pcpfast.v") and session.source_file == str(target)
                assert Tracer(session).trace.petanque_file == session.file
        assert rendered["plain"] == rendered["stubbed"]
    finally:
        pool.close()


def test_trace_round_trips_through_jsonl(pool, scratch_dir: Path, tmp_path: Path) -> None:
    tracer = Tracer(pool.open(scratch_dir / "Basic.v", "exists_pure"))
    tracer.start()
    trace = tracer.run_script(['iIntros "H".', 'iDestruct "H" as (n) "[%Hn HΦ]".', "subst.", "iFrame."])
    assert trace.finished
    path = trace.to_jsonl(tmp_path / "t.jsonl")
    again = Trace.from_jsonl(path)
    assert [s.to_json() for s in again.steps] == [s.to_json() for s in trace.steps]
    assert again.store.to_json() == trace.store.to_json() and again.finished
    assert again.dumps() == trace.dumps()


def test_the_oracle_answers_at_a_historical_state(pool, scratch_dir: Path) -> None:
    session = pool.open(scratch_dir / "Blame.v", "persistent_is_not_consumed")
    tracer = Tracer(session)
    tracer.start()
    tracer.run_script(['iIntros "[HP HQ]".', 'iDestruct "HP" as "#HP".', 'iFrame "HP".'])
    step1 = tracer.trace.steps[1]
    goal = step1.goals[0]
    annotate(session, goal, state=session.state(step1.state_id), affine=True)
    by_id = {h.id: h for h in goal.spatial}
    assert by_id["HP"].persistent is True and by_id["HQ"].persistent is False and by_id["HQ"].affine is True
    # At the final state HP is intuitionistic; probing the *historical* state still answers for it.
    assert query_hyp(session, "HP", state=session.state(step1.state_id)).persistent is True
    unknown = query_hyp(session, "Hnope", state=session.current)  # type: ignore[arg-type]
    assert unknown.persistent is None and unknown.error and "not found" in unknown.error


def test_a_lost_session_never_reports_a_tactic_failure(pool, scratch_dir: Path) -> None:
    session = pool.open(scratch_dir / "Basic.v", "sep_comm")
    session.start()
    session.mark_lost("petanque restarted (test)")
    with pytest.raises(StateError, match="proof_open again"):
        session.run("idtac.")
    with pytest.raises(StateError):
        session.goals()
