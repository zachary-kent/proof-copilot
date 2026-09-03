"""The state layer against real Rocq: session, trace, reflection, oracle, render."""

from __future__ import annotations

from pathlib import Path

from tests.conftest import needs_petanque, needs_rocq

pytestmark = [needs_petanque, needs_rocq]


def test_a_real_trace_parses_both_contexts_and_the_modality(pool, scratch_dir: Path) -> None:
    from pcp.core.session import ProofSession
    from pcp.core.trace import Tracer

    tracer = Tracer(ProofSession(pool, scratch_dir / "Basic.v", "inv_open"))
    tracer.start()
    trace = tracer.run_script(
        ['iIntros "#Hinv".', 'iInv "Hinv" as "HP" "Hclose".',
         'iMod ("Hclose" with "HP") as "_".', "done."]
    )
    assert trace.finished, trace.error
    after_intro = trace.steps[1].goals[0]
    assert [h.id for h in after_intro.intuitionistic] == ["Hinv"]
    # Opening an invariant changes the mask, and the mask is a field, not a blob.
    opened = trace.steps[2].goals[0]
    assert opened.modality.mask and "↑N" in opened.modality.mask


def test_state_hash_detects_a_no_op_loop(pool, scratch_dir: Path) -> None:
    """An agent repeating a no-op tactic in a cycle is detectable mechanically."""
    from pcp.core.session import ProofSession

    session = ProofSession(pool, scratch_dir / "Basic.v", "sep_comm")
    session.start()
    session.run('iIntros "[HP HQ]".')
    session.run("idtac.")
    repeat = session.run("idtac.")
    assert repeat.ok
    assert repeat.loop_of is not None, "a state we have already been in must be flagged"


def test_speculative_fan_out_does_not_move_the_session(pool, scratch_dir: Path) -> None:
    from pcp.core.session import ProofSession

    session = ProofSession(pool, scratch_dir / "Basic.v", "sep_comm")
    session.start()
    before = session.current.st
    results = session.try_many(['iIntros "[HP HQ]".', "reflexivity.", "exact I."])
    assert [r.ok for r in results] == [True, False, False]
    assert session.current.st == before


def test_the_persistence_oracle_answers_from_rocq_not_from_the_printed_form(pool, scratch_dir: Path) -> None:
    from pcp.core.ipm.oracle import annotate
    from pcp.core.session import ProofSession
    from pcp.core.trace import Tracer

    session = ProofSession(pool, scratch_dir / "Blame.v", "persistent_is_not_consumed")
    tracer = Tracer(session)
    tracer.start()
    tracer.run_script(['iIntros "[HP HQ]".'])
    goal = tracer.trace.steps[-1].goals[0]
    annotate(session, goal, affine=True)
    by_id = {h.id: h for h in goal.spatial}
    assert by_id["HP"].persistent is True
    assert by_id["HQ"].persistent is False
    assert by_id["HQ"].affine is True


def test_the_reflected_dump_works_and_beats_the_printer_on_one_thing(pool, scratch_dir: Path, tmp_path: Path) -> None:
    """PLAN.md 3.1's open question, answered: tactic messages survive petanque.

    And the capability the printer parser cannot offer at all -- printing options set
    for *one* hypothesis while everything else stays folded.
    """
    import os

    from pcp.core.ipm.reflect import Reflector, build_idump, coqpath_with
    from pcp.core.session import ProofSession, SessionPool

    root = tmp_path / "coq"
    build_idump(root)
    previous = os.environ.get("COQPATH", "")
    os.environ["COQPATH"] = coqpath_with(root) + (":" + previous if previous else "")
    os.environ["ROCQPATH"] = os.environ["COQPATH"]
    local = SessionPool(scratch_dir, size=1)
    try:
        session = ProofSession(
            local, scratch_dir / "Blame.v", "persistent_is_not_consumed",
            pre_commands="Require Import pcp.IDump.",
        )
        session.start()
        assert session.run('iIntros "[#HP HQ]".').ok
        reflector = Reflector(session)
        assert reflector.probe(), "iDump did not load or produced no records"
        goal = reflector.dump()
        assert goal is not None
        assert [h.id for h in goal.intuitionistic] == ["HP"]
        assert [h.id for h in goal.spatial] == ["HQ"]
        assert goal.goal.strip() == "P ∗ P ∗ Q"
        one = reflector.dump_hyp("HQ", printing="Set Printing All.")
        assert one is not None and one.name == "HQ"
    finally:
        local.close()
        os.environ["COQPATH"] = previous
        os.environ.pop("ROCQPATH", None)


def test_deterministic_replay(pool, scratch_dir: Path) -> None:
    """A trace is (root state, tactic list); everything else is derived."""
    from pcp.core.session import ProofSession
    from pcp.core.trace import Tracer

    script = ['iIntros "[HP [HQ HR]]".', "iFrame."]
    hashes = []
    for _ in range(2):
        tracer = Tracer(ProofSession(pool, scratch_dir / "Basic.v", "destruct_nested"))
        tracer.start()
        trace = tracer.run_script(script)
        hashes.append([s.state_hash for s in trace.steps])
    assert hashes[0] == hashes[1]


def test_trace_round_trips_through_jsonl(pool, scratch_dir: Path, tmp_path: Path) -> None:
    from pcp.core.session import ProofSession
    from pcp.core.trace import Trace, Tracer

    tracer = Tracer(ProofSession(pool, scratch_dir / "Basic.v", "exists_pure"))
    tracer.start()
    trace = tracer.run_script(
        ['iIntros "H".', 'iDestruct "H" as (n) "[%Hn HΦ]".', "subst.", "iFrame."]
    )
    path = trace.write(tmp_path / "t.jsonl")
    again = Trace.read(path)
    assert len(again.steps) == len(trace.steps)
    assert [e.kind for e in again.events] == [e.kind for e in trace.events]
    assert len(again.store) == len(trace.store)


def test_render_reports_what_it_elided(pool, scratch_dir: Path) -> None:
    """A model that knows it is looking at a partial view asks for more."""
    from pcp.core.render import RenderOptions, render_goal
    from pcp.core.session import ProofSession
    from pcp.core.trace import Tracer

    tracer = Tracer(ProofSession(pool, scratch_dir / "Basic.v", "destruct_nested"))
    tracer.start()
    tracer.run_script(['iIntros "[HP [HQ HR]]".'])
    goal = tracer.trace.steps[-1].goals[0]

    full = render_goal(goal, options=RenderOptions(diff_only=False))
    assert full.rendered == full.total
    assert "token budget" in full.text

    tiny = render_goal(goal, options=RenderOptions(diff_only=False, budget=6, show_pure=False))
    assert tiny.rendered < tiny.total
    assert "budget exhausted" in tiny.text


def test_stubbing_the_prefix_does_not_change_the_goal(pool, scratch_dir: Path, tmp_path: Path) -> None:
    """The soundness condition for the fast `proof_open`.

    `petanque/start` must elaborate everything before the theorem, which on a real
    development is minutes of other people's proof automation.  None of it can affect
    this goal -- `Qed` proofs are opaque, so the state at `thm` depends on the
    *statements* before it and never on their bodies.  This asserts that equality
    rather than trusting the argument.
    """
    from pcp.core.session import ProofSession, SessionPool
    from pcp.core.trace import goals_from_petanque

    src = (scratch_dir / "Basic.v").read_text(encoding="utf-8")
    work = tmp_path / "w"
    work.mkdir()
    (work / "_CoqProject").write_text((scratch_dir / "_CoqProject").read_text(encoding="utf-8"), encoding="utf-8")
    target = work / "Basic.v"
    target.write_text(src, encoding="utf-8")

    local = SessionPool(work, size=1)
    try:
        rendered = {}
        for label, stub in (("plain", False), ("stubbed", True)):
            session = ProofSession(local, target, "load_twice", stub_prefix=stub)
            state = session.start()
            goal = goals_from_petanque(session.goals(state))[0]
            rendered[label] = (goal.goal, [(h.id, h.prop) for h in goal.ipm_hyps])
        assert rendered["plain"] == rendered["stubbed"]
    finally:
        local.close()


def test_the_stubbed_twin_keeps_the_target_and_drops_the_rest(tmp_path: Path) -> None:
    from pcp.core.session import _stubbed_copy

    src = tmp_path / "D.v"
    src.write_text(
        "Lemma a : True.\nProof. exact I. Qed.\n\nLemma target : True.\nProof. exact I. Qed.\n",
        encoding="utf-8",
    )
    twin = Path(_stubbed_copy(str(src), keep="target"))
    assert twin != src and twin.parent == src.parent
    text = twin.read_text(encoding="utf-8")
    assert "Lemma a : True." in text and text.count("exact I.") == 1
    assert "Lemma target : True.\nProof. exact I. Qed." in text
    # Rewriting is idempotent, so a warm pool keeps hitting its document cache.
    assert Path(_stubbed_copy(str(src), keep="target")).read_text(encoding="utf-8") == text


def test_the_pool_routes_a_file_back_to_the_server_that_knows_it(tmp_path: Path) -> None:
    """Affinity is worth more than parallelism here: coq-lsp caches the checked
    document, so a second `start` on the same file costs 0.3 s against 22 s."""
    from pcp.core.session import SessionPool

    import threading

    class FakeServer:
        def __init__(self) -> None:
            self.lock = threading.RLock()

    pool = SessionPool(tmp_path, size=3)
    try:
        cold, warm = FakeServer(), FakeServer()
        pool._servers = [cold, warm]  # type: ignore[list-item]
        pool._affinity[id(warm)] = {"/x/F.v"}

        chosen = pool._pick_free("/x/F.v")
        assert chosen is warm, "a warm server must win over a cold one"
        chosen.lock.release()

        # With no file named, any free server will do.
        assert pool._pick_free(None) in (cold, warm)
    finally:
        pool._servers = []
        pool.close()
