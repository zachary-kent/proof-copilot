"""The resource ledger (PLAN.md 4) -- the flagship feature.

Claim 2: Iris debugging failures are resource-accounting failures.  "One spatial
hypothesis gets eliminated by some tactic, but is needed many steps later" is a
bookkeeping failure, and bookkeeping over 200 steps is what a machine does well.

The honesty requirement is tested as hard as the happy path: when matching is
ambiguous the ledger must say `unknown`, because a confidently wrong provenance
chain is worse than no chain -- the agent will trust it and spend twenty turns in
the wrong place.
"""

from __future__ import annotations

from pathlib import Path

from pcp.core.ipm.model import Hyp, IrisGoal, Modality
from pcp.core.ledger.diff import align_goals, diff_context, diff_step, to_events
from tests.conftest import needs_petanque, needs_rocq


def goal(spatial=(), intuit=(), concl="Q", mask=None, laters=0) -> IrisGoal:
    g = IrisGoal(
        spatial=[Hyp(id=n, prop=p, klass="spatial") for n, p in spatial],
        intuitionistic=[Hyp(id=n, prop=p, klass="intuitionistic", persistent=True) for n, p in intuit],
        goal=concl,
    )
    g.modality = Modality(mask=mask, laters=laters)
    return g


# --------------------------------------------------------------------- diffing

def test_the_five_matching_rules() -> None:
    prev = [Hyp("H1", "P"), Hyp("H2", "Q"), Hyp("H3", "R"), Hyp("H4", "S")]
    nxt = [Hyp("H1", "P"), Hyp("H2", "Q'"), Hyp("H3b", "R"), Hyp("H5", "T")]
    d = diff_context(prev, nxt)
    assert d.unchanged == ["H1"]
    assert d.updated == ["H2"]
    assert d.renamed == [("H3", "H3b")]
    assert d.consumed == ["H4"]
    assert d.produced == ["H5"]


def test_matching_is_name_first_hash_second() -> None:
    """IPM names are unique within a context and are the primary key."""
    prev = [Hyp("H", "P"), Hyp("H2", "P")]
    nxt = [Hyp("H", "P")]
    d = diff_context(prev, nxt)
    assert d.unchanged == ["H"] and d.consumed == ["H2"]


def test_identical_props_with_moved_names_are_unknown_not_guessed() -> None:
    """Fractional halves and duplicate `own` fragments print identically.  When all
    their names move at once, which went where is not recoverable -- say so."""
    prev = [Hyp("Ha", "l ↦{#1/2} v"), Hyp("Hb", "l ↦{#1/2} v")]
    nxt = [Hyp("Hc", "l ↦{#1/2} v"), Hyp("Hd", "l ↦{#1/2} v")]
    d = diff_context(prev, nxt)
    assert set(d.ambiguous) == {"Ha", "Hb", "Hc", "Hd"}
    assert not d.consumed and not d.produced


def test_evar_instantiation_is_not_a_consumption() -> None:
    """Iris proofs are evar-dense; instantiating one reprints untouched hypotheses."""
    d = diff_context([Hyp("H", "P ?x")], [Hyp("H", "P 42")])
    assert d.instantiated == ["H"] and not d.updated and not d.consumed


def test_evar_renumbering_alone_is_unchanged() -> None:
    d = diff_context([Hyp("H", "P ?Goal3")], [Hyp("H", "P ?Goal7")])
    assert d.unchanged == ["H"]


def test_goal_alignment_finds_the_untouched_tail() -> None:
    a, b = goal(concl="A"), goal(concl="B")
    alignment = align_goals([a, b], [goal(concl="A1"), goal(concl="A2"), b])
    assert alignment.spawned
    assert len(alignment.children) == 2
    assert [g.goal for g in alignment.untouched] == ["B"]


def test_closing_the_last_goal_consumes_what_was_live() -> None:
    """`unused_at_qed` is only meaningful if the closing step is attributed."""
    prev = [goal(spatial=[("H", "P")], concl="P")]
    diffs, alignment = diff_step(1, "iFrame.", prev, [])
    assert len(diffs) == 1 and diffs[0].goal_closed
    events = to_events(diffs[0], prev[0], alignment.children[0])
    assert [e.kind for e in events if e.hyp == "H"] == ["Frame"]


def test_persistent_hypotheses_are_never_reported_as_consumed() -> None:
    """Calling their disappearance at Qed a consumption teaches the opposite of #5."""
    prev = [goal(intuit=[("HP", "P")], concl="P")]
    diffs, alignment = diff_step(1, "iApply \"HP\".", prev, [])
    events = to_events(diffs[0], prev[0], alignment.children[0])
    assert not [e for e in events if e.kind == "Consume"]


def test_spatial_to_intuitionistic_is_persist_not_consume() -> None:
    prev = [goal(spatial=[("H", "□ P")], concl="Q")]
    nxt = [goal(intuit=[("H2", "□ P")], concl="Q")]
    diffs, alignment = diff_step(1, 'iDestruct "H" as "#H2".', prev, nxt)
    events = to_events(diffs[0], prev[0], alignment.children[0])
    kinds = {e.kind for e in events}
    assert "Persist" in kinds and "Consume" not in kinds


def test_an_ambient_mask_change_is_not_reported() -> None:
    """`None` and `⊤` are the same mask; reporting `⊤ → ⊤` is noise, and noise in a
    mask report is worse than silence."""
    prev = [goal(concl="P")]
    nxt = [goal(concl="P", mask="⊤")]
    diffs, alignment = diff_step(1, "wp_pures.", prev, nxt)
    assert diffs[0].mask_change is None


def test_a_real_mask_change_is_reported() -> None:
    prev = [goal(concl="P", mask="⊤")]
    nxt = [goal(concl="P", mask="⊤ ∖ ↑N")]
    diffs, alignment = diff_step(1, 'iInv "H" as "HP".', prev, nxt)
    events = to_events(diffs[0], prev[0], alignment.children[0])
    assert any(e.kind == "MaskChange" and "⊤ ∖ ↑N" in e.detail for e in events)


# ---------------------------------------------------------------------- queries

def _trace_with(events) -> object:
    from pcp.core.ledger.events import EventLog
    from pcp.core.ipm.model import Step
    from pcp.core.trace import Trace

    t = Trace(file="f.v", thm="t")
    t.events = EventLog()
    for e in events:
        t.events.add(e)
    t.steps = [Step(step=99, state_id=1, tactic="last", goals=[goal(spatial=[("HP", "P")])])]
    return t


def test_blame_names_the_step_the_tactic_and_a_repair_class() -> None:
    from pcp.core.ledger.events import Event
    from pcp.core.ledger.query import LedgerQuery

    trace = _trace_with([
        Event(step=1, kind="Intro", tactic='iIntros "[H1 H2]".', hyp="H1"),
        Event(step=12, kind="Split", tactic='iDestruct "H1" as "[Ha Hb]".', hyp="Ha", sources=["H1"],
              targets=["Ha", "Hb"]),
        Event(step=19, kind="Consume", tactic="iApply wp_store.", hyp="Ha", targets=[]),
    ])
    blame = LedgerQuery(trace).blame(47, "Ha")
    assert blame.culprit is not None and blame.culprit.step == 19
    assert blame.repair in ("split-differently", "duplicate-it-is-persistent")
    assert "iApply wp_store." in blame.render()


def test_blame_says_so_when_the_hypothesis_is_actually_live() -> None:
    from pcp.core.ledger.events import Event
    from pcp.core.ledger.query import LedgerQuery

    trace = _trace_with([Event(step=1, kind="Intro", tactic='iIntros "HP".', hyp="HP")])
    blame = LedgerQuery(trace).blame(9, "HP")
    assert blame.repair == "restate"
    assert "still live" in blame.advice


def test_provenance_marks_an_unknown_chain_as_a_lead_not_a_fact() -> None:
    from pcp.core.ledger.events import Event
    from pcp.core.ledger.query import LedgerQuery

    trace = _trace_with([
        Event(step=3, kind="Unknown", tactic="iInduction x as [] \"IH\".", hyp="Hx", confidence="unknown"),
    ])
    prov = LedgerQuery(trace).where_did_it_go("Hx")
    assert prov.fate == "unknown"
    assert "lead, not a fact" in prov.note


# ------------------------------------------------------------------- end to end

@needs_petanque
@needs_rocq
def test_real_iris_proof_produces_a_usable_chain(pool, scratch_dir: Path) -> None:
    from pcp.core.ledger.query import LedgerQuery
    from pcp.core.session import ProofSession
    from pcp.core.trace import Tracer

    tracer = Tracer(ProofSession(pool, scratch_dir / "Blame.v", "premature_consumption"))
    tracer.start()
    trace = tracer.run_script(['iIntros "[[HP HQ] HR]".', 'iFrame.'])
    assert trace.finished

    q = LedgerQuery(trace)
    kinds = [e.kind for e in trace.events]
    assert kinds.count("Intro") == 3
    assert "Frame" in kinds

    prov = q.where_did_it_go("HP")
    assert prov.fate == "consumed"
    assert any(link.step == 1 for link in prov.backward)

    blame = q.blame(5, "HP")
    assert blame.repair == "frame-later"
    assert "framed" in blame.render()


@needs_petanque
@needs_rocq
def test_leftovers_surfaces_the_spatial_context_before_the_opaque_error(pool, scratch_dir: Path) -> None:
    """Failure mode #2, answered *before* the agent hits `done` and gets nothing."""
    from pcp.core.ledger.query import LedgerQuery
    from pcp.core.session import ProofSession
    from pcp.core.trace import Tracer

    tracer = Tracer(ProofSession(pool, scratch_dir / "Blame.v", "leftover_spatial"))
    tracer.start()
    trace = tracer.run_script(['iIntros "[HP HQ]".'])
    left = LedgerQuery(trace).leftovers()
    assert {h.id for h in left} == {"HP", "HQ"}
