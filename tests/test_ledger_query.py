"""Provenance, blame, leftovers, unused (pcp.state.ledger.query) over stand-in traces."""

from __future__ import annotations

from types import SimpleNamespace

from pcp.state.ipm.model import Hyp, IrisGoal, Step
from pcp.state.ledger.diff import diff_step
from pcp.state.ledger.events import Event
from pcp.state.ledger.query import (
    blame,
    first_use,
    last_use,
    leftovers,
    render_leftovers,
    render_unused,
    unused_at_qed,
    where_did_it_go,
)


def sp(*pairs):
    return [Hyp(i, p) for i, p in pairs]


def it(*pairs):
    return [Hyp(i, p, klass="intuitionistic") for i, p in pairs]


def trace_of(tactics: list[str], states: list[list[IrisGoal]], *, finished=False):
    """Steps 0..n with ledger events computed by ``diff_step`` -- no hand-built events."""
    steps = [Step(step=0, state_id=0, tactic="<start>", goals=states[0])]
    events: list[Event] = []
    for i, (tac, goals) in enumerate(zip(tactics, states[1:], strict=True), start=1):
        steps.append(Step(step=i, state_id=i, tactic=tac, goals=goals))
        events += diff_step(states[i - 1], goals, step=i, tactic=tac)
    return SimpleNamespace(steps=steps, events=events, finished=finished)


def test_blame_after_a_real_split_lists_the_pieces() -> None:
    g0 = [IrisGoal(goal="R ∗ Q ∗ P", spatial=sp(("HP", "P"), ("H", "Q ∗ R")))]
    g1 = [IrisGoal(goal="R ∗ Q ∗ P", spatial=sp(("HP", "P"), ("HQ", "Q"), ("HR", "R")))]
    tr = trace_of(['iDestruct "H" as "[HQ HR]".'], [g0, g1])
    b = blame(tr, 2, "H")
    assert b.repair == "split-differently"
    assert b.culprit is not None and b.culprit.targets == ["HQ", "HR"]
    text = b.render()
    assert 'why is "H" not available at step 2?' in text
    assert '"H" was split at step 1' in text and "splitd" not in text
    assert '"HQ", "HR"' in text and "repair class: split-differently" in text


def test_where_did_it_go_finds_a_hypothesis_live_in_a_sibling_goal() -> None:
    g0 = [IrisGoal(goal="(P ∗ Q) ∗ R", spatial=sp(("HP", "P"), ("HQ", "Q"), ("HR", "R")))]
    g1 = [IrisGoal(goal_id="g0", goal="R", spatial=sp(("HR", "R"))),
          IrisGoal(goal_id="g1", goal="P ∗ Q", spatial=sp(("HP", "P"), ("HQ", "Q")))]
    tr = trace_of(['iSplitL "HR".'], [g0, g1])
    p = where_did_it_go(tr, "HP")
    assert p.fate == "live" and p.live_in == "g1"
    assert where_did_it_go(tr, "HR").live_in == "g0"


def test_frame_then_blame_is_frame_later_in_the_readme_shape() -> None:
    g0 = [IrisGoal(goal="P ∗ Q", spatial=sp(("HP", "P"), ("HQ", "Q")))]
    g1 = [IrisGoal(goal="Q", spatial=sp(("HQ", "Q")))]
    tr = trace_of(['iFrame "HP".'], [g0, g1])
    assert where_did_it_go(tr, "HP").fate == "framed"
    b = blame(tr, 5, "HP")
    assert b.repair == "frame-later"
    lines = b.render().splitlines()
    assert lines[0] == 'why is "HP" not available at step 5?'
    assert lines[1] == '  "HP" was framed at step 1 by `iFrame "HP".`'
    assert lines[2] == "  repair class: frame-later"
    assert lines[3] == "  step 1 framed it into the goal -- frame later, or split the goal first."


def test_persistent_repair_class_is_reachable() -> None:
    # A boxed spatial hypothesis consumed whole: persistence is read at the step it existed.
    g0 = [IrisGoal(goal="Q", spatial=sp(("HP", "□ P"), ("Hw", "P -∗ Q")))]
    g1 = [IrisGoal(goal="Q", spatial=sp(("Hw'", "Q")))]
    tr = trace_of(['iSpecialize ("Hw" with "HP").'], [g0, g1])
    events = [e for e in tr.events if e.hyp == "HP"]
    assert events and events[0].kind == "Consume"
    assert blame(tr, 3, "HP").repair == "duplicate-it-is-persistent"
    # An intuitionistic hypothesis cleared from the context.
    h0 = [IrisGoal(goal="Q", intuitionistic=it(("Hinv", "inv N P")))]
    h1 = [IrisGoal(goal="Q")]
    tr2 = trace_of(['iClear "Hinv".'], [h0, h1])
    assert blame(tr2, 2, "Hinv").repair == "duplicate-it-is-persistent"
    assert where_did_it_go(tr2, "Hinv").fate == "consumed"


def test_intuitionistic_hypothesis_at_qed_is_never_consumed() -> None:
    g0 = [IrisGoal(goal="P ∗ Q", intuitionistic=it(("HP", "P")), spatial=sp(("HQ", "Q")))]
    tr = trace_of(["iFrame."], [g0, []], finished=True)
    p = where_did_it_go(tr, "HP")
    assert p.fate == "live" and "persistent" in p.note
    assert where_did_it_go(tr, "HQ").fate == "framed"
    assert blame(tr, 3, "HP").repair == "restate"


def test_unknown_last_event_is_unknown_not_consumed() -> None:
    steps = [Step(step=0, state_id=0, tactic="<start>", goals=[IrisGoal(goal="P")]),
             Step(step=1, state_id=1, tactic="iLöb as \"IH\".", goals=[IrisGoal(goal="P")])]
    events = [Event(step=1, kind="Intro", tactic='iLöb as "IH".', hyp="IH", targets=["IH"])]
    tr = SimpleNamespace(steps=steps, events=events)
    p = where_did_it_go(tr, "IH")
    assert p.fate == "unknown" and "lost track" in p.note
    assert blame(tr, 2, "IH").repair == "unknown"
    assert where_did_it_go(tr, "nope").fate == "never-seen"


def test_rename_aliases_follow_the_chain() -> None:
    g0 = [IrisGoal(goal="P", spatial=sp(("H", "P")))]
    g1 = [IrisGoal(goal="P", spatial=sp(("HP", "P")))]
    tr = trace_of(['iRename "H" into "HP".'], [g0, g1])
    p = where_did_it_go(tr, "H")
    assert p.fate == "live" and p.live_as == "HP" and p.aliases == ["HP"]


def test_leftovers_unused_first_and_last_use() -> None:
    g0 = [IrisGoal(goal="P ∗ Q -∗ P")]
    g1 = [IrisGoal(goal="P", spatial=sp(("HP", "P"), ("HQ", "Q")))]
    tr = trace_of(['iIntros "[HP HQ]".'], [g0, g1])
    assert [h.id for h in leftovers(tr)] == ["HP", "HQ"]
    assert [h.id for h in leftovers(tr, 0)] == []
    assert "HP" in render_leftovers(leftovers(tr)) and render_leftovers([]) == "the spatial context is empty"
    assert unused_at_qed(tr) == [], "still live is not unused"
    tr2 = trace_of(['iIntros "[HP HQ]".', "iFrame."], [g0, g1, []], finished=True)
    assert unused_at_qed(tr2) == [] and render_unused([]) == "every resource was consumed"
    assert first_use(tr2, "HQ").kind == "Intro" and last_use(tr2, "HQ").kind == "Frame"
