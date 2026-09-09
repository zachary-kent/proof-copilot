"""Structural diff rules (pcp.state.ledger.diff), one test per matching rule and per legacy bug."""

from __future__ import annotations

import _ipm_standin  # noqa: F401

from pcp.state.ipm.model import Hyp, IrisGoal, Modality
from pcp.state.ledger.diff import align_goals, diff_context, diff_step, is_instantiation


def sp(*pairs: tuple[str, str]) -> list[Hyp]:
    return [Hyp(i, p) for i, p in pairs]


def it(*pairs: tuple[str, str]) -> list[Hyp]:
    return [Hyp(i, p, klass="intuitionistic") for i, p in pairs]


def goal(gid: str, conclusion: str, *, spatial=(), intuit=(), pure=(), mask=None, laters=0, fupd=False, bupd=False) -> IrisGoal:
    return IrisGoal(
        goal_id=gid, goal=conclusion, spatial=list(spatial), intuitionistic=list(intuit),
        pure=[Hyp(i, p, klass="pure") for i, p in pure],
        modality=Modality(mask=mask, laters=laters, fupd=fupd, bupd=bupd),
    )


def kinds(events, *ks):
    return [e for e in events if e.kind in ks]


# ---------------------------------------------------------------- context rules


def test_context_rules_unchanged_rename_update_consume_produce() -> None:
    prev = sp(("A", "P"), ("B", "Q"), ("C", "R"), ("D", "S"))
    next_ = sp(("A", "P"), ("B2", "Q"), ("C", "R'"), ("E", "T"))
    cd = diff_context(prev, next_)
    assert cd.unchanged == ("A",)
    assert cd.renamed == (("B", "B2"),)
    assert cd.updated == ("C",)
    assert cd.consumed == ("D",)
    assert cd.produced == ("E",)


def test_instantiate_with_unicode_evar_is_not_consume_or_produce() -> None:
    assert is_instantiation("own γ ?Φ", "own γ (λ v, ⌜v = 3⌝)")
    assert is_instantiation("P ?Goal3", "P ?Goal7")
    assert not is_instantiation("P", "Q")
    prev = [goal("g0", "WP e {{ ?Φ }}", spatial=sp(("H", "own γ ?Φ"), ("HQ", "Q")))]
    next_ = [goal("g0", "WP e {{ λ v, ⌜v = 3⌝ }}", spatial=sp(("H", "own γ (λ v, ⌜v = 3⌝)"), ("HQ", "Q")))]
    events = diff_step(prev, next_, step=2, tactic="iExists (λ v, ⌜v = 3⌝).")
    assert [e.kind for e in events] == ["Instantiate"] and events[0].hyp == "H"


def test_sibling_evar_instantiation_does_not_fabricate_a_goal_split() -> None:
    prev = [goal("g0", "Q ?x", spatial=sp(("H", "P"))), goal("g1", "S ?x", spatial=sp(("H2", "R ?x")))]
    next_ = [goal("g0", "Q 3", spatial=sp(("H", "P"))), goal("g1", "S 3", spatial=sp(("H2", "R 3")))]
    al = align_goals(prev, next_)
    assert len(al.children) == 1 and len(al.untouched) == 1
    events = diff_step(prev, next_, step=2, tactic="iExists 3.")
    assert not kinds(events, "GoalSplit", "Consume", "Produce"), [e.render() for e in events]


# ------------------------------------------------------------------ closing


def test_closing_a_non_final_goal_emits_goal_closed_and_consumption() -> None:
    prev = [goal("g0", "R", spatial=sp(("HR", "R"))), goal("g1", "P ∗ Q", spatial=sp(("HP", "P"), ("HQ", "Q")))]
    next_ = [goal("g0", "P ∗ Q", spatial=sp(("HP", "P"), ("HQ", "Q")))]
    events = diff_step(prev, next_, step=3, tactic="iFrame.")
    closed = kinds(events, "GoalClosed")
    assert len(closed) == 1 and closed[0].goal_id == "g0" and "siblings remain" in closed[0].detail
    spent = kinds(events, "Frame", "Consume")
    assert [(e.kind, e.hyp, e.confidence) for e in spent] == [("Frame", "HR", "certain")]
    assert spent[0].detail == "spent closing the goal" and spent[0].sources == ["HR"]


def test_qed_under_a_mask_emits_no_mask_change_or_later_intro() -> None:
    prev = [goal("g0", "▷ P", spatial=sp(("HP", "P")), intuit=it(("Hinv", "inv N P")), mask="⊤ ∖ ↑N", laters=1)]
    events = diff_step(prev, [], step=4, tactic="iFrame.")
    assert not kinds(events, "MaskChange", "LaterIntro", "ModIntro")
    assert [e.kind for e in events] == ["GoalClosed", "Frame"]
    assert "proof is complete" in events[0].detail
    assert not [e for e in events if e.hyp == "Hinv"], "intuitionistic hypotheses are never consumed"


def test_several_goals_closing_together_is_uncertain() -> None:
    prev = [goal("g0", "P", spatial=sp(("HP", "P"))), goal("g1", "Q", spatial=sp(("HQ", "Q")))]
    events = diff_step(prev, [], step=2, tactic="all: iFrame.")
    assert [e.kind for e in kinds(events, "GoalClosed")] == ["GoalClosed", "GoalClosed"]
    assert all(e.confidence == "unknown" for e in kinds(events, "Consume"))


# ----------------------------------------------------------------- persistence


def test_intuitionistic_destruct_is_split_not_consume() -> None:
    prev = [goal("g0", "R", intuit=it(("H", "P ∧ Q")))]
    next_ = [goal("g0", "R", intuit=it(("H1", "P"), ("H2", "Q")))]
    events = diff_step(prev, next_, step=2, tactic='iDestruct "H" as "[H1 H2]".')
    assert not kinds(events, "Consume")
    splits = kinds(events, "Split")
    assert [e.hyp for e in splits] == ["H1", "H2"]
    assert all(e.sources == ["H"] and e.targets == ["H1", "H2"] and e.klass == "intuitionistic" for e in splits)


def test_boxed_hypothesis_moved_with_hash_is_persist() -> None:
    prev = [goal("g0", "P ∗ P", spatial=sp(("H", "□ P")))]
    next_ = [goal("g0", "P ∗ P", intuit=it(("H2", "P")))]
    events = diff_step(prev, next_, step=2, tactic='iDestruct "H" as "#H2".')
    assert [e.kind for e in events] == ["Persist"]
    assert events[0].hyp == "H2" and events[0].sources == ["H"]


def test_same_name_spatial_to_intuitionistic_is_persist() -> None:
    prev = [goal("g0", "P", spatial=sp(("Hinv", "inv N P")))]
    next_ = [goal("g0", "P", intuit=it(("Hinv", "inv N P")))]
    events = diff_step(prev, next_, step=2, tactic='iDestruct "Hinv" as "#Hinv".')
    assert [e.kind for e in events] == ["Persist"]


def test_framing_a_persistent_hypothesis_keeps_it_live() -> None:
    prev = [goal("g0", "P ∗ P ∗ Q", intuit=it(("HP", "P")), spatial=sp(("HQ", "Q")))]
    next_ = [goal("g0", "Q", intuit=it(("HP", "P")), spatial=sp(("HQ", "Q")))]
    events = diff_step(prev, next_, step=2, tactic='iFrame "HP".')
    assert [(e.kind, e.hyp, e.klass) for e in events] == [("Frame", "HP", "intuitionistic")]


# ------------------------------------------------------------------- splitting


def test_split_events_carry_targets() -> None:
    prev = [goal("g0", "R ∗ Q ∗ P", spatial=sp(("HP", "P"), ("H", "Q ∗ R")))]
    next_ = [goal("g0", "R ∗ Q ∗ P", spatial=sp(("HP", "P"), ("HQ", "Q"), ("HR", "R")))]
    events = diff_step(prev, next_, step=2, tactic='iDestruct "H" as "[HQ HR]".')
    consume = kinds(events, "Consume")
    assert [(e.hyp, e.sources, e.targets) for e in consume] == [("H", ["H"], ["HQ", "HR"])]
    splits = kinds(events, "Split")
    assert [(e.hyp, e.sources, e.targets) for e in splits] == [("HQ", ["H"], ["HQ", "HR"]), ("HR", ["H"], ["HQ", "HR"])]


def test_goal_split_routes_hypotheses_without_consuming_them() -> None:
    prev = [goal("g0", "(P ∗ Q) ∗ R", spatial=sp(("HP", "P"), ("HQ", "Q"), ("HR", "R")))]
    next_ = [goal("g0", "R", spatial=sp(("HR", "R"))), goal("g1", "P ∗ Q", spatial=sp(("HP", "P"), ("HQ", "Q")))]
    events = diff_step(prev, next_, step=2, tactic='iSplitL "HR".')
    split = kinds(events, "GoalSplit")
    assert len(split) == 1 and split[0].goal_id == "g0" and split[0].targets == ["g0", "g1"]
    assert "HR → g0" in split[0].detail and "HP, HQ → g1" in split[0].detail
    assert not kinds(events, "Consume", "Frame", "Produce", "Unknown"), [e.render() for e in events]


def test_disjunction_destruct_splits_into_two_goals() -> None:
    prev = [goal("g0", "R", spatial=sp(("H", "P ∨ Q"), ("HS", "S")))]
    next_ = [goal("g0", "R", spatial=sp(("H1", "P"), ("HS", "S"))), goal("g1", "R", spatial=sp(("H2", "Q"), ("HS", "S")))]
    events = diff_step(prev, next_, step=2, tactic='iDestruct "H" as "[H1|H2]".')
    assert kinds(events, "GoalSplit")
    consume = kinds(events, "Consume")
    assert [(e.hyp, e.goal_id, e.targets) for e in consume] == [("H", "g0", ["H1", "H2"])]
    splits = kinds(events, "Split")
    assert [(e.hyp, e.goal_id, e.sources, e.targets) for e in splits] == [
        ("H1", "g0", ["H"], ["H1", "H2"]), ("H2", "g1", ["H"], ["H1", "H2"]),
    ]
    assert not [e for e in events if e.hyp == "HS"], "HS moved to both children: still live, not consumed"


def test_touching_several_goals_at_once_is_unknown() -> None:
    prev = [goal("g0", "P", spatial=sp(("HP", "P"))), goal("g1", "Q ∗ Q", spatial=sp(("HQ", "Q")))]
    next_ = [goal("g0", "P'", spatial=sp(("HP", "P"))), goal("g1", "Q'", spatial=sp(("HQ", "Q")))]
    events = diff_step(prev, next_, step=2, tactic="all: simpl.")
    assert [e.kind for e in events] == ["Unknown"] and events[0].confidence == "unknown"


def test_identical_props_with_moved_names_are_unknown() -> None:
    prev = [goal("g0", "R", spatial=sp(("A", "own γ (◯ 1)"), ("B", "own γ (◯ 1)")))]
    next_ = [goal("g0", "R", spatial=sp(("C", "own γ (◯ 1)"), ("D", "own γ (◯ 1)")))]
    events = diff_step(prev, next_, step=2, tactic="iRename \"A\" into \"C\"; iRename \"B\" into \"D\".")
    assert {e.kind for e in events} == {"Unknown"}
    assert {e.hyp for e in events} == {"A", "B", "C", "D"}
    assert all(e.confidence == "unknown" for e in events)


# --------------------------------------------------------------- frame/intro


def test_frame_is_detected_structurally_when_the_goal_loses_the_conjunct() -> None:
    prev = [goal("g0", "P ∗ Q", spatial=sp(("HP", "P"), ("HQ", "Q")))]
    next_ = [goal("g0", "Q", spatial=sp(("HQ", "Q")))]
    events = diff_step(prev, next_, step=2, tactic='iApply (sep_mono_l with "HP").')
    assert [(e.kind, e.hyp) for e in events] == [("Frame", "HP")]


def test_intro_events_and_pure_move_detail() -> None:
    prev = [goal("g0", "P ∗ ⌜x = 3⌝ -∗ Q")]
    next_ = [goal("g0", "Q", spatial=sp(("HP", "P"), ("Hx", "⌜x = 3⌝")))]
    events = diff_step(prev, next_, step=1, tactic='iIntros "[HP Hx]".')
    assert [(e.kind, e.hyp, e.targets) for e in events] == [("Intro", "HP", ["HP", "Hx"]), ("Intro", "Hx", ["HP", "Hx"])]
    moved = diff_step(next_, [goal("g0", "Q", spatial=sp(("HP", "P")), pure=(("Hx", "x = 3"),))],
                      step=2, tactic='iDestruct "Hx" as %Hx.')
    assert [(e.kind, e.hyp) for e in moved] == [("Consume", "Hx")] and "pure" in moved[0].detail


def test_modality_events() -> None:
    prev = [goal("g0", "|={⊤}=> P", spatial=sp(("HP", "P")), fupd=True)]
    inv = [goal("g0", "▷ P", spatial=sp(("HP", "P"), ("Hclose", "▷ P ={⊤ ∖ ↑N,⊤}=∗ True")), mask="⊤ ∖ ↑N", laters=1, fupd=True)]
    events = diff_step(prev, inv, step=2, tactic='iInv "Hinv" as "HP2" "Hclose".')
    assert [e.detail for e in kinds(events, "MaskChange")] == ["⊤ → ⊤ ∖ ↑N"]
    assert [e.detail for e in kinds(events, "LaterIntro")] == ["later depth +1"]
    intro = diff_step([goal("g0", "|==> P", spatial=sp(("HP", "P")), bupd=True)],
                      [goal("g0", "P", spatial=sp(("HP", "P")))], step=3, tactic="iModIntro.")
    assert [e.kind for e in intro] == ["ModIntro"]
    imod = diff_step([goal("g0", "R", spatial=sp(("H", "|==> P")))],
                     [goal("g0", "R", spatial=sp(("H", "P")))], step=3, tactic='iMod "H" as "H".')
    assert [e.kind for e in imod] == ["Update"], "eliminating a hypothesis' modality is not a ModIntro"


def test_step_zero_and_rename_events() -> None:
    assert diff_step([], [goal("g0", "P")], step=0, tactic="<start>") == []
    events = diff_step([goal("g0", "P", spatial=sp(("H", "P")))], [goal("g0", "P", spatial=sp(("HP", "P")))],
                       step=1, tactic='iRename "H" into "HP".')
    assert [(e.kind, e.hyp, e.sources) for e in events] == [("Rename", "HP", ["H"])]
