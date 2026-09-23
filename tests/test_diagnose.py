"""Diagnosis by construction (pcp.state.diagnose)."""

from __future__ import annotations

from pcp.state.diagnose import diagnose
from pcp.state.ipm.model import Hyp, IrisGoal, Modality


def test_iapply_gets_a_unification_report_not_the_leftover_report() -> None:
    goal = IrisGoal(goal="Q", spatial=[Hyp("Hw", "P -∗ Q'"), Hyp("HP", "P")])
    text = diagnose('iApply "Hw".', "iApply: cannot apply", goal)
    assert 'applying "Hw"' in text and "first mismatch" in text and "`Q'` vs `Q`" in text
    assert "premises that would remain: `P`" in text
    assert "spatial context is not empty" not in text
    lemma = diagnose('wp_apply (wp_load with "Hl").', "unification failed", goal)
    assert "applying `wp_load`" in lemma and "About wp_load." in lemma
    assert "spatial context is not empty" not in lemma


def test_closing_tactics_get_the_leftover_report() -> None:
    goal = IrisGoal(goal="P", spatial=[Hyp("HP", "P"), Hyp("HQ", "Q")])
    for tac in ("iFrame.", "done.", 'iExact "HP".', "by iFrame."):
        text = diagnose(tac, "", goal)
        assert 'the spatial context is not empty: "HP", "HQ"' in text, tac


def test_iintros_pure_pattern_peels_the_forall() -> None:
    goal = IrisGoal(goal="∀ x : nat, P x -∗ Q")
    ok = diagnose('iIntros "%x H".', "err", goal)
    assert "nothing left to introduce" not in ok and "pattern/prop mismatch" not in ok
    bad = diagnose('iIntros "%x [H1|H2]".', "err", IrisGoal(goal="∀ x : nat, P x ∗ R -∗ Q"))
    assert "introducing premise 2" in bad and "disjunction" in bad
    binder = diagnose('iIntros (x) "[H1 H2]".', "err", IrisGoal(goal="∀ x y : nat, P x -∗ Q"))
    assert "introduce the variable first" in binder, binder
    too_many = diagnose('iIntros "H1 H2".', "err", IrisGoal(goal="P -∗ Q"))
    assert "pattern 2 (H2) has nothing left to introduce" in too_many


def test_lemma_with_subject_is_reported_honestly() -> None:
    goal = IrisGoal(goal="R", spatial=[Hyp("H", "l ↦ v")])
    text = diagnose('iDestruct (foo with "H") as "[H1 H2]".', "err", goal)
    assert "conclusion of `foo`" in text and "About foo." in text
    assert 'destructuring "H"' not in text
    text2 = diagnose('iMod (inv_acc with "Hinv") as "[HP Hclose]".', "err", goal)
    assert "conclusion of `inv_acc`" in text2


def test_named_subject_is_aligned_and_legal_tokens_never_fail_to_parse() -> None:
    goal = IrisGoal(goal="R", spatial=[Hyp("H", "P ∗ Q")])
    for pattern in ("[H1 H2]", "[%x H]", "[#H1 H2]", "(H1 & H2)", ">[H1 H2]", "[H1|H2]", "[_ ?]", "->", "[]"):
        text = diagnose(f'iDestruct "H" as "{pattern}".', "err", goal)
        assert "does not parse" not in text, pattern
    bad = diagnose('iDestruct "H" as "[H1 H2".', "err", goal)
    assert "does not parse" in bad and 'a pattern that fits "H": [H1 H2]' in bad
    mismatch = diagnose('iDestruct "H" as "[H1|H2]".', "err", goal)
    assert 'destructuring "H"' in mismatch and "disjunction" in mismatch and "a pattern that fits: [H1 H2]" in mismatch


def test_imod_peels_the_update_modality_before_binders() -> None:
    goal = IrisGoal(goal="R", spatial=[Hyp("H", "|==> ∃ x, P x ∗ Q")])
    text = diagnose('iMod "H" as (x) "[H1|H2]".', "err", goal)
    assert "binder names were given" not in text
    assert "disjunction" in text and "separating conjunction" in text
    extra = diagnose('iDestruct "H" as (x y) "[H1 H2]".', "err", IrisGoal(goal="R", spatial=[Hyp("H", "∃ x, P x")]))
    assert "2 binder names were given but the hypothesis has 1" in extra


def test_icombine_gives_pattern_is_honest() -> None:
    goal = IrisGoal(goal="R", spatial=[Hyp("H1", "l ↦{#1/2} v"), Hyp("H2", "l ↦{#1/2} w")])
    assert diagnose('iCombine "H1" "H2" as "H".', "err", goal).count("destructuring") == 0
    text = diagnose('iCombine "H1" "H2" gives "%Heq".', "err", goal)
    assert "does not parse" not in text and 'destructuring "H1"' not in text


def test_mask_block_only_when_the_error_mentions_masks() -> None:
    goal = IrisGoal(goal="|={⊤ ∖ ↑N}=> P", modality=Modality(mask="⊤ ∖ ↑N", fupd=True))
    with_mask = diagnose("wp_store.", "iInv: mask ↑N is not a subset of ⊤ ∖ ↑N", goal)
    assert "current modality: mask ⊤ ∖ ↑N" in with_mask and "fupd_mask_subseteq" in with_mask
    without = diagnose("wp_store.", "wp_store: cannot find 'Store' in WP", goal)
    assert "current modality" not in without


def test_empty_inputs() -> None:
    assert diagnose("", "", None) == ""
    assert diagnose("iFrame.", "boom", None) == "boom"
