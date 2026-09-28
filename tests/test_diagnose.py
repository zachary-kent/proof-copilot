"""Diagnosis by construction (pcp.state.diagnose)."""

from __future__ import annotations

from pcp.state.diagnose import diagnose, diagnose_structured
from pcp.state.ipm.model import Hyp, IrisGoal, Modality


def test_iapply_gets_a_unification_report_not_the_leftover_report() -> None:
    goal = IrisGoal(goal="Q", spatial=[Hyp("Hw", "P -∗ Q'"), Hyp("HP", "P")])
    text = diagnose('iApply "Hw".', "iApply: cannot apply", goal)
    assert 'applying "Hw"' in text and "first mismatch" in text and "`Q'` vs `Q`" in text
    assert "premises that would remain: `P`" in text
    assert "spatial context is not empty" not in text
    # A lemma's statement is not in the proof state: against a non-WP goal nothing
    # observable bears on the failure, so nothing is said (calibration, D2).
    lemma = diagnose('wp_apply (wp_load with "Hl").', "unification failed", goal)
    assert lemma == "unification failed"
    wp = IrisGoal(goal="WP ! #l {{ v, Φ v }}", spatial=[Hyp("Hl", "l ↦ #1")])
    lemma = diagnose('wp_apply (acquire_spec with "Hl").', "unification failed", wp)
    assert "the WP's next redex is `! #l` (a load)" in lemma and "About acquire_spec." in lemma
    assert "spatial context is not empty" not in lemma


def test_closing_tactics_name_the_unmatched_conjunct_not_the_leftovers() -> None:
    goal = IrisGoal(goal="P ∗ R", spatial=[Hyp("HP", "P"), Hyp("HQ", "Q")])
    for tac in ("iFrame.", "done.", 'iExact "HP".', "by iFrame."):
        text = diagnose(tac, "Tactic failure: done: goal not solved", goal)
        assert "no hypothesis matches this goal conjunct: `R`" in text, tac
        # Leftovers do not stop an affine goal from closing: they are not blamed.
        assert "spatial context is not empty" not in text and '"HQ"' not in text, tac
    matched = diagnose("done.", "done failed", IrisGoal(goal="P", spatial=[Hyp("HP", "P"), Hyp("HQ", "Q")]))
    assert matched == "done failed"
    linear = diagnose("done.", "iStopProof: spatial context not empty (not affine)", goal)
    assert 'the error is about the remaining spatial context: "HP", "HQ"' in linear


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


PATTERN_ERROR = "Tactic failure: iDestruct: (P) is not a separating conjunction (IntoSep)."


def test_lemma_with_subject_is_reported_honestly() -> None:
    goal = IrisGoal(goal="R", spatial=[Hyp("H", "l ↦ v")])
    text = diagnose('iDestruct (foo with "H") as "[H1 H2]".', PATTERN_ERROR, goal)
    assert "conclusion of `foo`" in text and "About foo." in text
    assert 'destructuring "H"' not in text
    text2 = diagnose('iMod (inv_acc with "Hinv") as "[HP Hclose]".', PATTERN_ERROR, goal)
    assert "conclusion of `inv_acc`" in text2
    # An error that is not about the pattern gets no pattern paragraph at all (issue 8).
    assert diagnose('iMod (inv_acc with "Hinv") as "[HP Hclose]".', "err", goal) == "err"


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


# ------------------------------------------------------- framing (issue 8)

ISSUE8_TACTIC = 'iMod (hazptr.(hazard_domain_register) (node vs) with "Hdom [$Hb $†Hb //]") as "Hmanaged".'
ISSUE8_ERROR = "Tactic failure: iFrame: cannot frame († backup … n)."


def _issue8_goal(conclusion: str = "WP #() {{ v, Φ v }}") -> IrisGoal:
    return IrisGoal(
        goal=conclusion,
        pure=[Hyp("Hlen", "n = length vs", klass="pure")],
        intuitionistic=[Hyp("Hdom", "hazard_domain γ d", klass="intuitionistic")],
        spatial=[Hyp("Hb", "backup ↦∗ vs"), Hyp("†Hb", "† backup … n")],
    )


def test_record_projection_is_not_taken_for_the_lemma() -> None:
    from pcp.state.tactic import term_head

    assert term_head('(hazptr.(hazard_domain_register) (node vs) with "Hdom")') == "hazard_domain_register"
    assert term_head('((foo x) with "H")') == "foo"
    assert term_head("(@lem _ with \"H\")") == "lem"
    text = diagnose('iDestruct (hazptr.(hazard_domain_register) with "H") as "[H1 H2]".', PATTERN_ERROR,
                    IrisGoal(goal="R", spatial=[Hyp("H", "P")]))
    assert "conclusion of `hazard_domain_register`" in text and "`hazptr`" not in text


def test_framing_error_gets_no_destruct_pattern_report_and_names_the_equality() -> None:
    text = diagnose(ISSUE8_TACTIC, ISSUE8_ERROR, _issue8_goal())
    assert "Hmanaged" not in text.split(ISSUE8_ERROR)[-1]
    assert "conclusion of" not in text and "`hazptr`" not in text
    assert 'framing failed on `† backup … n` (hypothesis "†Hb")' in text
    assert "premise of `hazard_domain_register`" in text
    assert '"Hlen" : n = length vs' in text
    assert "tactics that apply" not in text


def test_framing_error_compares_with_the_closest_counterpart() -> None:
    goal = _issue8_goal("† backup … (length vs) ∗ backup ↦∗ vs")
    text = diagnose('iFrame "†Hb".', "iFrame: cannot frame († backup … n)", goal)
    assert "the term to frame has `n`; the closest goal conjunct `† backup … (length vs)` has `length vs`" in text, text
    assert "spatial context is not empty" not in text


# ------------------------------------------------------ focusing (issue 12)


def test_focus_error_suggests_a_bullet_not_goal_tactics() -> None:
    goal = IrisGoal(goal="WP e {{ v, Φ v }}")
    text = diagnose("rewrite Nat.add_0_r.", "Error: Expected a single focused goal but 2 goals are focused.", goal)
    assert "2 goals are focused" in text and "bullet (`- tac.`)" in text and "`{ tac. … }`" in text
    assert "wp_apply" not in text and "wp_pures" not in text and "tactics that apply" not in text
    counted = diagnose("rewrite H.", "Expected a single focused goal", goal, n_goals=3)
    assert "3 goals are focused" in counted
    bullet = diagnose("- done.", "Wrong bullet -: Current bullet - is not finished.", goal)
    assert "bullet mismatch" in bullet and "wp_" not in bullet
    nogoal = diagnose("- done.", "No such goal. Focus next goal with bullet +.", goal)
    assert "`+`" in nogoal and "wp_" not in nogoal


# ------------------------------------------- calibration and structure (D2)


def test_structured_diagnosis_carries_repair_class_confidence_and_evidence() -> None:
    dx = diagnose_structured(ISSUE8_TACTIC, ISSUE8_ERROR, _issue8_goal())
    assert dx.family == "frame" and dx.repair == "rewrite-before-frame" and dx.confidence == "low"
    assert dx.text == diagnose(ISSUE8_TACTIC, ISSUE8_ERROR, _issue8_goal())
    assert any("n = length vs" in e for e in dx.evidence)
    close = diagnose_structured('iFrame "†Hb".', "iFrame: cannot frame († backup … n)",
                                _issue8_goal("† backup … (length vs) ∗ backup ↦∗ vs"))
    assert (close.repair, close.confidence) == ("rewrite-before-frame", "high")
    focus = diagnose_structured("rewrite H.", "Expected a single focused goal but 2 goals are focused.", None)
    assert (focus.family, focus.repair, focus.confidence) == ("focus", "bullet", "high")
    assert focus.to_json() == {"family": "focus", "repair": "bullet", "confidence": "high",
                               "evidence": ["error: expected a single focused goal"]}


def test_nothing_observed_means_nothing_said() -> None:
    """The ledger's rule applied to the prose: no generic tactic list, no leftovers
    paragraph, no mask block, when nothing in the goal or error backs them."""
    goal = IrisGoal(goal="P ∗ Q", spatial=[Hyp("HP", "P"), Hyp("HQ", "Q")])
    dx = diagnose_structured("iSomething.", "Tactic failure: something went wrong.", goal)
    assert dx.text == "Tactic failure: something went wrong." and (dx.repair, dx.confidence) == ("unknown", "low")
    assert "tactics that apply" not in diagnose("iInv N as \"H\".", "Tactic failure: iInv: failed.", goal)
    assert "current modality" not in diagnose("iInv N as \"H\".", "Tactic failure: iInv: failed.", goal)


def test_goal_shape_tactics_only_when_the_error_says_the_tactic_does_not_fit() -> None:
    goal = IrisGoal(goal="P ∨ Q", spatial=[Hyp("HP", "P")])
    dx = diagnose_structured('iSplitL "HP".', "Tactic failure: iSplitL: P ∨ Q is not a separating conjunction.", goal)
    assert dx.repair == "goal-shape" and dx.confidence == "low" and "iLeft" in dx.text


def test_failed_wp_tactic_names_the_actual_redex() -> None:
    goal = IrisGoal(goal='WP let: "x" := ! #l in "x" {{ v, Φ v }}', spatial=[Hyp("Hk", "k ↦ #0")])
    dx = diagnose_structured("wp_store.", "Tactic failure: wp_store: cannot find 'Store' in the WP.", goal)
    assert dx.repair == "wp-next-step" and dx.confidence == "high"
    assert "the WP's next redex is `! #l`: a load" in dx.text and "not what `wp_store` steps" in dx.text
    assert "there is no `l ↦ …` in the context" in dx.text
    not_wp = diagnose_structured("wp_load.", "wp_load: cannot find 'Load'", IrisGoal(goal="|={⊤}=> Φ #1"))
    assert "is not a WP at its head" in not_wp.text


def test_long_errors_keep_their_cause_at_the_tail() -> None:
    error = "Error: In environment\n" + "\n".join(f"x{i} : nat" for i in range(400)) + \
        "\nThe term \"v\" has type \"vec val 2\" while it is expected to have type \"vec loc ?n\"."
    text = diagnose("exact v.", error, None)
    assert text.endswith('while it is expected to have type "vec loc ?n".') and len(text) <= 1300
