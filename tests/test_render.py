"""Budgeted rendering (pcp.state.render)."""

from __future__ import annotations

import _ipm_standin  # noqa: F401

from pcp.state.digest import PropStore
from pcp.state.ipm.model import Hyp, IrisGoal, Modality
from pcp.state.render import render_goal

INV = "inv N (∃ v,\n  l ↦ v ∗\n  own γ v ∗\n  ⌜v = 3⌝ ∗\n  True)"


def wp_goal() -> IrisGoal:
    return IrisGoal(
        goal="WP ! #l {{ w, ⌜w = v⌝ ∗ l ↦ v }}",
        pure=[Hyp("σ", "state", klass="pure")],
        intuitionistic=[Hyp("Hinv", INV, klass="intuitionistic", persistent=True)],
        spatial=[Hyp("Hl", "l ↦ v"), Hyp("HQ", "Q")],
        modality=Modality(wp=None),
    )


def test_explicit_selection_beats_diff_only() -> None:
    goal = wp_goal()
    r = render_goal(goal, select="Hinv", diff_only=True, prev=goal)
    assert '"Hinv" :' in r.text and r.shown == 1
    assert "Hinv=unchanged" not in r.text
    assert "Hl" in r.manifest and "HQ" in r.manifest


def test_diff_only_demotes_unchanged_including_pure() -> None:
    goal = wp_goal()
    changed = wp_goal()
    changed.spatial[1] = Hyp("HQ", "Q'")
    r = render_goal(changed, diff_only=True, prev=goal)
    assert '"HQ" : Q\'' in r.text
    assert "σ=unchanged" in r.text and "Hinv=unchanged" in r.text and "Hl=unchanged" in r.text
    assert r.shown == 1 and r.total == 4


def test_footer_is_always_present_and_reports_elision() -> None:
    goal = wp_goal()
    r = render_goal(goal, budget=10_000)
    assert r.text.splitlines()[-1].startswith("rendered 4/4 hypotheses · ")
    tight = render_goal(goal, budget=30)
    assert "… budget exhausted, omitted:" in tight.text
    assert tight.elided and tight.text.splitlines()[-1].startswith(f"rendered {tight.shown}/4 hypotheses")
    assert "⊢ WP" in tight.text, "the goal is charged first and always rendered"


def test_full_never_folds_folded_does() -> None:
    goal = wp_goal()
    full = render_goal(goal, select="Hinv", mode="full")
    assert INV in full.text and "⟨fold:" not in full.text
    folded = render_goal(goal, select="Hinv", mode="folded")
    assert "⟨fold:" in folded.text and "5 lines⟩" in folded.text


def test_relevance_on_a_wp_goal_keeps_spatial_hypotheses() -> None:
    goal = wp_goal()
    r = render_goal(goal, relevance=True)
    assert '"Hl" :' in r.text and '"HQ" :' in r.text, r.text
    assert "Hl~" not in r.text


def test_relevance_never_demotes_everything() -> None:
    goal = IrisGoal(goal="own γ x", spatial=[Hyp("HP", "P"), Hyp("HQ", "Q")])
    r = render_goal(goal, relevance=True)
    assert r.shown == 2 and "~" not in r.text


def test_relevance_demotes_the_irrelevant_when_something_intersects() -> None:
    goal = IrisGoal(goal="l ↦ v ∗ True", spatial=[Hyp("Hl", "l ↦ v"), Hyp("HQ", "Q")],
                    intuitionistic=[Hyp("Hinv", "inv N P", klass="intuitionistic")])
    r = render_goal(goal, relevance=True)
    assert '"Hl" :' in r.text and "HQ~" in r.text and "Hinv~" in r.text
    named = render_goal(goal, relevance=True, relevant_to='iApply (foo with "HQ").')
    assert '"HQ" :' in named.text


def test_header_flags_store_and_selector_manifest() -> None:
    goal = wp_goal()
    store = PropStore()
    r = render_goal(goal, select="spatial", store=store)
    assert r.text.startswith("goal g0")
    assert "  … not shown: σ, Hinv" in r.text
    assert store.get(goal.intuitionistic[0].hash) == INV
    assert "[persistent]" in render_goal(goal, select="Hinv").text
