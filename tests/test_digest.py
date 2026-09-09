"""PropStore, Selector, head symbols and folding (pcp.state.digest)."""

from __future__ import annotations

import _ipm_standin  # noqa: F401  -- installs skeleton/pattern stand-ins when absent

from pcp.state.digest import (
    PropStore,
    Selector,
    estimate_tokens,
    fold_id,
    head_symbol,
    heads,
    render_prop,
)
from pcp.state.ipm.model import Hyp, IrisGoal
from pcp.state.props import prop_hash

FIVE_LINES = "inv N (∃ v,\n  l ↦ v ∗\n  own γ v ∗\n  ⌜v = 3⌝ ∗\n  True)"


def test_store_keeps_first_spelling_and_full_hashes() -> None:
    store = PropStore()
    h1 = store.put("P ?Goal3")
    h2 = store.put("P  ?Goal7")
    assert h1 == h2 and store.get(h1) == "P ?Goal3"
    assert len(h1.split(":")[1]) == 32, "128-bit hashes, not the legacy 32-bit truncation"
    assert PropStore.from_json(store.to_json()).get(h1) == "P ?Goal3"


def test_store_update_interns_every_prop_of_a_goal() -> None:
    goal = IrisGoal(goal="WP e {{ Φ }}", pure=[Hyp("σ", "state", klass="pure")], spatial=[Hyp("Hl", "l ↦ v")])
    store = PropStore()
    store.update([goal])
    assert store.get(goal.goal_hash) == "WP e {{ Φ }}"
    assert store.get(goal.spatial[0].hash) == "l ↦ v"
    assert store.get(goal.pure[0].hash) == "state"
    assert prop_hash("l ↦ v") in store


def test_selector_grammar() -> None:
    sel = Selector.parse("H*, spatial, mentions:γ, head:WP")
    assert sel.globs == ("H*",) and "spatial" in sel.classes
    assert sel.mentions == ("γ",) and sel.heads == ("WP",)
    assert Selector.parse("").everything and Selector.parse(None).everything
    assert sel.matches("Hinv", "inv N P", "intuitionistic")
    assert sel.matches("Q", "own γ x", "intuitionistic")
    assert sel.matches("X", "WP e {{ Φ }}", "intuitionistic")
    assert not sel.matches("X", "P", "intuitionistic")
    assert Selector.parse("changed").matches("X", "P", "spatial", changed=True)
    assert not Selector.parse("changed").matches("X", "P", "spatial", changed=False)


def test_selector_explicit_is_by_name_not_by_class() -> None:
    assert Selector.parse("Hinv").explicit("Hinv", "inv N P")
    assert Selector.parse("mentions:γ").explicit("H", "own γ x")
    assert not Selector.parse("spatial").explicit("H", "P")
    assert not Selector.parse("").explicit("H", "P")
    assert Selector.parse("x").explicit("_1", "nat", names=["x"])


def test_head_symbol_wp_pointsto_own_and_connectives() -> None:
    assert head_symbol("WP e {{ Φ }}") == "WP"
    assert head_symbol("▷ □ WP e @ ⊤ {{ Φ }}") == "WP"
    assert head_symbol("l ↦ v") == "↦"
    assert head_symbol("l ↦{#q} v") == "↦"
    assert head_symbol("own γ (● x)") == "own"
    assert head_symbol("P ∗ Q") == "∗"
    assert head_symbol("⌜x = 3⌝") == "⌜⌝"
    assert head_symbol("∃ n, Φ n") == "∃"


def test_heads_of_a_wp_goal_include_its_postcondition() -> None:
    hs = heads("WP ! #l {{ w, ⌜w = v⌝ ∗ l ↦ v }}")
    assert "WP" in hs and "↦" in hs


def test_full_never_folds_and_folded_modes_do() -> None:
    assert render_prop(FIVE_LINES, "full") == FIVE_LINES
    assert render_prop(FIVE_LINES, "full", fold_over_lines=1) == FIVE_LINES
    folded = render_prop(FIVE_LINES, "folded", hash="h:341b3329abcdef")
    assert folded.startswith("⟨fold:341b3329 · inv N (∃ v,") and folded.endswith("5 lines⟩")
    assert render_prop("P ∗ Q", "folded") == "P ∗ Q", "short props are not stubbed"
    assert render_prop(FIVE_LINES, "summary") == "inv N (∃ v,"
    assert render_prop("P", "hash-only", hash="h:abc") == "h:abc"
    assert fold_id("h:0123456789abcdef") == "01234567"


def test_estimate_tokens_is_chars_over_four() -> None:
    assert estimate_tokens("") == 0
    assert estimate_tokens("ab") == 1
    assert estimate_tokens("x" * 400) == 100
