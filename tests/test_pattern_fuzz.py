"""Property tests for the intro-pattern compiler and aligner (PLAN.md 7).

Two directions, and both matter:

* **No false negatives** -- the pattern the compiler synthesises for a prop must
  align with that prop.  If it did not, ``proof_destruct auto`` would emit tactics
  that fail.
* **No false positives** -- a pattern broken in one specific way must be reported,
  and a pattern that is merely *shorter* (right-nesting absorbs the rest) must not
  be.  A spurious mismatch sends the agent to the wrong place, which is the exact
  failure the aligner exists to prevent.
"""

from __future__ import annotations

import random

import pytest

from pcp.core.ipm.pattern import (
    PatternSyntaxError,
    align,
    compile_auto,
    parse_pattern,
)
from pcp.core.ipm.skeleton import parse_skeleton
from tests.gen import CAUGHT_MUTATIONS, mutate_pattern, random_pattern_for, random_skel


def test_compiled_pattern_always_aligns() -> None:
    """The compiler's own output must fit, for every shape we can generate."""
    bad: list[str] = []
    for seed in range(1500):
        rng = random.Random(seed)
        skel = random_skel(rng, depth=rng.choice([2, 3, 4]))
        d = compile_auto(skel, "H")
        report = align(d.pattern, skel, binders=d.binders)
        if not report.ok:
            bad.append(f"seed {seed}: {skel.to_notation()!r}\n{report.render()}")
    assert not bad, "compiled patterns that do not align:\n" + "\n\n".join(bad[:5])


def test_compiled_pattern_round_trips_through_the_printer() -> None:
    """Rendering the pattern to a string and re-parsing must not change it."""
    bad: list[str] = []
    for seed in range(1000):
        rng = random.Random(seed + 50_000)
        skel = random_skel(rng, depth=3)
        text = compile_auto(skel, "H").pattern_text
        try:
            if parse_pattern(text).render() != text:
                bad.append(f"seed {seed}: {text!r} -> {parse_pattern(text).render()!r}")
        except PatternSyntaxError as exc:
            bad.append(f"seed {seed}: {text!r} failed to re-parse: {exc}")
    assert not bad, "pattern round-trip failures:\n" + "\n".join(bad[:10])


def test_broken_patterns_are_caught() -> None:
    """Each one-step corruption of a fitting pattern must produce a mismatch."""
    missed: list[str] = []
    tried = {k: 0 for k in CAUGHT_MUTATIONS}
    for seed in range(2000):
        rng = random.Random(seed + 100_000)
        skel = random_skel(rng, depth=rng.choice([2, 3]))
        binders = compile_auto(skel, "H").binders
        good = random_pattern_for(rng, skel)
        if align(good, skel, binders=binders).mismatch is not None:
            continue  # generator produced an already-bad pattern; covered elsewhere
        mutated = mutate_pattern(rng, good)
        if mutated is None:
            continue
        broken, kind = mutated
        tried[kind] += 1
        if align(broken, skel, binders=binders).ok:
            missed.append(f"seed {seed} [{kind}]: {skel.to_notation()!r}\n  {broken.render()}")
    assert not missed, "corruptions the aligner missed:\n" + "\n".join(missed[:10])
    for kind, n in tried.items():
        assert n > 20, f"mutation {kind!r} exercised only {n} times"


def test_shorter_patterns_are_legal_not_mismatches() -> None:
    """∗/∧/∨ associate right, so a shorter pattern absorbs the residual chain."""
    assert align("[H1 H2]", "P ∗ Q ∗ R").ok
    assert align("[H1|H2]", "P ∨ Q ∨ R").ok
    # A conjunction pattern on a disjunction is an error at any length.
    assert not align("[H1 H2]", "P ∨ Q ∨ R").ok
    assert align("[H1 [H2 H3]]", "P ∗ Q ∗ R").ok
    # ... but not when the residual would have to be split further than it goes.
    assert not align("[H1 H2 H3]", "P ∗ Q").ok
    # ... and left-nesting is a genuinely different term.
    assert not align("[Ha Hb Hc]", "(P ∗ Q) ∗ R").ok
    assert align("[[Ha Hb] Hc]", "(P ∗ Q) ∗ R").ok


def test_disjunction_versus_conjunction_is_the_headline_diagnosis() -> None:
    report = align("[H1|H2]", "l ↦ v ∗ P")
    assert not report.ok
    assert report.mismatch is not None
    assert "disjunction" in report.mismatch.reason
    assert report.suggestion == "[H1 H2]"
    text = report.render()
    assert "prop skeleton:" in text and "pattern tree:" in text


def test_existential_needs_a_witness() -> None:
    report = align("[H1 H2]", "∃ γ, own γ (◯ n) ∗ P")
    assert not report.ok
    assert "existential" in report.mismatch.reason  # type: ignore[union-attr]
    # The compiler's answer names the witness as an iDestruct binder.
    d = compile_auto(parse_skeleton("∃ γ, own γ (◯ n) ∗ P"), "H")
    assert d.binders == ["γ"]
    assert d.idestruct("H") == 'iDestruct "H" as (γ) "[H1 H2]".'


def test_update_modality_must_be_eliminated_before_destructing() -> None:
    report = align("[H1 H2]", "|={⊤}=> P ∗ Q")
    assert not report.ok
    assert "update modality" in report.mismatch.reason  # type: ignore[union-attr]
    assert align(">[H1 H2]", "|={⊤}=> P ∗ Q").ok


def test_persistent_and_pure_markers_are_placed_by_the_compiler() -> None:
    d = compile_auto(parse_skeleton("⌜n = 3⌝ ∗ □ P ∗ l ↦ v"), "H")
    assert d.pattern_text == "[%H1 #H2 H3]"
    assert d.pure_names == ["H1"]


@pytest.mark.parametrize(
    "text",
    ["[H1 H2", "]", "[H1|", "(H1 & )", "[[H1]", "&&&"],
)
def test_malformed_patterns_raise_rather_than_mislead(text: str) -> None:
    with pytest.raises(PatternSyntaxError):
        parse_pattern(text)


def test_pattern_parser_accepts_the_ampersand_sugar() -> None:
    assert parse_pattern("(H1 & H2 & H3)").render() == "[H1 H2 H3]"
    assert align("(H1 & H2 & H3)", "P ∗ Q ∗ R").ok
