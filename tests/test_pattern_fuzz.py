"""Property tests for the intro-pattern grammar, compiler and aligner (PLAN.md 7).

* **No false negatives**: the pattern the compiler synthesises for a prop must align
  with that prop, or ``proof_destruct auto`` would emit tactics that fail.
* **No false positives**: a pattern broken in one specific way must be reported, and a
  pattern that merely leaves a sub-hypothesis whole must not be.
* **Every legal IPM token parses** -- a false "does not parse" tells the worker that
  correct syntax is wrong.
"""

from __future__ import annotations

import random

import pytest
from gen import CAUGHT_MUTATIONS, LEGAL_MUTATIONS, mutate_pattern, random_pattern_for, random_skel

from pcp.errors import UsageError
from pcp.state.ipm.pattern import (
    DestructSpec,
    PatternSyntaxError,
    align,
    compile_auto,
    compile_spec,
    parse_pattern,
    parse_patterns,
    render_alignment,
)
from pcp.state.ipm.skeleton import parse_skeleton


def test_compiled_pattern_always_aligns() -> None:
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
    bad: list[str] = []
    for seed in range(1000):
        rng = random.Random(seed + 50_000)
        text = compile_auto(random_skel(rng, depth=3), "H").pattern_text
        try:
            again = parse_pattern(text).render()
        except PatternSyntaxError as exc:
            bad.append(f"seed {seed}: {text!r} failed to re-parse: {exc}")
            continue
        if again != text:
            bad.append(f"seed {seed}: {text!r} -> {again!r}")
    assert not bad, "pattern round-trip failures:\n" + "\n".join(bad[:10])


def test_broken_patterns_are_caught() -> None:
    missed: list[str] = []
    tried = dict.fromkeys(CAUGHT_MUTATIONS, 0)
    for seed in range(2000):
        rng = random.Random(seed + 100_000)
        skel = random_skel(rng, depth=rng.choice([2, 3]))
        binders = compile_auto(skel, "H").binders
        good = random_pattern_for(rng, skel)
        if align(good, skel, binders=binders).mismatch is not None:
            continue
        mutated = mutate_pattern(rng, good, skel=skel)
        if mutated is None:
            continue
        broken, kind = mutated
        tried[kind] += 1
        if align(broken, skel, binders=binders).ok:
            missed.append(f"seed {seed} [{kind}]: {skel.to_notation()!r}\n  {broken.render()}")
    assert not missed, "corruptions the aligner missed:\n" + "\n".join(missed[:10])
    for kind, n in tried.items():
        assert n > 20, f"mutation {kind!r} exercised only {n} times"


def test_under_destructing_is_legal() -> None:
    """Leaving a sub-hypothesis whole is fine; a spurious mismatch is a false positive."""
    flagged: list[str] = []
    tried = 0
    for seed in range(800):
        rng = random.Random(seed + 200_000)
        skel = random_skel(rng, depth=rng.choice([2, 3]))
        binders = compile_auto(skel, "H").binders
        good = random_pattern_for(rng, skel)
        if align(good, skel, binders=binders).mismatch is not None:
            continue
        mutated = mutate_pattern(rng, good, LEGAL_MUTATIONS, skel=skel)
        if mutated is None:
            continue
        tried += 1
        loose, _ = mutated
        if not align(loose, skel, binders=binders).ok:
            flagged.append(f"seed {seed}: {skel.to_notation()!r}\n  {loose.render()}")
    assert tried > 100
    assert not flagged, "legal patterns flagged:\n" + "\n".join(flagged[:10])


LEGAL_TOKENS = [
    "H", "?", "_", "%H", "%", "#H", "# H", ">H", ">[H1 H2]", "-#H", "- #H", "!>", "!%", "!#", "//", "/=", "*", "**",
    "$", "[H1 H2]", "[H1|H2]", "(H1 & H2)", "(H1 & H2 & H3)", "->", "<-", "[% H]", "[%x H]", "{H1 H2}", "{$H}",
    "[]", "[H1|]", "[|H2]", "[$ H2]", "[_ H]", "HΦ", "Hγ'", "[#H1 [%x H2]]", "[%x [%y H]]", "{%} H", "{#}",
    "[->  H]", "[<- H]", "H.1", ">%H", "#%H",
]


@pytest.mark.parametrize("text", LEGAL_TOKENS)
def test_every_legal_token_parses(text: str) -> None:
    pats = parse_patterns(text)
    assert pats
    for p in pats:
        assert parse_patterns(p.render())


def test_spacing_forms_mean_what_ipm_means() -> None:
    assert parse_pattern("[% H]").render() == "[% H]"
    two = parse_pattern("[% H]").children
    assert two[0].kind == "fresh" and two[0].pure and two[1].kind == "name"
    assert parse_pattern("[%H]").children[0].name == "H" and parse_pattern("[%H]").children[0].pure
    assert parse_pattern("# H").render() == "#H"
    assert [p.kind for p in parse_patterns("//=")] == ["simpl", "done"]
    assert parse_pattern("-#H").spatial


@pytest.mark.parametrize("text", ["[H1 H2", "]", "[H1|", "(H1 & )", "[[H1]", "&&&", "#", "-H", "(H1 H2)", "1", "[H1)"])
def test_malformed_patterns_raise_rather_than_mislead(text: str) -> None:
    with pytest.raises(PatternSyntaxError):
        parse_pattern(text)


def test_conjunction_patterns_are_binary() -> None:
    """Verified against Iris 4.5: `[a b c]` is "too many conjuncts", `[a]` "a single conjunct"."""
    assert not align("[H1 H2 H3]", "P ∗ Q ∗ R").ok
    assert "too many conjuncts" in align("[H1 H2 H3]", "P ∗ Q ∗ R").mismatch.reason  # type: ignore[union-attr]
    assert align("[H1 [H2 H3]]", "P ∗ Q ∗ R").ok
    assert align("(H1 & H2 & H3)", "P ∗ Q ∗ R").ok
    assert align("[H1 H2]", "P ∗ Q ∗ R").ok
    assert not align("[H1]", "P ∗ Q").ok
    assert not align("[%x]", "∃ x, P").ok
    assert not align("[H1|H2|H3]", "P ∨ Q ∨ R").ok
    assert align("[H1|[H2|H3]]", "P ∨ Q ∨ R").ok
    assert align("[H1|H2]", "P ∨ Q ∨ R").ok
    assert not align("[H1 H2]", "P ∨ Q ∨ R").ok
    assert not align("[Ha Hb]", "P ∗ Q ∨ R").ok
    assert not align("[Ha Hb Hc]", "(P ∗ Q) ∗ R").ok
    assert align("[[Ha Hb] Hc]", "(P ∗ Q) ∗ R").ok
    assert compile_auto(parse_skeleton("P ∗ Q ∗ R"), "H").pattern_text == "[H1 [H2 H3]]"
    assert compile_auto(parse_skeleton("P ∨ Q ∨ R"), "H").pattern_text == "[H1|[H2|H3]]"
    bare = align("[H1 H2|H3]", "P ∨ Q")
    assert not bare.ok and "a disjunct has multiple patterns" in bare.mismatch.reason  # type: ignore[union-attr]


def test_multi_binder_existentials() -> None:
    d = compile_auto(parse_skeleton("P ∗ ∃ x y, Q"), "H")
    assert d.pattern_text == "[H1 [%x [%y H2]]]"
    assert d.pure_names == ["x", "y"]
    assert align(d.pattern, "P ∗ ∃ x y, Q").ok
    assert align("[H1 [%x H2]]", "P ∗ ∃ x y, Q").ok  # H2 : ∃ y, Q -- legal
    assert not align("[H1 [%x %y H2]]", "P ∗ ∃ x y, Q").ok
    d2 = compile_auto(parse_skeleton("∃ x y, ⌜x = y⌝ ∗ P"), "H")
    assert d2.binders == ["x", "y"] and d2.idestruct("H") == 'iDestruct "H" as (x y) "[%H1 H2]".'
    assert align("[%H1 H2]", "∃ x y, ⌜x = y⌝ ∗ P", binders=["x", "y"]).ok
    assert align("[%y [%H1 H2]]", "∃ x y, ⌜x = y⌝ ∗ P", binders=["x"]).ok


def test_disjunction_versus_conjunction_is_the_headline_diagnosis() -> None:
    report = align("[H1|H2]", "l ↦ v ∗ P")
    assert not report.ok and report.mismatch is not None
    assert "disjunction" in report.mismatch.reason
    assert report.suggestion == "[H1 H2]"
    text = render_alignment(report)
    assert "prop skeleton:" in text and "pattern tree:" in text and "a pattern that fits: [H1 H2]" in text
    assert report.render() == text


def test_existential_needs_a_witness() -> None:
    report = align("[H1 H2]", "∃ γ, own γ (◯ n) ∗ P")
    assert not report.ok and "existential" in report.mismatch.reason  # type: ignore[union-attr]
    d = compile_auto(parse_skeleton("∃ γ, own γ (◯ n) ∗ P"), "H")
    assert d.binders == ["γ"] and d.idestruct("H") == 'iDestruct "H" as (γ) "[H1 H2]".'
    assert not align("%x", "∃ x, P").ok


def test_update_modality_must_be_eliminated_before_destructing() -> None:
    report = align("[H1 H2]", "|={⊤}=> P ∗ Q")
    assert not report.ok and "update modality" in report.mismatch.reason  # type: ignore[union-attr]
    assert align(">[H1 H2]", "|={⊤}=> P ∗ Q").ok
    assert align(">[H1 H2]", "|={E}▷=> P ∗ Q").ok
    assert compile_auto(parse_skeleton("|==> P ∗ Q"), "H").pattern_text == ">[H1 H2]"


def test_markers_are_checked_against_the_prop() -> None:
    assert not align("%H1", "∃ x, P").ok  # verified: `iPure: ... not pure`
    assert align("%H1", "l ↦ v ∗ P").ok  # unknown: IntoPure instances exist for ∗ of pure facts
    assert align("%H1", "⌜n = 3⌝").ok
    assert align("%H1", "⌜n = 3⌝ ∧ ⌜m = 4⌝").ok
    assert align("%H1", "own γ a").ok  # an atom may be IntoPure: unknown, accepted
    assert not align(">[H1 H2]", "P ∗ Q").ok
    assert not align("[]", "P ∗ Q").ok
    assert align("[]", "False").ok and align("[]", "⌜False⌝").ok
    assert align("[%H1 H2]", "⌜n = 3⌝ ∗ P").ok
    assert not align("->", "∃ x, P").ok and align("->", "P ∗ Q").ok
    assert align("[H1 #H2]", "P ∗ □ Q").ok
    assert align("[$ H2]", "P ∗ Q").ok


def test_persistent_and_pure_markers_are_placed_by_the_compiler() -> None:
    d = compile_auto(parse_skeleton("⌜n = 3⌝ ∗ □ P ∗ l ↦ v"), "H")
    assert d.pattern_text == "[%H1 [#H2 H3]]"
    assert d.pure_names == ["H1"]
    assert align(d.pattern, "⌜n = 3⌝ ∗ □ P ∗ l ↦ v").ok


def test_generated_names_avoid_the_live_context() -> None:
    d = compile_auto(parse_skeleton("P ∗ Q"), "H", taken={"H1", "H"})
    assert d.pattern_text == "[H2 H3]"
    d = compile_auto(parse_skeleton("∃ x, P ∗ Q"), "H", taken={"x"})
    assert d.binders == ["x1"]


def test_compile_spec_follows_the_skeleton() -> None:
    skel = parse_skeleton("P ∗ (Q ∨ R)")
    d = compile_spec({"names": ["H1", {"names": ["Ha", "Hb"]}]}, skel)
    assert d.pattern_text == "[H1 [Ha|Hb]]" and align(d.pattern, skel).ok
    d = compile_spec(DestructSpec(names=["Hl", "Hn"], pure=["Hn"]), "l ↦ v ∗ ⌜n = 3⌝")
    assert d.pattern_text == "[Hl %Hn]" and d.pure_names == ["Hn"]
    d = compile_spec({"names": ["Ha", "Hb", "Hc"]}, "P ∗ Q ∗ R")
    assert d.pattern_text == "[Ha [Hb Hc]]"
    d = compile_spec({"names": ["Ha", "Hb"]}, "P ∗ Q ∗ R")
    assert d.pattern_text == "[Ha Hb]" and align(d.pattern, "P ∗ Q ∗ R").ok
    d = compile_spec({"binders": ["x"], "names": ["Hx", "HP"], "pure": ["Hx"]}, "∃ x, ⌜x = 3⌝ ∗ P")
    assert d.idestruct("H") == 'iDestruct "H" as (x) "[%Hx HP]".'
    d = compile_spec({"names": ["HP", {"names": ["x", "y", "HQ"]}]}, "P ∗ ∃ x, ∃ y, Q")
    assert d.pattern_text == "[HP [%x [%y HQ]]]" and d.pure_names == ["x", "y"]
    d = compile_spec({"names": ["x", "HP"]}, "∃ x, P")
    assert d.pattern_text == "[%x HP]"
    d = compile_spec({"names": []}, "⌜False⌝")
    assert d.pattern_text == "[]"
    with pytest.raises(UsageError):
        compile_spec({"names": []}, "P ∗ Q")
    with pytest.raises(UsageError):
        compile_spec({"names": ["a"], "bogus": 1}, "P")
    with pytest.raises(UsageError):
        compile_spec({"names": ["a", "b", "c"]}, "P ∗ Q")
    with pytest.raises(UsageError):
        compile_spec({"binders": ["x", "y"], "names": ["H"]}, "∃ x, P")


def test_shorter_patterns_are_legal_not_mismatches() -> None:
    assert align("[H1 H2]", "P ∗ Q ∗ R").ok
    assert align("[H1|H2]", "P ∨ Q ∨ R").ok
    assert align("[H1 [H2 H3]]", "P ∗ Q ∗ R").ok
    assert not align("[H1 H2 H3]", "P ∗ Q").ok
    assert align("H", "P ∗ Q").ok
    assert align("[_ H]", "P ∗ Q").ok


def test_pattern_parser_accepts_the_ampersand_sugar() -> None:
    assert parse_pattern("(H1 & H2 & H3)").render() == "(H1 & H2 & H3)"
    assert parse_pattern("(H1 & H2)").children[1].name == "H2"
    assert align("(H1 & H2 & H3)", "P ∗ Q ∗ R").ok


def test_actions_and_clears_never_mismatch() -> None:
    for text in ("//", "/=", "!>", "*", "**", "{H1}", "{$H1}", "$", "_", "?"):
        assert align(text, "P ∗ Q").ok, text


def test_a_pattern_nested_past_the_stack_is_a_syntax_error_not_a_crash() -> None:
    for text in ("[" * 5000 + "H" + "]" * 5000, "#" * 5000 + "H", "[H " * 3000 + "H" + "]" * 3000):
        with pytest.raises(PatternSyntaxError):
            parse_pattern(text)
        with pytest.raises(PatternSyntaxError):
            align(text, "P ∗ Q")
