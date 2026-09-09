"""Property tests for the connective-skeleton parser (PLAN.md 3.2, 7).

The skeleton is the substrate for every mechanical answer pcp gives about a
hypothesis' shape, so it gets property tests rather than examples: a parser that is
right on the cases someone thought of is not evidence.
"""

from __future__ import annotations

import random

import pytest
from gen import random_skel

from pcp.state.ipm.skeleton import Skel, binder_names, is_splittable, parse_skeleton, peel, render

SEEDS = list(range(200))


def shape(node: Skel) -> tuple:
    """Structural identity: kind, binders and children, ignoring layout."""
    if node.kind == "atom":
        return ("atom", " ".join(node.text.split()))
    if node.kind == "pure":
        inner = node.children[0].text if node.children else node.text
        return ("pure", " ".join(inner.split()))
    return (node.kind, tuple(node.binders), tuple(shape(c) for c in node.children))


@pytest.mark.parametrize("seed", SEEDS)
def test_notation_round_trips(seed: int) -> None:
    rng = random.Random(seed)
    original = random_skel(rng, depth=3)
    text = render(original)
    reparsed = parse_skeleton(text)
    assert shape(reparsed) == shape(original), f"seed {seed}: {text!r}\n{reparsed.render()}"


@pytest.mark.parametrize("seed", SEEDS[:60])
def test_reparse_is_idempotent(seed: int) -> None:
    rng = random.Random(seed + 10_000)
    text = render(random_skel(rng, depth=4))
    once = parse_skeleton(text)
    twice = parse_skeleton(once.to_notation())
    assert shape(once) == shape(twice)


def test_deep_round_trip_bulk() -> None:
    """2000 seeded trees of depth 2-5, one assertion."""
    failures: list[str] = []
    for seed in range(2000):
        rng = random.Random(seed ^ 0xBEEF)
        original = random_skel(rng, depth=rng.choice([2, 3, 4, 5]))
        text = render(original)
        if shape(parse_skeleton(text)) != shape(original):
            failures.append(f"seed {seed}: {text!r}")
    assert not failures, "round-trip failures:\n" + "\n".join(failures[:10])


def test_never_raises_on_arbitrary_text() -> None:
    """Total function: unparsable input becomes an atom, never an exception."""
    rng = random.Random(0)
    alphabet = "PQ∗∧∨▷□⌜⌝()∃∀,|={}=>-→ γ^?[]⊢"
    for _ in range(500):
        junk = "".join(rng.choice(alphabet) for _ in range(rng.randrange(0, 40)))
        parse_skeleton(junk)
    assert parse_skeleton("").kind == "atom"


def test_right_association_is_flattened_left_is_not() -> None:
    flat = parse_skeleton("P ∗ Q ∗ R")
    right = parse_skeleton("P ∗ (Q ∗ R)")
    left = parse_skeleton("(P ∗ Q) ∗ R")
    assert shape(flat) == shape(right)
    assert shape(flat) != shape(left)
    assert len(left.children) == 2 and left.children[0].kind == "sep"


def test_iris_precedences() -> None:
    """The levels Iris declares (iris/bi/notation.v), spelled out."""
    assert shape(parse_skeleton("▷ P ∗ Q")) == shape(parse_skeleton("(▷ P) ∗ Q"))
    assert shape(parse_skeleton("□ P ∗ Q")) == shape(parse_skeleton("(□ P) ∗ Q"))
    assert shape(parse_skeleton("|==> P ∗ Q")) == shape(parse_skeleton("|==> (P ∗ Q)"))
    assert shape(parse_skeleton("|={⊤}=> P ∗ Q")) == shape(parse_skeleton("|={⊤}=> (P ∗ Q)"))
    assert shape(parse_skeleton("P ∗ Q ∨ R")) == shape(parse_skeleton("(P ∗ Q) ∨ R"))
    assert shape(parse_skeleton("P ∨ Q -∗ R")) == shape(parse_skeleton("(P ∨ Q) -∗ R"))
    assert shape(parse_skeleton("P -∗ Q -∗ R")) == shape(parse_skeleton("P -∗ (Q -∗ R)"))
    assert parse_skeleton("P ∗-∗ Q").kind == "wand_iff"
    # ↔ / ∗-∗ / ⊣⊢ are level 95, below -∗ / → at 99 (v1 put them on one level).
    assert shape(parse_skeleton("P ↔ Q -∗ R")) == shape(parse_skeleton("(P ↔ Q) -∗ R"))
    assert shape(parse_skeleton("P ∗-∗ Q → R")) == shape(parse_skeleton("(P ∗-∗ Q) → R"))
    assert parse_skeleton("P ⊣⊢ Q ∗ R").kind == "equiv"
    assert parse_skeleton("□ P ∗ Q ⊢ P ∗ P ∗ Q").kind == "entails"


def test_binders_in_operand_position_parse() -> None:
    """Coq prints `P -∗ ∃ x, Q x` without parentheses (89 golden states)."""
    node = parse_skeleton("P -∗ ∃ x, Q x")
    assert node.kind == "wand" and node.children[1].kind == "exists"
    node = parse_skeleton("P ∗ ∃ x y, Q x ∗ R")
    assert node.kind == "sep" and node.children[1].kind == "exists" and node.children[1].binders == ["x", "y"]
    assert node.children[1].children[0].kind == "sep"
    ih = parse_skeleton(
        "∀ (t2 : list (expr Λ)) (σ1 : state Λ), ⌜step (t, σ1)⌝ -∗ state_interp σ1 ={⊤}=∗ ∃ nt' : nat, ⌜κ0 = []⌝ ∗ Q"
    )
    assert ih.kind == "forall" and ih.binders == ["t2", "σ1"]
    inner = ih.children[0]
    assert inner.kind == "wand" and inner.children[1].kind == "wand"
    fupd = inner.children[1].children[1]
    assert fupd.kind == "fupd" and fupd.children[0].kind == "exists" and fupd.children[0].binders == ["nt'"]


def test_binders_and_masks() -> None:
    ex = parse_skeleton("∃ γ (v : val), own γ v")
    assert ex.kind == "exists" and ex.binders == ["γ", "v"]
    fu = parse_skeleton("|={⊤ ∖ ↑N,∅}=> P")
    assert fu.kind == "fupd" and fu.binders == ["⊤ ∖ ↑N,∅"]
    assert parse_skeleton("⌜n = 3⌝ ∗ P").children[0].kind == "pure"
    assert binder_names("(stateI : state Λ → list (observation Λ) → iProp Σ) (n : nat)") == ["stateI", "n"]
    assert binder_names("n : nat") == ["n"]
    assert binder_names("x y") == ["x", "y"]


def test_every_modality_prefix() -> None:
    step = parse_skeleton("|={E}▷=> P ∗ Q")
    assert step.kind == "fupd_step" and step.binders == ["E", "E"] and step.children[0].kind == "sep"
    step2 = parse_skeleton("|={E1}[E2]▷=> P")
    assert step2.kind == "fupd_step" and step2.binders == ["E1", "E2"]
    stepn = parse_skeleton("|={E}▷=>^n P")
    assert stepn.kind == "fupd_step" and stepn.binders == ["E", "E", "n"]
    big = parse_skeleton("£ (S n) ={∅}▷=∗^ (S (f n)) |={∅,E2}=> P ∗ Q")
    assert big.kind == "wand" and big.children[1].kind == "fupd_step" and big.children[1].binders == ["∅", "∅", "(S (f n))"]
    assert big.children[1].children[0].kind == "fupd"
    assert parse_skeleton("▷^(S n) (P ∗ Q)").binders == ["^(S n)"]
    wand = parse_skeleton("P ={E1}[E2]▷=∗ Q")
    assert wand.kind == "wand" and wand.children[1].kind == "fupd_step"
    assert parse_skeleton("|==> P").kind == "bupd"
    assert parse_skeleton("◇ P").kind == "except0"
    assert parse_skeleton("<pers> P").kind == "persistently"
    assert parse_skeleton("<affine> P").kind == "affinely"
    assert parse_skeleton("<absorb> P").kind == "absorbingly"
    assert parse_skeleton("■ P").kind == "plainly"
    later = parse_skeleton("▷^n (P ∗ Q)")
    assert later.kind == "later" and later.binders == ["^n"] and later.children[0].kind == "sep"
    cond = parse_skeleton("▷?q ▷ (P ≡ Q)")
    assert cond.kind == "later" and cond.binders == ["?q"] and cond.children[0].kind == "later"
    assert render(cond) == "▷?q ▷ (P ≡ Q)"
    assert parse_skeleton("£ n ∗ P").children[0].text == "£ n"


def test_notation_that_contains_operator_characters() -> None:
    """Real Iris notations in which `∗`, `-` and `>` are *letters*, not connectives."""
    cases = {
        "l ↦∗ vs": "atom",
        "l ↦∗{#q} vs": "atom",
        "P ={E}=∗ Q": "wand",
        "l ↦{#q} v": "atom",
        "own γ (◯ n)": "atom",
        "P ∗-∗ Q": "wand_iff",
        "P -∗ Q": "wand",
        "(f x) y": "atom",
    }
    for text, kind in cases.items():
        assert parse_skeleton(text).kind == kind, f"{text!r} parsed as {parse_skeleton(text)!r}"
    sep = parse_skeleton("l ↦∗ vs ∗ P")
    assert sep.kind == "sep" and sep.children[0].text == "l ↦∗ vs"
    fw = parse_skeleton("l ↦ v ={⊤ ∖ ↑N}=∗ P ∗ Q")
    assert fw.kind == "wand"
    assert fw.children[1].kind == "fupd" and fw.children[1].binders == ["⊤ ∖ ↑N"]
    assert fw.children[1].children[0].kind == "sep"
    bw = parse_skeleton("P ==∗ Q")
    assert bw.kind == "wand" and bw.children[1].kind == "bupd"
    assert parse_skeleton("(f x) y ∗ P").children[0].text == "(f x) y"


def test_peel_and_splittable() -> None:
    markers, core = peel(parse_skeleton("▷ |={⊤}=> □ (P ∗ Q)"))
    assert markers.laters == 1 and markers.update and markers.intuit and core.kind == "sep"
    assert is_splittable(parse_skeleton("|==> P ∗ Q"))
    assert not is_splittable(parse_skeleton("P -∗ Q"))
    assert is_splittable(parse_skeleton("⌜n = 3⌝"))


def test_json_round_trip() -> None:
    node = parse_skeleton("∃ x, ⌜x = 3⌝ ∗ ▷ (P ∨ Q)")
    assert shape(Skel.from_json(node.to_json())) == shape(node)
