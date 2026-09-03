"""Property tests for the connective-skeleton parser.

The skeleton is the substrate for every mechanical answer pcp gives about a
hypothesis' shape (PLAN.md 3.2, 7), so it gets property tests rather than a handful
of examples: a parser that is right on the cases someone thought of is not evidence.
"""

from __future__ import annotations

import random

import pytest

from pcp.core.ipm.skeleton import Skel, parse_skeleton
from tests.gen import random_skel

SEEDS = list(range(200))


def shape(node: Skel) -> tuple:
    """Structural identity: kind, binders and children, ignoring source spans."""
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
    text = original.to_notation()
    reparsed = parse_skeleton(text)
    assert shape(reparsed) == shape(original), f"seed {seed}: {text!r}\n{reparsed.render()}"


@pytest.mark.parametrize("seed", SEEDS[:60])
def test_reparse_is_idempotent(seed: int) -> None:
    """Parsing a rendered tree twice must not drift."""
    rng = random.Random(seed + 10_000)
    text = random_skel(rng, depth=4).to_notation()
    once = parse_skeleton(text)
    twice = parse_skeleton(once.to_notation())
    assert shape(once) == shape(twice)


def test_never_raises_on_arbitrary_text() -> None:
    """Total function: unparsable input becomes an atom, never an exception."""
    rng = random.Random(0)
    alphabet = "PQ∗∧∨▷□⌜⌝()∃∀,|={}=>-→ γ"
    for _ in range(500):
        junk = "".join(rng.choice(alphabet) for _ in range(rng.randrange(0, 40)))
        parse_skeleton(junk)  # must not raise


def test_right_association_is_flattened_left_is_not() -> None:
    """`P ∗ (Q ∗ R)` *is* `P ∗ Q ∗ R`; `(P ∗ Q) ∗ R` is a different term."""
    flat = parse_skeleton("P ∗ Q ∗ R")
    right = parse_skeleton("P ∗ (Q ∗ R)")
    left = parse_skeleton("(P ∗ Q) ∗ R")
    assert shape(flat) == shape(right)
    assert shape(flat) != shape(left)
    assert len(left.children) == 2 and left.children[0].kind == "sep"


def test_iris_precedences() -> None:
    """The precedences that matter, spelled out as the levels Iris declares."""
    # ▷ and □ are level 20: they bind their argument only.
    assert shape(parse_skeleton("▷ P ∗ Q")) == shape(parse_skeleton("(▷ P) ∗ Q"))
    assert shape(parse_skeleton("□ P ∗ Q")) == shape(parse_skeleton("(□ P) ∗ Q"))
    # |==> and |={E}=> are level 99 with the body at 200: they extend right.
    assert shape(parse_skeleton("|==> P ∗ Q")) == shape(parse_skeleton("|==> (P ∗ Q)"))
    assert shape(parse_skeleton("|={⊤}=> P ∗ Q")) == shape(parse_skeleton("|={⊤}=> (P ∗ Q)"))
    # ∗ and ∧ (80) bind tighter than ∨ (85), which binds tighter than -∗ (99).
    assert shape(parse_skeleton("P ∗ Q ∨ R")) == shape(parse_skeleton("(P ∗ Q) ∨ R"))
    assert shape(parse_skeleton("P ∨ Q -∗ R")) == shape(parse_skeleton("(P ∨ Q) -∗ R"))
    # -∗ is right-associative.
    assert shape(parse_skeleton("P -∗ Q -∗ R")) == shape(parse_skeleton("P -∗ (Q -∗ R)"))
    # ∗-∗ must not be read as a bare wand.
    assert parse_skeleton("P ∗-∗ Q").kind == "wand_iff"


def test_binders_and_masks() -> None:
    ex = parse_skeleton("∃ γ (v : val), own γ v")
    assert ex.kind == "exists" and ex.binders == ["γ", "v"]
    fu = parse_skeleton("|={⊤ ∖ ↑N,∅}=> P")
    assert fu.kind == "fupd" and fu.binders == ["⊤ ∖ ↑N,∅"]
    pure = parse_skeleton("⌜n = 3⌝ ∗ P")
    assert pure.children[0].kind == "pure"


def test_deep_round_trip_bulk() -> None:
    """A wider sweep than the parametrised seeds, deeper trees, one assertion."""
    failures: list[str] = []
    for seed in range(2000):
        rng = random.Random(seed ^ 0xBEEF)
        original = random_skel(rng, depth=rng.choice([2, 3, 4, 5]))
        text = original.to_notation()
        if shape(parse_skeleton(text)) != shape(original):
            failures.append(f"seed {seed}: {text!r}")
    assert not failures, "round-trip failures:\n" + "\n".join(failures[:10])


def test_notation_that_contains_operator_characters() -> None:
    """Real Iris notations in which `∗`, `-` and `>` are *letters*, not connectives."""
    cases = {
        "l ↦∗ vs": "atom",           # heap_lang array points-to
        "l ↦∗{#q} vs": "atom",
        "P ={E}=∗ Q": "wand",        # the fupd wand: P -∗ |={E}=> Q
        "l ↦{#q} v": "atom",
        "own γ (◯ n)": "atom",
        "P ∗-∗ Q": "wand_iff",
        "P -∗ Q": "wand",
    }
    for text, kind in cases.items():
        assert parse_skeleton(text).kind == kind, f"{text!r} parsed as {parse_skeleton(text)!r}"
    # And the array points-to survives being an operand.
    sep = parse_skeleton("l ↦∗ vs ∗ P")
    assert sep.kind == "sep" and sep.children[0].text == "l ↦∗ vs"

    # The modal wands unfold to their definitions, so downstream code sees a wand.
    fw = parse_skeleton("l ↦ v ={⊤ ∖ ↑N}=∗ P ∗ Q")
    assert fw.kind == "wand"
    assert fw.children[1].kind == "fupd" and fw.children[1].binders == ["⊤ ∖ ↑N"]
    assert fw.children[1].children[0].kind == "sep"
    bw = parse_skeleton("P ==∗ Q")
    assert bw.kind == "wand" and bw.children[1].kind == "bupd"
