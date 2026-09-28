"""The invariant-opening helper (pcp-issues MF6): `>` exactly on what Rocq says is Timeless."""

from __future__ import annotations

import shutil
from pathlib import Path

import pytest
from conftest import needs_petanque, needs_rocq

from pcp.state.invariant import build_pattern, find_invariant, inv_body
from pcp.state.ipm.parse import parse_goal

FIXTURE = Path(__file__).parent / "fixtures" / "iris_inv"
BODY = "∃ (n : Z) (m : nat), l ↦ #n ∗ ghost_var γ (1 / 2) n ∗ ⌜(0 ≤ n)%Z⌝ ∗ ▷ (True -∗ True) ∗ ⌜m = m⌝"


def test_timeless_answers_place_the_later_strippers() -> None:
    plan = build_pattern(BODY, timeless={0: True, 1: True, 3: False})
    assert plan.binders == ["n", "m"]
    assert plan.text() == "(>Hl & >Hγ & >%Hn & H & >%Hm)"
    # The probe's form: no `>` anywhere, pure conjuncts opened as ordinary hypotheses.
    assert plan.text(strip=False) == "(Hl & Hγ & Hn & H & Hm)"
    assert [(x.name, x.pure, x.timeless) for x in plan.leaves] == [
        ("Hl", False, True),
        ("Hγ", False, True),
        ("Hn", True, True),
        ("H", False, False),
        ("Hm", True, True),
    ]


def test_unknown_timelessness_stays_under_the_later() -> None:
    assert build_pattern(BODY).text() == "(Hl & Hγ & >%Hn & H & >%Hm)"


def test_names_are_fresh_against_both_contexts() -> None:
    plan = build_pattern(BODY, coq_names=["n", "Hm"], iris_names=["Hl", "Hγ"])
    assert plan.binders == ["n0", "m"]
    assert [x.name for x in plan.leaves] == ["Hl1", "Hγ1", "Hn", "H", "Hm1"]


def test_nested_existentials_disjunctions_and_single_leaves() -> None:
    assert build_pattern("∃ x, ∃ y, own γ x ∗ own γ y").binders == ["x", "y"]
    plan = build_pattern("l ↦ #1 ∨ (∃ v, l ↦ v ∗ ⌜v ≠ #1⌝)", timeless={0: True, 1: True})
    assert plan.text() == "[>Hl|[%v [>Hl1 >%Hv]]]"
    assert build_pattern("P", timeless={0: True}).text() == ">HP"
    assert build_pattern("P ∗ ∃ k, Q k", timeless={}).text() == "(HP & %k & HQ)"


def test_the_invariant_is_found_by_name_predicate_or_namespace() -> None:
    goal = parse_goal('"Hinv" : inv N (cnt_inv γ l)\n"Hx" : P\n--------------------------------------□\nTrue')
    assert inv_body(goal.intuitionistic[0].prop) == ("N", "cnt_inv γ l")
    assert find_invariant(goal, "Hinv").id == "Hinv"
    assert find_invariant(goal, "cnt_inv").id == "Hinv"
    assert find_invariant(goal, "N").id == "Hinv"
    assert find_invariant(goal, "nothing") is None
    assert inv_body("na_inv p N P") is None


# ---------------------------------------------------------------------------- live


@pytest.fixture(scope="module")
def inv_pool(tmp_path_factory):
    from pcp.state.pool import SessionPool

    root = tmp_path_factory.mktemp("iris_inv")
    for f in FIXTURE.iterdir():
        shutil.copy(f, root / f.name)
    pool = SessionPool(root, size=1)
    yield pool, root
    pool.close()


def _open(inv_pool, lemma: str, intro: str):
    pool, root = inv_pool
    s = pool.open(root / "Inv.v", lemma, start=True)
    assert s.run(intro).ok
    return s


@needs_rocq
@needs_petanque
def test_live_pattern_from_a_named_definition(inv_pool) -> None:
    s = _open(inv_pool, "load_goal", 'iIntros "#Hinv".')
    r = invariant_pattern_checked(s, "cnt_inv")  # found through the predicate's name
    assert r.unfolded == ["cnt_inv"]
    assert r.tactic == 'iInv "Hinv" as (n m) "(>Hl & >Hk & >%Hn & H & >%Hm)" "Hclose".'
    assert r.opened["Hl"] == "l ↦ #n" and r.opened["H"].startswith("▷")  # the wand keeps its later
    assert "Hn" in r.opened and r.opened["Hclose"].startswith("▷")


@needs_rocq
@needs_petanque
def test_live_pattern_avoids_taken_names_and_unfolds_a_wrapper(inv_pool) -> None:
    raw = invariant_pattern_checked(_open(inv_pool, "raw_goal", 'iIntros "#Hinv Hl".'), "Hinv")
    assert raw.tactic == 'iInv "Hinv" as (n0) "(>Hl1 & >Hk)" "Hclose".'
    named = invariant_pattern_checked(_open(inv_pool, "named_goal", 'iIntros "#Hc".'), "Hc")
    assert named.unfolded == ["is_cnt", "cnt_inv"] and named.tactic.startswith('iInv "Hc" as (n m) "(>Hl')


@needs_rocq
@needs_petanque
def test_live_an_arbitrary_prop_stays_under_the_later(inv_pool) -> None:
    r = invariant_pattern_checked(_open(inv_pool, "opaque_goal", 'iIntros "#HI".'), "HI")
    assert r.tactic == 'iInv "HI" as "HP" "Hclose".' and r.leaves[0].timeless is False


def invariant_pattern_checked(session, which: str):
    from pcp.state.invariant import invariant_pattern

    before = (session.current, session.step_number)
    r = invariant_pattern(session, which)
    assert r.ok and r.verified, r.explanation
    assert (session.current, session.step_number) == before  # never moves the session
    return r


@needs_rocq
@needs_petanque
def test_live_a_failing_opening_is_reported_not_hidden(inv_pool) -> None:
    from pcp.state.invariant import invariant_pattern

    s = _open(inv_pool, "load_goal", 'iIntros "#Hinv".')
    first = invariant_pattern(s, "Hinv")
    assert s.run(first.tactic).ok
    again = invariant_pattern(s, "Hinv")  # ↑N is no longer in the mask
    assert not again.ok and again.tactic and again.side_goals == ["↑N ⊆ ⊤ ∖ ↑N"]
    assert "FAILED" in again.explanation and "↑N ⊆ ⊤ ∖ ↑N" in (again.error or "")
