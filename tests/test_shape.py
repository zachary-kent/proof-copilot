"""Skeleton shape assertions (pcp-issues MF5): Rocq decides, the structural diff explains."""

from __future__ import annotations

import shutil
from pathlib import Path

import pytest
from conftest import needs_petanque, needs_rocq

from pcp.state.ipm.parse import parse_goal
from pcp.state.shape import compare_shape, expect_shape, probe_tactic, rocq_term

FIXTURE = Path(__file__).parent / "fixtures" / "iris_inv"


# ------------------------------------------------------------------ structural diff


def _diffs(expected: str, actual: str) -> list[tuple[str, str]]:
    return [(d.expected, d.actual) for d in compare_shape(expected, actual)[0]]


def test_the_address_offset_form_is_the_minimal_difference() -> None:
    diffs, _ = compare_shape(
        "WP ! #(l +ₗ 1) ;; ! #l {{ v, True }}", "WP ! #(l +ₗ (0 + 1));; ! #l {{ _, True }}"
    )
    assert [(d.expected, d.actual) for d in diffs] == [("1", "(0 + 1)")]
    assert "#(l +ₗ (0 + 1))" in diffs[0].path  # the path names the enclosing group


def test_holes_absorb_whole_subterms_and_spans() -> None:
    assert _diffs("WP _ {{ v, Φ v }}", "WP ! #l;; ! #l {{ w, Φ w }}") == []  # binder renamed too
    assert _diffs("_ ∗ Q", "A ∗ B ∗ Q") == []
    assert _diffs("∃ x, P x ∗ Q", "∃ y, P y ∗ Q") == []


def test_metavariables_bind_and_must_agree() -> None:
    diffs, binds = compare_shape("l ↦ #?n ∗ ghost_var γ q ?n", "l ↦ #3 ∗ ghost_var γ q 3")
    assert diffs == [] and binds == {"n": "3"}
    diffs, _ = compare_shape("l ↦ #?n ∗ ghost_var γ q ?n", "l ↦ #3 ∗ ghost_var γ q 4")
    assert len(diffs) == 1 and "?n must be the same term" in diffs[0].note


def test_connective_differences_are_located() -> None:
    assert _diffs("P ∗ Q", "P ∗ R ∗ Q") == [("", "R")]
    diffs, _ = compare_shape("|={⊤}=> P ∗ Q", "|={⊤ ∖ ↑N}=> P ∗ Q")
    assert [(d.expected, d.actual) for d in diffs] == [("", "∖ ↑N")] and "mask" in diffs[0].path
    diffs, _ = compare_shape("⌜(0 ≤ n)%Z⌝ ∗ P", "⌜0 ≤ m⌝ ∗ P")  # scope delimiters are not structure
    assert [(d.expected, d.actual) for d in diffs] == [("n", "m")] and diffs[
        0
    ].path == "conclusion › ∗[1] › ⌜…⌝"


def test_a_goal_object_gets_a_structural_verdict_with_hypotheses() -> None:
    goal = parse_goal('"Hl" : l ↦ #1\n--------------------------------------∗\nWP ! #l {{ v, ⌜v = #1⌝ }}')
    report = expect_shape(
        goal, '"Hl" : l ↦ #2\n--------------------------------------∗\nWP ! #l {{ w, ⌜w = #1⌝ }}'
    )
    by = {p.target: p for p in report.parts}
    assert by["conclusion"].ok() and by["conclusion"].verdict == "structural"
    assert not by["Hl"].ok() and [(d.expected, d.actual) for d in by["Hl"].diffs] == [("2", "1")]
    assert not report.ok and "Hl: MISMATCH (structural)" in report.render()


def test_rocq_term_gives_each_metavariable_occurrence_its_own_evar() -> None:
    term, metas = rocq_term("#?x ∗ ▷?p P ∗ ?x")
    assert term == "#(pcpmv_0) ∗ ▷?p P ∗ (pcpmv_1)"  # `▷?p` is a modality, not a hole
    assert metas == [("pcpmv_0", "x"), ("pcpmv_1", "x")]
    tactic, _ = probe_tactic("H", "P", kind="iris_hyp", selector=1)
    assert tactic.startswith('2: (iRevert "H";') and tactic.endswith(").")


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


@needs_rocq
@needs_petanque
def test_live_shape_is_decided_by_rocq_and_never_moves_the_session(inv_pool) -> None:
    pool, root = inv_pool
    s = pool.open(root / "Inv.v", "offset_goal", start=True)
    assert s.run('iIntros "#Hinv".').ok
    cur = s.current

    wrong = expect_shape(s, "WP ! #(l +ₗ 1) ;; ! #l {{ v, True }}")
    part = wrong.parts[0]
    assert not wrong.ok and part.verdict == "convertible" and part.unified
    assert [(d.expected, d.actual) for d in part.diffs] == [("1", "(0 + 1)")]
    assert expect_shape(s, "WP ! #(l +ₗ 1) ;; ! #l {{ v, True }}", strict=False).ok

    exact = expect_shape(s, "WP ! #(?x +ₗ (0 + 1)) ;; ! #?x {{ _, True }}")
    assert exact.ok and exact.parts[0].verdict == "syntactic" and exact.parts[0].bindings == {"x": "l"}

    off = expect_shape(s, "WP ! #(l +ₗ 2) ;; _ {{ _ }}")
    assert off.parts[0].verdict == "mismatch" and ("2", "(0 + 1)") in [
        (d.expected, d.actual) for d in off.parts[0].diffs
    ]

    bad = expect_shape(s, "WP ! #(j +ₗ 1) ;; _ {{ _ }}")  # no `j` in scope
    assert bad.parts[0].verdict == "error" and "j" in (bad.parts[0].error or "")

    hyps = expect_shape(s, "", hyps={"Hinv": "inv _ (cnt_inv ?k l)", "l": "loc"})
    assert hyps.ok, hyps.render()
    swapped = expect_shape(s, "", hyps={"Hinv": "inv _ (cnt_inv l _)"})  # arguments swapped
    assert not swapped.ok and swapped.parts[0].verdict == "mismatch"
    assert s.current is cur and s.step_number == 1
