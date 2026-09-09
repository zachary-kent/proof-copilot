"""The printer parser, the skeleton parser and the compiler against real Iris output.

``tests/goldens/ipm_states.jsonl`` is every goal seen while replaying real proof scripts
from the installed Iris library through petanque (``eval/extract_goldens.py``).  PLAN.md
14 asks for exactly this: printer parsing is layout-fragile, so it gets golden tests per
version, and the goldens come from Iris rather than from the parser author's
imagination.  Regenerate after a toolchain bump.
"""

from __future__ import annotations

import json
import re
from collections import Counter

import pytest
from conftest import GOLDENS, needs_goldens

from pcp.state.ipm.model import scan_modality
from pcp.state.ipm.parse import looks_like_ipm, parse_goal
from pcp.state.ipm.pattern import align, compile_auto
from pcp.state.ipm.skeleton import is_splittable, parse_skeleton, render

pytestmark = needs_goldens


@pytest.fixture(scope="module")
def goldens() -> list[dict]:
    return [json.loads(line) for line in GOLDENS.read_text(encoding="utf-8").splitlines() if line.strip()]


@pytest.fixture(scope="module")
def parsed(goldens: list[dict]) -> list[tuple[dict, object]]:
    return [(row, parse_goal(row["ty"], row["hyps"])) for row in goldens]


def test_corpus_is_substantial(goldens: list[dict]) -> None:
    assert len(goldens) > 500
    assert len({(r["file"], r["thm"]) for r in goldens}) > 100
    assert sum(1 for r in goldens if looks_like_ipm(r["ty"])) > 300


def test_every_goal_parses(parsed) -> None:
    for row, goal in parsed:
        assert goal is not None, f"{row['file']}:{row['thm']}"


#: An *independent* count: quoted names AND the unquoted anonymous `_ :` form.  v1's
#: cross-check counted quoted lines only and shared the parser's blind spot.
_HYP_LINE = re.compile(r'^(?:\s*"[^"]*"(?:\s+"[^"]*")*|_)\s*:', re.M)


def test_hypothesis_count_matches_an_independent_count(parsed) -> None:
    bad = []
    for row, goal in parsed:
        if not goal.is_ipm:
            continue
        expected = len(_HYP_LINE.findall(row["ty"]))
        got = len(goal.intuitionistic) + len(goal.spatial)
        if expected != got:
            bad.append(f"{row['file']}:{row['thm']} step {row['step']}: {expected} lines, {got} parsed")
    assert not bad, "hypothesis count mismatches:\n" + "\n".join(bad[:10])


def test_anonymous_hypotheses_are_addressable(parsed) -> None:
    states = 0
    for row, goal in parsed:
        anon = [h for h in goal.ipm_hyps if h.anonymous]
        if not anon:
            continue
        states += 1
        assert all(re.fullmatch(r"_\d+", h.id) for h in anon), row["thm"]
        assert all(h.prop.strip() for h in anon), row["thm"]
        assert all("\n_ :" not in h.prop for h in goal.ipm_hyps), f"{row['thm']}: anonymous line glued"
    assert states > 100


def test_names_are_unique_and_props_nonempty(parsed) -> None:
    bad = []
    for row, goal in parsed:
        if not goal.is_ipm:
            continue
        names = [h.id for h in goal.ipm_hyps]
        if len(names) != len(set(names)):
            bad.append(f"{row['thm']}: duplicates {[n for n, c in Counter(names).items() if c > 1]}")
        bad += [f"{row['thm']}: empty prop for {h.id!r}" for h in goal.ipm_hyps if not h.prop.strip()]
    assert not bad, "\n".join(bad[:10])


def test_the_goal_is_never_swallowed_into_the_context(parsed) -> None:
    bad = [f"{row['thm']} step {row['step']}" for row, goal in parsed if goal.is_ipm and not goal.goal.strip()]
    assert not bad, "\n".join(bad[:10])


_STRAY_SEPARATOR = re.compile(r"^\s*-{6,}\s*(?:□|∗)\s*$", re.M)


def test_no_separator_line_leaks_into_a_parsed_field(parsed) -> None:
    bad = []
    for row, goal in parsed:
        bad += [f"{row['thm']}: separator inside {h.id!r}" for h in goal.ipm_hyps if _STRAY_SEPARATOR.search(h.prop)]
        if _STRAY_SEPARATOR.search(goal.goal):
            bad.append(f"{row['thm']}: separator inside the goal")
    assert not bad, "\n".join(bad[:10])


def test_environment_notation_in_a_statement_is_not_mistaken_for_a_context(parsed) -> None:
    rows = [(row, goal) for row, goal in parsed if row["thm"].startswith("tac_")]
    if not rows:
        pytest.skip("no IPM tactic lemmas in this corpus sample")
    for row, goal in rows:
        for h in goal.ipm_hyps:
            assert "Γ" not in h.id, f"{row['thm']}: fabricated hypothesis {h.id!r}"


def test_pure_context_comes_from_petanque_verbatim(goldens: list[dict]) -> None:
    row = next(r for r in goldens if any(len(h["names"]) > 1 for h in r["hyps"]))
    goal = parse_goal(row["ty"], row["hyps"])
    grouped = next(h for h in goal.pure if len(h.names) > 1)
    assert grouped.id == grouped.names[0] and grouped.klass == "pure"
    assert len(goal.pure) == len(row["hyps"])


def test_modality_scan_finds_masks_and_total_wps(parsed) -> None:
    with_mask = total = stuck = 0
    for _, goal in parsed:
        m = scan_modality(goal.goal)
        if m.mask:
            with_mask += 1
            assert ";" not in m.mask, m.mask  # the stuckness bit is not part of the mask
        if m.wp is not None and m.wp.total:
            total += 1
        if "@ s;" in goal.goal or "NotStuck;" in goal.goal:
            stuck += 1
    assert with_mask > 20 and total > 20 and stuck > 100


def test_skeleton_parses_every_real_prop(parsed) -> None:
    total = structured = 0
    for _, goal in parsed:
        for prop in [h.prop for h in goal.ipm_hyps] + ([goal.goal] if goal.goal else []):
            total += 1
            if parse_skeleton(prop).kind != "atom":
                structured += 1
    assert total > 1000
    assert structured / total > 0.15, f"only {structured}/{total} props had structure"


def test_binders_in_operand_position_are_seen(parsed) -> None:
    """`P -∗ ∃ x, Q x` prints without parentheses; v1 made the whole prop an atom."""
    seen = 0
    for _, goal in parsed:
        for h in goal.ipm_hyps:
            if re.search(r"(?:-∗|=∗|∗|∧|∨|→)\s+[∃∀]", h.prop) and "match" not in h.prop:
                seen += 1
                assert parse_skeleton(h.prop).kind != "atom", h.prop
    assert seen > 30


def test_compiled_patterns_align_on_real_props(parsed) -> None:
    bad = []
    checked = 0
    for row, goal in parsed:
        for h in goal.ipm_hyps:
            skel = parse_skeleton(h.prop)
            if not is_splittable(skel):
                continue
            checked += 1
            d = compile_auto(skel, h.id, taken={x.id for x in goal.ipm_hyps})
            report = align(d.pattern, skel, binders=d.binders)
            if not report.ok:
                bad.append(f"{row['thm']} {h.id}: {h.prop!r}\n{report.render()}")
    assert checked > 50
    assert not bad, "compiled patterns that do not align on real props:\n" + "\n\n".join(bad[:5])


def test_round_trip_of_real_props(parsed) -> None:
    from test_skeleton_fuzz import shape

    bad = []
    checked = 0
    for row, goal in parsed:
        for prop in [h.prop for h in goal.ipm_hyps] + ([goal.goal] if goal.goal else []):
            skel = parse_skeleton(prop)
            if skel.kind == "atom":
                continue
            checked += 1
            if shape(parse_skeleton(render(skel))) != shape(skel):
                bad.append(f"{row['thm']}: {prop!r} -> {render(skel)!r}")
    assert checked > 50
    assert not bad, "real props that do not round-trip:\n" + "\n".join(bad[:10])
