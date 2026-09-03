"""The printer parser and the skeleton parser, against real Iris output.

The corpus in ``tests/goldens/ipm_states.jsonl`` is not invented: it is every goal
state seen while replaying real proof scripts from the installed Iris library through
petanque (``eval/extract_goldens.py``).  PLAN.md 14 asks for exactly this -- printer
parsing is layout-fragile, so it gets golden tests per version, and the goldens have
to come from Iris rather than from the parser author's imagination.

Regenerate after a toolchain bump:

    python eval/extract_goldens.py --limit-files 40 --limit-lemmas 12
"""

from __future__ import annotations

import json
import re
from collections import Counter
from pathlib import Path

import pytest

from pcp.core.ipm.model import scan_modality
from pcp.core.ipm.parse import looks_like_ipm, parse_goal
from pcp.core.ipm.pattern import align, compile_auto
from pcp.core.ipm.skeleton import is_splittable, parse_skeleton

GOLDENS = Path(__file__).parent / "goldens" / "ipm_states.jsonl"


def load() -> list[dict]:
    if not GOLDENS.exists():
        pytest.skip(f"{GOLDENS} not extracted; run eval/extract_goldens.py")
    return [json.loads(line) for line in GOLDENS.read_text(encoding="utf-8").splitlines() if line.strip()]


@pytest.fixture(scope="module")
def goldens() -> list[dict]:
    return load()


@pytest.fixture(scope="module")
def parsed(goldens: list[dict]) -> list[tuple[dict, object]]:
    return [
        (row, parse_goal(row["ty"], pure_hyps=[(h["names"], h["ty"]) for h in row["hyps"]]))
        for row in goldens
    ]


def test_corpus_is_substantial(goldens: list[dict]) -> None:
    assert len(goldens) > 500
    assert len({(r["file"], r["thm"]) for r in goldens}) > 100
    assert sum(1 for r in goldens if looks_like_ipm(r["ty"])) > 300


def test_every_goal_parses(parsed) -> None:
    """Total function: no state in the corpus may raise."""
    for row, goal in parsed:
        assert goal is not None, f"{row['file']}:{row['thm']}"


def test_hypothesis_count_matches_an_independent_count(parsed) -> None:
    """Cross-check the block parser against a dumb count of `"Name" :` lines.

    Two independent readings of the same text must agree, or the block boundaries
    are wrong somewhere -- which is exactly the failure mode that makes a printer
    parser dangerous rather than merely fragile.
    """
    bad = []
    for row, goal in parsed:
        if not goal.is_ipm:
            continue
        expected = len(re.findall(r'^\s*"[^"]*"(?:\s+"[^"]*")*\s*:', row["ty"], re.M))
        got = len(goal.intuitionistic) + len(goal.spatial)
        if expected != got:
            bad.append(f"{row['file']}:{row['thm']} step {row['step']}: {expected} lines, {got} parsed")
    assert not bad, "hypothesis count mismatches:\n" + "\n".join(bad[:10])


def test_names_are_unique_and_props_nonempty(parsed) -> None:
    bad = []
    for row, goal in parsed:
        if not goal.is_ipm:
            continue
        names = [h.id for h in goal.ipm_hyps]
        if len(names) != len(set(names)):
            dupes = [n for n, c in Counter(names).items() if c > 1]
            bad.append(f"{row['file']}:{row['thm']}: duplicate names {dupes}")
        for h in goal.ipm_hyps:
            if not h.prop.strip():
                bad.append(f"{row['file']}:{row['thm']}: empty prop for {h.id!r}")
    assert not bad, "\n".join(bad[:10])


def test_the_goal_is_never_swallowed_into_the_context(parsed) -> None:
    """Every IPM state has a conclusion; losing it means the separators were misread."""
    bad = [
        f"{row['file']}:{row['thm']} step {row['step']}"
        for row, goal in parsed
        if goal.is_ipm and not goal.goal.strip()
    ]
    assert not bad, "IPM states parsed with an empty goal:\n" + "\n".join(bad[:10])


#: A *standalone* separator line is what the block splitter consumes; finding one
#: inside a parsed field means a boundary was missed.  A separator glued to other
#: text is not a boundary at all -- Iris prints IPM *tactic lemmas* like
#: `tac_aupd_intro` with the environment variables inline (`Γp---------□`), and that
#: text belongs to the goal.
_STRAY_SEPARATOR = re.compile(r"^\s*-{6,}\s*(?:□|∗)\s*$", re.M)


def test_no_separator_line_leaks_into_a_parsed_field(parsed) -> None:
    bad = []
    for row, goal in parsed:
        for h in goal.ipm_hyps:
            if _STRAY_SEPARATOR.search(h.prop):
                bad.append(f"{row['file']}:{row['thm']}: separator line inside {h.id!r}")
        if _STRAY_SEPARATOR.search(goal.goal):
            bad.append(f"{row['file']}:{row['thm']}: separator line inside the goal")
    assert not bad, "\n".join(bad[:10])


def test_environment_notation_in_a_statement_is_not_mistaken_for_a_context(parsed) -> None:
    """Iris's own IPM tactic lemmas print `Γp---------□` inside their statements.

    Those are not context separators and the state is not an IPM state; treating it
    as one would fabricate hypotheses out of a lemma statement.
    """
    rows = [(row, goal) for row, goal in parsed if row["thm"].startswith("tac_")]
    if not rows:
        pytest.skip("no IPM tactic lemmas in this corpus sample")
    for row, goal in rows:
        for h in goal.ipm_hyps:
            assert "Γ" not in h.id, f"{row['thm']}: fabricated hypothesis {h.id!r}"


def test_modality_scan_never_raises_and_finds_masks(parsed) -> None:
    with_mask = 0
    for _, goal in parsed:
        m = scan_modality(goal.goal)
        if m.mask:
            with_mask += 1
    # Iris proofs are full of masked fupds and WPs; finding none would mean the
    # scanner is silently inert.
    assert with_mask > 20


def test_skeleton_parses_every_real_prop(parsed) -> None:
    """Total, and structurally informative on a good share of real props."""
    total = structured = 0
    for _, goal in parsed:
        props = [h.prop for h in goal.ipm_hyps] + ([goal.goal] if goal.goal else [])
        for prop in props:
            total += 1
            skel = parse_skeleton(prop)  # must not raise
            if skel.kind != "atom":
                structured += 1
    assert total > 1000
    # Most Iris hypotheses are applications (`l ↦ v`, `own γ a`) and legitimately
    # atomic, so this is a floor on *coverage*, not a claim about the corpus.
    assert structured / total > 0.15, f"only {structured}/{total} props had structure"


def test_compiled_patterns_align_on_real_props(parsed) -> None:
    """Every splittable real prop must get a pattern that fits it."""
    bad = []
    checked = 0
    for row, goal in parsed:
        for h in goal.ipm_hyps:
            skel = parse_skeleton(h.prop)
            if not is_splittable(skel):
                continue
            checked += 1
            d = compile_auto(skel, h.id)
            report = align(d.pattern, skel, binders=d.binders)
            if not report.ok:
                bad.append(f"{row['file']}:{row['thm']} {h.id}: {h.prop!r}\n{report.render()}")
    assert checked > 50, f"only {checked} splittable props found -- corpus or parser is inert"
    assert not bad, "compiled patterns that do not align on real props:\n" + "\n\n".join(bad[:5])


def test_round_trip_of_real_props(parsed) -> None:
    """Real props must survive skeleton -> notation -> skeleton unchanged."""
    from tests.test_skeleton_fuzz import shape

    bad = []
    checked = 0
    for row, goal in parsed:
        for prop in [h.prop for h in goal.ipm_hyps]:
            skel = parse_skeleton(prop)
            if skel.kind == "atom":
                continue
            checked += 1
            if shape(parse_skeleton(skel.to_notation())) != shape(skel):
                bad.append(f"{row['file']}:{row['thm']}: {prop!r} -> {skel.to_notation()!r}")
    assert checked > 50
    assert not bad, "real props that do not round-trip:\n" + "\n".join(bad[:10])
