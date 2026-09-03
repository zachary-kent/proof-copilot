"""Structured diagnosis of a failed tactic (PLAN.md 7).

Two failure families account for most of a worker's wasted turns, and both are
answered structurally rather than with a goal dump:

* **Pattern mismatches.**  `iDestruct` / `iIntros` / `iMod ... as` fail because the
  pattern does not fit the object.  The aligner walks both trees and names the first
  divergence.  This is *not opt-in*: any failing pattern-bearing tactic returns the
  report by construction, so the agent examines the object and the pattern every
  time by discipline of the tool, not of the agent.
* **Unification failures.**  `iApply` / `wp_apply` / `iFrame` fail because the
  lemma's conclusion does not match the goal.  The report names what is in the
  spatial context and what the goal's head is, instead of reprinting both.
"""

from __future__ import annotations

import re

from pcp.core.ipm.model import IrisGoal
from pcp.core.ipm.pattern import PatternSyntaxError, align, compile_auto
from pcp.core.ipm.skeleton import parse_skeleton
from pcp.core.search import tactics_for

#: Tactics that carry an intro pattern, and how to pull the hypothesis and pattern out.
_PATTERN_TACTIC = re.compile(
    r'^\s*(?P<tac>iDestruct|iIntros|iIntro|iMod|iPoseProof|iCombine|iSpecialize)\b(?P<rest>.*)$', re.S
)
_HYP = re.compile(r'"([^"]+)"')
_AS_PATTERN = re.compile(r'\bas\b\s*(?:\(([^)]*)\)\s*)?"([^"]*)"', re.S)
#: `iIntros (x y) "p1 p2"` -- the patterns apply to the *goal's* leading premises,
#: not to any named hypothesis, so they need their own alignment path.
_IINTROS = re.compile(r'^\s*iIntros?\b\s*(?:\(([^)]*)\)\s*)?"([^"]*)"', re.S)
_APPLY_TACTIC = re.compile(r"^\s*(iApply|wp_apply|iFrame|iExact|iAssumption|done|by\b)")


def diagnose(tactic: str, error: str, goal: IrisGoal | None) -> str:
    parts: list[str] = []
    if error:
        parts.append(error.strip()[:1200])

    pattern_report = _pattern_diagnosis(tactic, goal) or _intros_diagnosis(tactic, goal)
    if pattern_report:
        parts.append(pattern_report)

    apply_report = _apply_diagnosis(tactic, goal)
    if apply_report:
        parts.append(apply_report)

    if goal is not None:
        leftovers = [h.id for h in goal.spatial]
        if leftovers and _APPLY_TACTIC.match(tactic or ""):
            # Failure mode #2: `iFrame` / `done` fails because the spatial context is
            # not empty, and the error does not say so.
            parts.append(
                "the spatial context is not empty: "
                + ", ".join(f'"{n}"' for n in leftovers)
                + " -- these must be consumed or framed before the goal can close"
            )
        if goal.modality.mask:
            parts.append(f"current modality: {goal.modality.describe()}")
        suggestions = tactics_for(goal.goal)
        if suggestions:
            parts.append("tactics that apply to this goal shape: " + ", ".join(suggestions[:6]))
    return "\n\n".join(p for p in parts if p)


def _pattern_diagnosis(tactic: str, goal: IrisGoal | None) -> str:
    m = _PATTERN_TACTIC.match(tactic or "")
    if not m or goal is None:
        return ""
    rest = m.group("rest")
    am = _AS_PATTERN.search(rest)
    if not am:
        return ""
    binders = [b for b in (am.group(1) or "").split() if b]
    pattern = am.group(2)
    hyps = _HYP.findall(rest[: am.start()]) or _HYP.findall(rest)
    subject = next((h for h in hyps if goal.by_id(h)), None)
    if subject is None:
        return ""
    hyp = goal.by_id(subject)
    assert hyp is not None
    try:
        report = align(pattern, parse_skeleton(hyp.prop), binders=binders)
    except PatternSyntaxError as exc:
        skel = parse_skeleton(hyp.prop)
        return (
            f"the pattern {pattern!r} does not parse: {exc}\n"
            f"a pattern that fits \"{subject}\": {compile_auto(skel, subject).pattern_text}"
        )
    if report.ok:
        return ""
    return f'destructuring "{subject}":\n' + report.render()


def _intros_diagnosis(tactic: str, goal: IrisGoal | None) -> str:
    """Align `iIntros` patterns against the goal's leading premises.

    `iIntros "[HP|HQ]"` fails for exactly the same reason an `iDestruct` pattern
    does -- the pattern does not fit the thing it is taking apart -- but the thing is
    the wand's left-hand side, not a hypothesis, so it needs its own walk.
    """
    if goal is None:
        return ""
    m = _IINTROS.match(tactic or "")
    if not m:
        return ""
    from pcp.core.ipm.pattern import parse_patterns

    binders = [b for b in (m.group(1) or "").split() if b]
    try:
        patterns = parse_patterns(m.group(2))
    except PatternSyntaxError as exc:
        return f"the intro pattern {m.group(2)!r} does not parse: {exc}"

    node = parse_skeleton(goal.goal)
    for _ in binders:
        stripped = node.strip_transparent()
        if stripped.kind in ("forall", "exists") and stripped.children:
            node = stripped.children[0]
    reports: list[str] = []
    for i, pat in enumerate(patterns, start=1):
        node = node.strip_transparent()
        if node.kind not in ("wand", "impl"):
            reports.append(
                f"pattern {i} ({pat.render()}) has nothing left to introduce: the goal "
                f"is no longer an implication after {i - 1} intro(s)"
            )
            break
        premise, node = node.children[0], node.children[1]
        report = align(pat, premise)
        if not report.ok:
            reports.append(f"introducing premise {i}:\n" + report.render())
            break
    return "\n".join(reports)


def _apply_diagnosis(tactic: str, goal: IrisGoal | None) -> str:
    if goal is None or not _APPLY_TACTIC.match(tactic or ""):
        return ""
    skel = parse_skeleton(goal.goal)
    lines = ["goal structure:", skel.render(1)]
    if goal.spatial:
        lines.append("available spatial resources:")
        lines.extend(f'  "{h.id}" : {h.prop}' for h in goal.spatial[:12])
    return "\n".join(lines)
