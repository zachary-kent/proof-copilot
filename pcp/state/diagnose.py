"""Structured diagnosis of a failed tactic, by construction (PLAN.md 7).

Two failure families eat most of a worker's turns, and both are answered structurally
rather than with a goal dump:

* **Pattern mismatches** -- ``iDestruct`` / ``iIntros`` / ``iMod ... as`` fail because
  the pattern does not fit the object.  The aligner walks both trees and names the
  first divergence.  The object must be the *right* one: for ``iDestruct (lem with
  "H") as ...`` it is the lemma's conclusion, which is not in the proof state, and the
  report says so instead of aligning against ``H``.
* **Unification failures** -- ``iApply`` / ``wp_apply`` fail because the applied
  conclusion does not match the goal.  They get the conclusion-vs-goal report and
  *never* the leftover-spatial paragraph, which is for closing tactics (``iFrame``,
  ``done``, ``iExact``): telling an ``iApply`` to frame away the very resources the wand
  needs would be the wrong instruction.

The report is not opt-in: any failing ``proof_step`` gets it.
"""

from __future__ import annotations

import dataclasses
from typing import Any

from pcp.rocq.lexer import identifiers
from pcp.state.ipm.model import IrisGoal
from pcp.state.ipm.pattern import PatternSyntaxError, align, compile_auto
from pcp.state.ipm.skeleton import parse_skeleton
from pcp.state.props import normalize_prop
from pcp.state.search import tactics_for
from pcp.state.tactic import TacticCall, Token, parse_tactic

PATTERN_HEADS: frozenset[str] = frozenset({"iDestruct", "iMod", "iPoseProof", "iCombine", "iInv", "iDestructHyp", "iSpecialize"})
INTRO_HEADS: frozenset[str] = frozenset({"iIntros", "iIntro"})
APPLY_HEADS: frozenset[str] = frozenset({"iApply", "wp_apply"})
CLOSING_HEADS: frozenset[str] = frozenset({"iFrame", "done", "iExact", "iAssumption", "by", "iExFalso", "iPureIntro", "eauto", "auto"})
MASK_HEADS: frozenset[str] = frozenset({"iInv"})
_TRANSPARENT = frozenset({"later", "except0", "affinely", "absorbingly", "affine", "absorb"})
_BOX = frozenset({"box", "intuitionistically", "persistently", "plainly", "pers"})
_UPDATE = frozenset({"fupd", "fupd_step", "bupd"})
_BINDERS = ("forall", "exists")
_WORDS = {
    "sep": "a separating conjunction (∗)", "and": "a conjunction (∧)", "or": "a disjunction (∨)",
    "exists": "an existential (∃)", "forall": "a universal (∀)", "pure": "a pure fact (⌜⌝)",
    "wand": "a wand (-∗)", "impl": "an implication (→)", "atom": "an opaque proposition",
}


def diagnose(tactic: str, error: str, goal: IrisGoal | None = None) -> str:
    parts: list[str] = []
    if error and error.strip():
        parts.append(error.strip()[:1200])
    call = parse_tactic(tactic or "")
    if goal is not None:
        report = ""
        if call.head in PATTERN_HEADS:
            report = _pattern_report(call, goal)
        if not report and call.head in INTRO_HEADS:
            report = _intros_report(call, goal)
        parts.append(report)
        if call.head in APPLY_HEADS:
            parts.append(_apply_report(call, goal))
        elif call.head in CLOSING_HEADS:
            parts.append(_leftover_report(goal))
        if _mentions_mask(error) or call.head in MASK_HEADS:
            parts.append(_mask_report(goal))
        suggestions = tactics_for(goal.goal)
        if suggestions:
            parts.append("tactics that apply to this goal shape: " + ", ".join(suggestions[:6]))
    return "\n\n".join(p for p in parts if p)


# ------------------------------------------------------------------ skeletons


def _kind(node: Any) -> str:
    return str(getattr(node, "kind", "atom"))


def _children(node: Any) -> list[Any]:
    return list(getattr(node, "children", None) or [])


def _binders(node: Any) -> list[str]:
    return list(getattr(node, "binders", None) or [])


def _text(node: Any) -> str:
    if _kind(node) == "atom":
        return str(getattr(node, "text", ""))
    fn = getattr(node, "to_notation", None)
    if callable(fn):
        return str(fn())
    return " ".join(str(node.render()).split())


def _strip(node: Any, kinds: frozenset[str]) -> Any:
    while _kind(node) in kinds and _children(node):
        node = _children(node)[0]
    return node


def _describe(node: Any) -> str:
    k = _kind(node)
    if k in _BINDERS:
        sym = "∀" if k == "forall" else "∃"
        return f"{_WORDS[k]} `{sym} {' '.join(_binders(node))}, …`"
    if k == "atom":
        return f"`{_text(node)}`"
    return _WORDS.get(k, k)


def _with_binders(node: Any, binders: list[str]) -> Any:
    try:
        return dataclasses.replace(node, binders=binders)
    except (TypeError, ValueError):
        return node


def _peel_binders(node: Any, names: list[str]) -> tuple[Any, int]:
    """Consume one quantified variable per name; return the body and the shortfall."""
    left = len(names)
    while left > 0:
        node = _strip(node, _TRANSPARENT)
        if _kind(node) not in _BINDERS or not _children(node):
            return node, left
        binders = _binders(node) or ["_"]
        take = min(len(binders), left)
        left -= take
        if take < len(binders):
            return _with_binders(node, binders[take:]), 0
        node = _children(node)[0]
    return node, 0


def _render_alignment(report: Any) -> str:
    fn = getattr(report, "render", None)
    if callable(fn):
        return str(fn())
    lines = [f"pattern/prop mismatch: {getattr(report, 'reason', '') or getattr(report, 'mismatch', '')}"]
    if getattr(report, "mismatch", ""):
        lines.append(f"  at: {report.mismatch}")
    if getattr(report, "suggestion", ""):
        lines.append(f"a pattern that fits: {report.suggestion}")
    return "\n".join(lines)


def _fitting_pattern(node: Any, base: str) -> str:
    compiled = compile_auto(node, base)
    pat = getattr(compiled, "pattern", compiled)
    fn = getattr(pat, "render", None)
    return str(fn()) if callable(fn) else str(pat)


def _align_text(pattern: str, node: Any, subject: str) -> str:
    """``""`` when the pattern fits; the mismatch report otherwise."""
    try:
        report = align(pattern, node)
    except PatternSyntaxError as exc:
        # Only a genuinely illegal pattern gets this line; legal tokens never do.
        return f"the pattern {pattern!r} does not parse: {exc}\na pattern that fits \"{subject}\": {_fitting_pattern(node, subject)}"
    if getattr(report, "ok", False):
        return ""
    return _render_alignment(report)


# ------------------------------------------------------------ pattern-bearing


def _lemma_name(tok: Token) -> str:
    idents = identifiers(tok.text) if tok.kind == "group" else [tok.text]
    return idents[0] if idents else tok.text


def _pattern_report(call: TacticCall, goal: IrisGoal) -> str:
    clause = call.clause("as", "gives")
    if clause is None or clause.pattern is None:
        return ""
    subject = call.subject(before=clause.index)
    if subject is None:
        return ""
    pattern = clause.pattern
    if subject.kind != "string":
        name = _lemma_name(subject)
        return (
            f"the pattern {pattern!r} applies to the conclusion of `{name}`, which is not part of the proof "
            f"state, so it cannot be aligned here. `About {name}.` shows the statement; the hypotheses passed "
            f"with `with` are what the lemma's premises consume."
        )
    if call.head == "iCombine" or clause.keyword == "gives":
        if pattern.strip().lstrip("%#>").replace("_", "").isalnum():
            return ""
        return (f"the pattern {pattern!r} applies to the combined resource, which only exists after the "
                f"combination; name it first (`as \"H\"`) and destruct in a second step")
    hyp = goal.by_id(subject.text)
    if hyp is None:
        names = ", ".join(f'"{h.id}"' for h in goal.ipm_hyps)
        return f'no hypothesis named "{subject.text}" in the context; available: {names}'
    node = parse_skeleton(hyp.prop)
    if call.head == "iMod" or pattern.lstrip().startswith(">"):
        # `iMod` eliminates the update modality *before* the binders are introduced.
        node = _strip(_strip(node, _TRANSPARENT), _UPDATE)
    node, missing = _peel_binders(node, list(clause.binders))
    if missing:
        have = len(clause.binders) - missing
        return (f'destructuring "{subject.text}": {len(clause.binders)} binder names were given but the hypothesis '
                f"has {have} to introduce (it is {_describe(node)}) -- drop the extra binder names")
    text = _align_text(pattern, node, subject.text)
    return f'destructuring "{subject.text}":\n{text}' if text else ""


# --------------------------------------------------------------------- iIntros


def _split_patterns(text: str) -> list[str]:
    out: list[str] = []
    depth = 0
    buf = ""
    for ch in text:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch.isspace() and depth == 0:
            if buf:
                out.append(buf)
            buf = ""
        else:
            buf += ch
    if buf:
        out.append(buf)
    return out


def _intro_items(call: TacticCall) -> list[tuple[str, str]]:
    items: list[tuple[str, str]] = []
    for tok in call.tokens:
        if tok.kind == "group" and tok.text.startswith("("):
            items += [("binder", n) for n in tok.text[1:-1].split() if n != ":"]
        elif tok.kind == "string":
            items += [("pattern", p) for p in _split_patterns(tok.text)]
        elif tok.kind == "punct" and tok.text == ";":
            break
    return items


def _intros_report(call: TacticCall, goal: IrisGoal) -> str:
    """Align each ``iIntros`` item against the goal's leading binders and premises.

    A ``%x`` (or a ``(x)`` binder) peels one quantified variable; anything else needs
    a wand or implication whose premise it destructs.  ``iIntros "%x H"`` on
    ``∀ x, P -∗ Q`` therefore peels the ``∀`` first rather than reporting "nothing
    left to introduce".
    """
    node = parse_skeleton(goal.goal)
    for i, (kind, item) in enumerate(_intro_items(call), start=1):
        node = _strip(node, _TRANSPARENT)
        pure = kind == "binder" or item.lstrip("#>").startswith("%")
        if pure and _kind(node) in _BINDERS:
            node, _ = _peel_binders(node, ["_"])
            continue
        if _kind(node) not in ("wand", "impl") or len(_children(node)) < 2:
            if _kind(node) in _BINDERS:
                return (f"pattern {i} ({item}) meets {_describe(node)}: introduce the variable first, "
                        f"with `%{_binders(node)[0] if _binders(node) else 'x'}` or a `({'x'})` binder group")
            return (f"pattern {i} ({item}) has nothing left to introduce: the goal is {_describe(node)} "
                    f"after {i - 1} intro(s)")
        premise, rest = _children(node)[0], _children(node)[1]
        if kind == "binder":
            return f"binder ({item}) meets a premise, not a quantifier: the goal is {_describe(node)} after {i - 1} intro(s)"
        text = _align_text(item, premise, item.lstrip("%#>") or "H")
        if text:
            return f"introducing premise {i} ({item}):\n{text}"
        node = rest
    return ""


# ------------------------------------------------------------------- iApply


def _wand_chain(node: Any) -> tuple[list[str], list[Any], Any]:
    """``(binders, premises, conclusion)`` of a ``∀ xs, P -∗ Q -∗ R`` shape."""
    binders: list[str] = []
    premises: list[Any] = []
    node = _strip(node, _TRANSPARENT | _BOX)
    while True:
        if _kind(node) == "forall" and _children(node):
            binders += _binders(node)
            node = _strip(_children(node)[0], _TRANSPARENT | _BOX)
            continue
        if _kind(node) in ("wand", "impl") and len(_children(node)) >= 2:
            premises.append(_children(node)[0])
            node = _strip(_children(node)[1], _TRANSPARENT)
            continue
        return binders, premises, node


def _first_mismatch(a: Any, b: Any, path: str = "root") -> str:
    ka, kb = _kind(a), _kind(b)
    if ka == "atom" and kb == "atom":
        if normalize_prop(_text(a)) == normalize_prop(_text(b)):
            return ""
        return f"{path}: `{_text(a)}` vs `{_text(b)}`"
    if ka != kb:
        return f"{path}: {_describe(a)} vs {_describe(b)}"
    ca, cb = _children(a), _children(b)
    if len(ca) != len(cb):
        return f"{path}: {len(ca)} operands vs {len(cb)}"
    for i, (x, y) in enumerate(zip(ca, cb, strict=True), start=1):
        m = _first_mismatch(x, y, f"{path}.{i}")
        if m:
            return m
    return ""


def _apply_report(call: TacticCall, goal: IrisGoal) -> str:
    subject = call.subject()
    lines: list[str] = []
    goal_skel = parse_skeleton(goal.goal)
    hyp = goal.by_id(subject.text) if subject is not None and subject.kind == "string" else None
    if hyp is not None:
        binders, premises, conclusion = _wand_chain(parse_skeleton(hyp.prop))
        lines.append(f'applying "{hyp.id}": its conclusion is `{_text(conclusion)}`; the goal is `{" ".join(goal.goal.split())}`')
        mismatch = _first_mismatch(conclusion, _strip(goal_skel, _TRANSPARENT))
        lines.append(f"first mismatch at {mismatch}" if mismatch else
                     "the conclusion matches the goal structurally; the failure is inside an atom (arguments, evars, or a modality)")
        if premises:
            lines.append("premises that would remain: " + "; ".join(f"`{_text(p)}`" for p in premises))
        if binders:
            lines.append(f"quantified over {' '.join(binders)}; if unification cannot infer them, instantiate with "
                         f'`iApply ("{hyp.id}" $! …)`')
    else:
        name = _lemma_name(subject) if subject is not None else ""
        if name:
            lines.append(f"applying `{name}`: its statement is not part of the proof state, so the unification "
                         f"cannot be replayed here; `About {name}.` shows the conclusion it must match")
        lines.append("goal structure:")
        lines.append(_render_skel(goal_skel))
    if goal.spatial:
        lines.append("available spatial resources:")
        lines.extend(f'  "{h.id}" : {" ".join(h.prop.split())}' for h in goal.spatial[:12])
    return "\n".join(lines)


def _render_skel(node: Any) -> str:
    try:
        return str(node.render(1))
    except TypeError:
        return "\n".join("  " + ln for ln in str(node.render()).splitlines())


# ------------------------------------------------------------------- closing


def _leftover_report(goal: IrisGoal) -> str:
    """Failure mode #2: ``iFrame`` / ``done`` fail because the spatial context is not empty."""
    if not goal.spatial:
        return f'the spatial context is empty, so the failure is the goal itself: `{" ".join(goal.goal.split())}`'
    names = ", ".join(f'"{h.id}"' for h in goal.spatial)
    lines = [f"the spatial context is not empty: {names} -- these must be consumed or framed before the goal can close"]
    lines.extend(f'  "{h.id}" : {" ".join(h.prop.split())}' for h in goal.spatial[:12])
    return "\n".join(lines)


# --------------------------------------------------------------------- masks

_MASK_WORDS = ("mask", "namespace", "↑", "⊆", "subseteq", "fupd", "disjoint")


def _mentions_mask(error: str) -> bool:
    low = (error or "").lower()
    return any(w in low for w in _MASK_WORDS)


def _mask_report(goal: IrisGoal) -> str:
    m = goal.modality
    lines = [f"current modality: {m.describe()}"]
    if m.mask:
        lines.append(f"the goal is under mask {m.mask}; opening an invariant N needs ↑N ⊆ that mask -- "
                     f'`iMod (fupd_mask_subseteq E) as "Hclose"` narrows it and `iMod "Hclose"` restores it')
    else:
        lines.append("the goal carries no fupd/mask at its head; `iInv`/`iMod` need one (`iApply fupd_wp` or "
                     "`wp_apply`-style lemmas introduce it)")
    return "\n".join(lines)
