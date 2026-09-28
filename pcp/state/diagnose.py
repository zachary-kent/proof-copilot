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

Two error families are answered from the *error* before the tactic's shape, because
the tactic's shape is not what went wrong:

* **Framing failures** (``iFrame: cannot frame R``, also raised by ``$H`` inside a
  ``with "[…]"`` specialization) -- the destruct pattern after ``as`` never ran, so it
  is not aligned; instead the resource is compared with its closest counterpart and
  with the pure equalities about its arguments ("has ``n``; needs ``length vs``").
* **Focusing failures** (``Expected a single focused goal``, ``Wrong bullet``, ``No
  such goal``) -- the fix is a bullet or a ``{ }`` block, never another tactic for the
  goal's shape.

The report is not opt-in: any failing ``proof_step`` gets it.  It is also calibrated
(D2): a paragraph appears only when something observed in the goal or the error backs
it -- no tactic shortlist unless the error says the tactic does not fit the goal, no
leftover-resources paragraph unless the error complains about them (an affine goal
closes with leftovers), no pattern paragraph for an error that is not about the pattern.
:func:`diagnose_structured` returns the same text with its repair class and a
``high``/``low`` confidence, which ``diagnosis_log`` records for tuning.
"""

from __future__ import annotations

import dataclasses
import re
from dataclasses import dataclass, field
from typing import Any, Literal

from pcp.rocq.errors import shape_error
from pcp.rocq.lexer import identifiers
from pcp.state.ipm.model import IrisGoal
from pcp.state.ipm.pattern import PatternSyntaxError, align, compile_auto
from pcp.state.ipm.skeleton import parse_skeleton
from pcp.state.props import normalize_prop
from pcp.state.redex import next_redex, wp_expr
from pcp.state.search import tactics_for
from pcp.state.tactic import TacticCall, Token, parse_tactic, term_head

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
#: How much of a long error is kept; ``shape_error`` keeps its tail, where Rocq puts
#: the cause ("In environment … The term … has type …", issue 14).
ERROR_CHARS = 1200

#: The repair a diagnosis points at: what the feedback log counts hits and misses by.
RepairClass = Literal[
    "bullet", "rewrite-before-frame", "check-lemma-premise", "fix-pattern", "fix-intro-pattern",
    "missing-hypothesis", "fix-apply", "close-goal", "mask", "wp-next-step", "goal-shape", "unknown",
]
Confidence = Literal["high", "low"]


@dataclass
class Diagnosis:
    """A structured diagnosis: the string API is ``text``; the rest is what a server
    serialises and what the feedback log (``diagnosis_log.py``) tunes the heuristics by.

    ``confidence`` is ``high`` only when the report rests on a concrete observation that
    bears on the error (a named divergence, an unmatched conjunct, a focusing error);
    ``low`` when it is only a lead; with nothing to say, ``repair="unknown"`` and no report.
    """

    text: str
    report: str = ""
    family: str = ""
    repair: RepairClass = "unknown"
    confidence: Confidence = "low"
    tactic: str = ""
    error: str = ""
    #: The facts the report rests on, one short line each.
    evidence: list[str] = field(default_factory=list)

    def to_json(self) -> dict[str, Any]:
        return {"family": self.family, "repair": self.repair, "confidence": self.confidence, "evidence": list(self.evidence)}


@dataclass
class _Part:
    text: str
    repair: RepairClass = "unknown"
    confidence: Confidence = "low"
    evidence: list[str] = field(default_factory=list)


def diagnose(tactic: str, error: str, goal: IrisGoal | None = None, *, n_goals: int | None = None) -> str:
    """The error plus a structural report.  ``n_goals``: how many goals were focused."""
    return diagnose_structured(tactic, error, goal, n_goals=n_goals).text


def diagnose_structured(tactic: str, error: str, goal: IrisGoal | None = None, *, n_goals: int | None = None) -> Diagnosis:
    """:func:`diagnose` with its repair class, confidence and evidence.

    Every paragraph must be backed by something observed in the goal or the error;
    a generic suggestion that would fire on any failure of this tactic is omitted
    (the ledger's rule: say ``unknown`` -- here, say nothing -- rather than guess).
    """
    error = error or ""
    call = parse_tactic(tactic or "")
    family = error_family(error)
    parts: list[_Part] = []
    if family == "focus":
        parts.append(_focus_report(error, n_goals))
    elif goal is not None:
        parts += _goal_parts(call, error, family, goal)
    parts = [p for p in parts if p.text]
    lead = next((p for p in parts if p.repair != "unknown"), None)
    report = "\n\n".join(p.text for p in parts)
    text = "\n\n".join(t for t in (shape_error(error, ERROR_CHARS), report) if t)
    return Diagnosis(
        text=text, report=report, family=family or _tactic_family(call), tactic=(tactic or "").strip(), error=error,
        repair=lead.repair if lead else "unknown",
        confidence="high" if lead is not None and lead.confidence == "high" else "low",
        evidence=[e for p in parts for e in p.evidence],
    )


def _goal_parts(call: TacticCall, error: str, family: str, goal: IrisGoal) -> list[_Part]:
    parts: list[_Part] = []
    if family == "frame":
        return [_frame_report(error, call, goal)]
    if call.head in PATTERN_HEADS:
        parts.append(_pattern_report(call, goal, error))
    if not any(p.text for p in parts) and call.head in INTRO_HEADS:
        parts.append(_intros_report(call, goal))
    if call.head in APPLY_HEADS:
        parts.append(_apply_report(call, goal, error))
    elif call.head in CLOSING_HEADS:
        parts.append(_closing_report(goal, error))
    elif call.head.startswith("wp_"):
        parts.append(_wp_report(call, goal, error))
    if _mentions_mask(error):
        parts.append(_mask_report(goal))
    if not any(p.text for p in parts) and _misfit_error(error):
        # The error says the tactic does not fit the goal: only then is the goal's own
        # tactic shortlist an answer rather than noise.
        suggestions = tactics_for(goal.goal)
        if suggestions:
            parts.append(_Part("the error says the tactic does not fit the goal; tactics for its head "
                               f"({_describe(_strip(parse_skeleton(goal.goal), _TRANSPARENT))}): " + ", ".join(suggestions[:6]),
                               "goal-shape", "low", [f"goal head: {_describe(parse_skeleton(goal.goal))}"]))
    return parts


def _tactic_family(call: TacticCall) -> str:
    """The failure family when the error text does not decide it: the tactic's."""
    head = call.head
    if head in PATTERN_HEADS:
        return "pattern"
    if head in INTRO_HEADS:
        return "intro"
    if head in APPLY_HEADS:
        return "apply"
    if head in CLOSING_HEADS:
        return "close"
    if head.startswith("wp_"):
        return "wp"
    return ""


_FRAME_RE = re.compile(r"cannot frame\s+(.*)", re.S)
_FOCUS_MARKERS = (
    "expected a single focused goal", "no such goal", "wrong bullet", "no focused proof",
    "focus next goal with bullet", "unfocused goals remain", "this proof is focused",
)
#: Errors that are *about the pattern*: only then is a pattern alignment the answer.
_PATTERN_MARKERS = (
    "pattern", "intosep", "intoexist", "intoor", "intoand", "intopure", "intowand", "cannot destruct",
    "not a separating", "not a disjunction", "not an existential", "not a conjunction", "too many",
    "cannot be destructed", "nothing to introduce", "cannot introduce", "not a wand", "not an implication",
)
#: Errors that say the tactic does not fit the goal's shape.
_SHAPE_MARKERS = (
    "is not a", "cannot find", "no applicable tactic", "does not match", "not of the form", "goal is not",
    "nothing to introduce", "cannot apply",
)
_UNIFY_MARKERS = ("unify", "unification", "cannot infer", "evar", "instantiate")


def error_family(error: str | None) -> str:
    """``frame`` | ``focus`` | ``""``: the families the error itself decides (module docstring)."""
    low = " ".join((error or "").lower().split())
    if not low:
        return ""
    if any(m in low for m in _FOCUS_MARKERS):
        return "focus"
    if _FRAME_RE.search(error or ""):
        return "frame"
    return ""


def _low(error: str) -> str:
    return " ".join((error or "").lower().split())


def _pattern_error(error: str) -> bool:
    return any(m in _low(error) for m in _PATTERN_MARKERS)


def _misfit_error(error: str) -> bool:
    return any(m in _low(error) for m in _SHAPE_MARKERS)


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
    if tok.kind == "group":
        head = term_head(tok.text)
        if head:
            return head
    idents = identifiers(tok.text) if tok.kind == "group" else [tok.text]
    return idents[0] if idents else tok.text


def _pattern_report(call: TacticCall, goal: IrisGoal, error: str) -> _Part:
    clause = call.clause("as", "gives")
    if clause is None or clause.pattern is None:
        return _Part("")
    subject = call.subject(before=clause.index)
    if subject is None:
        return _Part("")
    pattern = clause.pattern
    about_pattern = _pattern_error(error)
    if subject.kind != "string":
        # The object is a lemma's conclusion, which the proof state does not show: there
        # is nothing to align, so this is only worth saying when the error is about the
        # pattern at all (issue 8: an iFrame failure got this paragraph).
        if not about_pattern:
            return _Part("")
        name = _lemma_name(subject)
        return _Part(f"the pattern {pattern!r} applies to the conclusion of `{name}`, which is not part of the proof "
                     f"state; `About {name}.` shows the statement to compare the pattern with.",
                     "fix-pattern", "low", [f"error is about the pattern; subject `{name}` is a term"])
    if call.head == "iCombine" or clause.keyword == "gives":
        if not about_pattern or pattern.strip().lstrip("%#>").replace("_", "").isalnum():
            return _Part("")
        return _Part(f"the pattern {pattern!r} applies to the combined resource, which only exists after the "
                     f"combination; name it first (`as \"H\"`) and destruct in a second step",
                     "fix-pattern", "low", ["error is about the pattern of a combination"])
    hyp = goal.by_id(subject.text)
    if hyp is None:
        names = ", ".join(f'"{h.id}"' for h in goal.ipm_hyps)
        return _Part(f'no hypothesis named "{subject.text}" in the context; available: {names}',
                     "missing-hypothesis", "high", [f'"{subject.text}" is not in the context'])
    node = parse_skeleton(hyp.prop)
    if call.head == "iMod" or pattern.lstrip().startswith(">"):
        # `iMod` eliminates the update modality *before* the binders are introduced.
        node = _strip(_strip(node, _TRANSPARENT), _UPDATE)
    node, missing = _peel_binders(node, list(clause.binders))
    if missing:
        have = len(clause.binders) - missing
        return _Part(f'destructuring "{subject.text}": {len(clause.binders)} binder names were given but the hypothesis '
                     f"has {have} to introduce (it is {_describe(node)}) -- drop the extra binder names",
                     "fix-pattern", "high", [f"{len(clause.binders)} binders given, {have} quantified"])
    text = _align_text(pattern, node, subject.text)
    if not text:
        return _Part("")
    # A divergence is an observation either way; it is the *answer* when the error is about the pattern.
    return _Part(f'destructuring "{subject.text}":\n{text}', "fix-pattern", "high" if about_pattern else "low",
                 [f'pattern {pattern!r} diverges from "{subject.text}"'])


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


def _intros_report(call: TacticCall, goal: IrisGoal) -> _Part:
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
                return _Part(f"pattern {i} ({item}) meets {_describe(node)}: introduce the variable first, "
                             f"with `%{_binders(node)[0] if _binders(node) else 'x'}` or a `({'x'})` binder group",
                             "fix-intro-pattern", "high", [f"intro {i} meets a quantifier"])
            return _Part(f"pattern {i} ({item}) has nothing left to introduce: the goal is {_describe(node)} "
                         f"after {i - 1} intro(s)", "fix-intro-pattern", "high", [f"only {i - 1} premise(s) to introduce"])
        premise, rest = _children(node)[0], _children(node)[1]
        if kind == "binder":
            return _Part(f"binder ({item}) meets a premise, not a quantifier: the goal is {_describe(node)} after "
                         f"{i - 1} intro(s)", "fix-intro-pattern", "high", [f"binder {i} meets a premise"])
        text = _align_text(item, premise, item.lstrip("%#>") or "H")
        if text:
            return _Part(f"introducing premise {i} ({item}):\n{text}", "fix-intro-pattern", "high",
                         [f"intro pattern {i} diverges from its premise"])
        node = rest
    return _Part("")


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


def _apply_report(call: TacticCall, goal: IrisGoal, error: str) -> _Part:
    subject = call.subject()
    goal_skel = parse_skeleton(goal.goal)
    hyp = goal.by_id(subject.text) if subject is not None and subject.kind == "string" else None
    if hyp is not None:
        binders, premises, conclusion = _wand_chain(parse_skeleton(hyp.prop))
        lines = [f'applying "{hyp.id}": its conclusion is `{_text(conclusion)}`; the goal is `{" ".join(goal.goal.split())}`']
        mismatch = _first_mismatch(conclusion, _strip(goal_skel, _TRANSPARENT))
        lines.append(f"first mismatch at {mismatch}" if mismatch else
                     "the conclusion matches the goal structurally; the failure is inside an atom (arguments, evars, or a modality)")
        if premises:
            lines.append("premises that would remain: " + "; ".join(f"`{_text(p)}`" for p in premises))
        if binders and any(m in _low(error) for m in _UNIFY_MARKERS):
            lines.append(f"quantified over {' '.join(binders)} and the error is about unification: instantiate them "
                         f'with `iApply ("{hyp.id}" $! …)`')
        return _Part("\n".join(lines), "fix-apply", "high" if mismatch else "low",
                     [f"conclusion vs goal: {mismatch or 'structurally equal'}"])
    # A lemma: its statement is not in the proof state, so no unification can be
    # replayed.  What *is* observable for `wp_apply` is the redex it has to match.
    name = _lemma_name(subject) if subject is not None else ""
    expr = wp_expr(goal.goal) if call.head == "wp_apply" else None
    if expr is None:
        return _Part("")
    red = next_redex(expr)
    if red.kind == "unknown":
        return _Part("")
    line = f"the WP's next redex is `{red.text}`"
    if red.kind == "call":
        line += f" (a call to `{red.text.split()[0]}`)"
    elif red.why:
        line += f" ({red.why.split(':')[0]})"
    line += f": `{name}`'s WP must be about that expression (`About {name}.`)" if name else ""
    return _Part(line, "fix-apply", "low", [f"next redex: {red.text} ({red.kind})"])


# ------------------------------------------------------------------- closing


def _closing_report(goal: IrisGoal, error: str) -> _Part:
    """``iFrame`` / ``done`` / ``iExact``: which goal conjuncts nothing in the context matches.

    Leftover *spatial* hypotheses do not stop a goal from closing in an affine logic
    (heap_lang's); the unmatched conjuncts do.  The leftovers are named only when the
    error itself complains about them.
    """
    conjuncts = _conjunct_texts(parse_skeleton(goal.goal)) if goal.goal.strip() else []
    have = {normalize_prop(_unparen(h.prop)) for h in goal.ipm_hyps} | {normalize_prop(_unparen(h.prop)) for h in goal.pure}
    trivial = {"True", "emp", "True%I"}
    unmatched = [c for c in conjuncts if normalize_prop(_unparen(c)) not in have and c.strip() not in trivial]
    low = _low(error)
    if goal.spatial and any(m in low for m in ("affine", "leftover", "not empty", "spatial context")):
        names = ", ".join(f'"{h.id}"' for h in goal.spatial)
        return _Part(f"the error is about the remaining spatial context: {names} must be consumed or framed first",
                     "close-goal", "high", ["error mentions leftover resources"])
    if not unmatched:
        return _Part("")
    if not goal.spatial and not goal.intuitionistic and len(unmatched) == len(conjuncts):
        return _Part(f'the IPM context is empty, so nothing can close the goal but a proof of it: `{" ".join(goal.goal.split())}`',
                     "close-goal", "high", ["empty context"])
    shown = ", ".join(f"`{c}`" for c in unmatched[:6])
    return _Part(f"no hypothesis matches {'this goal conjunct' if len(unmatched) == 1 else 'these goal conjuncts'}: "
                 f"{shown} -- prove {'it' if len(unmatched) == 1 else 'them'} (or rewrite a hypothesis into that form) first",
                 "close-goal", "high", [f"unmatched conjunct: {c}" for c in unmatched[:6]])


# ---------------------------------------------------------------------- wp_*


def _wp_report(call: TacticCall, goal: IrisGoal, error: str) -> _Part:
    """A ``wp_load``/``wp_store``/… that failed: what the WP's next redex actually is."""
    expr = wp_expr(goal.goal)
    if expr is None:
        if goal.goal.strip():
            return _Part(f"the goal is not a WP at its head (`{_one_line(goal.goal, 100)}`), so `{call.head}` has "
                         "nothing to step", "wp-next-step", "high", ["goal head is not WP"])
        return _Part("")
    red = next_redex(expr)
    if red.kind == "unknown":
        return _Part("")
    line = f"the WP's next redex is `{red.text}`: {red.why}"
    confidence: Confidence = "low"
    if red.next and not red.next.startswith(call.head):
        confidence = "high"
        line += f" -- not what `{call.head}` steps"
    if red.kind == "heap" and red.loc:
        loc = red.loc.lstrip("#")
        if not any(_points_to(h.prop, loc) for h in goal.ipm_hyps):
            confidence = "high"
            line += f"; there is no `{loc} ↦ …` in the context"
    return _Part(line, "wp-next-step", confidence, [f"next redex: {red.text} ({red.kind})"])


def _points_to(prop: str, loc: str) -> bool:
    words = " ".join(prop.split()).split(" ", 2)
    return len(words) >= 2 and words[0] == loc and words[1].startswith("↦")


def _one_line(text: str, width: int) -> str:
    one = " ".join(text.split())
    return one if len(one) <= width else one[: width - 1] + "…"


# --------------------------------------------------------------------- masks

_MASK_WORDS = ("mask", "namespace", "↑", "⊆", "subseteq", "fupd", "disjoint")


def _mentions_mask(error: str) -> bool:
    low = (error or "").lower()
    return any(w in low for w in _MASK_WORDS)


def _mask_report(goal: IrisGoal) -> _Part:
    m = goal.modality
    lines = [f"current modality: {m.describe()}"]
    if m.mask:
        lines.append(f"the goal is under mask {m.mask}; opening an invariant N needs ↑N ⊆ that mask -- "
                     f'`iMod (fupd_mask_subseteq E) as "Hclose"` narrows it and `iMod "Hclose"` restores it')
        return _Part("\n".join(lines), "mask", "high", [f"error mentions masks; goal mask {m.mask}"])
    lines.append("the goal carries no fupd/mask at its head; `iInv`/`iMod` need one (`iApply fupd_wp` or "
                 "`wp_apply`-style lemmas introduce it)")
    return _Part("\n".join(lines), "mask", "low", ["error mentions masks; no mask at the goal's head"])


# ------------------------------------------------------------------- focusing

_FOCUSED_RE = re.compile(r"(\d+)\s+goals?\s+(?:are|is)\s+focused", re.I)
_NEXT_BULLET_RE = re.compile(r"(?:focus next goal with bullet|expecting)\s+([-+*]+|\{)", re.I)


def _focus_report(error: str, n_goals: int | None) -> _Part:
    """A bullet/brace answer: suggesting ``wp_pures`` for a focusing error sends the
    worker after the goal's shape when the proof script's structure is what failed."""
    low = " ".join((error or "").lower().split())
    m = _FOCUSED_RE.search(error or "")
    n = int(m.group(1)) if m else n_goals
    bullet = _NEXT_BULLET_RE.search(error or "")
    if "expected a single focused goal" in low:
        count = f"{n} goals are focused" if n and n > 1 else "several goals are focused"
        return _Part(f"{count}: the tactic needs exactly one. Prefix a bullet (`- tac.`) to work on the first goal, "
                     f"or wrap its script in `{{ tac. … }}`; `all: tac.` runs it on every goal.",
                     "bullet", "high", ["error: expected a single focused goal"])
    if "wrong bullet" in low or bullet:
        want = f" `{bullet.group(1)}`" if bullet else ""
        return _Part(f"bullet mismatch: the current goal is not finished, or the next goal expects the bullet{want}. "
                     "Close the current goal before the next bullet, and keep one bullet symbol per nesting level.",
                     "bullet", "high", ["error: bullet mismatch"])
    return _Part("no goal is focused here: the previous bullet or `{ }` block already closed its goal. "
                 "Use the next bullet (or `}`) to move to the remaining goals.", "bullet", "high", ["error: no focused goal"])


# -------------------------------------------------------------------- framing


def _frame_target(error: str) -> str:
    m = _FRAME_RE.search(error or "")
    if m is None:
        return ""
    text = " ".join(m.group(1).split()).rstrip(".").strip()
    return _unparen(text)


def _unparen(text: str) -> str:
    t = text.strip()
    while t.startswith("(") and t.endswith(")") and _balanced_inside(t[1:-1]):
        t = t[1:-1].strip()
    return t


def _balanced_inside(text: str) -> bool:
    depth = 0
    for ch in text:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


def _app_tokens(term: str) -> list[str]:
    """Top-level whitespace-separated operands, brackets kept whole, outer parens dropped."""
    return [_unparen(t) for t in _split_patterns(_unparen(" ".join(term.split())))]


def _differences(a: list[str], b: list[str]) -> list[tuple[str, str]] | None:
    """The operand pairs where ``a`` and ``b`` differ, when they share a head and shape."""
    if len(a) != len(b) or len(a) < 2:
        return None
    diffs = [(x, y) for x, y in zip(a, b, strict=True) if normalize_prop(x) != normalize_prop(y)]
    if not diffs or len(diffs) * 2 > len(a):
        return None
    # The head (first operand, or the notation symbol) must agree.
    same = [x for x, y in zip(a, b, strict=True) if normalize_prop(x) == normalize_prop(y)]
    if not any(not x.isidentifier() or x == a[0] for x in same):
        return None
    return diffs


def _conjunct_texts(node: Any) -> list[str]:
    node = _strip(node, _TRANSPARENT)
    if _kind(node) == "sep":
        return [t for c in _children(node) for t in _conjunct_texts(c)]
    return [_text(node)]


def _equalities(goal: IrisGoal, operand: str) -> list[str]:
    """Pure hypotheses ``operand = e`` / ``e = operand``, rendered ``"H" : …``."""
    want = normalize_prop(operand)
    out = []
    for h in goal.pure:
        sides = [normalize_prop(_unparen(s)) for s in h.prop.split("=", 1)] if "=" in h.prop else []
        if len(sides) == 2 and want in sides and "≠" not in h.prop:
            out.append(f'"{h.id}" : {" ".join(h.prop.split())}')
    return out


def _frame_report(error: str, call: TacticCall, goal: IrisGoal) -> _Part:
    """``iFrame: cannot frame R``: which operand of ``R`` is off, and against what.

    ``R`` is the resource being framed (a hypothesis), so the useful comparison is with
    the *other* side: a goal conjunct or another hypothesis with the same head and one
    differing operand.  When the target is a lemma premise (``iMod (lem with "[$H]")``)
    it is not in the proof state; the pure equalities about ``R``'s operands are then
    what says "``n`` is ``length vs``: rewrite first".
    """
    target = _frame_target(error)
    if not target:
        return _Part("")
    want = normalize_prop(target)
    source = next((h for h in goal.ipm_hyps if normalize_prop(h.prop) == want), None)
    lines = [f"framing failed on `{target}`" + (f' (hypothesis "{source.id}")' if source else "")
             + ": nothing on the other side matches it exactly."]
    toks = _app_tokens(target)
    candidates: list[tuple[str, str]] = [(f"goal conjunct `{c}`", c) for c in _conjunct_texts(parse_skeleton(goal.goal))]
    candidates += [(f'hypothesis "{h.id}"', h.prop) for h in goal.spatial + goal.intuitionistic
                   if normalize_prop(h.prop) != want]
    best: tuple[int, str, list[tuple[str, str]]] | None = None
    for where, text in candidates:
        diffs = _differences(toks, _app_tokens(text))
        if diffs and (best is None or len(diffs) < best[0]):
            best = (len(diffs), where, diffs)
    repair: RepairClass = "unknown"
    confidence: Confidence = "low"
    evidence = [f"cannot frame `{target}`"]
    if best is not None:
        _, where, diffs = best
        have = ", ".join(f"`{x}`" for x, _ in diffs)
        need = ", ".join(f"`{y}`" for _, y in diffs)
        lines.append(f"the term to frame has {have}; the closest {where} has {need} -- rewrite first so they agree.")
        repair, confidence = "rewrite-before-frame", "high"
        evidence.append(f"closest {where} differs in {need}")
    elif call.head in PATTERN_HEADS | APPLY_HEADS and (subject := call.subject()) is not None and subject.kind == "group":
        name = _lemma_name(subject)
        lines.append(f"the frame target is a premise of `{name}`, which is not part of the proof state; "
                     f"`About {name}.` shows what it expects -- compare its arguments with `{target}`.")
        repair = "check-lemma-premise"
    facts = [f for tok in toks[1:] if tok.isidentifier() for f in _equalities(goal, tok)]
    if facts:
        lines.append("pure facts about its operands (rewrite with one before framing): " + "; ".join(_dedupe_str(facts)))
        repair = "rewrite-before-frame"
        evidence += [f"pure fact {f}" for f in _dedupe_str(facts)]
    return _Part("\n".join(lines), repair, confidence, evidence)


def _dedupe_str(items: list[str]) -> list[str]:
    return list(dict.fromkeys(items))
