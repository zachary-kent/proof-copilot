"""Budgeted, per-hypothesis rendering (PLAN.md 5).

Iris goals are enormous, so every render passes through a token budget and **elision is
visible**: every render ends with ``rendered a/b hypotheses · t/limit token budget`` and
a manifest of what was left out and why.  A model that knows it is looking at a partial
view asks for more; a model that does not, hallucinates.

Policy, in priority order (each is explicit here, not implicit in loop order):

1. the goal is charged *first* -- hypotheses cannot starve it;
2. an **explicitly** selected hypothesis (by id, ``mentions:``, ``head:``) is shown even
   under ``diff_only`` or the relevance filter;
3. the relevance filter never demotes everything: if no spatial hypothesis intersects
   the goal's head symbols, every spatial hypothesis stays;
4. changed hypotheses are allocated budget before unchanged ones, spatial before
   intuitionistic before pure; pure hypotheses take part in the diff too.

What the printer hides (``pcp.state.printing``) is marked on the line it misleads: a
hidden coercion adds a ``↳ with coercions`` line with the explicit form, equalities are
flagged with their carrier (``[= at Z]``), and implicit arguments -- mostly noise --
are shown only for a hypothesis selected explicitly.

:func:`goal_list` is the other half of "what changed" (pcp-issues MF3): when a step
changes the number or the identity of the goals, the goals after it are listed in
order, each with a one-line shape (:func:`goal_shape`), which one is focused, which
are new and which goal was closed -- so "did ``wp_apply`` leave a side goal, and where
did it go?" is read off the result instead of guessed.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from pcp.state.digest import PropStore, Selector, estimate_tokens, head_symbol, heads, render_prop
from pcp.state.ipm.model import Hyp, IrisGoal
from pcp.state.ledger.diff import align_goals
from pcp.state.printing import GoalHidden, Hidden
from pcp.state.tactic import parse_tactic


@dataclass
class Rendered:
    text: str
    shown: int
    total: int
    tokens: int
    limit: int
    #: Selected but not affordable.
    elided: list[str] = field(default_factory=list)
    #: Not selected / unchanged / irrelevant, with their markers.
    manifest: list[str] = field(default_factory=list)

    def __str__(self) -> str:
        return self.text


@dataclass
class _Line:
    hyp: Hyp
    section: str
    text: str
    priority: int
    order: int


_SECTIONS = (("pure", "pure"), ("intuitionistic", "intuitionistic □"), ("spatial", "spatial ∗"))


def render_goal(
    goal: IrisGoal,
    *,
    select: str | None = None,
    mode: str = "full",
    budget: int = 4000,
    diff_only: bool = False,
    prev: IrisGoal | None = None,
    relevance: bool = False,
    relevant_to: str | None = None,
    store: PropStore | None = None,
    fold_over_lines: int = 4,
    show_pure: bool = True,
    hidden: GoalHidden | None = None,
) -> Rendered:
    sel = Selector.parse(select)
    prev_hashes = {h.id: h.hash for h in prev.all_hyps} if prev is not None else {}
    if store is not None:
        store.update(goal)
    describe = goal.modality.describe()
    header = f"goal {goal.goal_id}" + (f" · {describe}" if describe != "—" else "")
    goal_line = "⊢ " + render_prop(goal.goal, mode, fold_over_lines=fold_over_lines, hash=goal.goal_hash)
    goal_hidden = hidden.goal if hidden is not None else None
    carrier = _carrier_bit(goal_hidden)
    goal_line += f"   [{carrier}]" if carrier else ""
    if mode in ("full", "folded"):
        goal_line += _hidden_lines(goal_hidden, explicit=False)
    spent = estimate_tokens(header) + estimate_tokens(goal_line)

    relevant = _relevant_set(goal, relevant_to) if relevance else None
    manifest: list[str] = []
    candidates: list[_Line] = []
    total = 0
    order = 0
    for klass, _title in _SECTIONS:
        if klass == "pure" and not show_pure:
            continue
        for h in goal.context(klass):  # type: ignore[arg-type]
            total += 1
            order += 1
            changed = prev is None or prev_hashes.get(h.id) != h.hash
            explicit = sel.explicit(h.id, h.prop, names=h.names)
            if not sel.matches(h.id, h.prop, klass, names=h.names, changed=changed):
                manifest.append(h.id)
                continue
            if not explicit:
                if diff_only and prev is not None and not changed:
                    manifest.append(f"{h.id}=unchanged")
                    continue
                if relevant is not None and klass != "pure" and h.id not in relevant:
                    manifest.append(f"{h.id}~")
                    continue
            priority = 0 if explicit else _priority(klass, changed)
            detail = hidden.get(h) if hidden is not None else None
            candidates.append(_Line(h, klass, _hyp_line(h, mode, fold_over_lines, detail, explicit=explicit),
                                    priority, order))

    accepted: set[int] = set()
    elided: list[str] = []
    for line in sorted(candidates, key=lambda c: (c.priority, c.order)):
        cost = estimate_tokens(line.text)
        if spent + cost <= budget:
            spent += cost
            accepted.add(line.order)
        else:
            elided.append(line.hyp.id)
    elided.sort(key=lambda i: next(c.order for c in candidates if c.hyp.id == i))

    lines = [header]
    for klass, title in _SECTIONS:
        body = [c.text for c in candidates if c.section == klass and c.order in accepted]
        if body:
            lines.append(title)
            lines.extend(body)
    lines.append(goal_line)
    if manifest:
        lines.append(f"  … not shown: {', '.join(manifest)}")
    if elided:
        lines.append(f"  … budget exhausted, omitted: {', '.join(elided)}")
    shown = len(accepted)
    lines.append(f"rendered {shown}/{total} hypotheses · {_k(spent)}/{_k(budget)} token budget"
                 + (f" · {len(elided)} elided" if elided else ""))
    return Rendered(text="\n".join(lines), shown=shown, total=total, tokens=spent, limit=budget,
                    elided=elided, manifest=manifest)


def _priority(klass: str, changed: bool) -> int:
    base = {"spatial": 1, "intuitionistic": 2, "pure": 3}[klass]
    return base if changed else base + 3


def _hyp_line(h: Hyp, mode: str, fold_over_lines: int, hidden: Hidden | None = None, *, explicit: bool = False) -> str:
    name = ", ".join(h.names) if len(h.names) > 1 else h.id
    text = render_prop(h.prop, mode, fold_over_lines=fold_over_lines, hash=h.hash)
    extra = _hidden_lines(hidden, explicit=explicit) if mode in ("full", "folded") else ""
    return f'  "{name}" : {text}' + _flags(h, hidden) + extra


def _hidden_lines(hidden: Hidden | None, *, explicit: bool) -> str:
    """The explicit forms under a line: coercions always, implicit arguments on request."""
    if not hidden:
        return ""
    out = ""
    if hidden.coercions and hidden.explicit:
        out += f"\n      ↳ with coercions ({', '.join(hidden.coercions)}): {' '.join(hidden.explicit.split())}"
    if explicit and hidden.implicit:
        out += f"\n      ↳ with implicit arguments: {' '.join(hidden.implicit.split())}"
    return out


def _carrier_bit(hidden: Hidden | None) -> str:
    if hidden is None or not hidden.carriers:
        return ""
    return "= at " + ", ".join(hidden.carriers[:3]) + (", …" if len(hidden.carriers) > 3 else "")


def _flags(h: Hyp, hidden: Hidden | None = None) -> str:
    bits = []
    carrier = _carrier_bit(hidden)
    if carrier:
        bits.append(carrier)
    if h.persistent:
        bits.append("persistent")
    elif h.persistent is False and h.klass == "spatial":
        bits.append("spatial")
    if h.affine is False:
        bits.append("not affine")
    return f"   [{', '.join(bits)}]" if bits else ""


def _relevant_set(goal: IrisGoal, relevant_to: str | None) -> set[str] | None:
    """Ids of the hypotheses whose head symbols intersect the goal's (or the tactic's).

    ``None`` means "do not filter": nothing intersected, and hiding every spatial
    resource on a WP goal is worse than no filter at all.
    """
    goal_heads = heads(goal.goal)
    named: set[str] = set()
    if relevant_to:
        call = parse_tactic(relevant_to)
        named = set(call.all_strings)
        goal_heads |= {w for w in call.words if w not in ("with", "as", "in")}
    relevant = {h.id for h in goal.ipm_hyps if h.id in named or heads(h.prop) & goal_heads}
    # A WP goal's spatial context is the program's footprint: every resource is relevant.
    if "WP" in goal_heads or not any(h.id in relevant for h in goal.spatial):
        relevant |= {h.id for h in goal.spatial}
    if not relevant or relevant >= {h.id for h in goal.ipm_hyps}:
        return None
    return relevant


def _k(n: int) -> str:
    return f"{n / 1000:.1f}k" if n >= 1000 else str(n)


# ------------------------------------------------------------------ goal shapes

#: Width of a goal's shape line.
SHAPE_CHARS = 100
#: A few head symbols read better as words.
_HEAD_WORDS = {"⌜⌝": "pure ⌜…⌝", "∗": "∗ (sep)", "-∗": "-∗ (wand)", "∃": "∃", "∀": "∀", "∧": "∧", "∨": "∨"}


def goal_shape(goal: IrisGoal, width: int = SHAPE_CHARS) -> str:
    """``<kind> · <conclusion, one line>``: what a tactic will meet at this goal.

    The kind is the head of the conclusion as the IPM sees it -- a WP (with its
    expression), an update ``|={E}=>``, a later, a pure ``⌜…⌝``, a connective -- or a
    Coq-level equality for a goal outside the IPM, since the tactics that apply
    (``wp_*`` / ``iMod`` / ``iPureIntro`` / ``lia`` / ``f_equal``) are chosen by it.  An
    atom is its own shape.
    """
    m = goal.modality
    text = " ".join(goal.goal.split())
    if m.wp is not None:
        kind = ("TWP " if m.wp.total else "WP ") + m.wp.expr_summary
    elif m.fupd:
        kind = f"|={{{m.mask}}}=>" if m.mask else "fupd"
    elif m.bupd:
        kind = "|==>"
    elif m.except0:
        kind = "◇"
    elif m.laters:
        kind = "▷" if m.laters == 1 else f"▷^{m.laters}"
    else:
        head = head_symbol(text) if text else ""
        if not goal.is_ipm and head == "=":
            kind = "Coq equality"
        else:
            kind = _HEAD_WORDS.get(head, head)
    if not kind or kind == text:
        line = text
    else:
        line = f"{kind} · {text}"
    return line if len(line) <= width else line[: width - 1].rstrip() + "…"


def goal_list(before: list[IrisGoal], after: list[IrisGoal]) -> dict[str, Any] | None:
    """The goals after a step, in order, when it changed their number or identity; else ``None``.

    ``status`` is ``new`` for a goal the step produced (from the focused goal, or from
    several at once under ``all:``), ``kept`` for one it left alone; ``focused`` marks
    the goal the next tactic runs on.  ``closed`` lists the goals that are gone.  A step
    that just transforms the focused goal (one in, one out) is not a change of goals
    and gets no list -- the rendered goal already shows it.
    """
    al = align_goals(list(before), list(after))
    if before and len(after) == len(before) and len(al.children) == 1 and len(al.touched) <= 1:
        return None
    if not before and not after:
        return None
    produced = {id(g) for g in al.children}
    goals = [
        {"n": i, "id": g.goal_id, "shape": goal_shape(g), "status": "new" if id(g) in produced else "kept",
         "focused": i == 1}
        for i, g in enumerate(after, start=1)
    ]
    closed = [goal_shape(g) for g in al.touched] if not al.children else []
    return {"before": len(before), "after": len(after), "goals": goals, "closed": closed}


def n_goals(n: int) -> str:
    return f"{n} goal{'s' if n != 1 else ''}"


def describe_goal_list(change: dict[str, Any] | None) -> str:
    """One clause for a ``what`` line: ``1 goal → 3 (2 new)``, ``goal closed, 2 left``."""
    if change is None:
        return ""
    new = sum(1 for g in change["goals"] if g["status"] == "new")
    before, after = change["before"], change["after"]
    if after == 0:
        return "no goals left"
    if change["closed"] and not new:
        return f"goal closed, {after} left" + (f"; now focused: {change['goals'][0]['shape']}" if after else "")
    return f"{before} goal{'s' if before != 1 else ''} → {after} ({new} new)"
