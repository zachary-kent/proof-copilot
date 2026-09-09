"""Budgeted, per-hypothesis rendering (PLAN.md 5).

Iris goals are enormous, so every render passes through a token budget and **elision is
visible**: every render ends with ``rendered a/b hypotheses · t/limit token budget`` and
a manifest of what was left out and why.  A model that knows it is looking at a partial
view asks for more; a model that does not, hallucinates.

Policy, in priority order (each a legacy bug when it was implicit in loop order):

1. the goal is charged *first* -- hypotheses cannot starve it;
2. an **explicitly** selected hypothesis (by id, ``mentions:``, ``head:``) is shown even
   under ``diff_only`` or the relevance filter;
3. the relevance filter never demotes everything: if no spatial hypothesis intersects
   the goal's head symbols, every spatial hypothesis stays;
4. changed hypotheses are allocated budget before unchanged ones, spatial before
   intuitionistic before pure; pure hypotheses take part in the diff too.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from pcp.state.digest import PropStore, Selector, estimate_tokens, heads, render_prop
from pcp.state.ipm.model import Hyp, IrisGoal
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
) -> Rendered:
    sel = Selector.parse(select)
    prev_hashes = {h.id: h.hash for h in prev.all_hyps} if prev is not None else {}
    if store is not None:
        store.update(goal)
    describe = goal.modality.describe()
    header = f"goal {goal.goal_id}" + (f" · {describe}" if describe != "—" else "")
    goal_line = "⊢ " + render_prop(goal.goal, mode, fold_over_lines=fold_over_lines, hash=goal.goal_hash)
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
            candidates.append(_Line(h, klass, _hyp_line(h, mode, fold_over_lines), priority, order))

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


def _hyp_line(h: Hyp, mode: str, fold_over_lines: int) -> str:
    name = ", ".join(h.names) if len(h.names) > 1 else h.id
    text = render_prop(h.prop, mode, fold_over_lines=fold_over_lines, hash=h.hash)
    return f'  "{name}" : {text}' + _flags(h)


def _flags(h: Hyp) -> str:
    bits = []
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
    resource on a WP goal is worse than no filter at all (legacy bug).
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
