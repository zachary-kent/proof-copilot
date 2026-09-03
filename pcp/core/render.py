"""Budgeted, per-hypothesis rendering (PLAN.md 5).

Iris goals are enormous -- WP goals carry whole program terms, invariant bodies are
multi-line -- and dumping the full state every step destroys the context window.
Every render therefore passes through a budget, and **elision is visible**: each
render ends with `rendered 8/41 hypotheses · 1.2k/4k token budget`.  A model that
knows it is looking at a partial view asks for more; a model that does not,
hallucinates.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from pcp.core.digest import (
    Mode,
    PropStore,
    RenderBudget,
    Selector,
    head_symbol,
    matches,
    render_prop,
)
from pcp.core.ipm.model import Hyp, IrisGoal


@dataclass
class RenderOptions:
    select: str | None = None
    mode: Mode = "full"
    budget: int = 4000
    #: After the first step, render what changed plus a one-line manifest of what did
    #: not.  Default on: repeating an unchanged invariant 300 times is the single
    #: biggest waste in a long proof.
    diff_only: bool = True
    #: Keep hypotheses whose head symbols intersect the goal's; demote the rest.
    relevance: bool = False
    fold_over_lines: int = 4
    show_pure: bool = True
    #: Per-hypothesis mode overrides, by id.
    modes: dict[str, Mode] = field(default_factory=dict)


@dataclass
class RenderResult:
    text: str
    rendered: int
    total: int
    tokens: int
    limit: int
    elided: list[str] = field(default_factory=list)

    def __str__(self) -> str:
        return self.text


def render_goal(
    goal: IrisGoal,
    *,
    previous: IrisGoal | None = None,
    options: RenderOptions | None = None,
    store: PropStore | None = None,
) -> RenderResult:
    opts = options or RenderOptions()
    sel = Selector.parse(opts.select)
    budget = RenderBudget(limit=opts.budget)
    prev_hashes = {h.id: h.hash for h in previous.ipm_hyps} if previous else {}
    goal_heads = {head_symbol(goal.goal)} | {head_symbol(p) for p in _goal_operands(goal.goal)}

    lines: list[str] = []
    manifest: list[str] = []
    total = 0
    rendered = 0
    elided: list[str] = []

    header = f"goal {goal.goal_id}" + (f" · {goal.modality.describe()}" if goal.modality.describe() != "—" else "")
    lines.append(header)

    sections: list[tuple[str, list[Hyp], str]] = []
    if opts.show_pure and goal.pure:
        sections.append(("pure", goal.pure, "pure"))
    sections.append(("intuitionistic □", goal.intuitionistic, "intuitionistic"))
    sections.append(("spatial ∗", goal.spatial, "spatial"))

    for title, hyps, klass in sections:
        if not hyps:
            continue
        body: list[str] = []
        for h in hyps:
            total += 1
            changed = prev_hashes.get(h.id) != h.hash
            if not matches(h.id, h.prop, klass, sel, changed=changed):
                manifest.append(h.id)
                continue
            if opts.diff_only and previous is not None and not changed:
                manifest.append(f"{h.id}=unchanged")
                continue
            if opts.relevance and klass != "pure" and not _relevant(h.prop, goal_heads):
                manifest.append(f"{h.id}~")
                continue
            mode = opts.modes.get(h.id, opts.mode)
            h_hash = store.put(h.prop) if store else h.hash
            text = render_prop(h.prop, h_hash, mode, fold_over_lines=opts.fold_over_lines)
            line = f'  "{h.id}" : {text}' + _flags(h)
            if budget.can_afford(line):
                budget.charge(line)
                body.append(line)
                rendered += 1
            else:
                budget.skip(line)
                elided.append(h.id)
        if body:
            lines.append(title)
            lines.extend(body)

    goal_hash = store.put(goal.goal) if store else goal.goal_hash
    goal_text = render_prop(goal.goal, goal_hash, opts.mode, fold_over_lines=opts.fold_over_lines)
    lines.append("⊢ " + goal_text)
    budget.charge(goal_text)

    if manifest:
        lines.append(f"  … not shown: {', '.join(manifest)}")
    if elided:
        lines.append(f"  … budget exhausted, omitted: {', '.join(elided)}")
    lines.append(
        f"rendered {rendered}/{total} hypotheses · "
        f"{_k(budget.spent)}/{_k(budget.limit)} token budget"
        + (f" · {_k(budget.elided)} elided" if budget.elided else "")
    )
    return RenderResult(
        text="\n".join(lines),
        rendered=rendered,
        total=total,
        tokens=budget.spent,
        limit=budget.limit,
        elided=elided,
    )


def _flags(h: Hyp) -> str:
    bits = []
    if h.persistent:
        bits.append("persistent")
    elif h.persistent is False and h.klass == "spatial":
        bits.append("spatial")
    if h.affine is False:
        bits.append("not affine")
    return f"   [{', '.join(bits)}]" if bits else ""


def _goal_operands(goal: str) -> list[str]:
    from pcp.core.ipm.skeleton import parse_skeleton

    skel = parse_skeleton(goal)
    return [n.text for n in skel.walk() if n.kind == "atom" and n.text]


def _relevant(prop: str, goal_heads: set[str]) -> bool:
    from pcp.core.ipm.skeleton import parse_skeleton

    heads = {head_symbol(prop)}
    heads |= {head_symbol(n.text) for n in parse_skeleton(prop).walk() if n.kind == "atom" and n.text}
    return bool(heads & goal_heads)


def _k(n: int) -> str:
    return f"{n / 1000:.1f}k" if n >= 1000 else str(n)


def render_manifest(goal: IrisGoal) -> str:
    """One line naming everything, for when the budget allowed almost nothing."""
    names = [f'"{h.id}"' for h in goal.ipm_hyps]
    return f"{len(names)} hypotheses: " + ", ".join(names)
