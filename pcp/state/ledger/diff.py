"""Structural diff between consecutive proof states (PLAN.md 4.1, 4.4).

The matching rules, per context class, name-first / hash-second:

    same name, same hash            unchanged
    same name, evars instantiated   instantiate   (never consume/produce)
    same name, different hash       update
    same hash, different name       rename        (only one old and one new share it)
    in prev, not in next            consume
    in next, not in prev            produce

Goal alignment is suffix-anchored and compares goals **modulo evar instantiation**, so
``iExists 3`` instantiating ``?x`` in an untouched sibling does not fabricate a
``GoalSplit`` (legacy bug).  A step is classified by how many goals it touched:

* the focused goal has no counterpart and no children -> **closed**: ``GoalClosed`` plus
  the consumption of every live spatial hypothesis, whether or not siblings remain
  (legacy: closing a non-final goal recorded nothing);
* one child -> the ordinary diff;
* several children -> ``GoalSplit``; a hypothesis that moved to a child is still live
  there and is *not* consumed; only what is gone from every child is consumed;
* several *previous* goals touched at once -> ``Unknown`` with ``confidence="unknown"``.

Honesty rules (PLAN.md 4.4) are structural, not heuristic: no synthetic child goal (so
closing under a mask cannot emit a ``MaskChange``), no ``Consume`` for a persistent
(intuitionistic) hypothesis that was destructed, and ``Unknown`` whenever several
hypotheses print identically and all their names moved.
"""

from __future__ import annotations

import re
from collections import defaultdict
from collections.abc import Sequence
from dataclasses import dataclass
from typing import Any

from pcp.state.ipm.model import Hyp, IrisGoal, Modality, Step, canonical_mask
from pcp.state.ipm.skeleton import parse_skeleton
from pcp.state.ledger.events import Event
from pcp.state.props import normalize_prop, prop_hash
from pcp.state.tactic import TacticCall, parse_tactic

EVAR = "?_"

DESTRUCT_HEADS: frozenset[str] = frozenset({"iDestruct", "iMod", "iInv", "iPoseProof", "iDestructHyp"})
INTRO_HEADS: frozenset[str] = frozenset({"iIntros", "iIntro"})
SPECIALIZE_HEADS: frozenset[str] = frozenset({"iSpecialize"})
_BOX_PREFIXES = ("□", "<pers>", "■")


# ------------------------------------------------------------- evar instantiation


def is_instantiation(before: str, after: str) -> bool:
    """Did ``before`` become ``after`` purely by instantiating evars?

    Liberal by design: an evar may become any non-empty text.  ``Instantiate`` is
    excluded from consume/produce, and a step whose only differences are reprints of
    hypotheses no tactic touched must never read as a mass consumption.  Unicode evars
    (``?Φ``, ``?γ``) are handled by ``props.normalize_prop``.
    """
    b, a = normalize_prop(before), normalize_prop(after)
    if b == a:
        return True
    if EVAR not in b:
        return False
    pattern = "(?:.+?)".join(re.escape(part) for part in b.split(EVAR))
    return re.fullmatch(pattern, a, flags=re.S) is not None


def _same_prop(x: Hyp, y: Hyp) -> bool:
    return x.hash == y.hash or is_instantiation(x.prop, y.prop)


# --------------------------------------------------------------- goal alignment


@dataclass
class GoalAlignment:
    """How the goals after a step relate to the goals before it."""

    parent: IrisGoal | None
    #: New goals that are not part of the untouched tail.
    children: list[IrisGoal]
    #: Trailing goals that survived unchanged (modulo evar instantiation).
    untouched: list[IrisGoal]
    #: Previous goals without a counterpart; the focused goal is always first.
    touched: list[IrisGoal]

    @property
    def spawned(self) -> bool:
        return len(self.children) > 1

    @property
    def closed(self) -> bool:
        return self.parent is not None and not self.children


def same_goal(a: IrisGoal, b: IrisGoal) -> bool:
    """Equal modulo evar instantiation: same hypothesis names, props and conclusion."""
    ah, bh = a.ipm_hyps, b.ipm_hyps
    if [h.id for h in ah] != [h.id for h in bh] or [h.klass for h in ah] != [h.klass for h in bh]:
        return False
    if a.goal_hash != b.goal_hash and not is_instantiation(a.goal, b.goal):
        return False
    return all(_same_prop(x, y) for x, y in zip(ah, bh, strict=True))


def align_goals(prev: list[IrisGoal], next_: list[IrisGoal]) -> GoalAlignment:
    if not prev:
        return GoalAlignment(None, list(next_), [], [])
    tail = prev[1:]
    keep = 0
    while keep < len(tail) and keep < len(next_) and same_goal(tail[-1 - keep], next_[-1 - keep]):
        keep += 1
    cut = len(next_) - keep
    return GoalAlignment(prev[0], list(next_[:cut]), list(next_[cut:]), list(prev[: len(prev) - keep]))


# ----------------------------------------------------------------- context diff


@dataclass(frozen=True)
class ContextDiff:
    unchanged: tuple[str, ...] = ()
    renamed: tuple[tuple[str, str], ...] = ()
    updated: tuple[str, ...] = ()
    consumed: tuple[str, ...] = ()
    produced: tuple[str, ...] = ()
    instantiated: tuple[str, ...] = ()
    #: Names the matcher refused to attribute.
    ambiguous: tuple[str, ...] = ()


def diff_context(prev: list[Hyp], next_: list[Hyp]) -> ContextDiff:
    prev_by_name = {h.id: h for h in prev}
    next_by_name = {h.id: h for h in next_}
    unchanged: list[str] = []
    updated: list[str] = []
    instantiated: list[str] = []
    renamed: list[tuple[str, str]] = []
    ambiguous: list[str] = []
    unmatched_prev: list[Hyp] = []
    unmatched_next: list[Hyp] = []
    for name, ph in prev_by_name.items():
        nh = next_by_name.get(name)
        if nh is None or ph.anonymous or nh.anonymous:
            # An anonymous hypothesis' id (`_1`, `_2`) is its *position*, so the name
            # says nothing once anything before it went away: it is matched by prop
            # below, never by id (an `iFrame` that spent `_1` read as "Update _1").
            unmatched_prev.append(ph)
        elif ph.hash == nh.hash:
            unchanged.append(name)
        elif is_instantiation(ph.prop, nh.prop):
            instantiated.append(name)
        else:
            updated.append(name)
    for name, nh in next_by_name.items():
        old = prev_by_name.get(name)
        if old is None or nh.anonymous or old.anonymous:
            unmatched_next.append(nh)
    # A permutation of names over unchanged props (`iRename` cycles) prints exactly
    # like a set of updates; the printed state cannot tell the two apart, so neither
    # is claimed (PLAN.md 4.4).
    old_hashes = {n: prev_by_name[n].hash for n in updated}
    new_hashes = {n: next_by_name[n].hash for n in updated}
    swapped = [n for n in updated if any(new_hashes[n] == old_hashes[m] for m in updated if m != n)]
    if swapped:
        ambiguous.extend(swapped)
        updated = [n for n in updated if n not in swapped]
    # Anonymous hypotheses print identically whenever their props do, so pairing them
    # by prop in display order is exact, not a guess: nothing observable distinguishes
    # two anonymous `P`s.  A pair whose position moved is a rename (`_2` -> `_1`).
    anon_prev: dict[str, list[Hyp]] = defaultdict(list)
    for h in unmatched_prev:
        if h.anonymous:
            anon_prev[h.hash].append(h)
    for h in [x for x in unmatched_next if x.anonymous]:
        olds = anon_prev.get(h.hash)
        if not olds:
            continue
        old = olds.pop(0)
        unmatched_prev.remove(old)
        unmatched_next.remove(h)
        if old.id == h.id:
            unchanged.append(h.id)
        else:
            renamed.append((old.id, h.id))

    by_hash_prev: dict[str, list[Hyp]] = defaultdict(list)
    for h in unmatched_prev:
        by_hash_prev[h.hash].append(h)
    by_hash_next: dict[str, list[Hyp]] = defaultdict(list)
    for h in unmatched_next:
        by_hash_next[h.hash].append(h)
    consumed = {h.id for h in unmatched_prev}
    produced = {h.id for h in unmatched_next}
    for hsh, olds in by_hash_prev.items():
        news = by_hash_next.get(hsh, [])
        if not news:
            continue
        if len(olds) == 1 and len(news) == 1:
            renamed.append((olds[0].id, news[0].id))
            consumed.discard(olds[0].id)
            produced.discard(news[0].id)
        else:
            # Several hypotheses print identically and all their names moved: which went
            # where is not recoverable from the printed state.  Say so.
            ambiguous.extend(x.id for x in olds + news)
            consumed.difference_update(x.id for x in olds)
            produced.difference_update(x.id for x in news)
    order_prev = {h.id: i for i, h in enumerate(prev)}
    order_next = {h.id: i for i, h in enumerate(next_)}
    return ContextDiff(
        unchanged=tuple(unchanged),
        renamed=tuple(renamed),
        updated=tuple(updated),
        consumed=tuple(sorted(consumed, key=lambda n: order_prev[n])),
        produced=tuple(sorted(produced, key=lambda n: order_next[n])),
        instantiated=tuple(instantiated),
        ambiguous=tuple(ambiguous),
    )


# -------------------------------------------------------------------- the step


def diff_step(prev_goals: list[IrisGoal], next_goals: list[IrisGoal], *, step: int, tactic: str) -> list[Event]:
    """The ledger events of one step (PLAN.md 4.1)."""
    if not prev_goals:
        return []
    al = align_goals(prev_goals, next_goals)
    call = parse_tactic(tactic)
    ctx = _Ctx(step, tactic.strip(), call)
    assert al.parent is not None
    if len(al.touched) > 1:
        return _multi_goal(ctx, al)
    if not al.children:
        return _closed(ctx, al.parent, final=not next_goals)
    if len(al.children) == 1:
        return _single(ctx, al.parent, al.children[0])
    return _split(ctx, al.parent, al.children)


def attach(tracer: Any) -> Any:
    """Hook the ledger into a ``Tracer``: every successful step's events go to ``trace.events``.

    The tracer knows nothing about the ledger (it only offers ``on_step(step, prev)``),
    so attaching is explicit; a trace recorded without it is repaired by
    :func:`replay_events`.
    """
    trace = tracer.trace

    def on_step(step: Step, prev: list[IrisGoal]) -> None:
        if step.ok:
            trace.events.extend(diff_step(list(prev), list(step.goals), step=step.step, tactic=step.tactic))

    tracer.on_step = on_step
    return tracer


def replay_events(steps: Sequence[Step]) -> list[Event]:
    """The ledger of a whole trace, recomputed from its steps.

    Events are a pure function of consecutive states, so a trace that was recorded
    without them (or after a change to the matcher) is re-derived, never re-run
    (PLAN.md 6: everything but the tactic list is derived and cacheable).
    """
    out: list[Event] = []
    prev: list[IrisGoal] | None = None
    for s in steps:
        if not s.ok:
            break
        if prev is not None:
            out += diff_step(prev, list(s.goals), step=s.step, tactic=s.tactic)
        prev = list(s.goals)
    return out


def parent_goal_id(prev_goals: list[IrisGoal]) -> str | None:
    """The goal a step acted on: petanque focuses ``goals[0]``."""
    return prev_goals[0].goal_id if prev_goals else None


@dataclass(frozen=True)
class _Ctx:
    step: int
    tactic: str
    call: TacticCall

    def event(self, kind: str, goal_id: str, **kw: object) -> Event:
        return Event(step=self.step, kind=kind, tactic=self.tactic, goal_id=goal_id, **kw)  # type: ignore[arg-type]


@dataclass(frozen=True)
class _Pair:
    """The structural facts of one (parent, child) goal pair."""

    child: IrisGoal
    intuit: ContextDiff
    spatial: ContextDiff
    #: new intuitionistic name -> old spatial name (spatial -> intuitionistic moves)
    persisted: dict[str, str]

    @property
    def consumed_spatial(self) -> list[str]:
        return [n for n in self.spatial.consumed if n not in self.persisted.values()]

    @property
    def gone_intuit(self) -> list[str]:
        return [n for n in self.intuit.consumed if n not in self.persisted.values()]

    @property
    def produced(self) -> list[str]:
        return list(self.spatial.produced) + [n for n in self.intuit.produced if n not in self.persisted]

    def klass_of(self, name: str) -> str:
        return "intuitionistic" if name in self.intuit.produced else "spatial"


def _peel_box(prop: str) -> str:
    text = prop.strip()
    while True:
        for p in _BOX_PREFIXES:
            if text.startswith(p):
                text = text[len(p) :].lstrip()
                break
        else:
            return text


def _pair(parent: IrisGoal, child: IrisGoal) -> _Pair:
    intuit = diff_context(parent.intuitionistic, child.intuitionistic)
    spatial = diff_context(parent.spatial, child.spatial)
    persisted: dict[str, str] = {}
    gone = [(n, h) for n in spatial.consumed for h in parent.spatial if h.id == n]
    for new in intuit.produced:
        nh = next(h for h in child.intuitionistic if h.id == new)
        for old, oh in gone:
            if old in persisted.values():
                continue
            # Iris strips the box on the way into the intuitionistic context:
            # `H : □ P` becomes `H2 : P`, so compare with the box peeled on both sides.
            if old == new or oh.hash == nh.hash or prop_hash(_peel_box(oh.prop)) == prop_hash(_peel_box(nh.prop)):
                persisted[new] = old
                break
    return _Pair(child, intuit, spatial, persisted)


def _matching_events(ctx: _Ctx, pr: _Pair) -> list[Event]:
    gid = pr.child.goal_id
    out: list[Event] = []
    for klass, cd in (("intuitionistic", pr.intuit), ("spatial", pr.spatial)):
        for name in cd.ambiguous:
            out.append(ctx.event("Unknown", gid, hyp=name, klass=klass, confidence="unknown",
                                 detail="the printed state does not say which name became which "
                                        "(identical props whose names all moved, or names permuted)"))
        for name in cd.instantiated:
            out.append(ctx.event("Instantiate", gid, hyp=name, klass=klass, detail="evar instantiated; not a consumption"))
        for old, new in cd.renamed:
            out.append(ctx.event("Rename", gid, hyp=new, sources=[old], targets=[new], klass=klass))
        for name in cd.updated:
            out.append(ctx.event("Update", gid, hyp=name, klass=klass))
    for new, old in pr.persisted.items():
        out.append(ctx.event("Persist", gid, hyp=new, sources=[old], targets=[new], klass="intuitionistic",
                             detail="moved spatial → intuitionistic"))
    return out


def _produce_kind(call: TacticCall, sources: list[str], produced: int) -> str:
    if call.head in INTRO_HEADS:
        return "Intro"
    if call.head in SPECIALIZE_HEADS:
        return "Specialize"
    if len(sources) == 1 and (produced > 1 or call.head in DESTRUCT_HEADS):
        return "Split"
    return "Produce"


def _conjuncts(goal: str) -> set[str]:
    skel = parse_skeleton(goal) if goal.strip() else None
    if skel is None:
        return set()
    if getattr(skel, "kind", "") == "sep":
        return {normalize_prop(_node_text(c)) for c in skel.children}
    return {normalize_prop(goal)}


def _node_text(node: object) -> str:
    if getattr(node, "kind", "") == "atom":
        return str(getattr(node, "text", ""))
    to_notation = getattr(node, "to_notation", None)
    if callable(to_notation):
        return str(to_notation())
    return " ".join(str(node.render()).split())  # type: ignore[attr-defined]


def _framed(prop: str, parent: IrisGoal, child: IrisGoal) -> bool:
    """A spatial hypothesis vanished and the goal lost the matching conjunct."""
    if parent.goal_hash == child.goal_hash:
        return False
    p = normalize_prop(prop)
    return p in _conjuncts(parent.goal) and p not in _conjuncts(child.goal)


def _consume_kind(ctx: _Ctx, prop: str, parent: IrisGoal, child: IrisGoal | None) -> str:
    if ctx.call.mentions("iFrame"):
        return "Frame"
    if child is not None and _framed(prop, parent, child):
        return "Frame"
    return "Consume"


def _persistent_uses(ctx: _Ctx, parent: IrisGoal, child: IrisGoal | None, produced: list[str]) -> list[Event]:
    """A tactic that *names* an intuitionistic hypothesis and keeps it used it.

    ``iFrame "HP"``, ``iInv "Hinv" as ...``, ``iPoseProof "HP" as ...``, ``iApply "HP"``,
    ``iMod ("Hclose" with "HP")``: the hypothesis is still there afterwards, so no
    consume-side event would ever mention it and ``unused_at_qed`` would call an
    invariant that was opened at every step "never used".  Recorded as a ``Frame`` of
    class ``intuitionistic`` -- the one kind the queries already read as "a use that
    is not a loss".  Only when the step visibly did something (goal changed, something
    produced, or the goal closed): naming a hypothesis in a no-op is not a use.
    """
    if child is not None and parent.goal_hash == child.goal_hash and not produced:
        return []
    kept = {h.id for h in parent.intuitionistic}
    if child is not None:
        kept &= {h.id for h in child.intuitionistic}
    gid = child.goal_id if child is not None else parent.goal_id
    if ctx.call.head == "iFrame":
        detail = "framed a persistent hypothesis; it stays available"
    else:
        detail = "used by name; persistent, so it stays available"
    return [
        ctx.event("Frame", gid, hyp=name, sources=[name], targets=list(produced), klass="intuitionistic", detail=detail)
        for name in _dedupe(ctx.call.all_strings)
        if name in kept
    ]


def _modal(m: Modality) -> bool:
    return m.fupd or m.bupd or m.except0


def _modality_events(ctx: _Ctx, parent: IrisGoal, child: IrisGoal) -> list[Event]:
    out: list[Event] = []
    gid = child.goal_id
    before, after = canonical_mask(parent.modality.mask), canonical_mask(child.modality.mask)
    # `None` and `⊤` are the same ambient mask; reporting `⊤ → ⊤` would be noise, and
    # noise in a mask report is worse than silence.
    if before != after:
        out.append(ctx.event("MaskChange", gid, detail=f"{before} → {after}"))
    laters = child.modality.laters - parent.modality.laters
    if laters:
        out.append(ctx.event("LaterIntro", gid, detail=f"later depth {laters:+d}"))
    if ctx.call.head == "iModIntro" or (_modal(parent.modality) and not _modal(child.modality) and ctx.call.head != "iMod"):
        out.append(ctx.event("ModIntro", gid, detail="the goal's modality was introduced"))
    return out


def _single(ctx: _Ctx, parent: IrisGoal, child: IrisGoal) -> list[Event]:
    pr = _pair(parent, child)
    gid = child.goal_id
    out = _matching_events(ctx, pr)
    produced = pr.produced
    old_pure = {n for h in parent.pure for n in h.names}
    new_pure = [n for h in child.pure for n in h.names if n not in old_pure]
    # What a consumed hypothesis became includes the Coq-context names it left behind
    # (`iDestruct "H" as (n) "[%Hn HΦ]"` -> `HΦ, n, Hn`), so `blame` lists every piece.
    targets = produced + [n for n in new_pure if n not in produced] if pr.consumed_spatial else produced
    for name in pr.consumed_spatial:
        hyp = next(h for h in parent.spatial if h.id == name)
        if name in new_pure:
            detail = f"moved to the pure (Coq) context as {name}"
        elif produced:
            detail = ""
        elif parent.goal_hash != child.goal_hash:
            detail = "used against the goal"
        else:
            detail = ""
        out.append(ctx.event(_consume_kind(ctx, hyp.prop, parent, child), gid, hyp=name, sources=[name],
                             targets=targets, klass="spatial", detail=detail))
    sources = pr.consumed_spatial + (pr.gone_intuit if produced else [])
    if not produced:
        for name in pr.gone_intuit:
            out.append(ctx.event("Consume", gid, hyp=name, sources=[name], klass="intuitionistic",
                                 detail="cleared from the intuitionistic context (persistent: never a spatial consumption; re-introduce it)"))
    kind = _produce_kind(ctx.call, sources, len(produced))
    for name in produced:
        out.append(ctx.event(kind, gid, hyp=name, sources=sources, targets=targets, klass=pr.klass_of(name)))
    out += _persistent_uses(ctx, parent, child, produced)
    out += _modality_events(ctx, parent, child)
    return out


def _closed(ctx: _Ctx, parent: IrisGoal, *, final: bool) -> list[Event]:
    gid = parent.goal_id
    detail = "the last goal closed; the proof is complete" if final else "the focused goal closed; siblings remain"
    out = [ctx.event("GoalClosed", gid, detail=detail)]
    # Everything spatial that was still live was spent on the goal -- what makes
    # `unused_at_qed` meaningful.  Intuitionistic hypotheses are never consumed.
    for h in parent.spatial:
        out.append(ctx.event(_consume_kind(ctx, h.prop, parent, None), gid, hyp=h.id, sources=[h.id],
                             klass="spatial", detail="spent closing the goal"))
    out += _persistent_uses(ctx, parent, None, [])
    return out


def _dedupe(names: list[str]) -> list[str]:
    return list(dict.fromkeys(names))


def _split(ctx: _Ctx, parent: IrisGoal, children: list[IrisGoal]) -> list[Event]:
    pairs = [_pair(parent, c) for c in children]
    out: list[Event] = []
    for pr in pairs:
        out += _matching_events(ctx, pr)
    consumed_spatial = [h.id for h in parent.spatial if all(h.id in pr.consumed_spatial for pr in pairs)]
    gone_intuit = [h.id for h in parent.intuitionistic if all(h.id in pr.gone_intuit for pr in pairs)]
    produced_all = _dedupe([n for pr in pairs for n in pr.produced])
    routed = _routing(parent, pairs)
    detail = f"one goal became {len(children)}"
    if routed:
        detail += " (routed: " + "; ".join(f"{', '.join(names)} → {gid}" for gid, names in routed) + ")"
    out.insert(0, ctx.event("GoalSplit", parent.goal_id, targets=[c.goal_id for c in children], detail=detail))
    for name in consumed_spatial:
        hyp = next(h for h in parent.spatial if h.id == name)
        out.append(ctx.event(_consume_kind(ctx, hyp.prop, parent, None), parent.goal_id, hyp=name, sources=[name],
                             targets=produced_all, klass="spatial", detail="gone from every child goal"))
    sources = consumed_spatial + (gone_intuit if produced_all else [])
    if not produced_all:
        for name in gone_intuit:
            out.append(ctx.event("Consume", parent.goal_id, hyp=name, sources=[name], klass="intuitionistic",
                                 detail="cleared from the intuitionistic context in every child (persistent: not a spatial consumption)"))
    kind = _produce_kind(ctx.call, sources, len(produced_all))
    for pr in pairs:
        for name in pr.produced:
            out.append(ctx.event(kind, pr.child.goal_id, hyp=name, sources=sources, targets=produced_all,
                                 klass=pr.klass_of(name)))
        out += _persistent_uses(ctx, parent, pr.child, pr.produced)
        out += _modality_events(ctx, parent, pr.child)
    return out


def _routing(parent: IrisGoal, pairs: list[_Pair]) -> list[tuple[str, list[str]]]:
    """Hypotheses that went to *some* children only: ``[(goal_id, [names])]``."""
    out: list[tuple[str, list[str]]] = []
    for pr in pairs:
        present = {h.id for h in pr.child.ipm_hyps}
        moved = [h.id for h in parent.ipm_hyps if h.id in present and any(h.id not in {x.id for x in q.child.ipm_hyps} for q in pairs)]
        if moved:
            out.append((pr.child.goal_id, moved))
    return out


def _multi_goal(ctx: _Ctx, al: GoalAlignment) -> list[Event]:
    ids = ", ".join(g.goal_id for g in al.touched)
    if not al.children:
        out: list[Event] = []
        for g in al.touched:
            out.append(ctx.event("GoalClosed", g.goal_id, detail=f"{len(al.touched)} goals closed at once ({ids})"))
            for h in g.spatial:
                out.append(ctx.event("Consume", g.goal_id, hyp=h.id, sources=[h.id], klass="spatial", confidence="unknown",
                                     detail=f"spent closing one of {len(al.touched)} goals that closed together"))
        return out
    return [
        ctx.event(
            "Unknown", al.touched[0].goal_id, confidence="unknown", targets=[c.goal_id for c in al.children],
            detail=f"the tactic changed {len(al.touched)} goals at once ({ids}); hypothesis-level attribution "
            "is only reliable for single-focused-goal steps",
        )
    ]
