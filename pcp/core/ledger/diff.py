"""Structural diff between consecutive IPM contexts (PLAN.md 4.1).

The matching rules:

    same name, same hash         unchanged
    same hash, different name    rename
    same name, different hash    update
    in prev, not in next         consume
    in next, not in prev         produce

Matching is **name-first, hash-second**: IPM names are unique within a context and
are the primary key; hashes distinguish a rename from destroy-and-create, and matter
because identical printed props are routine in Iris (fractional halves, duplicate
``own`` fragments).

Two honesty rules are load-bearing:

* Hashes are modulo evar names, and a step whose only differences are evar
  instantiations is classified ``Instantiate`` -- never consume/produce.
* When the matching is genuinely ambiguous the ledger emits ``Unknown`` and says so.
  Exotic tactics (``iInduction``, ``iLöb``, project-local IPM tactics) *will* defeat
  the matcher, and a confidently wrong provenance chain is worse than none.
"""

from __future__ import annotations

import re
from collections import defaultdict
from dataclasses import dataclass, field

from pcp.core.digest import normalize
from pcp.core.ipm.model import Hyp, IrisGoal, canonical_mask
from pcp.core.ledger.events import Event

_EVAR_TOKEN = re.compile(r"\?(?:Goal)?[A-Za-z_][A-Za-z0-9_']*")


# ------------------------------------------------------------------- goal alignment

@dataclass
class GoalAlignment:
    """How the goals after a step relate to the goals before it.

    Petanque presents goals as a list whose head is focused, so a tactic acts on
    ``goals[0]``.  The children of that goal are the new goals that are not part of
    the untouched tail.
    """

    parent: IrisGoal | None
    children: list[IrisGoal] = field(default_factory=list)
    untouched: list[IrisGoal] = field(default_factory=list)
    #: ``True`` when the step left more than one goal in play -- the ledger's
    #: guarantees are scoped to single-focused-goal steps.
    spawned: bool = False


def align_goals(prev: list[IrisGoal], next_: list[IrisGoal]) -> GoalAlignment:
    if not prev:
        return GoalAlignment(parent=None, children=list(next_), spawned=len(next_) > 1)
    tail = prev[1:]
    # Longest suffix of `next_` that matches the untouched tail of `prev`.
    keep = 0
    while keep < len(tail) and keep < len(next_) and _same_goal(tail[len(tail) - 1 - keep], next_[len(next_) - 1 - keep]):
        keep += 1
    children = next_[: len(next_) - keep] if keep else list(next_)
    untouched = next_[len(next_) - keep :] if keep else []
    return GoalAlignment(parent=prev[0], children=children, untouched=untouched, spawned=len(children) > 1)


def _same_goal(a: IrisGoal, b: IrisGoal) -> bool:
    return a.goal_hash == b.goal_hash and [h.hash for h in a.ipm_hyps] == [h.hash for h in b.ipm_hyps]


# ------------------------------------------------------------------- context diff

@dataclass
class ContextDiff:
    unchanged: list[str] = field(default_factory=list)
    renamed: list[tuple[str, str]] = field(default_factory=list)
    updated: list[str] = field(default_factory=list)
    consumed: list[str] = field(default_factory=list)
    produced: list[str] = field(default_factory=list)
    instantiated: list[str] = field(default_factory=list)
    #: Names the matcher refused to attribute.
    ambiguous: list[str] = field(default_factory=list)

    @property
    def quiet(self) -> bool:
        return not (self.renamed or self.updated or self.consumed or self.produced or self.instantiated)


def diff_context(prev: list[Hyp], next_: list[Hyp]) -> ContextDiff:
    out = ContextDiff()
    prev_by_name = {h.id: h for h in prev}
    next_by_name = {h.id: h for h in next_}

    # -- pass 1: name-first ------------------------------------------------
    unmatched_prev: list[Hyp] = []
    unmatched_next: list[Hyp] = []
    for name, ph in prev_by_name.items():
        nh = next_by_name.get(name)
        if nh is None:
            unmatched_prev.append(ph)
        elif ph.hash == nh.hash:
            out.unchanged.append(name)
        elif _is_instantiation(ph.prop, nh.prop):
            out.instantiated.append(name)
        else:
            out.updated.append(name)
    for name, nh in next_by_name.items():
        if name not in prev_by_name:
            unmatched_next.append(nh)

    # -- pass 2: hash-second, on what names could not match -----------------
    prev_by_hash: dict[str, list[Hyp]] = defaultdict(list)
    for h in unmatched_prev:
        prev_by_hash[h.hash].append(h)
    next_by_hash: dict[str, list[Hyp]] = defaultdict(list)
    for h in unmatched_next:
        next_by_hash[h.hash].append(h)

    consumed_names = {h.id for h in unmatched_prev}
    produced_names = {h.id for h in unmatched_next}
    for h, olds in prev_by_hash.items():
        news = next_by_hash.get(h, [])
        if not news:
            continue
        if len(olds) == 1 and len(news) == 1:
            out.renamed.append((olds[0].id, news[0].id))
            consumed_names.discard(olds[0].id)
            produced_names.discard(news[0].id)
        else:
            # Several hypotheses print identically and the names all moved: which
            # went where is not recoverable from the printed state.
            out.ambiguous.extend([x.id for x in olds] + [x.id for x in news])
            consumed_names.difference_update(x.id for x in olds)
            produced_names.difference_update(x.id for x in news)

    out.consumed = sorted(consumed_names, key=_order(prev))
    out.produced = sorted(produced_names, key=_order(next_))
    return out


def _order(hyps: list[Hyp]):
    index = {h.id: i for i, h in enumerate(hyps)}
    return lambda name: index.get(name, 1 << 30)


def _is_instantiation(before: str, after: str) -> bool:
    """Did ``before`` become ``after`` purely by instantiating evars?

    Iris proofs are evar-dense; instantiating one reprints hypotheses no tactic
    touched.  Those steps must not read as consume/produce.
    """
    b, a = normalize(before), normalize(after)
    if b == a:
        return True
    if "?" not in b:
        return False
    pattern = "".join(
        "(?:.+?)" if _EVAR_TOKEN.fullmatch(tok) or tok == "?_" else re.escape(tok)
        for tok in _tokenize_for_instantiation(b)
    )
    return re.fullmatch(pattern, a, flags=re.S) is not None


def _tokenize_for_instantiation(text: str) -> list[str]:
    out: list[str] = []
    i = 0
    while i < len(text):
        m = _EVAR_TOKEN.match(text, i) or re.compile(r"\?_").match(text, i)
        if m:
            out.append(m.group(0))
            i = m.end()
        else:
            out.append(text[i])
            i += 1
    return out


# ------------------------------------------------------------------- classification



@dataclass
class StepDiff:
    """Everything one step did, ready to be turned into events."""

    step: int
    tactic: str
    goal_id: str
    intuit: ContextDiff
    spatial: ContextDiff
    alignment: GoalAlignment
    mask_change: tuple[str | None, str | None] | None = None
    later_change: int = 0
    goal_changed: bool = False
    #: The step closed the last goal; the whole spatial context went into it.
    goal_closed: bool = False


def diff_step(
    step: int,
    tactic: str,
    prev_goals: list[IrisGoal],
    next_goals: list[IrisGoal],
) -> tuple[list[StepDiff], GoalAlignment]:
    """Diff one step.  Returns one :class:`StepDiff` per child goal."""
    alignment = align_goals(prev_goals, next_goals)
    parent = alignment.parent
    diffs: list[StepDiff] = []
    if parent is None:
        return diffs, alignment
    if not alignment.children and not alignment.untouched and not next_goals:
        # The tactic closed the last goal.  Everything still live was spent on it,
        # and saying so is what makes `unused_at_qed` meaningful: a resource that is
        # never consumed anywhere usually means the statement is over-strong.
        alignment.children = [IrisGoal(goal_id=f"{parent.goal_id}:closed", goal="")]
        closed = True
    else:
        closed = False
    for child in alignment.children:
        diffs.append(
            StepDiff(
                step=step,
                tactic=tactic,
                goal_id=child.goal_id,
                intuit=diff_context(parent.intuitionistic, child.intuitionistic),
                spatial=diff_context(parent.spatial, child.spatial),
                alignment=alignment,
                mask_change=(
                    (parent.modality.mask, child.modality.mask)
                    # `None` (no modality in the goal) and an explicit `⊤` are the
                    # same ambient mask; reporting `⊤ → ⊤` is noise, and noise in a
                    # mask report is worse than silence -- mask arithmetic is the
                    # thing the agent is meant to trust here.
                    if canonical_mask(parent.modality.mask) != canonical_mask(child.modality.mask)
                    else None
                ),
                later_change=child.modality.laters - parent.modality.laters,
                goal_changed=parent.goal_hash != child.goal_hash,
                goal_closed=closed,
            )
        )
    return diffs, alignment


def to_events(sd: StepDiff, parent: IrisGoal, child: IrisGoal) -> list[Event]:
    """Turn a structural diff into attributed events.

    Attribution is ``produce(step, tactic, from=[consumed ids])``: within one step,
    what was produced came from what was consumed.  When several hypotheses were
    consumed and several produced, the attribution is to the whole consumed set --
    which is true, and coarser than a guess.
    """
    events: list[Event] = []
    tac = sd.tactic.strip()
    low = tac.lower()

    if sd.alignment.spawned and child is sd.alignment.children[0]:
        events.append(
            Event(
                step=sd.step,
                kind="GoalSplit",
                tactic=tac,
                goal_id=sd.goal_id,
                targets=[g.goal_id for g in sd.alignment.children],
                detail=f"one goal became {len(sd.alignment.children)}",
            )
        )

    for klass, cd in (("intuitionistic", sd.intuit), ("spatial", sd.spatial)):
        for name in cd.ambiguous:
            events.append(
                Event(
                    step=sd.step,
                    kind="Unknown",
                    tactic=tac,
                    goal_id=sd.goal_id,
                    hyp=name,
                    klass=klass,
                    confidence="unknown",
                    detail="several hypotheses print identically and all their names moved",
                )
            )
        for name in cd.instantiated:
            events.append(
                Event(step=sd.step, kind="Instantiate", tactic=tac, goal_id=sd.goal_id, hyp=name, klass=klass)
            )
        for old, new in cd.renamed:
            events.append(
                Event(
                    step=sd.step,
                    kind="Rename",
                    tactic=tac,
                    goal_id=sd.goal_id,
                    hyp=new,
                    sources=[old],
                    klass=klass,
                )
            )
        for name in cd.updated:
            events.append(
                Event(step=sd.step, kind="Update", tactic=tac, goal_id=sd.goal_id, hyp=name, klass=klass)
            )

    # A hypothesis that left the spatial context and appeared in the intuitionistic
    # one with the same content was made persistent, not consumed.
    # `persisted` maps the *new* intuitionistic name to the *old* spatial one, so the
    # spatial side must be filtered against its values, not its keys.
    persisted = _persisted(sd, parent, child)
    consumed_spatial = [n for n in sd.spatial.consumed if n not in persisted.values()]
    produced_intuit = [n for n in persisted if n in sd.intuit.produced]

    for new_name, old_name in persisted.items():
        events.append(
            Event(
                step=sd.step,
                kind="Persist",
                tactic=tac,
                goal_id=sd.goal_id,
                hyp=new_name,
                sources=[old_name],
                klass="intuitionistic",
                detail="moved spatial → intuitionistic",
            )
        )

    kind_for_consume: str = "Consume"
    if low.startswith("iframe"):
        kind_for_consume = "Frame"
    for name in consumed_spatial:
        events.append(
            Event(
                step=sd.step,
                kind=kind_for_consume,  # type: ignore[arg-type]
                tactic=tac,
                goal_id=sd.goal_id,
                hyp=name,
                targets=[n for n in sd.spatial.produced if n not in produced_intuit],
                klass="spatial",
                detail=_consume_detail(tac, sd),
            )
        )
    # Intuitionistic hypotheses are duplicable: they are never *consumed*, and
    # calling their disappearance at Qed a consumption would teach the agent the
    # opposite of failure mode #5.  Report it only when a tactic really drops them.
    if not sd.goal_closed:
        for name in sd.intuit.consumed:
            if name in persisted.values():
                continue
            events.append(
                Event(
                    step=sd.step,
                    kind="Consume",
                    tactic=tac,
                    goal_id=sd.goal_id,
                    hyp=name,
                    klass="intuitionistic",
                    detail="cleared from the intuitionistic context (not a spatial consumption)",
                )
            )

    sources = list(consumed_spatial)
    if not sd.goal_closed:
        sources += [n for n in sd.intuit.consumed if n not in persisted.values()]
    produce_kind: str = "Produce"
    if low.startswith(("iintros", "iintro")):
        produce_kind = "Intro"
    elif low.startswith("idestruct") and len(sources) == 1 and len(sd.spatial.produced) > 1:
        produce_kind = "Split"
    elif low.startswith("ispecialize"):
        produce_kind = "Specialize"
    for klass, cd in (("spatial", sd.spatial), ("intuitionistic", sd.intuit)):
        for name in cd.produced:
            if name in produced_intuit:
                continue
            events.append(
                Event(
                    step=sd.step,
                    kind=produce_kind,  # type: ignore[arg-type]
                    tactic=tac,
                    goal_id=sd.goal_id,
                    hyp=name,
                    sources=list(sources),
                    klass=klass,
                )
            )

    if sd.mask_change:
        before, after = sd.mask_change
        events.append(
            Event(
                step=sd.step,
                kind="MaskChange",
                tactic=tac,
                goal_id=sd.goal_id,
                detail=f"{before or '⊤'} → {after or '⊤'}",
            )
        )
    if sd.later_change:
        events.append(
            Event(
                step=sd.step,
                kind="LaterIntro",
                tactic=tac,
                goal_id=sd.goal_id,
                detail=f"later depth {sd.later_change:+d}",
            )
        )
    if low.startswith(("imodintro", "imod ", "imod")) and not sd.mask_change:
        events.append(Event(step=sd.step, kind="ModIntro", tactic=tac, goal_id=sd.goal_id))
    return events


def _persisted(sd: StepDiff, parent: IrisGoal, child: IrisGoal) -> dict[str, str]:
    """new intuitionistic name -> old spatial name, for spatial→intuitionistic moves."""
    out: dict[str, str] = {}
    gone = {n: parent.by_id(n) for n in sd.spatial.consumed}
    for new_name in sd.intuit.produced:
        nh = child.by_id(new_name)
        if nh is None:
            continue
        for old_name, oh in gone.items():
            if oh is not None and oh.hash == nh.hash and old_name not in out.values():
                out[new_name] = old_name
                break
    return out


def _consume_detail(tactic: str, sd: StepDiff) -> str:
    if sd.goal_closed:
        return "spent closing the goal"
    if sd.spatial.produced:
        return ""
    if sd.goal_changed:
        return "used against the goal"
    return ""
