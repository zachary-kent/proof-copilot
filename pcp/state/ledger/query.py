"""The queries the ledger exists to answer (PLAN.md 4.2).

*"H is not available at step 47"* is answered with a provenance chain and a repair
class, not a 200-line goal dump.  Every answer carries its confidence: when the matcher
hit an ambiguity the chain says so (PLAN.md 4.4).

The queries are functions over anything with ``.steps`` and ``.events`` (a ``Trace``,
or a stand-in in tests) so the ledger stays importable without petanque.  Liveness is
checked in **every** goal of a step, not ``goals[0]`` (legacy bug: a hypothesis live in a
sibling goal was reported consumed), and an unrecognised last event yields ``unknown``,
never ``consumed``.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from dataclasses import dataclass, field
from typing import Literal, Protocol

from pcp.state.ipm.model import Hyp, IrisGoal, Step
from pcp.state.ledger.events import CONSUME_KINDS, PRODUCE_KINDS, Event, past_tense

Fate = Literal["live", "consumed", "framed", "persisted", "renamed", "split", "never-seen", "unknown"]
RepairClass = Literal["split-differently", "frame-later", "duplicate-it-is-persistent", "restate", "unknown"]
_CULPRIT_KINDS = frozenset({"Consume", "Frame", "Split", "Persist"})


class TraceLike(Protocol):
    steps: Sequence[Step]
    events: Iterable[Event]


# ----------------------------------------------------------------------- shapes


@dataclass(frozen=True)
class ProvenanceLink:
    step: int
    tactic: str
    kind: str
    detail: str = ""
    confidence: str = "certain"

    def render(self) -> str:
        line = f"step {self.step}: {self.kind} by `{self.tactic}`"
        if self.detail:
            line += f" -- {self.detail}"
        if self.confidence != "certain":
            line += "  [uncertain]"
        return line


@dataclass
class Provenance:
    hyp: str
    fate: Fate
    backward: list[ProvenanceLink] = field(default_factory=list)
    forward: list[ProvenanceLink] = field(default_factory=list)
    aliases: list[str] = field(default_factory=list)
    live_as: str | None = None
    live_in: str | None = None
    note: str = ""

    def render(self) -> str:
        head = f'"{self.hyp}": {self.fate}'
        if self.live_as and self.live_as != self.hyp:
            head += f" (now `{self.live_as}`)"
        if self.live_in:
            head += f" in {self.live_in}"
        lines = [head]
        if self.aliases:
            lines.append("  known also as: " + ", ".join(f'"{a}"' for a in self.aliases))
        lines += ["  ← " + link.render() for link in self.backward]
        lines += ["  → " + link.render() for link in self.forward]
        if self.note:
            lines.append("  note: " + self.note)
        return "\n".join(lines)


@dataclass
class Blame:
    hyp: str
    failing_step: int
    culprit: Event | None
    provenance: Provenance
    repair: RepairClass
    advice: str

    def render(self) -> str:
        lines = [f'why is "{self.hyp}" not available at step {self.failing_step}?']
        if self.culprit is not None:
            lines.append(
                f'  "{self.hyp}" was {past_tense(self.culprit.kind)} at step {self.culprit.step} by `{self.culprit.tactic}`'
            )
        lines.append(f"  repair class: {self.repair}")
        if self.advice:
            lines.append(f"  {self.advice}")
        lines.append("")
        lines.append(self.provenance.render())
        return "\n".join(lines)


# ---------------------------------------------------------------------- helpers


def _events(trace: TraceLike) -> list[Event]:
    events = list(trace.events)
    if not events and len(list(trace.steps)) > 1:
        # A trace recorded without its ledger: events are derived from the steps.
        from pcp.state.ledger.diff import replay_events

        events = replay_events(list(trace.steps))
    return events


def step_at(trace: TraceLike, n: int) -> Step | None:
    for s in trace.steps:
        if s.step == n:
            return s
    return None


def final_step(trace: TraceLike) -> Step | None:
    steps = list(trace.steps)
    return steps[-1] if steps else None


def goals_at(trace: TraceLike, step: int | None = None) -> list[IrisGoal]:
    s = final_step(trace) if step is None else step_at(trace, step)
    return list(s.goals) if s is not None else []


def goals_before(trace: TraceLike, n: int) -> list[IrisGoal]:
    """The state a step-``n`` tactic ran from.

    A failed step records the goals *before* the failing tactic; otherwise it is the
    previous step's result.
    """
    s = step_at(trace, n)
    if s is not None and not s.ok:
        return list(s.goals)
    prev = step_at(trace, n - 1)
    if prev is not None:
        return list(prev.goals)
    return goals_at(trace)


def find_live(goals: Iterable[IrisGoal], names: set[str]) -> tuple[str, Hyp] | None:
    """``(goal_id, hyp)`` for the first goal (any goal) holding one of ``names``."""
    for g in goals:
        for h in g.ipm_hyps:
            if h.id in names or names & set(h.names):
                return g.goal_id, h
    return None


def aliases(events: Iterable[Event], hyp: str) -> set[str]:
    """The rename closure of a name, in both directions."""
    names = {hyp}
    renames = [(e.sources[0], e.hyp) for e in events if e.kind == "Rename" and e.sources and e.hyp]
    changed = True
    while changed:
        changed = False
        for old, new in renames:
            if old in names and new not in names:
                names.add(new)
                changed = True
            if new in names and old not in names:
                names.add(old)
                changed = True
    return names


def _last_intuitionistic_home(trace: TraceLike, family: set[str], upto: int | None) -> tuple[int, str] | None:
    """The last step/goal where the family sat in an intuitionistic context."""
    for s in reversed(list(trace.steps)):
        if upto is not None and s.step >= upto:
            continue
        for g in s.goals:
            for h in g.intuitionistic:
                if h.id in family:
                    return s.step, g.goal_id
        if any(h.id in family for g in s.goals for h in g.spatial):
            return None
    return None


# ---------------------------------------------------------------------- queries


def where_did_it_go(trace: TraceLike, hyp: str, *, at_step: int | None = None) -> Provenance:
    """The full provenance chain of a hypothesis, backwards and forwards (PLAN.md 4.2).

    ``at_step`` restricts the question to the state a step ran from (used by ``blame``).
    """
    events = [e for e in _events(trace) if at_step is None or e.step < at_step]
    family = aliases(events, hyp)
    mine = [e for e in events if e.hyp in family or family & set(e.sources)]
    prov = Provenance(hyp=hyp, fate="never-seen", aliases=sorted(family - {hyp}))
    for e in mine:
        link = ProvenanceLink(e.step, e.tactic, e.kind, e.detail, e.confidence)
        if e.hyp in family and e.kind in PRODUCE_KINDS:
            prov.backward.append(link)
        else:
            prov.forward.append(link)

    goals = goals_at(trace) if at_step is None else goals_before(trace, at_step)
    live = find_live(goals, family)
    if live is not None:
        prov.fate = "live"
        prov.live_in, prov.live_as = live[0], live[1].id
        return prov
    last = mine[-1] if mine else None
    home = None if last is not None and _lost(last, family) else _last_intuitionistic_home(trace, family, at_step)
    if home is not None:
        # Persistent resources are never consumed: it sat in the intuitionistic context
        # until its goal closed or moved on.
        prov.fate = "live"
        prov.live_in = home[1]
        prov.note = (
            f"last seen in the intuitionistic context of {home[1]} at step {home[0]}; persistent "
            "resources are never consumed, so it was not spent"
        )
        return prov
    if last is None:
        seen = _last_seen(trace, family, at_step)
        if seen is not None:
            prov.fate = "unknown"
            prov.note = f"live in {seen[1]} at step {seen[0]} and gone later, with no ledger event recording why"
        else:
            prov.note = "no ledger event mentions this name in this trace"
        return prov
    if any(e.confidence == "unknown" for e in mine):
        prov.fate = "unknown"
        prov.note = "the matcher could not attribute one of the steps; treat this chain as a lead, not a fact"
        return prov
    _fate_from_last(prov, last, family)
    return prov


def _lost(e: Event, family: set[str]) -> bool:
    """A consume-side event that really took the family away (a persistent frame does not)."""
    if not (e.hyp in family or family & set(e.sources)):
        return False
    return e.kind == "Consume" or (e.kind == "Frame" and e.klass != "intuitionistic")


def _last_seen(trace: TraceLike, family: set[str], upto: int | None) -> tuple[int, str] | None:
    for s in reversed(list(trace.steps)):
        if upto is not None and s.step >= upto:
            continue
        hit = find_live(s.goals, family)
        if hit is not None:
            return s.step, hit[0]
    return None


def _fate_from_last(prov: Provenance, last: Event, family: set[str]) -> None:
    as_source = bool(family & set(last.sources)) and last.hyp not in family
    if last.kind == "Consume":
        prov.fate = "consumed"
        if last.klass == "intuitionistic":
            prov.note = "it was cleared from the intuitionistic context; being persistent it can be re-introduced"
    elif last.kind == "Frame":
        prov.fate = "framed"
    elif last.kind == "Rename" and as_source:
        prov.fate, prov.live_as = "renamed", last.hyp
    elif last.kind == "Split" and as_source:
        prov.fate = "split"
    elif last.kind == "Persist" and as_source:
        prov.fate, prov.live_as = "persisted", last.hyp
    else:
        prov.fate = "unknown"
        prov.note = (
            f"the last event was {last.kind} at step {last.step} and the name is not live afterwards; "
            "the ledger lost track of it (an exotic tactic, or a goal that closed without a record)"
        )


def first_use(trace: TraceLike, hyp: str) -> Event | None:
    return next((e for e in _events(trace) if e.mentions(hyp)), None)


def last_use(trace: TraceLike, hyp: str) -> Event | None:
    found = None
    for e in _events(trace):
        if e.mentions(hyp):
            found = e
    return found


def leftovers(trace: TraceLike, step: int | None = None) -> list[Hyp]:
    """Spatial hypotheses still live in the focused goal (failure mode #2, before ``done``)."""
    goals = goals_at(trace, step)
    return list(goals[0].spatial) if goals else []


def unused_at_qed(trace: TraceLike) -> list[str]:
    """Resources introduced and never consumed anywhere -- usually an over-strong statement."""
    introduced: dict[str, int] = {}
    used: set[str] = set()
    for e in _events(trace):
        if e.kind in ("Intro", "Produce", "Split", "Specialize") and e.hyp:
            introduced.setdefault(e.hyp, e.step)
        if e.kind in ("Consume", "Frame", "Specialize", "Split", "Rename", "Persist"):
            used.update(e.sources)
            if e.kind in CONSUME_KINDS and e.hyp:
                used.add(e.hyp)
    live = {h.id for g in goals_at(trace) for h in g.ipm_hyps}
    return sorted(n for n in introduced if n not in used and n not in live)


def blame(trace: TraceLike, failing_step: int, needed_hyp: str) -> Blame:
    """Why is ``needed_hyp`` not available at ``failing_step``, and how to repair it?"""
    prov = where_did_it_go(trace, needed_hyp, at_step=failing_step)
    family = {needed_hyp, *prov.aliases}
    culprit: Event | None = None
    for e in _events(trace):
        if e.step >= failing_step:
            break
        if e.kind not in _CULPRIT_KINDS:
            continue
        if e.kind in ("Split", "Persist"):
            if family & set(e.sources) and e.hyp not in family:
                culprit = e
        elif e.hyp in family or family & set(e.sources):
            culprit = e
    repair: RepairClass = "unknown"
    advice = ""
    if prov.fate == "live":
        repair = "restate"
        where = f' as "{prov.live_as}"' if prov.live_as and prov.live_as != needed_hyp else ""
        where += f" in {prov.live_in}" if prov.live_in else ""
        advice = f'"{needed_hyp}" is still live{where} -- the failure is not a missing resource.'
    elif culprit is None:
        advice = f'no ledger event consumed "{needed_hyp}" before step {failing_step}' + (
            f"; {prov.note}" if prov.note else ""
        )
    elif culprit.kind == "Split" or (culprit.kind == "Consume" and len(culprit.targets) > 1):
        repair = "split-differently"
        advice = (
            f"step {culprit.step} split it into " + ", ".join(f'"{t}"' for t in culprit.targets)
            + " -- destructure differently, or re-assemble the pieces."
        )
    elif culprit.kind == "Frame":
        repair = "frame-later"
        advice = f"step {culprit.step} framed it into the goal -- frame later, or split the goal first."
    elif culprit.kind == "Persist" or was_persistent(trace, needed_hyp, culprit):
        repair = "duplicate-it-is-persistent"
        advice = (
            f'"{needed_hyp}" is Persistent -- keep a copy (`iDestruct "{needed_hyp}" as "#{needed_hyp}"`, '
            "or introduce it with `#`) instead of consuming it."
        )
    else:
        repair = "split-differently"
        advice = f"step {culprit.step} consumed it with `{culprit.tactic}` -- keep a fraction or split it before that step."
    return Blame(needed_hyp, failing_step, culprit, prov, repair, advice)


def was_persistent(trace: TraceLike, name: str, culprit: Event) -> bool:
    """Persistence read at the step the hypothesis existed, not in the final goal.

    A blamed hypothesis is, by construction, gone from the final goal, which is why
    the legacy ``duplicate-it-is-persistent`` was unreachable.
    """
    if culprit.klass == "intuitionistic":
        return True
    for g in goals_before(trace, culprit.step):
        h = g.by_id(name)
        if h is not None:
            return h.klass == "intuitionistic" or bool(h.persistent) or h.prop.lstrip().startswith(("□", "<pers>"))
    return False


# -------------------------------------------------------------------- rendering


def render_provenance(prov: Provenance) -> str:
    return prov.render()


def render_blame(b: Blame) -> str:
    return b.render()


def render_leftovers(hyps: Sequence[Hyp]) -> str:
    if not hyps:
        return "the spatial context is empty"
    return "\n".join(f'  "{h.id}" : {" ".join(h.prop.split())}' for h in hyps)


def render_unused(names: Sequence[str]) -> str:
    return ", ".join(f'"{n}"' for n in names) if names else "every resource was consumed"


def render_events(events: Iterable[Event]) -> str:
    return "\n".join(e.render() for e in events)
