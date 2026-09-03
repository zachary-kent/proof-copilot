"""The queries the ledger exists to answer (PLAN.md 4.2).

The flagship claim: *"H is not available at step 47"* should be answered with a
provenance chain, not with a 200-line goal dump the model has to re-derive the answer
from.  Bookkeeping over 200 steps is what a machine does well and an LLM does badly.

Every answer here carries its confidence.  When the matcher hit an ambiguity the
chain says so rather than presenting a guess as a fact (PLAN.md 4.4).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Literal

from pcp.core.ipm.model import Hyp, IrisGoal
from pcp.core.ledger.events import Event, EventLog
from pcp.core.trace import Trace

Fate = Literal["live", "consumed", "renamed", "split", "persisted", "never-seen", "unknown"]

#: How to repair a "hypothesis is gone" failure, given how it went away.
RepairClass = Literal["split-differently", "frame-later", "duplicate-it-is-persistent", "restate", "unknown"]


@dataclass
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
    """Where a hypothesis came from and where it went, forwards and backwards."""

    hyp: str
    fate: Fate
    backward: list[ProvenanceLink] = field(default_factory=list)
    forward: list[ProvenanceLink] = field(default_factory=list)
    aliases: list[str] = field(default_factory=list)
    live_as: str | None = None
    note: str = ""

    def render(self) -> str:
        lines = [f'"{self.hyp}": {self.fate}' + (f" (now `{self.live_as}`)" if self.live_as else "")]
        if self.aliases:
            lines.append("  known also as: " + ", ".join(f'"{a}"' for a in self.aliases))
        for link in self.backward:
            lines.append("  ← " + link.render())
        for link in self.forward:
            lines.append("  → " + link.render())
        if self.note:
            lines.append("  note: " + self.note)
        return "\n".join(lines)


class LedgerQuery:
    """Read-only queries over one trace's event log."""

    def __init__(self, trace: Trace) -> None:
        self.trace = trace
        self.log: EventLog = trace.events

    # -- helpers -----------------------------------------------------------
    def _final_goal(self, step: int | None = None) -> IrisGoal | None:
        s = self.trace.step_at(step) if step is not None else self.trace.final
        if s is None or not s.goals:
            return None
        return s.goals[0]

    def _aliases(self, hyp: str) -> list[str]:
        """Follow rename chains in both directions."""
        names = {hyp}
        changed = True
        while changed:
            changed = False
            for e in self.log:
                if e.kind != "Rename":
                    continue
                if e.hyp in names and e.sources and e.sources[0] not in names:
                    names.add(e.sources[0])
                    changed = True
                if e.sources and e.sources[0] in names and e.hyp and e.hyp not in names:
                    names.add(e.hyp)
                    changed = True
        return sorted(names - {hyp})

    # -- public queries ----------------------------------------------------
    def where_did_it_go(self, hyp: str) -> Provenance:
        """The full provenance chain for a hypothesis (PLAN.md 4.2)."""
        aliases = self._aliases(hyp)
        family = {hyp, *aliases}
        events = [e for e in self.log if (e.hyp in family) or (set(e.sources) & family)]
        prov = Provenance(hyp=hyp, fate="never-seen", aliases=aliases)
        if not events:
            prov.note = "no ledger event mentions this name in this trace"
            return prov

        for e in events:
            link = ProvenanceLink(e.step, e.tactic, e.kind, e.detail, e.confidence)
            if e.hyp in family and e.kind in ("Intro", "Produce", "Split", "Rename", "Specialize", "Persist"):
                prov.backward.append(link)
            else:
                prov.forward.append(link)

        goal = self._final_goal()
        live_names = {h.id for h in goal.ipm_hyps} if goal else set()
        alive = family & live_names
        if alive:
            prov.fate = "live"
            prov.live_as = sorted(alive)[0]
        elif any(e.confidence == "unknown" for e in events):
            prov.fate = "unknown"
            prov.note = "the matcher could not attribute one of the steps; treat this chain as a lead, not a fact"
        else:
            last = events[-1]
            prov.fate = {
                "Consume": "consumed",
                "Frame": "consumed",
                "Rename": "renamed",
                "Split": "split",
                "Persist": "persisted",
            }.get(last.kind, "consumed")
        return prov

    def first_use(self, hyp: str) -> Event | None:
        for e in self.log:
            if e.hyp == hyp or hyp in e.sources:
                return e
        return None

    def last_use(self, hyp: str) -> Event | None:
        found = None
        for e in self.log:
            if e.hyp == hyp or hyp in e.sources:
                found = e
        return found

    def leftovers(self, step: int | None = None) -> list[Hyp]:
        """Spatial hypotheses still live.

        Surfaces failure mode #2 -- ``iFrame`` / ``done`` failing because the spatial
        context is not empty -- *before* the agent hits the opaque error.
        """
        goal = self._final_goal(step)
        return list(goal.spatial) if goal else []

    def unused_at_qed(self) -> list[str]:
        """Resources that were never consumed anywhere.

        Usually a sign the *statement* is over-strong, which is orchestration-relevant
        signal: it is the ledger-level twin of the gate's unused-premise report, and
        an early warning of a `weaken` fight later (PLAN.md 8.7).
        """
        introduced: dict[str, int] = {}
        used: set[str] = set()
        for e in self.log:
            if e.kind in ("Intro", "Produce", "Split") and e.hyp:
                introduced.setdefault(e.hyp, e.step)
            if e.kind in ("Consume", "Frame", "Specialize", "Split", "Rename", "Persist"):
                used.update(e.sources)
                if e.kind in ("Consume", "Frame") and e.hyp:
                    used.add(e.hyp)
        live = {h.id for h in self.leftovers()}
        return sorted(n for n in introduced if n not in used and n not in live)

    def blame(self, failing_step: int, needed_hyp: str) -> "Blame":
        """Why is ``needed_hyp`` not available at ``failing_step``?"""
        prov = self.where_did_it_go(needed_hyp)
        culprit = None
        for e in self.log:
            if e.step >= failing_step:
                break
            if e.kind in ("Consume", "Frame") and (e.hyp == needed_hyp or needed_hyp in e.sources):
                culprit = e
            if e.kind == "Split" and needed_hyp in e.sources:
                culprit = e
        repair: RepairClass = "unknown"
        advice = ""
        if prov.fate == "live":
            repair = "restate"
            advice = (
                f'"{needed_hyp}" is still live'
                + (f' as "{prov.live_as}"' if prov.live_as and prov.live_as != needed_hyp else "")
                + " -- the failure is not a missing resource."
            )
        elif culprit is not None:
            if culprit.kind == "Split" or (culprit.targets and len(culprit.targets) > 1):
                repair = "split-differently"
                advice = (
                    f"step {culprit.step} split it into "
                    + ", ".join(f'"{t}"' for t in culprit.targets)
                    + " -- destructure differently, or re-assemble the pieces."
                )
            elif culprit.kind == "Frame":
                repair = "frame-later"
                advice = f"step {culprit.step} framed it into the goal -- frame later, or split the goal first."
            else:
                persistent = self._is_persistent(needed_hyp)
                if persistent:
                    repair = "duplicate-it-is-persistent"
                    advice = f'"{needed_hyp}" is Persistent -- duplicate it before use instead of consuming it.'
                else:
                    repair = "split-differently"
                    advice = f"step {culprit.step} consumed it with `{culprit.tactic}`."
        return Blame(hyp=needed_hyp, failing_step=failing_step, culprit=culprit, provenance=prov,
                     repair=repair, advice=advice)

    def _is_persistent(self, hyp: str) -> bool:
        goal = self._final_goal()
        if goal is None:
            return False
        h = goal.by_id(hyp)
        return bool(h and h.persistent)


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
                f'  "{self.hyp}" was {self.culprit.kind.lower()}d at step {self.culprit.step} '
                f"by `{self.culprit.tactic}`"
            )
        lines.append(f"  repair class: {self.repair}")
        if self.advice:
            lines.append(f"  {self.advice}")
        lines.append("")
        lines.append(self.provenance.render())
        return "\n".join(lines)
