"""The ledger event vocabulary (PLAN.md 4.1; trace JSONL record shape in contract 5.5).

One record per hypothesis-level thing a tactic did.  The event log is the durable
artifact: ``where_did_it_go`` and ``blame`` are queries over it, and a worker's
compacted history keeps it when the goal renders are dropped.

Field discipline, which the queries rely on: every *consume-side* event (``Consume``,
``Frame``) names what it consumed in ``sources`` and what that became in ``targets``;
every *produce-side* event (``Intro``, ``Produce``, ``Split``, ``Specialize``) has the
new name as ``hyp``, its provenance in ``sources`` and **all** names the step produced
from those sources in ``targets`` -- so ``blame`` can say "step 2 split it into H1, H2"
without hand-built events.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Literal

EventKind = Literal[
    "Intro",
    "Consume",
    "Produce",
    "Split",
    "Rename",
    "Update",
    "Instantiate",
    "Frame",
    "Persist",
    "Specialize",
    "ModIntro",
    "MaskChange",
    "LaterIntro",
    "GoalSplit",
    "GoalClosed",
    "Unknown",
]
KINDS: tuple[str, ...] = (
    "Intro", "Consume", "Produce", "Split", "Rename", "Update", "Instantiate", "Frame", "Persist",
    "Specialize", "ModIntro", "MaskChange", "LaterIntro", "GoalSplit", "GoalClosed", "Unknown",
)
#: Events whose ``hyp`` is a *new* name (they carry ``targets``).
PRODUCE_KINDS: frozenset[str] = frozenset({"Intro", "Produce", "Split", "Specialize", "Persist", "Rename"})
#: Events whose ``hyp`` is a name that *went away* (they carry ``sources``).
CONSUME_KINDS: frozenset[str] = frozenset({"Consume", "Frame"})

#: Confidence is part of the record, not an afterthought (PLAN.md 4.4).
Confidence = Literal["certain", "unknown"]

_PAST: dict[str, str] = {
    "Intro": "introduced", "Consume": "consumed", "Produce": "produced", "Split": "split",
    "Rename": "renamed", "Update": "updated", "Instantiate": "instantiated", "Frame": "framed",
    "Persist": "made persistent", "Specialize": "specialized", "ModIntro": "modality-introduced",
    "MaskChange": "mask-changed", "LaterIntro": "later-stripped", "GoalSplit": "goal-split",
    "GoalClosed": "goal-closed", "Unknown": "lost track of",
}


def past_tense(kind: str) -> str:
    """``Split`` -> ``split``, never ``splitd``."""
    return _PAST.get(kind, kind.lower())


@dataclass
class Event:
    step: int
    kind: EventKind
    tactic: str
    goal_id: str = "g0"
    #: The single subject of the event, when there is one.
    hyp: str | None = None
    #: What this event consumed / where its subject came from.
    sources: list[str] = field(default_factory=list)
    #: What this event (or the step it belongs to) produced.
    targets: list[str] = field(default_factory=list)
    detail: str = ""
    confidence: Confidence = "certain"
    klass: str = "spatial"

    def to_json(self) -> dict[str, Any]:
        return {
            "step": self.step,
            "kind": self.kind,
            "tactic": self.tactic,
            "goal_id": self.goal_id,
            "hyp": self.hyp,
            "sources": list(self.sources),
            "targets": list(self.targets),
            "detail": self.detail,
            "confidence": self.confidence,
            "klass": self.klass,
        }

    @classmethod
    def from_json(cls, d: dict[str, Any]) -> Event:
        return cls(
            step=int(d["step"]),
            kind=d["kind"],
            tactic=d.get("tactic", ""),
            goal_id=d.get("goal_id", "g0"),
            hyp=d.get("hyp"),
            sources=list(d.get("sources") or []),
            targets=list(d.get("targets") or []),
            detail=d.get("detail", ""),
            confidence=d.get("confidence", "certain"),
            klass=d.get("klass", "spatial"),
        )

    def mentions(self, name: str) -> bool:
        return self.hyp == name or name in self.sources

    def render(self) -> str:
        bits = [f"step {self.step}", self.kind]
        if self.hyp:
            bits.append(f'"{self.hyp}"')
        if self.sources and self.sources != [self.hyp]:
            bits.append("from " + ", ".join(f'"{s}"' for s in self.sources))
        if self.targets:
            bits.append("→ " + ", ".join(f'"{t}"' for t in self.targets))
        line = " · ".join(bits)
        if self.detail:
            line += f" ({self.detail})"
        if self.confidence == "unknown":
            line += "  [UNKNOWN -- the matcher could not attribute this reliably]"
        return line


class EventLog(list[Event]):
    """An append-only list of events with the few views the queries need.

    A plain ``list`` subclass so a trace can hold it as ``events: list``; every query is
    a linear scan, which is fine at proof scale (hundreds of steps).
    """

    def add(self, event: Event) -> Event:
        self.append(event)
        return event

    def at_step(self, step: int) -> list[Event]:
        return [e for e in self if e.step == step]

    def to_json(self) -> list[dict[str, Any]]:
        return [e.to_json() for e in self]

    @classmethod
    def from_json(cls, data: list[dict[str, Any]]) -> EventLog:
        return cls(Event.from_json(d) for d in data)

    def render(self) -> str:
        return "\n".join(e.render() for e in self)
