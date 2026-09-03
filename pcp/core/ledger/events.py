"""The ledger event vocabulary (PLAN.md 4.1).

One record per hypothesis-level thing a tactic did.  The event log is the durable
artifact: ``where_did_it_go`` and ``blame`` are queries over it, and a worker's
compacted history keeps it when the goal renders are dropped.
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
    "Unknown",
]

#: Confidence is part of the record, not an afterthought.  A confidently wrong
#: provenance chain is worse than no chain (PLAN.md 4.4).
Confidence = Literal["certain", "unknown"]


@dataclass
class Event:
    step: int
    kind: EventKind
    tactic: str
    goal_id: str = "g0"
    #: The hypothesis this event is *about*, when there is a single subject.
    hyp: str | None = None
    #: Provenance: what this event consumed / where the subject came from.
    sources: list[str] = field(default_factory=list)
    #: What this event produced.
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
            "sources": self.sources,
            "targets": self.targets,
            "detail": self.detail,
            "confidence": self.confidence,
            "klass": self.klass,
        }

    @classmethod
    def from_json(cls, d: dict[str, Any]) -> "Event":
        return cls(
            step=d["step"],
            kind=d["kind"],
            tactic=d.get("tactic", ""),
            goal_id=d.get("goal_id", "g0"),
            hyp=d.get("hyp"),
            sources=d.get("sources", []),
            targets=d.get("targets", []),
            detail=d.get("detail", ""),
            confidence=d.get("confidence", "certain"),
            klass=d.get("klass", "spatial"),
        )

    def render(self) -> str:
        bits = [f"step {self.step}", self.kind]
        if self.hyp:
            bits.append(f'"{self.hyp}"')
        if self.sources:
            bits.append("from " + ", ".join(f'"{s}"' for s in self.sources))
        if self.targets:
            bits.append("→ " + ", ".join(f'"{t}"' for t in self.targets))
        line = " · ".join(bits)
        if self.detail:
            line += f" ({self.detail})"
        if self.confidence == "unknown":
            line += "  [UNKNOWN -- the matcher could not attribute this reliably]"
        return line


class EventLog:
    """Append-only log with the indexes the queries need."""

    def __init__(self) -> None:
        self.events: list[Event] = []

    def add(self, event: Event) -> Event:
        self.events.append(event)
        return event

    def extend(self, events: list[Event]) -> None:
        self.events.extend(events)

    def __len__(self) -> int:
        return len(self.events)

    def __iter__(self):
        return iter(self.events)

    def for_hyp(self, hyp: str) -> list[Event]:
        return [e for e in self.events if e.hyp == hyp or hyp in e.sources or hyp in e.targets]

    def at_step(self, step: int) -> list[Event]:
        return [e for e in self.events if e.step == step]

    def to_json(self) -> list[dict[str, Any]]:
        return [e.to_json() for e in self.events]

    @classmethod
    def from_json(cls, data: list[dict[str, Any]]) -> "EventLog":
        log = cls()
        log.events = [Event.from_json(d) for d in data]
        return log
