"""Tactic-by-tactic capture and deterministic replay (PLAN.md 3.2, 6).

A trace is ``(root state, tactic list)``.  Everything else -- goals, hashes, ledger
events -- is derived and cacheable by hash, so re-running a trace after a tool change
is free for the unchanged prefix.  That is what makes the eval corpus (PLAN.md 13)
cheap to re-derive when the ledger's heuristics change.
"""

from __future__ import annotations

import json
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable

from pcp.core.digest import PropStore
from pcp.core.ipm.model import SCHEMA_VERSION, IrisGoal, Step
from pcp.core.ipm.parse import parse_goal
from pcp.core.ledger.diff import diff_step, to_events
from pcp.core.ledger.events import Event, EventLog
from pcp.core.session import ProofSession, StepResult


def goals_from_petanque(raw_goals: Iterable[Any]) -> list[IrisGoal]:
    """Turn petanque ``Goal`` records into :class:`IrisGoal`s.

    ``goal.ty`` carries the IPM render; ``goal.hyps`` carries the ordinary Coq
    context already structured, so it needs no parsing at all.
    """
    out: list[IrisGoal] = []
    for i, g in enumerate(raw_goals):
        pure = [(list(h.names), h.ty) for h in getattr(g, "hyps", [])]
        out.append(parse_goal(g.ty, goal_id=f"g{i}", pure_hyps=pure))
    return out


@dataclass
class Trace:
    """One proof attempt: the steps, the events, and the prop store behind them."""

    file: str
    thm: str
    tactics: list[str] = field(default_factory=list)
    steps: list[Step] = field(default_factory=list)
    events: EventLog = field(default_factory=EventLog)
    store: PropStore = field(default_factory=PropStore)
    finished: bool = False
    error: str | None = None
    failed_at: int | None = None
    started_at: float = field(default_factory=time.time)

    # -- accessors ---------------------------------------------------------
    @property
    def final(self) -> Step | None:
        return self.steps[-1] if self.steps else None

    def step_at(self, n: int) -> Step | None:
        for s in self.steps:
            if s.step == n:
                return s
        return None

    def live_spatial(self, step: int | None = None) -> list[str]:
        s = self.final if step is None else self.step_at(step)
        if s is None or not s.goals:
            return []
        return [h.id for h in s.goals[0].spatial]

    # -- serialization -----------------------------------------------------
    def to_jsonl(self) -> str:
        # `rec` is the record discriminator, deliberately not `kind`: an Event
        # already has a `kind` of its own, and spreading it over a marker silently
        # turns every event line into an unreadable step.
        header = {
            "v": SCHEMA_VERSION,
            "rec": "header",
            "file": self.file,
            "thm": self.thm,
            "finished": self.finished,
            "error": self.error,
            "failed_at": self.failed_at,
            "props": self.store.to_json(),
        }
        lines = [json.dumps(header, ensure_ascii=False)]
        lines += [json.dumps({"rec": "step", **s.to_json()}, ensure_ascii=False) for s in self.steps]
        lines += [json.dumps({"rec": "event", **e.to_json()}, ensure_ascii=False) for e in self.events]
        return "\n".join(lines) + "\n"

    def write(self, path: str | Path) -> Path:
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(self.to_jsonl(), encoding="utf-8")
        return p

    @classmethod
    def read(cls, path: str | Path) -> "Trace":
        trace: Trace | None = None
        for line in Path(path).read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            d = json.loads(line)
            rec = d.get("rec") or ("header" if "props" in d else "step")
            if rec == "header":
                trace = cls(
                    file=d["file"],
                    thm=d["thm"],
                    finished=d.get("finished", False),
                    error=d.get("error"),
                    failed_at=d.get("failed_at"),
                    store=PropStore.from_json(d.get("props", {})),
                )
            elif rec == "event":
                assert trace is not None
                trace.events.add(Event.from_json(d))
            else:
                assert trace is not None
                trace.steps.append(Step.from_json(d))
                trace.tactics.append(d["tactic"])
        if trace is None:
            raise ValueError(f"{path}: no trace header")
        return trace


class Tracer:
    """Drives a :class:`ProofSession` and accumulates a :class:`Trace`."""

    def __init__(self, session: ProofSession, *, store: PropStore | None = None) -> None:
        self.session = session
        self.trace = Trace(file=session.file, thm=session.thm, store=store or PropStore())
        self._prev_goals: list[IrisGoal] = []
        self._n = 0

    def start(self) -> list[IrisGoal]:
        state = self.session.start()
        goals = goals_from_petanque(self.session.goals(state))
        self._intern(goals)
        self.trace.steps.append(
            Step(step=0, state_id=state.st, tactic="<start>", goals=goals, state_hash=state.hash)
        )
        self._prev_goals = goals
        return goals

    def step(self, tactic: str, *, timeout: float | None = None) -> Step:
        """Run one tactic, record the state, and attribute the ledger events."""
        if not self.trace.steps:
            self.start()
        self._n += 1
        result: StepResult = self.session.run(tactic, timeout=timeout)
        self.trace.tactics.append(tactic)
        if not result.ok:
            step = Step(
                step=self._n,
                state_id=-1,
                tactic=tactic,
                goals=self._prev_goals,
                ok=False,
                error=result.error,
                elapsed_ms=result.elapsed_ms,
                messages=result.messages,
            )
            self.trace.steps.append(step)
            self.trace.error = result.error
            self.trace.failed_at = self._n
            return step

        goals = goals_from_petanque(self.session.goals(result.state))
        self._intern(goals)
        step = Step(
            step=self._n,
            state_id=result.state.st,
            tactic=tactic,
            goals=goals,
            state_hash=result.state_hash,
            elapsed_ms=result.elapsed_ms,
            messages=result.messages,
        )
        diffs, alignment = diff_step(self._n, tactic, self._prev_goals, goals)
        if alignment.parent is not None:
            step.parent_goal = alignment.parent.goal_id
            for sd, child in zip(diffs, alignment.children):
                self.trace.events.extend(to_events(sd, alignment.parent, child))
        self.trace.steps.append(step)
        self._prev_goals = goals
        if result.proof_finished:
            self.trace.finished = True
        return step

    def run_script(self, tactics: list[str], *, timeout: float | None = None) -> Trace:
        for tactic in tactics:
            step = self.step(tactic, timeout=timeout)
            if not step.ok:
                break
        return self.trace

    def _intern(self, goals: list[IrisGoal]) -> None:
        for g in goals:
            for h in g.pure + g.intuitionistic + g.spatial:
                self.trace.store.put(h.prop)
            if g.goal:
                self.trace.store.put(g.goal)
