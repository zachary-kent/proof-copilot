"""Tactic-by-tactic capture and the trace artifact (PLAN.md 3.2, 6, 13).

A trace is ``(root state, tactic list)``; everything else -- goals, hashes, ledger
events -- is derived, so re-running a trace after a tool change is free for the
unchanged prefix.  The JSONL layout (schema ``v = 1``) is the external contract
(``contract.md`` 5.5): a header line, one ``step`` line per tactic (step 0 is
``<start>``; a failed step has ``state_id -1`` and the goals *before* the tactic), then
the ledger's ``event`` lines.  ``rec`` is the discriminator (an event already has a
``kind`` of its own).

Goals are acquired through the reflected dump when a :class:`Reflector` is given and
answers, and through the printer parser otherwise (PLAN.md 3.1).  The ledger is another
module: it appends to ``Trace.events`` (anything with ``to_json``) through the
``on_step`` hook or after the fact.
"""

from __future__ import annotations

import json
import time
from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any

from pcp.state.ipm.model import SCHEMA_VERSION, IrisGoal, Step
from pcp.state.ipm.parse import goals_from_petanque
from pcp.state.petanque import StateHandle
from pcp.state.session import ProofSession, StepResult
from pcp.util.io import atomic_write_text, read_text

if TYPE_CHECKING:
    from pcp.state.ipm.reflect import Reflector

START_TACTIC = "<start>"


def new_store() -> Any:
    """A ``PropStore`` (``pcp.state.digest``), imported lazily -- it is a sibling module."""
    from pcp.state.digest import PropStore

    return PropStore()


def _event_from_json(d: dict[str, Any]) -> Any:
    try:
        from pcp.state.ledger.events import Event
    except ImportError:  # the ledger is optional at read time; keep the record as data
        return {k: v for k, v in d.items() if k != "rec"}
    return Event.from_json(d)


@dataclass
class Trace:
    """One proof attempt: steps, ledger events and the prop store behind them."""

    file: str
    thm: str
    tactics: list[str] = field(default_factory=list)
    steps: list[Step] = field(default_factory=list)
    events: list[Any] = field(default_factory=list)
    store: Any = None
    finished: bool = False
    error: str | None = None
    failed_at: int | None = None
    #: The file petanque actually opened, when it was the statements-only twin.
    petanque_file: str | None = None
    started_at: float = field(default_factory=time.time)

    def __post_init__(self) -> None:
        if self.store is None:
            self.store = new_store()

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

    def events_at(self, step: int) -> list[Any]:
        return [e for e in self.events if _event_step(e) == step]

    # -- serialization -----------------------------------------------------
    def header(self) -> dict[str, Any]:
        d: dict[str, Any] = {
            "v": SCHEMA_VERSION,
            "rec": "header",
            "file": self.file,
            "thm": self.thm,
            "finished": self.finished,
            "error": self.error,
            "failed_at": self.failed_at,
            "props": self.store.to_json(),
        }
        if self.petanque_file and self.petanque_file != self.file:
            d["petanque_file"] = self.petanque_file
        return d

    def dumps(self) -> str:
        lines = [json.dumps(self.header(), ensure_ascii=False)]
        lines += [json.dumps({"rec": "step", **s.to_json()}, ensure_ascii=False) for s in self.steps]
        lines += [json.dumps({"rec": "event", **_event_json(e)}, ensure_ascii=False) for e in self.events]
        return "\n".join(lines) + "\n"

    def to_jsonl(self, path: str | Path) -> Path:
        return atomic_write_text(path, self.dumps())

    @classmethod
    def loads(cls, text: str) -> Trace:
        trace: Trace | None = None
        for line in text.splitlines():
            if not line.strip():
                continue
            d = json.loads(line)
            rec = d.get("rec") or _infer_rec(d)
            if rec == "header":
                store = new_store()
                store.update(d.get("props") or {})
                trace = cls(
                    file=d["file"],
                    thm=d.get("thm", ""),
                    finished=bool(d.get("finished", False)),
                    error=d.get("error"),
                    failed_at=d.get("failed_at"),
                    petanque_file=d.get("petanque_file"),
                    store=store,
                )
                continue
            if trace is None:
                raise ValueError("trace JSONL does not start with a header line")
            if rec == "event":
                trace.events.append(_event_from_json(d))
            else:
                step = Step.from_json(d)
                trace.steps.append(step)
                trace.tactics.append(step.tactic)
        if trace is None:
            raise ValueError("no trace header")
        return trace

    @classmethod
    def from_jsonl(cls, path: str | Path) -> Trace:
        return cls.loads(read_text(path))


def _infer_rec(d: dict[str, Any]) -> str:
    """The record kind of a line written before ``rec`` existed.

    A step always carries ``state_id``/``goals``; an event always carries ``kind`` and
    never those -- so an old event line lacking ``confidence`` is still an event, not
    a ``Step`` read that dies on ``KeyError('state_id')`` (legacy bug).
    """
    if "props" in d:
        return "header"
    if "state_id" in d or "goals" in d:
        return "step"
    if "kind" in d:
        return "event"
    return "step"


def _event_json(e: Any) -> dict[str, Any]:
    return e.to_json() if hasattr(e, "to_json") else dict(e)


def _event_step(e: Any) -> int | None:
    if isinstance(e, dict):
        return e.get("step")
    return getattr(e, "step", None)


class Tracer:
    """Drives a :class:`ProofSession` and accumulates a :class:`Trace`.

    ``reflector`` (when given) is the primary goal source; ``on_step(step, prev_goals)``
    is where the ledger attaches its diff.
    """

    def __init__(
        self,
        session: ProofSession,
        *,
        reflector: Reflector | None = None,
        store: Any = None,
        on_step: Callable[[Step, list[IrisGoal]], None] | None = None,
    ) -> None:
        self.session = session
        self.reflector = reflector
        self.on_step = on_step
        self.trace = Trace(
            file=session.source_file,
            thm=session.thm,
            store=store,
            petanque_file=session.file if session.file != session.source_file else None,
        )
        self._prev_goals: list[IrisGoal] = []
        self._n = 0

    @property
    def prev_goals(self) -> list[IrisGoal]:
        return self._prev_goals

    def step_number(self, history_index: int | None) -> int | None:
        """The trace step at which the session's ``history_index``-th committed state was recorded.

        ``ProofSession.loop_of`` counts committed states only, while trace steps also
        number failed tactics; after any failure the two diverge, and the model reads
        trace steps.  Not a defect in the session: the trace is where the numbering lives.
        """
        if history_index is None:
            return None
        ok_steps = [s.step for s in self.trace.steps if s.ok]
        return ok_steps[history_index] if 0 <= history_index < len(ok_steps) else history_index

    def goals_at(self, state: StateHandle) -> list[IrisGoal]:
        """Goals at ``state``: reflected for the focused goal when possible, printer-parsed otherwise."""
        printed = goals_from_petanque(self.session.goals(state))
        if self.reflector is not None:
            return self.reflector.goals(state=state, printed=printed)
        return printed

    def start(self) -> list[IrisGoal]:
        """Step 0.  Idempotent: a second call returns the recorded root goals."""
        if self.trace.steps:
            return self.trace.steps[0].goals
        state = self.session.start()
        goals = self.goals_at(state)
        self._intern(goals)
        self.trace.steps.append(
            Step(step=0, state_id=state.st, tactic=START_TACTIC, goals=goals, state_hash=state.state_hash,
                 messages=list(state.messages))
        )
        self._prev_goals = goals
        return goals

    def step(self, tactic: str, *, timeout: float | None = None) -> Step:
        """Run one tactic and record it; a failure records the pre-failure goals and stays put."""
        if not self.trace.steps:
            self.start()
        self._n += 1
        result: StepResult = self.session.run(tactic, timeout=timeout)
        self.trace.tactics.append(tactic)
        if not result.ok or result.state is None:
            step = Step(
                step=self._n, state_id=-1, tactic=tactic, goals=self._prev_goals, ok=False,
                error=result.error, elapsed_ms=result.elapsed_ms, messages=list(result.messages),
            )
            self.trace.steps.append(step)
            self.trace.error = result.error
            self.trace.failed_at = self._n
            return step
        goals = self.goals_at(result.state)
        self._intern(goals)
        step = Step(
            step=self._n,
            state_id=result.state.st,
            tactic=tactic,
            goals=goals,
            parent_goal=self._prev_goals[0].goal_id if self._prev_goals else None,
            state_hash=result.state_hash,
            elapsed_ms=result.elapsed_ms,
            messages=list(result.messages),
            loop_of=self.step_number(result.loop_of),
        )
        self.trace.steps.append(step)
        prev, self._prev_goals = self._prev_goals, goals
        # `error`/`failed_at` describe how the trace *currently* ends: a step that
        # succeeds after an earlier failure (the MCP model retries in place) clears
        # them; the failed step itself stays in `steps` with `ok=False`.
        self.trace.error = None
        self.trace.failed_at = None
        if result.proof_finished:
            self.trace.finished = True
        if self.on_step is not None:
            self.on_step(step, prev)
        return step

    def run_script(self, tactics: list[str], *, timeout: float | None = None) -> Trace:
        """Step until the first failure; returns the trace either way."""
        for tactic in tactics:
            if not self.step(tactic, timeout=timeout).ok:
                break
        return self.trace

    def _intern(self, goals: list[IrisGoal]) -> None:
        for g in goals:
            for h in g.all_hyps:
                self.trace.store.put(h.prop)
            if g.goal:
                self.trace.store.put(g.goal)
