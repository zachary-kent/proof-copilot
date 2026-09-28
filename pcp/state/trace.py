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

Incremental replay (pcp-issues D5): a trace is (root, tactic list), so after an edit
only the sentences from the first changed one need to run again.  :class:`ReplayCache`
keeps, per (file, lemma, the statements before it), the states the last trace of that
lemma reached; :meth:`Tracer.resume` adopts the longest common prefix of sentences
instead of re-running it.  Petanque states are immutable, so reuse is sound as long as
the process and its generation are the same -- a restarted process has none of them,
and the replay falls back to a full run.
"""

from __future__ import annotations

import hashlib
import json
import threading
import time
from collections import OrderedDict
from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any

from pcp.errors import StateError
from pcp.rocq.assemble import stub_proof_bodies
from pcp.rocq.decls import find_block
from pcp.rocq.errors import DEFAULT_PREFIX_TIMEOUT, PrefixCheck, check_prefix, shape_error
from pcp.state.ipm.model import SCHEMA_VERSION, IrisGoal, Step
from pcp.state.ipm.parse import goals_from_petanque
from pcp.state.petanque import StartFailed, StateHandle
from pcp.state.printing import GoalHidden, reprint
from pcp.state.session import ProofSession, StepResult
from pcp.util.io import atomic_write_text, read_text

if TYPE_CHECKING:
    from pcp.state.ipm.reflect import Reflector

START_TACTIC = "<start>"
# Step numbering, shared by ``Trace.steps``, ``proof_state(step=...)``, ``failed_at``,
# ``pcp trace`` and every MCP result: step 0 is the root state (``<start>``); step ``k`` is the state
# after the script's ``k``-th sentence (1-based), and a failed step ``k`` is the
# ``k``-th sentence failing, recorded with the goals it was applied to.  So a script
# of ``n`` sentences that fails at its last one has ``n + 1`` step records and
# ``failed_at == n``.


@dataclass(frozen=True)
class SentenceAt:
    """A proof sentence's 1-based position in its source file."""

    line: int
    column: int


def proof_script(source: str, lemma: str) -> tuple[list[str], list[SentenceAt]] | None:
    """The lemma's own proof as sentences, each with its place in ``source``; ``None`` if it has none."""
    block = find_block(source, lemma)
    if block is None or not block.has_proof:
        return None
    sentences = [s for s in block.sentences if s.code.strip()]
    places = []
    for s in sentences:
        at = s.code_start
        places.append(SentenceAt(source.count("\n", 0, at) + 1, at - (source.rfind("\n", 0, at) + 1) + 1))
    return [s.code for s in sentences], places


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
    #: The step that failed (numbered as in the module's step-numbering note), and where its sentence sits in
    #: the source file when the script was the file's own proof (1-based).
    failed_at: int | None = None
    failed_line: int | None = None
    failed_column: int | None = None
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
        if self.failed_line is not None:
            d["failed_line"] = self.failed_line
            d["failed_column"] = self.failed_column
        if self.petanque_file and self.petanque_file != self.file:
            d["petanque_file"] = self.petanque_file
        return d

    def failure(self) -> dict[str, Any] | None:
        """How the trace currently ends, if it ends in a failure: step, sentence, place, error.

        ``step`` is the number ``proof_state`` shows for the failed step (its goals are
        the ones the sentence was applied to).
        """
        if self.failed_at is None:
            return None
        failed = self.step_at(self.failed_at)
        out: dict[str, Any] = {"step": self.failed_at, "sentence": failed.tactic if failed else None,
                               "error": self.error}
        if self.failed_line is not None:
            out["line"] = self.failed_line
            out["column"] = self.failed_column
        return out

    def failure_note(self) -> str | None:
        """``stopped at step N (file:L:C) `sentence`: error`` -- the CLI's one line."""
        f = self.failure()
        if f is None:
            return None
        where = f" ({Path(self.file).name}:{f['line']}:{f['column']})" if "line" in f else ""
        sentence = " ".join(str(f["sentence"] or "").split())
        return f"stopped at step {f['step']}{where} `{sentence}`: {f['error']}"

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
                    failed_line=d.get("failed_line"),
                    failed_column=d.get("failed_column"),
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
    a ``Step`` read that dies on ``KeyError('state_id')``.
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


class ExplainedStartFailure(StartFailed):
    """A :class:`StartFailed` with the prefix check behind its message (``check``), so a
    result can place the cause (file, line, sentence) instead of only saying it."""

    def __init__(self, message: str, *, check: PrefixCheck | None, **kw: Any) -> None:
        super().__init__(message, **kw)
        self.check = check


def explain_start_failure(
    exc: StartFailed, source: str | Path, *, root: str | Path | None = None, timeout: float = DEFAULT_PREFIX_TIMEOUT
) -> StartFailed:
    """``exc`` with the document's real cause in front, when coqc can name one.

    petanque names the lemma ("Theorem not found", "The reference X was not found")
    when the cause is usually earlier -- a ``Require`` of a stale or missing library, a
    statement that does not elaborate -- or it just runs out of time.  The statements
    up to the lemma are compiled with the project's ``coqc`` (bounded by ``timeout``)
    and the first error is reported in source coordinates; petanque's own message is
    kept after it.
    """
    budget = min(timeout, exc.budget_s) if exc.timed_out and exc.budget_s else timeout
    check = check_prefix(source, exc.thm, root=root, timeout=budget)
    if check is None:
        cause = f"{Path(source).name} declares no `{exc.thm}`"
    elif check.unavailable:
        cause = ""
    elif check.ok:
        cause = (
            f"coqc checks the statements up to {exc.thm} (proofs admitted) in {check.elapsed_s:.0f} s"
            + (", so the time goes into a proof body before it (open it with fast=True)" if exc.timed_out
               else ", so the failure is petanque's own (its load path or ROCQLIB? see `pcp doctor`)")
        )
    else:
        cause = check.render()
    if exc.timed_out:
        message = f"{exc}; {cause}" if cause else str(exc)
    else:
        # With the cause named, petanque's lemma-local symptom is kept short (its tail).
        message = f"{cause}\n  petanque said: {shape_error(exc.detail, 300)}" if cause else str(exc)
    return ExplainedStartFailure(message, check=check, thm=exc.thm, file=exc.file, detail=exc.detail,
                                 timed_out=exc.timed_out, budget_s=exc.budget_s)


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
        self._hidden: dict[int, list[GoalHidden] | None] = {}
        #: The session's answer to the last :meth:`step` (``timed_out``, the typeclass
        #: trace) -- what a ``Step`` record does not carry.
        self.last_result: StepResult | None = None
        #: Wall time of ``petanque/start`` (ms); 0 when the root was adopted by :meth:`resume`.
        self.start_ms = 0

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

    def hidden_at(self, step: Step) -> list[GoalHidden] | None:
        """What the printer hides in ``step``'s goals (``pcp.state.printing``), once per state.

        A failed step shows the goals its sentence was applied to, so it is reprinted
        at the last good state before it.  ``None`` when that state has left the
        session's table or the reprint was refused -- rendering then marks nothing.
        """
        target: Step | None = step
        if not step.ok or step.state_id < 0:
            target = next((s for s in reversed(self.trace.steps) if s.ok and s.step < step.step and s.state_id >= 0), None)
        if target is None:
            return None
        if target.state_id not in self._hidden:
            try:
                state = self.session.state(target.state_id)
            except StateError:
                return None
            # The reflected goals are not a printer's output: let reprint fetch the plain print.
            plain = list(target.goals) if self.reflector is None else None
            self._hidden[target.state_id] = reprint(self.session, state, plain)
        return self._hidden[target.state_id]

    def start(self) -> list[IrisGoal]:
        """Step 0.  Idempotent: a second call returns the recorded root goals."""
        if self.trace.steps:
            return self.trace.steps[0].goals
        started = time.perf_counter()
        try:
            state = self.session.start()
        except StartFailed as exc:
            proc = self.session.process
            root = proc.toolchain.project if proc is not None else None
            raise explain_start_failure(exc, self.session.source_file, root=root) from None
        self.start_ms = int((time.perf_counter() - started) * 1000)
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
        self.last_result = result
        self.trace.tactics.append(tactic)
        if not result.ok or result.state is None:
            step = Step(
                step=self._n, state_id=-1, tactic=tactic, goals=self._prev_goals, ok=False,
                error=result.error, elapsed_ms=result.elapsed_ms, messages=list(result.messages),
            )
            self.trace.steps.append(step)
            self.trace.error = result.error
            self.trace.failed_at = self._n
            self.trace.failed_line = self.trace.failed_column = None
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
        self.trace.failed_line = self.trace.failed_column = None
        if result.proof_finished:
            self.trace.finished = True
        if self.on_step is not None:
            self.on_step(step, prev)
        return step

    def run_script(
        self, tactics: list[str], *, timeout: float | None = None, locations: list[SentenceAt] | None = None
    ) -> Trace:
        """Step until the first failure; returns the trace either way.

        ``locations`` (from :func:`proof_script`) places the failing sentence in the
        source file, so the failure says *where* as well as *what*.
        """
        for i, tactic in enumerate(tactics):
            if not self.step(tactic, timeout=timeout).ok:
                if locations is not None and i < len(locations):
                    self.trace.failed_line = locations[i].line
                    self.trace.failed_column = locations[i].column
                break
        return self.trace

    def resume(self, entry: ReplayEntry, tactics: list[str]) -> int | None:
        """Adopt ``entry``'s root and its longest prefix of ``tactics``; the number of sentences adopted.

        ``None`` when nothing can be reused -- the session is pinned to another process,
        or that process restarted since -- and the caller starts from scratch.  Must be
        called on a fresh tracer, before :meth:`start`.
        """
        proc = self.session.process
        if self.trace.steps or proc is None or proc.id != entry.process or proc.generation != entry.generation:
            return None
        k = entry.common_prefix(tactics)
        try:
            self.session.resume(entry.states[0], list(zip(tactics[:k], entry.states[1 : k + 1], strict=True)))
        except StateError:
            return None
        self.trace.steps = list(entry.steps[: k + 1])
        self.trace.tactics = [s.tactic for s in self.trace.steps[1:]]
        self.trace.events = [e for e in entry.events if (_event_step(e) or 0) <= k]
        self.trace.finished = bool(k and entry.states[k].proof_finished)
        for s in self.trace.steps:
            self._intern(s.goals)
        self._prev_goals = list(self.trace.steps[-1].goals)
        self._n = k
        return k

    def replay_entry(self) -> ReplayEntry | None:
        """What a later trace of this lemma can reuse: the committed prefix of this one."""
        session = self.session
        proc = session.process
        if proc is None or session.root is None or session.lost or not self.trace.steps:
            return None
        ok = [s for s in self.trace.steps if s.ok]
        states = [session.root, *(state for _, state in session.history)]
        if len(ok) != len(states) or any(s.tactic != t for s, (t, _) in zip(ok[1:], session.history, strict=True)):
            return None  # stepped past a failure in place: the numbering no longer lines up
        steps_ms = sum(s.elapsed_ms for s in ok[1:])
        return ReplayEntry(process=proc.id, generation=proc.generation, steps=ok, states=states,
                           events=list(self.trace.events), start_ms=self.start_ms, steps_ms=steps_ms)

    def _intern(self, goals: list[IrisGoal]) -> None:
        for g in goals:
            for h in g.all_hyps:
                self.trace.store.put(h.prop)
            if g.goal:
                self.trace.store.put(g.goal)


# ------------------------------------------------------------ incremental replay

#: Traces kept for reuse.  Each holds handles only; the states live in ``pet`` anyway.
REPLAY_CACHE_SIZE = 16


@dataclass
class ReplayEntry:
    """The committed prefix of one trace: step records and the states behind them.

    ``states[i]`` is the state after ``steps[i]`` (``states[0]`` the root); both lists
    have one element per successful step, in order.
    """

    process: int
    generation: int
    steps: list[Step]
    states: list[StateHandle]
    events: list[Any] = field(default_factory=list)
    start_ms: int = 0
    steps_ms: int = 0

    @property
    def tactics(self) -> list[str]:
        return [s.tactic for s in self.steps[1:]]

    def common_prefix(self, tactics: list[str]) -> int:
        k = 0
        for old, new in zip(self.tactics, tactics, strict=False):
            if old.strip() != new.strip():
                break
            k += 1
        return k

    def saved_ms(self, k: int) -> int:
        """What adopting ``k`` sentences (and the root) saved, by the first run's clock."""
        return self.start_ms + sum(s.elapsed_ms for s in self.steps[1 : k + 1])


def replay_key(source_file: str | Path, thm: str, *, stub_prefix: bool, pre_commands: str | None = None,
               workspace: str | Path | None = None) -> tuple[str, ...] | None:
    """What a trace's root state depends on: the file, the lemma, and the text before its proof.

    With ``stub_prefix`` the proofs before the lemma are not part of it (the twin
    stubs them), so editing a proof -- this one's or an earlier one's -- keeps the key;
    editing any statement up to the lemma's changes it.  ``None`` when the file does not
    declare ``thm`` (nothing to cache).
    """
    path = Path(source_file).resolve()
    try:
        text = read_text(path)
    except OSError:
        return None
    if stub_prefix:
        text, _ = stub_proof_bodies(text, also={thm})
    block = find_block(text, thm)
    if block is None:
        return None
    digest = hashlib.sha256(text[: block.statement_end].encode("utf-8")).hexdigest()
    return (str(path), thm, "fast" if stub_prefix else "full", pre_commands or "", str(workspace or ""), digest)


class ReplayCache:
    """A bounded LRU of :class:`ReplayEntry` by :func:`replay_key`.  Thread-safe."""

    def __init__(self, size: int = REPLAY_CACHE_SIZE) -> None:
        self.size = size
        self._entries: OrderedDict[tuple[str, ...], ReplayEntry] = OrderedDict()
        self._lock = threading.Lock()

    def get(self, key: tuple[str, ...] | None) -> ReplayEntry | None:
        if key is None:
            return None
        with self._lock:
            entry = self._entries.get(key)
            if entry is not None:
                self._entries.move_to_end(key)
            return entry

    def put(self, key: tuple[str, ...] | None, entry: ReplayEntry | None) -> None:
        if key is None or entry is None:
            return
        with self._lock:
            self._entries[key] = entry
            self._entries.move_to_end(key)
            while len(self._entries) > self.size:
                self._entries.popitem(last=False)

    def drop(self, key: tuple[str, ...] | None) -> None:
        with self._lock:
            self._entries.pop(key, None)  # type: ignore[arg-type]

    def __len__(self) -> int:
        return len(self._entries)
