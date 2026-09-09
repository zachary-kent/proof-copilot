"""A logical proof session over one pinned ``pet`` process (PLAN.md 6, 7).

A session is a root state plus the states reachable from it -- ``current``,
``history``, an LRU of handles, and state-hash loop detection.  It owns no process; it
is *bound* to the one the pool chose, and every call goes there.  ``lost`` is set when
that process restarted, and every later call raises ``StateError`` telling the worker
to ``proof_open`` again, instead of a stale id being reported as a tactic failure.

Speculation is free: ``run(commit=False)``, ``try_many``, ``query`` and the oracle probes
never move the session (petanque states are immutable).
"""

from __future__ import annotations

import contextlib
import math
import time
from collections import OrderedDict
from collections.abc import Iterator
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any

from pcp.errors import StateError
from pcp.rocq.assemble import stubbed_twin
from pcp.rocq.lexer import first_word, split_sentences
from pcp.state.petanque import DEFAULT_STEP_TIMEOUT, GoalView, PetProcess, StateHandle, TacticError

if TYPE_CHECKING:
    from pcp.state.pool import SessionPool

#: Budget for the ``Set Typeclasses Debug`` re-run after a timeout (PLAN.md 6).
TYPECLASS_DEBUG_TIMEOUT = 10.0
TYPECLASS_DEBUG_CHARS = 8000


@dataclass
class StepResult:
    """What one ``run`` produced.  ``ok=False`` is a *Rocq* failure, never a dead process."""

    ok: bool
    state: StateHandle | None = None
    state_hash: int | None = None
    error: str | None = None
    messages: list[str] = field(default_factory=list)
    elapsed_ms: int = 0
    proof_finished: bool = False
    #: Step number (0 = root) at which this exact state was already seen; set for
    #: committed *and* speculative runs (v1 dropped it on the committed path).
    loop_of: int | None = None
    timed_out: bool = False
    #: The ``Set Typeclasses Debug`` trace of the re-run, when the step timed out.
    typeclass_debug: str | None = None
    tactic: str = ""

    @property
    def state_id(self) -> int | None:
        return self.state.st if self.state is not None else None


class ProofSession:
    """See the module docstring.  Construct through ``SessionPool.open``."""

    def __init__(
        self,
        pool: SessionPool | None,
        process: PetProcess | None,
        file: str | Path,
        thm: str,
        *,
        pre_commands: str | None = None,
        step_timeout: float = DEFAULT_STEP_TIMEOUT,
        lru_size: int = 512,
        stub_prefix: bool = False,
    ) -> None:
        self.pool = pool
        self.process = process
        self.source_file = str(Path(file).resolve())
        #: The file petanque sees: the statements-only twin when ``stub_prefix``.
        #: Sound because ``Qed`` proofs are opaque: the state at ``thm`` depends on
        #: the *statements* before it, never on their bodies (tested).
        self.file = str(stubbed_twin(self.source_file, keep=thm)) if stub_prefix else self.source_file
        self.thm = thm
        self.pre_commands = pre_commands
        self.step_timeout = step_timeout
        self.stub_prefix = stub_prefix
        self.label = thm
        self.root: StateHandle | None = None
        self.current: StateHandle | None = None
        self.history: list[tuple[str, StateHandle]] = []
        self.lost = False
        self.lost_reason: str | None = None
        self._lru: OrderedDict[int, StateHandle] = OrderedDict()
        self._lru_size = lru_size
        self._seen: dict[int, int] = {}

    # -- binding ---------------------------------------------------------------
    def bind(self, process: PetProcess) -> None:
        self.process = process

    def mark_lost(self, reason: str) -> None:
        self.lost = True
        self.lost_reason = reason

    @property
    def started(self) -> bool:
        return self.root is not None

    @property
    def step_number(self) -> int:
        return len(self.history)

    def _require_live(self) -> PetProcess:
        if self.lost:
            raise StateError(f"session {self.label} was lost when {self.lost_reason}; call proof_open again")
        if self.process is None:
            raise StateError(f"session {self.label} is not bound to a petanque process")
        return self.process

    @contextlib.contextmanager
    def _held(self) -> Iterator[PetProcess]:
        """The pinned process, held for one call; re-checked after the pool's health pass."""
        proc = self._require_live()
        cm = self.pool.acquire(proc) if self.pool is not None else proc.lock
        with cm:
            self._require_live()
            yield proc

    # -- start -----------------------------------------------------------------
    def start(self) -> StateHandle:
        """``petanque/start`` on the pinned process; seeds loop detection with the root."""
        with self._held() as proc:
            self.root = proc.start(self.file, self.thm, self.pre_commands)
            self.current = self.root
            self.history = []
            self._seen = {}
            self._lru.clear()
            self._remember(self.root)
            if self.root.state_hash is not None:
                self._seen[self.root.state_hash] = 0
            return self.root

    def _remember(self, state: StateHandle) -> None:
        self._lru[state.st] = state
        self._lru.move_to_end(state.st)
        while len(self._lru) > self._lru_size:
            self._lru.popitem(last=False)

    def state(self, state_id: int | None = None) -> StateHandle:
        if state_id is None:
            if self.current is None:
                raise StateError(f"session {self.label} is not started")
            return self.current
        st = self._lru.get(state_id)
        if st is None:
            raise StateError(f"state {state_id} is not in session {self.label}'s state table (LRU of {self._lru_size})")
        return st

    def _base(self, from_state: StateHandle | None) -> StateHandle:
        if from_state is not None:
            return from_state
        if self.current is None:
            raise StateError(f"session {self.label} is not started; call start() first")
        return self.current

    # -- stepping --------------------------------------------------------------
    def run(
        self,
        tactic: str,
        *,
        from_state: StateHandle | None = None,
        commit: bool = True,
        timeout: float | None = None,
    ) -> StepResult:
        """Run one command.  ``commit=False`` is speculative: the session does not move.

        A Rocq failure is a ``StepResult(ok=False)``; a transport failure or a lost
        session raises ``StateError`` (PLAN.md 4.4 honesty: never call a dead process a
        wrong tactic).
        """
        limit = self.step_timeout if timeout is None else timeout
        started = time.perf_counter()
        with self._held() as proc:
            base = self._base(from_state)
            try:
                state = proc.run(base, tactic, timeout=limit)
            except TacticError as exc:
                elapsed = int((time.perf_counter() - started) * 1000)
                result = StepResult(
                    ok=False, error=exc.message, elapsed_ms=elapsed, timed_out=exc.timed_out, tactic=tactic
                )
                if exc.timed_out:
                    result.typeclass_debug = self._typeclass_debug(proc, base, tactic, limit)
                return result
            elapsed = int((time.perf_counter() - started) * 1000)
            result = StepResult(
                ok=True,
                state=state,
                state_hash=state.state_hash,
                messages=list(state.messages),
                elapsed_ms=elapsed,
                proof_finished=state.proof_finished,
                tactic=tactic,
            )
            h = state.state_hash
            if h is not None and h in self._seen:
                result.loop_of = self._seen[h]
            if commit:
                self.current = state
                self.history.append((tactic, state))
                self._remember(state)
                if h is not None:
                    self._seen.setdefault(h, len(self.history))
        return result

    def try_many(self, tactics: list[str], *, from_state: StateHandle | None = None) -> list[StepResult]:
        """Speculative fan-out from one state (``proof_try``); nothing enters history."""
        with self._held():
            base = self._base(from_state)
            return [self.run(t, from_state=base, commit=False) for t in tactics]

    def _typeclass_debug(self, proc: PetProcess, base: StateHandle, tactic: str, limit: float) -> str | None:
        """Re-run a timed-out tactic under ``Set Typeclasses Debug`` and keep its trace.

        The trace is on the *follow-up* run's feedback, not the probe's, and a run that
        fails returns no feedback at all -- so the tactic is re-run under ``try (timeout
        n (...))``, which succeeds (without progress) and keeps every message emitted.
        """
        code = _single_tactic(tactic)
        if code is None:
            return None
        budget = max(1, min(int(math.ceil(TYPECLASS_DEBUG_TIMEOUT)), int(math.ceil(limit))))
        try:
            probe = proc.run(base, "Set Typeclasses Debug.", timeout=TYPECLASS_DEBUG_TIMEOUT, with_hash=False)
            follow = proc.run(probe, f"try (timeout {budget} ({code})).", timeout=budget + 2, with_hash=False)
        except TacticError:
            return None
        text = "\n".join(follow.messages).strip()
        return text[:TYPECLASS_DEBUG_CHARS] or None

    # -- inspection ------------------------------------------------------------
    def goals(self, state: StateHandle | None = None) -> list[GoalView]:
        with self._held() as proc:
            return proc.goals(self._base(state))

    def premises(self, state: StateHandle | None = None) -> Any:
        with self._held() as proc:
            return proc.premises(self._base(state))

    def ast(self, text: str, state: StateHandle | None = None) -> Any:
        with self._held() as proc:
            return proc.ast(self._base(state), text)

    def state_equal(self, a: StateHandle, b: StateHandle) -> bool:
        with self._held() as proc:
            return proc.state_equal(a, b)

    def query(self, command: str, state: StateHandle | None = None) -> list[str]:
        """Messages of a query command (``Search``, ``Print``, ``About``); ``[]`` if Rocq rejects it."""
        result = self.run(command, from_state=state, commit=False)
        return result.messages if result.ok else []

    # -- replay ----------------------------------------------------------------
    def replay(self, tactics: list[str]) -> list[StepResult]:
        """Deterministic replay from the root: a trace is (root, tactic list) (PLAN.md 6)."""
        with self._held():
            if self.root is None:
                self.start()
            assert self.root is not None
            self.current = self.root
            self.history = []
            self._seen = {self.root.state_hash: 0} if self.root.state_hash is not None else {}
            out: list[StepResult] = []
            for tactic in tactics:
                res = self.run(tactic)
                out.append(res)
                if not res.ok:
                    break
            return out

    def __repr__(self) -> str:
        proc = f"#{self.process.id}" if self.process else "unbound"
        return f"<ProofSession {self.thm} @ {proc} steps={len(self.history)} lost={self.lost}>"


def _single_tactic(tactic: str) -> str | None:
    """The tactic expression of a single plain sentence, or ``None`` if it cannot be wrapped."""
    sentences = [s for s in split_sentences(tactic) if s.code.strip()]
    if len(sentences) != 1:
        return None
    sent = sentences[0]
    code = sent.code.strip()
    if sent.is_bullet or sent.is_brace or not code.endswith("."):
        return None
    word = first_word(code)
    if not word or not code.startswith(word):  # goal selector or attribute in front
        return None
    return code[:-1].strip()
