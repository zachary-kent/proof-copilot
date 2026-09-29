"""The MCP tool surface: transport-free, locked, and honest about lost state (PLAN.md 7).

The tools behind a hard cap (:data:`pcp.mcp.names.TOOLS`).  The implementations live on
:class:`PcpServer`, which knows nothing about MCP, so the model, the CLI, the tests and
the ablation harness call exactly the same code -- an ablation over a different code
path measures nothing (PLAN.md 13).  :func:`register` is the mechanical adapter onto
whichever ``mcp`` SDK generation is installed.

Why it is locked: the ``mcp`` SDK runs synchronous tools on worker threads and a
client issues independent tool calls in parallel, so nothing may mint duplicate
session ids or interleave ``proof_step``/``proof_try`` on one session (ARCHITECTURE.md
8, "state sent to the wrong process").  The session table is mutated under one lock
and every session carries its own lock, so two calls on one session serialise while
two sessions pinned to two ``pet`` processes proceed concurrently.

Why a "lost" shape exists: a process that died or restarted is a *transport* fact, not
a wrong tactic (PLAN.md 4.4).  Any tool that meets a ``StateError`` answers
``{"ok": false, "lost": true, "action": "call proof_open again"}`` and never presents
it as a tactic failure.  Every tool answers JSON for every input: a ``PcpError`` is a
failure result and an unexpected exception is logged to stderr and returned with
``"error": "<Type>: <msg>"`` -- the server never dies from one bad call.

One schema (pcp-issues D3, :mod:`pcp.mcp.result`): every result -- errors, timeouts
and lost sessions included -- opens with ``ok``, ``what``, ``where``, ``goal``, ``next``,
so an agent chains calls without a follow-up to learn where it is.  A failed sentence
carries the sentence, its step (and file line/column for a trace of the file's own
proof), the goal it was applied to and the error with its cause kept; a step that
changes the goals lists them in order with their shapes (``goal_list``, MF3).

Extending it: a *tool* is a name in :data:`pcp.mcp.names.TOOLS` (and ``BLURBS``), a
``@_guard``-ed method here returning :func:`pcp.mcp.result.result` /
:func:`~pcp.mcp.result.failure`, and a wrapper in :func:`tool_functions` whose docstring
is the description the model reads.  A *result section* (a report computed from a
step's before/after goals, added under its own key) is a :data:`ResultSection` in
:data:`RESULT_SECTIONS`; nothing else needs to change.

Deliberately not tools: ``prove_this_lemma``, ``fix_this_proof``.  A tool that tries to
be an agent is a tool you cannot ablate.
"""

from __future__ import annotations

import functools
import inspect
import json
import logging
import os
import sys
import threading
import time
from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from pcp import __version__
from pcp.config.toolchain import project_root, workspace_for
from pcp.errors import PcpError, StateError, ToolchainError, UsageError
from pcp.mcp.names import MAX_TOOLS, MCP_SERVER_NAME, TOOLS
from pcp.mcp.result import BLOCK_KEYS, conform, failure, one_line, result, where
from pcp.rocq.assemble import Development, parse_plan
from pcp.rocq.body import strip_proof_wrapper
from pcp.rocq.decls import find_block
from pcp.rocq.errors import shape_error
from pcp.rocq.lexer import split_sentences, terminate_sentence
from pcp.state.candidates import closest_survivor
from pcp.state.diagnose import diagnose_structured, error_family
from pcp.state.diagnosis_log import record_diagnosis, record_feedback
from pcp.state.invariant import invariant_pattern
from pcp.state.ipm.model import IrisGoal, Step
from pcp.state.ipm.pattern import DestructSpec, compile_auto, compile_spec
from pcp.state.ipm.reflect import REQUIRE, Reflector, build_idump, env_with_idump
from pcp.state.ipm.skeleton import parse_skeleton
from pcp.state.ledger.diff import attach, step_warnings
from pcp.state.ledger.effects import effect_lines
from pcp.state.ledger.query import (
    blame,
    leftovers,
    render_blame,
    render_events,
    render_leftovers,
    render_provenance,
    render_unused,
    unused_at_qed,
    where_did_it_go,
)
from pcp.state.petanque import StartFailed
from pcp.state.pool import SessionPool
from pcp.state.printing import GoalHidden
from pcp.state.render import Rendered, describe_goal_list, goal_list, goal_shape, n_goals, render_goal
from pcp.state.search import notation_resolve, premise_search
from pcp.state.session import ProofSession
from pcp.state.shape import expect_shape
from pcp.state.trace import ReplayCache, SentenceAt, Trace, Tracer, proof_script, replay_key
from pcp.util.io import read_text
from pcp.util.proc import kill_tree

assert len(TOOLS) <= MAX_TOOLS, "the tool surface is capped (PLAN.md 7)"

_log = logging.getLogger("pcp.mcp")

LOST_ACTION = "call proof_open again"
#: petanque caps a speculative fan-out at about twenty states (PLAN.md 7).
MAX_TRY = 20
DEFAULT_STEP_BUDGET = 3000
DEFAULT_STATE_BUDGET = 4000
#: Wall clock of ``petanque/start`` for the server's processes.  A statements-only
#: (``fast``) open of a 1400-line Iris file takes ~3 s cold and a full one ~80 s, so
#: 300 s only ever cuts off a document that diverges -- reported as a result, and the
#: killed process restarts on its next call instead of wedging the pool.
PROOF_OPEN_START_TIMEOUT = 300.0
#: Size of a Rocq error in a ``proof_try`` row (``shape_error`` keeps its tail).
TRY_ERROR_CHARS = 400
#: Budget of ``verify_node``'s gate compile (``Gate.timeout``).
VERIFY_TIMEOUT = 600.0
#: Open sessions kept; beyond this the oldest is closed (its twin released).
MAX_SESSIONS = 64
#: ``proof_trace(events=...)``: the whole ledger log, the steps near where the trace
#: ends (the default), or none.  A 180-sentence replay's full log ran to ~60 KB, past
#: what an MCP client returns inline (session 3, issue 20); ``proof_ledger(s, "events")``
#: still has every event.
TRACE_EVENTS = ("near", "all", "none")
#: How many steps before the end (or the failure) ``events="near"`` keeps.
TRACE_EVENT_WINDOW = 5
#: At most this many warnings in a trace result, each with its step.
TRACE_WARNINGS = 20
LEDGER_QUERIES = ("where_did_it_go", "blame", "leftovers", "unused_at_qed", "events")
#: How often the parent watch looks at ``getppid``.
PARENT_WATCH_INTERVAL_S = 2.0
NO_SDK_MESSAGE = (
    "no usable MCP server API found. Install it with pip install 'proof-copilot[mcp]' "
    "(mcp 1.x or 2.x both work)."
)


# ------------------------------------------------------------------- sessions


@dataclass
class SessionRecord:
    """One open proof: the pinned session, its tracer (ledger attached), and a lock."""

    id: str
    session: ProofSession
    tracer: Tracer
    reflector: Reflector | None = None
    lock: threading.RLock = field(default_factory=threading.RLock, repr=False)
    #: The step whose goals the model last saw rendered: the diff-only baseline of a
    #: bare ``proof_state`` is "what changed since you last looked", which after a
    #: ``proof_trace`` or ``proof_destruct(apply)`` is several steps back.
    seen_step: int | None = None

    @property
    def trace(self) -> Trace:
        return self.tracer.trace

    @property
    def final_goals(self) -> list[IrisGoal]:
        final = self.trace.final
        return list(final.goals) if final is not None else []

    @property
    def seen_goals(self) -> list[IrisGoal] | None:
        seen = self.trace.step_at(self.seen_step) if self.seen_step is not None else None
        return list(seen.goals) if seen is not None else None


@dataclass
class SectionContext:
    """What a result section sees: one step of one session, before and after.

    ``after`` is ``None`` when the sentence failed (``before`` is then the goals it was
    applied to); ``step`` is ``None`` for a speculative run, which records nothing.
    """

    tool: str
    rec: SessionRecord
    tactic: str | None
    before: list[IrisGoal]
    after: list[IrisGoal] | None
    step: Step | None
    ok: bool
    events: list[Any] = field(default_factory=list)


#: A result section: named, computed from a :class:`SectionContext`, added to the
#: result of ``proof_step`` / ``proof_trace`` / ``proof_destruct(apply=True)`` under its
#: name when it returns something non-empty.  The extension point for reports that are
#: not the server's own (tactic effects, shape checks): register one in
#: :data:`RESULT_SECTIONS` (every server) or ``PcpServer.sections`` (one server).  A
#: section that raises is logged and left out -- it never costs the model its result.
ResultSection = Callable[[SectionContext], Any]
RESULT_SECTIONS: dict[str, ResultSection] = {}


def _state_error(exc: StateError, *, lost: bool) -> dict[str, Any]:
    """A transport fact as a result: a lost session, or a call that ran out of time."""
    message = str(exc)
    timed_out = "wall clock" in message or "timed out" in message.lower()
    if not lost:
        return failure(message, message, timed_out=timed_out,
                       next=["call again; a killed petanque restarts on its next call" if timed_out
                             else "`pcp doctor` if petanque cannot start in this project"])
    what = ("the call ran past its wall clock; petanque was killed and the session is lost" if timed_out
            else "the session is lost: its petanque process restarted (not a tactic failure)")
    return failure(what, message, lost=True, action=LOST_ACTION, timed_out=timed_out,
                   next=["proof_open(file, lemma) again, then replay (proof_trace(file, lemma, script) replays a script)"])


def _guard(*, lost: bool) -> Callable[[Callable[..., dict[str, Any]]], Callable[..., dict[str, Any]]]:
    """Every tool answers a JSON object in the one schema (:mod:`pcp.mcp.result`), whatever happens."""

    def deco(fn: Callable[..., dict[str, Any]]) -> Callable[..., dict[str, Any]]:
        @functools.wraps(fn)
        def wrapper(self: PcpServer, *args: Any, **kwargs: Any) -> dict[str, Any]:
            try:
                out = fn(self, *args, **kwargs)
            except StateError as exc:
                out = _state_error(exc, lost=lost)
            except PcpError as exc:
                out = self._usage_failure(exc)
            except Exception as exc:  # noqa: BLE001 -- the server never dies from one bad call
                _log.exception("tool %s failed", fn.__name__)
                out = failure(f"internal error in {fn.__name__}", f"{type(exc).__name__}: {exc}",
                              next=["the server is still up: retry, or report this with the `error` text"])
            return conform(out)

        return wrapper

    return deco


def default_blame_step(trace: Trace) -> int:
    """The step ``blame`` asks about when none is given: the failed one, else the next one.

    Steps are numbered ``0..n``; the default is the failed step when the trace
    stopped at one, never ``len(steps)``, so the report never names a step that
    never ran.
    """
    if trace.failed_at is not None:
        return trace.failed_at
    return trace.final.step + 1 if trace.final is not None else 0


def _q(text: str) -> str:
    """A tool argument as the model would write it (JSON string quoting)."""
    return json.dumps(" ".join(text.split()), ensure_ascii=False)


def _is_timeout(error: str | None) -> bool:
    low = (error or "").lower()
    return "timeout!" in low or "timed out" in low


# --------------------------------------------------------------------- server


class PcpServer:
    """The tool implementations.  Thread-safe; every method returns a JSON-shaped dict."""

    def __init__(self, workspace: str | Path, *, pool_size: int = 2, coq_root: str | Path | None = None) -> None:
        resolved = Path(workspace).resolve()
        if not resolved.is_dir():
            placeholder = " (an unexpanded template placeholder? the host must substitute it)" if "${" in str(workspace) else ""
            raise UsageError(f"--workspace {workspace!r} does not exist{placeholder}")
        #: Where the host launched us (Claude Code: the git root); the workspace is the
        #: pcp project in or around it, which relative paths and ``.pcp/`` belong to.
        self.launch_dir = resolved
        self.workspace = workspace_for(resolved)
        self.pool_size = pool_size
        #: Where ``IDump.vo`` is built for ``reflect=True``.  Absolute, under the
        #: workspace by default -- never relative to the process's cwd.
        self.coq_root = Path(coq_root).resolve() if coq_root is not None else self.workspace / ".pcp" / "coq"
        self.pool = SessionPool(self.workspace, size=pool_size, start_timeout=PROOF_OPEN_START_TIMEOUT)
        #: One pool per (project root, reflect): a file whose nearest ``_CoqProject`` is
        #: not the workspace's is elaborated by a ``pet`` rooted at *its* project, so its
        #: ``-Q``/``-R`` flags apply (issue 6 on the MCP path).
        self._pools_by: dict[tuple[Path, bool], SessionPool] = {(self.workspace, False): self.pool}
        self._pool_lock = threading.Lock()
        self._lock = threading.RLock()
        self._sessions: dict[str, SessionRecord] = {}
        self._n = 0
        self.replays = ReplayCache()
        self.sections: dict[str, ResultSection] = dict(RESULT_SECTIONS)

    # -- lifecycle -------------------------------------------------------------
    def close(self) -> None:
        """Stop every petanque process, waiting for in-flight calls.  Idempotent."""
        with self._lock:
            records, self._sessions = list(self._sessions.values()), {}
        for rec in records:
            rec.session.close()
        for pool in self._pools():
            pool.close()

    def terminate(self) -> None:
        """Kill every petanque process outright, without waiting on in-flight calls.

        The parent-watch path: the client is already gone, and a graceful ``close``
        would wait on a process lock held by a runaway call (the 372 GB server).
        """
        for pool in self._pools():
            for proc in pool.processes:
                pid = proc.pid
                if pid is not None:
                    try:
                        kill_tree(pid, grace_s=0.5)
                    except Exception:  # noqa: BLE001 -- best effort on the way out
                        _log.debug("could not kill petanque %s", pid, exc_info=True)

    def _pools(self) -> list[SessionPool]:
        with self._pool_lock:
            return list(self._pools_by.values())

    # -- registry --------------------------------------------------------------
    @property
    def sessions(self) -> list[str]:
        with self._lock:
            return list(self._sessions)

    def record(self, sid: str) -> SessionRecord:
        with self._lock:
            rec = self._sessions.get(sid)
        if rec is None:
            raise UsageError(f"no session {sid!r}; call proof_open first")
        return rec

    def _register(self, session: ProofSession, tracer: Tracer, reflector: Reflector | None) -> SessionRecord:
        """Add a started session; the oldest ones beyond :data:`MAX_SESSIONS` are closed."""
        with self._lock:
            self._n += 1
            rec = SessionRecord(f"s{self._n}", session, tracer, reflector)
            self._sessions[rec.id] = rec
            evicted = []
            while len(self._sessions) > MAX_SESSIONS:
                evicted.append(self._sessions.pop(next(iter(self._sessions))))
        for old in evicted:
            old.session.close()
        return rec

    def _drop(self, rec: SessionRecord) -> None:
        with self._lock:
            self._sessions.pop(rec.id, None)
        rec.session.close()

    def _resolve(self, file: str | Path) -> Path:
        """Absolute as given; relative to the project, else to where the host launched us
        (a path copied from the host's own listing is relative to *its* directory)."""
        p = Path(file).expanduser()
        if p.is_absolute():
            return p.resolve()
        mine = (self.workspace / p).resolve()
        if mine.exists() or self.launch_dir == self.workspace:
            return mine
        theirs = (self.launch_dir / p).resolve()
        return theirs if theirs.exists() else mine

    def _file(self, file: str) -> Path:
        path = self._resolve(file)
        if not path.is_file():
            also = f" and {self.launch_dir}" if self.launch_dir != self.workspace else ""
            raise UsageError(f"{file}: no such file (resolved against {self.workspace}{also})")
        return path

    def _rel(self, path: str | Path) -> str:
        """``path`` as the model names files: relative to the workspace when under it."""
        p = Path(path)
        try:
            return str(p.resolve().relative_to(self.workspace))
        except ValueError:
            return str(p)

    def _root_for(self, path: Path | None) -> Path:
        if path is None:
            return self.workspace
        root = project_root(path)
        return root.resolve() if root is not None else self.workspace

    def _pool_for(self, *, reflect: bool, file: Path | None = None) -> SessionPool:
        """The pool for ``file``'s project root; a reflect pool spawns with ``IDump`` on the load path.

        A ``pet`` captures its environment at spawn, so ``reflect`` cannot be switched on
        for a process that is already running: patching ``os.environ`` after the fact
        would leave ``Require Import pcp.IDump`` failing inside ``start``.  Hence a
        second pool whose every process is born with the right env; it costs nothing
        until the first ``reflect=True``.  Likewise a pool per project root, spawned on
        the first file that needs it.
        """
        key = (self._root_for(file), reflect)
        with self._pool_lock:
            pool = self._pools_by.get(key)
            if pool is None:
                cfg: dict[str, Any] = {"start_timeout": PROOF_OPEN_START_TIMEOUT}
                if reflect:
                    build_idump(self.coq_root)
                    cfg["env"] = env_with_idump(dict(os.environ), self.coq_root)
                pool = SessionPool(key[0], size=self.pool_size, **cfg)
                self._pools_by[key] = pool
            return pool

    def _new_session(self, path: Path, lemma: str, *, reflect: bool, fast: bool) -> tuple[ProofSession, Tracer, Reflector | None]:
        pool = self._pool_for(reflect=reflect, file=path)
        session = pool.open(path, lemma, pre_commands=REQUIRE if reflect else None, stub_prefix=fast)
        reflector = Reflector(session) if reflect else None
        return session, attach(Tracer(session, reflector=reflector)), reflector

    def _lemma_where(self, path: Path, lemma: str, *, step: int | None = None) -> dict[str, Any] | None:
        try:
            source = read_text(path)
        except OSError:
            return where(file=self._rel(path), step=step)
        block = find_block(source, lemma)
        if block is None:
            return where(file=self._rel(path), step=step)
        at = block.statement_start
        return where(file=self._rel(path), line=source.count("\n", 0, at) + 1,
                     column=at - (source.rfind("\n", 0, at) + 1) + 1, step=step)

    def _usage_failure(self, exc: PcpError) -> dict[str, Any]:
        message = str(exc)
        if message.startswith("no session"):
            hint = [f"proof_open(file, lemma) first; open sessions: {', '.join(self.sessions) or 'none'}"]
        elif "no such file" in message:
            hint = [f"pass a path relative to the workspace ({self.workspace}) or an absolute one"]
        else:
            hint = ["fix the arguments and call again (`pcp tools list` prints every signature)"]
        return failure(message, message, next=hint)

    # -- rendering and diagnosis ------------------------------------------------
    def _render(
        self,
        rec: SessionRecord,
        goals: list[IrisGoal],
        *,
        prev: list[IrisGoal] | None = None,
        select: str | None = None,
        mode: str = "full",
        budget: int = DEFAULT_STEP_BUDGET,
        diff_only: bool = True,
        relevance: bool = False,
        at: Step | None = None,
    ) -> list[Rendered]:
        """One budgeted render per goal, diffed positionally against ``prev`` (PLAN.md 5).

        Positional: goal ``i`` against the previous goal ``i``, never every goal
        against ``prev[0]``; a goal with no counterpart renders in full.  ``at`` is the
        step the goals belong to: its state is reprinted once (cached) so the render
        can mark hidden coercions and equality carriers (``pcp.state.printing``).
        """
        hidden: list[GoalHidden] | None = rec.tracer.hidden_at(at) if at is not None else None
        out: list[Rendered] = []
        for i, goal in enumerate(goals):
            base = prev[i] if prev is not None and i < len(prev) else None
            out.append(
                render_goal(
                    goal,
                    select=select,
                    mode=mode,
                    budget=budget,
                    diff_only=diff_only and base is not None,
                    prev=base,
                    relevance=relevance,
                    store=rec.trace.store,
                    hidden=hidden[i] if hidden is not None and i < len(hidden) else None,
                )
            )
        return out

    def _diagnosis(self, tactic: str, error: str | None, before: list[IrisGoal]) -> dict[str, Any]:
        """Diagnosis by construction, against the goal the tactic was applied to, logged for tuning.

        ``n_goals`` lets a focusing failure say how many goals were focused ("2 goals
        are focused: prefix a bullet") instead of suggesting a tactic.  The id is what
        ``diagnosis_feedback`` takes when the named repair class was wrong.
        """
        goal = before[0] if before else None
        dx = diagnose_structured(tactic, error or "", goal, n_goals=len(before) if before else None)
        did = record_diagnosis(self.workspace, dx, goal_hash=goal.goal_hash if goal else "")
        return {"diagnosis": dx.text, "diagnosis_id": did, "diagnosis_class": dx.repair,
                "diagnosis_confidence": dx.confidence}

    def _sections(self, out: dict[str, Any], ctx: SectionContext) -> dict[str, Any]:
        for name, section in self.sections.items():
            if name in out or name in BLOCK_KEYS:
                continue
            try:
                value = section(ctx)
            except Exception:  # noqa: BLE001 -- a report never costs the model its result
                _log.warning("result section %s failed", name, exc_info=True)
                continue
            if value not in (None, "", [], {}):
                out[name] = value
        return out

    def _step_failure(
        self,
        rec: SessionRecord,
        tactic: str,
        before: list[IrisGoal],
        error: str | None,
        *,
        step: Step | None,
        timed_out: bool,
        typeclass_debug: str | None = None,
        speculative: bool = False,
        tool: str = "proof_step",
    ) -> dict[str, Any]:
        """A failed sentence: what, where (step and tactic), the goal it met, the error's cause, what to try.

        The focused goal is rendered against what the model last saw, so an attempt
        that changes nothing costs the conclusion and a manifest, not the whole context.
        """
        sid = rec.id
        shaped = shape_error(error)
        n = step.step if step is not None else None
        at = step if step is not None else rec.trace.final
        goal = [r.text for r in self._render(rec, before[:1], prev=rec.seen_goals, at=at)] if before else None
        family = error_family(error)
        dx = self._diagnosis(tactic, error, before)
        confident = dx["diagnosis_confidence"] == "high" and dx["diagnosis_class"] != "unknown"
        if timed_out:
            what = f"`{one_line(tactic, 80)}` timed out" + (f" at step {n}" if n is not None else "")
            hints = [f"the tactic ran past its time budget: try a more targeted one, or proof_try({_q(sid)}, [variants])"]
            if typeclass_debug:
                hints.append("`typeclass_debug` has the instance search it was stuck in")
            if confident:
                hints.insert(0, f"`diagnosis` names the likely cause ({dx['diagnosis_class']}, high confidence)")
        else:
            what = f"`{one_line(tactic, 80)}` failed" + (f" at step {n}" if n is not None else "") + f": {one_line(error)}"
            hints = []
            if family == "focus":
                hints.append(f"{len(before)} goals are focused: prefix a bullet (`- {one_line(tactic, 60)}`) or wrap it in `{{ … }}`")
            if confident:
                hints.append(f"`diagnosis` names the repair ({dx['diagnosis_class']}, high confidence): "
                             f"apply it, or proof_try({_q(sid)}, [variants]) to test fixes at once")
            else:
                hints.append(f"proof_try({_q(sid)}, [variants]) to test fixes at once; "
                             + ("`diagnosis` is only a lead (low confidence)" if dx["diagnosis_class"] != "unknown"
                                else "`diagnosis` has no structural lead here"))
            if family == "frame":
                hints.append(f'proof_ledger({_q(sid)}, "leftovers") for what the context still holds')
        if speculative:
            hints.append("speculative: the session did not move")
        elif len(before) > 1:
            hints.append(f"proof_state({_q(sid)}) renders every goal ({len(before)})")
        if dx["diagnosis_id"] and dx["diagnosis_class"] != "unknown":
            hints.append(f"if its repair class proves wrong: diagnosis_feedback({_q(dx['diagnosis_id'])}, actual=...)")
        out = failure(
            what, shaped, where=where(file=self._rel(rec.session.source_file), sentence=tactic, step=n),
            goal=goal, next=hints, timed_out=timed_out, **dx,
        )
        if n is not None:
            out["step"] = n
        if len(before) > 1:
            out["goal_shapes"] = [goal_shape(g) for g in before]
        if typeclass_debug:
            out["typeclass_debug"] = shape_error(typeclass_debug)
        return self._sections(out, SectionContext(tool, rec, tactic, before, None, step, False))

    def _step_success(
        self,
        rec: SessionRecord,
        tactic: str,
        before: list[IrisGoal],
        step: Step,
        *,
        select: str | None = None,
        budget: int = DEFAULT_STEP_BUDGET,
        tool: str = "proof_step",
        first_step: int | None = None,
    ) -> dict[str, Any]:
        """A committed sentence (or, from ``first_step``, a chain): what changed, the goals
        in order when they changed, warnings, effects."""
        sid = rec.id
        rendered = self._render(rec, step.goals, prev=before, select=select, budget=budget, at=step)
        rec.seen_step = step.step
        events = [e for k in range(first_step if first_step is not None else step.step, step.step + 1)
                  for e in rec.trace.events_at(k)]
        warnings = step_warnings(events)
        change = goal_list(before, step.goals)
        finished = rec.trace.finished
        what = f"`{one_line(tactic, 80)}` → step {step.step}: " + (
            "proof finished" if finished else describe_goal_list(change) or n_goals(len(step.goals)))
        hints: list[str] = []
        if finished:
            hints = self._finished_next(rec)
        else:
            if step.loop_of is not None:
                what += f"; repeats step {step.loop_of} (no progress)"
                hints.append(f"the state is the one at step {step.loop_of}: this tactic did nothing here")
            if change is not None and any(g["status"] == "new" for g in change["goals"]) and len(step.goals) > 1:
                hints.append(f"{len(step.goals)} goals: focus the first with a bullet (`- tac.`) or `{{ … }}`; "
                             "`goal_list` has them in order")
            if warnings:
                hints.append("read `warnings` before going on")
            hints.append(f"proof_step({_q(sid)}, tactic) for the next sentence")
        if warnings:
            what += f"; {len(warnings)} warning{'s' if len(warnings) != 1 else ''}"
        out = result(
            True, what, where=where(file=self._rel(rec.session.source_file), sentence=tactic, step=step.step),
            goal=[r.text for r in rendered], next=hints,
            state_id=step.state_id,
            proof_finished=finished,
            loop_of=step.loop_of,
            ledger=[e.to_json() for e in events],
            effects=effect_lines(events),
            warnings=warnings,
            step=step.step,
        )
        if change is not None:
            out["goal_list"] = change
        return self._sections(out, SectionContext(tool, rec, tactic, before, list(step.goals), step, True, events))

    def _finished_next(self, rec: SessionRecord) -> list[str]:
        body = " ".join(s.tactic.strip() for s in rec.trace.steps[1:] if s.ok)
        file, lemma = self._rel(rec.session.source_file), rec.session.thm
        return [f"verify_node({_q(file)}, {_q(lemma)}, {_q(body)}) runs the gate on this script",
                "then write the script into the file"]

    # -- state and trace --------------------------------------------------------
    @_guard(lost=False)
    def proof_open(self, file: str, lemma: str, *, reflect: bool = False, fast: bool = True) -> dict[str, Any]:
        path = self._file(file)
        session, tracer, reflector = self._new_session(path, lemma, reflect=reflect, fast=fast)
        try:
            goals = tracer.start()  # outside the table lock: `petanque/start` takes seconds
        except StartFailed as exc:
            session.close()
            return self._start_failure(exc, path, lemma)
        except BaseException:
            session.close()
            raise
        rec = self._register(session, tracer, reflector)
        rec.seen_step = 0
        root = rec.trace.steps[0]
        sid = rec.id
        out = result(
            True,
            f"opened {lemma} ({self._rel(path)}): {len(goals)} goal{'s' if len(goals) != 1 else ''}"
            + (f"; focused: {goal_shape(goals[0])}" if goals else ""),
            where=self._lemma_where(path, lemma, step=0),
            goal=[r.text for r in self._render(rec, goals, diff_only=False, at=root)],
            next=[f"proof_step({_q(sid)}, tactic) runs one sentence",
                  f"proof_try({_q(sid)}, [t1, t2, ...]) tries candidates without moving"],
            session=sid,
            state_id=root.state_id,
        )
        if len(goals) > 1:
            out["goal_list"] = goal_list([], goals)
        return out

    def _start_failure(self, exc: StartFailed, path: Path, lemma: str) -> dict[str, Any]:
        """A result, not a lost session: the document does not check up to the lemma (or
        not in time); the message names the first error before it, and ``where`` places it."""
        check = getattr(exc, "check", None)
        if check is not None and check.line is not None:
            at = where(file=self._rel(path), line=check.line, column=check.column, sentence=check.sentence or None)
        else:
            at = self._lemma_where(path, lemma)
        if exc.timed_out:
            what = f"opening {lemma} timed out: {one_line(str(exc))}"
            hints = ["the document before the lemma does not check in time: fix or `Admit` the sentence `where` names",
                     "fast=True (the default) skips the proofs before the lemma"]
        elif check is not None and check.in_statement:
            what = f"the statement of {lemma} does not elaborate"
            hints = [f"fix the statement at line {check.line}: the cause is at the end of `error`"]
        else:
            what = f"could not open {lemma}: {one_line(str(exc))}"
            hints = ["fix the first error before the lemma (`where`); a failing Require usually means a stale or missing .vo",
                     "`pcp doctor` if petanque cannot load this project at all"]
        return failure(what, str(exc), where=at, next=hints, timed_out=exc.timed_out, lemma=lemma)

    @_guard(lost=True)
    def proof_step(
        self,
        session: str,
        tactic: str,
        *,
        mode: str = "commit",
        select: str | None = None,
        budget: int = DEFAULT_STEP_BUDGET,
    ) -> dict[str, Any]:
        rec = self.record(session)
        tactic = terminate_sentence(tactic)
        sid = rec.id
        file = self._rel(rec.session.source_file)
        with rec.lock:
            before = rec.final_goals
            if mode == "speculative":
                run = rec.session.run(tactic, commit=False)
                loop_of = rec.tracer.step_number(run.loop_of)
                if not run.ok or run.state is None:
                    out = self._step_failure(rec, tactic, before, run.error, step=None, timed_out=run.timed_out,
                                             typeclass_debug=run.typeclass_debug, speculative=True)
                    out["loop_of"] = loop_of
                    return out
                after = rec.tracer.goals_at(run.state)
                change = goal_list(before, after)
                out = result(
                    True,
                    f"`{one_line(tactic, 80)}` would succeed (speculative): "
                    + ("proof finished" if run.proof_finished else describe_goal_list(change) or n_goals(len(after))),
                    where=where(file=file, sentence=tactic),
                    goal=[r.text for r in self._render(rec, after, prev=before, select=select, budget=budget)],
                    next=[f"proof_step({_q(sid)}, {_q(tactic)}) commits it"],
                    # Only a failure gets a diagnosis; a success never gets the
                    # apply/leftover paragraphs, which would mislead the model.
                    error=None, loop_of=loop_of, diagnosis="", proof_finished=run.proof_finished,
                )
                if change is not None:
                    out["goal_list"] = change
                return self._sections(out, SectionContext("proof_step", rec, tactic, before, after, None, True))
            sentences = [x.text.strip() for x in split_sentences(tactic)]
            if len(sentences) > 1:
                return self._step_chain(rec, sentences, before, select=select, budget=budget)
            step = rec.tracer.step(tactic)
            last = rec.tracer.last_result
            if not step.ok:
                return self._step_failure(rec, tactic, before, step.error, step=step,
                                          timed_out=bool(last and last.timed_out) or _is_timeout(step.error),
                                          typeclass_debug=last.typeclass_debug if last else None)
            return self._step_success(rec, tactic, before, step, select=select, budget=budget)

    def _step_chain(self, rec: SessionRecord, sentences: list[str], before: list[IrisGoal], *,
                    select: str | None, budget: int) -> dict[str, Any]:
        """Several sentences in one ``proof_step``: each is its own step (session 3, issue 23).

        Run as one, a failure deep in the chain came back with the goal from before the
        whole chain and no word on which sentence failed.  Stepped one by one, the failure
        is the failing sentence's, against the goal it met; the ones before it stay
        committed (as in ``proof_trace``), and the result says so.
        """
        sid, n = rec.id, len(sentences)
        first: int | None = None
        for i, sentence in enumerate(sentences, 1):
            at = rec.final_goals
            step = rec.tracer.step(sentence)
            first = step.step if first is None else first
            if not step.ok:
                last = rec.tracer.last_result
                out = self._step_failure(rec, sentence, at, step.error, step=step,
                                         timed_out=bool(last and last.timed_out) or _is_timeout(step.error),
                                         typeclass_debug=last.typeclass_debug if last else None)
                out["what"] = one_line(f"sentence {i}/{n} of the chain: {out['what']}")
                done = (f"sentences 1-{i - 1} were committed (steps {first}-{step.step - 1})" if i > 1
                        else "nothing was committed")
                out["next"].insert(0, f"{done}: proof_step({_q(sid)}, ...) from `{one_line(sentence, 60)}` on, not the whole chain")
                out["chain"] = {"sentences": n, "failed": i, "committed": i - 1, "sentence": sentence}
                return out
            if rec.trace.finished and i < n:
                break
        out = self._step_success(rec, " ".join(sentences), before, step, select=select, budget=budget, first_step=first)
        out["chain"] = {"sentences": n, "committed": i, "steps": [first, step.step]}
        if i < n:
            out["next"].insert(0, f"the proof finished after sentence {i}/{n}; the rest was not run")
        return out

    @_guard(lost=True)
    def proof_state(
        self,
        session: str,
        *,
        step: int | None = None,
        select: str | None = None,
        mode: str = "full",
        budget: int = DEFAULT_STATE_BUDGET,
        diff_only: bool = True,
        relevance: bool = False,
    ) -> dict[str, Any]:
        rec = self.record(session)
        with rec.lock:
            target = rec.trace.step_at(step) if step is not None else rec.trace.final
            if target is None:
                last = rec.trace.final.step if rec.trace.final is not None else 0
                return failure(f"no step {step}", f"no step {step}", next=[f"steps run so far: 0..{last}"])
            prev = self._baseline(rec, target, explicit=step is not None) if diff_only else None
            rendered = self._render(
                rec, target.goals, prev=prev, select=select, mode=mode, budget=budget,
                diff_only=diff_only, relevance=relevance, at=target,
            )
            rec.seen_step = target.step
            texts = [r.text for r in rendered]
            at = where(file=self._rel(rec.session.source_file),
                       sentence=target.tactic if target.step > 0 else None, step=target.step)
            n = len(target.goals)
            if target.ok:
                out = result(True, f"step {target.step}: {n} goal{'s' if n != 1 else ''}"
                             + (f"; focused: {goal_shape(target.goals[0])}" if target.goals else ""),
                             where=at, goal=texts, step=target.step, goals=texts)
            else:
                # A failed step records the goals *before* the tactic; say so rather
                # than let the model believe the tactic applied.
                out = failure(f"step {target.step} failed; these are the goals `{one_line(target.tactic, 60)}` was applied to",
                              shape_error(target.error), where=at, goal=texts, step=target.step, goals=texts,
                              next=[f"proof_step({_q(rec.id)}, tactic) retries from here"])
            elided = [h for r in rendered for h in r.elided]
            if elided:
                out["elided"] = elided
                out["next"].append(f"budget=... or select=\"{','.join(elided[:3])}\" shows what was elided")
            if n > 1:
                out["goal_shapes"] = [goal_shape(g) for g in target.goals]
            return out

    @staticmethod
    def _baseline(rec: SessionRecord, target: Step, *, explicit: bool) -> list[IrisGoal] | None:
        if target.step == 0:
            return None
        base = target.step - 1
        if not explicit and rec.seen_step is not None and rec.seen_step < target.step:
            base = rec.seen_step
        prev = rec.trace.step_at(base)
        return list(prev.goals) if prev is not None else None

    @_guard(lost=True)
    def proof_trace(
        self, file: str, lemma: str, script: list[str] | None = None, *, incremental: bool = True,
        events: str = "near",
    ) -> dict[str, Any]:
        if events not in TRACE_EVENTS:
            message = f"events={events!r}; one of {', '.join(TRACE_EVENTS)}"
            return failure(message, message, next=[f"events is one of {', '.join(TRACE_EVENTS)}"])
        path = self._file(file)
        tactics = list(script) if script is not None else None
        places = None
        if tactics is None:
            own = proof_script(read_text(path), lemma)
            if own is None:
                return failure(f"{file}: {lemma} has no proof; pass a script", f"{file}: {lemma} has no proof; pass a script",
                               where=self._lemma_where(path, lemma),
                               next=[f"proof_trace({_q(self._rel(path))}, {_q(lemma)}, script=[...])"])
            tactics, places = own
        return self._trace(path, lemma, tactics, places, incremental=incremental, events=events)

    def _trace(self, path: Path, lemma: str, tactics: list[str], places: list[SentenceAt] | None,
               *, incremental: bool, events: str = "near") -> dict[str, Any]:
        """Replay ``tactics``, reusing the last trace's states up to the first changed sentence (D5)."""
        key = replay_key(path, lemma, stub_prefix=True, workspace=self._root_for(path))
        session, tracer, _ = self._new_session(path, lemma, reflect=False, fast=True)
        entry = self.replays.get(key) if incremental else None
        reused = tracer.resume(entry, tactics) if entry is not None else None
        if reused is None:
            try:
                tracer.start()
            except StartFailed as exc:
                session.close()
                return self._start_failure(exc, path, lemma)
            except BaseException:
                session.close()
                raise
        rec = self._register(session, tracer, None)
        k = reused or 0
        with rec.lock:
            try:
                tracer.run_script(tactics[k:], locations=places[k:] if places is not None else None)
            except StateError:
                if reused is None:
                    raise
                # The process went away under the reused states: forget them and run in full, once.
                self.replays.drop(key)
                self._drop(rec)
                return self._trace(path, lemma, tactics, places, incremental=False, events=events)
            self.replays.put(key, tracer.replay_entry())
            return self._trace_result(rec, path, lemma, reused=reused, saved_ms=entry.saved_ms(k) if entry and reused is not None else 0,
                                      events=events)

    @staticmethod
    def _trace_events(trace: Any, end: int, mode: str) -> tuple[list[str], list[str]]:
        """The rendered events ``mode`` keeps, and the warnings (with their steps), for a trace ending at ``end``."""
        warnings = [f"step {getattr(e, 'step', '?')}: {w}" for e in trace.events for w in step_warnings([e])]
        if mode == "all":
            kept = list(trace.events)
        elif mode == "near":
            kept = [e for e in trace.events if (at := getattr(e, "step", None)) is not None and at > end - TRACE_EVENT_WINDOW]
        else:
            kept = []
        return [e.render() for e in kept], warnings[:TRACE_WARNINGS]

    def _trace_result(self, rec: SessionRecord, path: Path, lemma: str, *, reused: int | None, saved_ms: int,
                      events: str = "near") -> dict[str, Any]:
        trace = rec.trace
        final = trace.final
        sid, file = rec.id, self._rel(path)
        n = final.step if final is not None else 0
        k = reused or 0
        shown, warnings = self._trace_events(trace, trace.failed_at if trace.failed_at is not None else n, events)
        fields: dict[str, Any] = {
            "session": sid,
            # The number of sentences run, the failed one included: the same
            # numbering as `proof_state`'s `step` (0 is the root state).
            "steps": n,
            "finished": trace.finished,
            "error": shape_error(trace.error) if trace.error else None,
            "events": shown,
            "events_total": len(trace.events),
            "warnings": warnings,
            # Incremental replay: the first sentence actually re-run (0: from `start`,
            # nothing reused; k+1: the root and k sentences were the last trace's).
            "replayed_from": k + 1 if reused is not None else 0,
            "reused_steps": k,
            "saved_ms": saved_ms,
        }
        reuse = f" (reused {k} step{'s' if k != 1 else ''}, ~{saved_ms / 1000:.1f} s saved)" if reused is not None else ""
        failed = trace.step_at(trace.failed_at) if trace.failed_at is not None else None
        info = trace.failure()
        if info is not None and failed is not None:
            # Where and what, without a follow-up call: the failing sentence, its
            # place in the file (when the script is the file's own proof), the
            # error with its cause kept, and the goals it was applied to.
            last = rec.tracer.last_result
            timed_out = bool(last is not None and last.timed_out) or _is_timeout(trace.error)
            info["error"] = shape_error(info["error"])
            if info.get("line") is not None:
                info["file"] = file
            met = [r.text for r in self._render(rec, failed.goals, diff_only=False, at=failed)]
            dx = self._diagnosis(failed.tactic, trace.error, list(failed.goals))
            info["diagnosis"] = dx.pop("diagnosis")
            info.update(dx)
            info["timed_out"] = timed_out
            rec.seen_step = failed.step
            fields["failure"] = info
            place = (f"edit {file}:{info['line']}" if info.get("line") is not None
                     else f"change sentence {failed.step} of `script`")
            fields.pop("error")
            # `error` and `goal` are the block's; `failure` does not repeat them (issue 20).
            error = info.pop("error")
            out = failure(
                (trace.failure_note() or "stopped") + reuse,
                error,
                where=where(file=file, line=info.get("line"), column=info.get("column"), sentence=failed.tactic,
                            step=failed.step),
                goal=met,
                next=[f"proof_step({_q(sid)}, replacement) -- the session is at the state before `{one_line(failed.tactic, 60)}`",
                      f"or {place} and proof_trace({_q(file)}, {_q(lemma)}) again: only the sentences from the edit on rerun"],
                timed_out=timed_out,
                **fields,
            )
            if len(failed.goals) > 1:
                out["goal_shapes"] = [goal_shape(g) for g in failed.goals]
            self._events_hint(out, sid, events)
            return self._sections(out, SectionContext("proof_trace", rec, failed.tactic, list(failed.goals), None, failed, False,
                                                      list(trace.events)))
        goals = list(final.goals) if final is not None else []
        if trace.finished:
            what, goal, hints = f"replayed {n} sentence{'s' if n != 1 else ''}: proof finished", None, self._finished_next(rec)
        else:
            what = f"replayed {n} sentence{'s' if n != 1 else ''}; {len(goals)} goal{'s' if len(goals) != 1 else ''} remain"
            goal = [r.text for r in self._render(rec, goals, diff_only=False, at=final)] if goals else None
            hints = [f"proof_step({_q(sid)}, tactic) continues from the end of the script"]
        if fields["warnings"]:
            hints.insert(0, "read `warnings`: a step succeeded in a way that is often a mistake")
        if final is not None:
            rec.seen_step = final.step
        out = result(True, what + reuse, where=where(file=file, step=n), goal=goal, next=hints, **fields)
        if len(goals) > 1:
            out["goal_list"] = goal_list([], goals)
        self._events_hint(out, sid, events)
        prev = trace.step_at(n - 1) if n > 0 else None
        return self._sections(out, SectionContext("proof_trace", rec, final.tactic if final and n else None,
                                                  list(prev.goals) if prev else [], goals, final, True, list(trace.events)))

    @staticmethod
    def _events_hint(out: dict[str, Any], sid: str, mode: str) -> None:
        if len(out["events"]) < out["events_total"]:
            which = f"the last {TRACE_EVENT_WINDOW} steps'" if mode == "near" else "no"
            out["next"].append(f"`events` has {which} ledger events of {out['events_total']}: "
                               f'proof_ledger({_q(sid)}, "events") has them all')

    @_guard(lost=True)
    def proof_close(self, session: str) -> dict[str, Any]:
        """Forget a session and let go of its statements-only twin (the last user removes it)."""
        with self._lock:
            rec = self._sessions.pop(session, None)
        if rec is None:
            raise UsageError(f"no session {session!r}; open sessions: {', '.join(self.sessions) or 'none'}")
        rec.session.close()
        return result(True, f"closed {session}", closed=session, sessions=self.sessions)

    @_guard(lost=True)
    def proof_ledger(
        self, session: str, query: str, *, hyp: str | None = None, step: int | None = None
    ) -> dict[str, Any]:
        rec = self.record(session)
        with rec.lock:
            trace: Any = rec.trace  # the queries take anything with .steps/.events (TraceLike)
            at = where(file=self._rel(rec.session.source_file), step=step)
            if query in ("where_did_it_go", "blame") and not hyp:
                return failure("hyp is required", "hyp is required", where=at,
                               next=[f'proof_ledger({_q(rec.id)}, {_q(query)}, hyp="H")'])
            fields: dict[str, Any]
            if query == "where_did_it_go":
                fields = {"answer": render_provenance(where_did_it_go(trace, str(hyp)))}
            elif query == "blame":
                at = where(file=self._rel(rec.session.source_file), step=step if step is not None else default_blame_step(trace))
                fields = {"answer": render_blame(blame(trace, at["step"] if at else 0, str(hyp)))}
            elif query == "leftovers":
                hyps = leftovers(trace, step)
                fields = {"answer": render_leftovers(hyps), "count": len(hyps)}
            elif query == "unused_at_qed":
                fields = {"answer": render_unused(unused_at_qed(trace))}
            elif query == "events":
                fields = {"answer": render_events(trace.events)}
            else:
                message = f"unknown query {query!r}; one of {', '.join(LEDGER_QUERIES)}"
                return failure(message, message, next=[f"query is one of {', '.join(LEDGER_QUERIES)}"])
            return result(True, fields["answer"], where=at, **fields)

    @_guard(lost=True)
    def proof_try(self, session: str, tactics: list[str]) -> dict[str, Any]:
        """Speculative fan-out: near-free on a flat-rate tier, so spend it (PLAN.md 7).

        Each survivor says how many goals it leaves and, when it changes the goals,
        lists them in order with their shapes -- the side goal a candidate leaves is
        often what decides between two survivors.
        """
        rec = self.record(session)
        given = list(tactics)
        batch = [terminate_sentence(str(t)) for t in given[:MAX_TRY]]
        sid = rec.id
        with rec.lock:
            before = rec.final_goals
            results = rec.session.try_many(batch)
            rows: list[dict[str, Any]] = []
            for t, r in zip(batch, results, strict=True):
                row: dict[str, Any] = {
                    "tactic": t,
                    "ok": r.ok,
                    "error": shape_error(r.error, TRY_ERROR_CHARS),
                    "proof_finished": r.proof_finished,
                    "state_id": r.state_id,
                }
                if r.timed_out:
                    row["timed_out"] = True
                if r.ok and r.state is not None and not r.proof_finished:
                    after = rec.tracer.goals_at(r.state)
                    row["goals"] = len(after)
                    change = goal_list(before, after)
                    if change is not None:
                        row["goal_list"] = change
                    elif after:
                        row["shape"] = goal_shape(after[0])
                rows.append(row)
        survivors = [row["tactic"] for row in rows if row["ok"]]
        for row in rows:
            if not row["ok"] and survivors:
                # What separates it from a near-identical survivor (session 3, issue 22).
                close = closest_survivor(row["tactic"], survivors)
                if close is not None:
                    close.pop("changed_tokens")
                    row["vs_survivor"] = close
        finishing = [row["tactic"] for row in rows if row["ok"] and row["proof_finished"]]
        what = f"{len(survivors)}/{len(batch)} candidates survive" + (f"; {len(finishing)} finish the proof" if finishing else "")
        best = finishing[0] if finishing else (survivors[0] if survivors else None)
        hints = ([f"proof_step({_q(sid)}, {_q(best)}) commits a survivor"] if best is not None
                 else ["no candidate survived: read each row's `error`, or proof_state for the goal"])
        final = rec.trace.final
        out = result(bool(survivors), what, where=where(file=self._rel(rec.session.source_file),
                                                        step=final.step if final is not None else None),
                     next=hints, survivors=survivors, results=rows)
        if len(given) > MAX_TRY:
            out["dropped"] = len(given) - MAX_TRY
        return out

    @_guard(lost=True)
    def proof_destruct(
        self,
        session: str,
        hyp: str,
        *,
        spec: dict[str, Any] | None = None,
        apply: bool = False,
    ) -> dict[str, Any]:
        """Intent in, syntax out: no model hand-assembles a nested pattern (PLAN.md 7)."""
        rec = self.record(session)
        sid = rec.id
        with rec.lock:
            before = rec.final_goals
            goal = before[0] if before else None
            if goal is None:
                return failure("no goal", "no goal", next=["the proof is finished: nothing to destruct"])
            h = goal.by_id(hyp)
            if h is None:
                available = [x.id for x in goal.ipm_hyps]
                return failure(f'no hypothesis named "{hyp}"', f'no hypothesis named "{hyp}"',
                               next=[f"one of: {', '.join(available) or '(none)'}"], available=available)
            skel = parse_skeleton(h.prop)
            if spec is not None:
                if not isinstance(spec, dict):
                    raise UsageError("spec must be a JSON object: {names, pure, intuit, binders}")
                d = compile_spec(DestructSpec.from_json(spec), skel)
            else:
                d = compile_auto(skel, hyp, taken=[x.id for x in goal.all_hyps if x.id != hyp])
            tactic = d.idestruct(hyp)
            fields: dict[str, Any] = {
                "tactic": tactic,
                "pattern": d.pattern_text,
                "binders": list(d.binders),
                "skeleton": skel.render(),
            }
            if not apply:
                return result(True, f"compiled {tactic}", next=[f"proof_step({_q(sid)}, {_q(tactic)}) runs it",
                                                               "or call again with apply=true"], **fields)
            step = rec.tracer.step(tactic)
            if not step.ok:
                # The real error, diagnosed against the goal it was applied to, not
                # against the skeleton the compiled pattern came from (a tautology).
                last = rec.tracer.last_result
                out = self._step_failure(rec, tactic, before, step.error, step=step,
                                         timed_out=bool(last and last.timed_out), tool="proof_destruct")
                return {**out, **fields}
            out = self._step_success(rec, tactic, before, step, tool="proof_destruct")
            out["error"] = None
            return {**out, **fields}

    @_guard(lost=True)
    def proof_expect(
        self, session: str, expected: str, *, hyps: dict[str, str] | None = None, strict: bool = True
    ) -> dict[str, Any]:
        """Skeleton shape assertion (MF5): does the goal have this shape?  Never moves the session."""
        if hyps is not None and not isinstance(hyps, dict):
            raise UsageError('hyps must be a JSON object: {"H": "expected prop"}')
        rec = self.record(session)
        with rec.lock:
            report = expect_shape(rec.session, expected, hyps=hyps or None, strict=strict).to_json()
            final = rec.trace.final
        ok = bool(report.pop("ok"))
        at = where(file=self._rel(rec.session.source_file), step=final.step if final is not None else None)
        if ok:
            return result(True, "the goal has the expected shape", where=at, **report)
        hints = ["`parts[].diffs` name the minimal differing subterms and their path: restate them in the goal's form"]
        if any(p.get("verdict") == "convertible" for p in report.get("parts", [])):
            hints.append("convertible only: a tactic matching syntactically will not see it; strict=false accepts it")
        return result(False, one_line(report.get("answer") or "the goal does not have the expected shape"),
                      where=at, next=hints, **report)

    @_guard(lost=True)
    def proof_inv(self, session: str, inv: str, *, apply: bool = False) -> dict[str, Any]:
        """The ``iInv`` that opens an invariant, from its definition (MF6); ``apply`` runs it."""
        rec = self.record(session)
        sid = rec.id
        with rec.lock:
            before = rec.final_goals
            r = invariant_pattern(rec.session, inv)
            fields = r.to_json()
            fields.pop("ok", None)
            error = fields.pop("error", None)
            if not r.ok:
                return failure(f"could not open {inv}: {one_line(r.error or r.explanation)}", error,
                               next=["read `explanation`; `side_goals` names what the mask or expression lacks"],
                               **fields)
            if not apply:
                return result(True, f"opens with {r.tactic}", next=[f"proof_step({_q(sid)}, {_q(r.tactic)}) runs it",
                                                                   "or call again with apply=true"], **fields)
            step = rec.tracer.step(r.tactic)
            fields["applied"] = step.ok
            if not step.ok:
                last = rec.tracer.last_result
                out = self._step_failure(rec, r.tactic, before, step.error, step=step,
                                         timed_out=bool(last and last.timed_out), tool="proof_inv")
                return {**out, **fields}
            out = self._step_success(rec, r.tactic, before, step, tool="proof_inv")
            return {**out, **fields}

    @_guard(lost=False)
    def diagnosis_feedback(
        self, diagnosis_id: str, *, correct: bool = False, note: str = "", actual: str | None = None
    ) -> dict[str, Any]:
        """The agent's verdict on a diagnosis's repair class, for tuning the heuristics (D2)."""
        out = record_feedback(self.workspace, diagnosis_id, correct=correct, note=note, actual=actual)
        if out.get("ok"):
            rest = {k: v for k, v in out.items() if k != "ok"}
            return result(True, f"recorded: diagnosis {diagnosis_id} was {'right' if correct else 'wrong'}", **rest)
        message = str(out.get("error") or "feedback not recorded")
        return failure(message, message, next=["pass the `diagnosis_id` a failed proof_step returned"])

    # -- search -----------------------------------------------------------------
    @_guard(lost=True)
    def premise_search(
        self,
        session: str,
        *,
        pattern: str | None = None,
        query: str | None = None,
        scope: str | None = None,
    ) -> dict[str, Any]:
        rec = self.record(session)
        roots = [rec.session.pool.workspace] if rec.session.pool is not None else [self.workspace]
        with rec.lock:
            found = premise_search(rec.session, pattern=pattern or "", query=query or "", scope=scope or "", roots=roots)
        hints = [] if found.count else ["widen the pattern (`_` for holes), or search by name with `query`"]
        return result(True, f"{found.count} premise{'s' if found.count != 1 else ''} found", next=hints,
                      answer=found.answer, count=found.count)

    @_guard(lost=True)
    def notation_resolve(self, session: str, token: str) -> dict[str, Any]:
        rec = self.record(session)
        with rec.lock:
            answer = notation_resolve(rec.session, token)
        return result(True, answer or f"nothing known about {token}", answer=answer)

    # -- integrity --------------------------------------------------------------
    @_guard(lost=False)
    def verify_node(self, file: str, lemma: str, body: str, *, plan: str | None = None) -> dict[str, Any]:
        """The deterministic gate as a tool (PLAN.md 8.7): the same ``Gate.run`` the scheduler runs.

        Statements-only prefix (sound: ``Qed`` is opaque) so a call costs seconds, not a
        full recompile; the plan path is resolved against the workspace, not the cwd.
        Bounded by :data:`VERIFY_TIMEOUT`; running out is ``timed_out``, never a verdict
        on the body.
        """
        from pcp.orch.gate import Gate  # lazy: pcp-state never needs the orchestrator

        path = self._file(file)
        nodes = parse_plan(read_text(self._resolve(plan))) if plan else []
        gate = Gate(Development(path), timeout=VERIFY_TIMEOUT).run(
            lemma, nodes, target_body=strip_proof_wrapper(body), truncate=True, stub_prefix=True
        )
        report = gate.render()
        timed_out = gate.infrastructure and "timed out" in report
        at = self._lemma_where(path, lemma)
        fields: dict[str, Any] = {"report": report, "assumptions": gate.assumptions}
        if gate.ok:
            return result(True, one_line(report), where=at, next=["write the body into the file"], **fields)
        failed = "; ".join(one_line(c.render(), 160) for c in gate.failures) or one_line(report)
        hints = (["the gate could not finish (`timed_out`): not a verdict on the body; retry, or check the file compiles"]
                 if timed_out else ["fix what the failed checks name (`report`), then verify_node again"])
        return failure(one_line(report) + f": {failed}", shape_error(failed), where=at, next=hints,
                       timed_out=timed_out, infrastructure=gate.infrastructure, **fields)


# ------------------------------------------------------------------ MCP adapter


def _dumps(obj: Any) -> str:
    return json.dumps(obj, default=str, ensure_ascii=False)


def tool_functions(server: PcpServer) -> dict[str, Callable[..., str]]:
    """The tools as plain functions returning JSON strings, keyed by name.

    Their docstrings are the descriptions the model reads; the ``""``/``-1`` sentinels
    exist because MCP clients send every optional argument.  ``server`` is only touched
    when a function is called (``pcp tools list`` passes ``None`` to read signatures).
    """

    def proof_open(file: str, lemma: str, reflect: bool = False, fast: bool = True) -> str:
        """Open a lemma for stepping; returns a session id and its Iris proof state, per hypothesis.

        Every pcp tool answers {"ok", "what" (one line), "where" {file, line, column, sentence,
        step}, "goal" (rendered goals), "next" (concrete next calls), ...}; a failure adds
        "error" (cause kept), "timed_out", or "lost".  `file` is relative to the workspace.
        `fast` (default) elaborates only the statements before the lemma -- other proofs cannot
        affect its goal -- and is seconds instead of minutes.  `reflect` reads hypotheses
        through the Ltac2 dump (exact, layout-independent)."""
        return _dumps(server.proof_open(file, lemma, reflect=reflect, fast=fast))

    def proof_step(session: str, tactic: str, mode: str = "commit", select: str = "", budget: int = DEFAULT_STEP_BUDGET) -> str:
        """Run one tactic sentence from the current state and see exactly what changed: no file edit, no recompile.

        `mode="speculative"` does not move the session.  When the goals change, `goal_list` lists
        them in order with their shapes (new / kept / focused, and what closed).  `warnings`
        flags a success that is often a mistake (e.g. a fraction split); `effects` says what the
        step did to the goal.  A failure carries the step, the goal it met, the error and a
        structured diagnosis with its repair class and confidence -- read it before retrying.
        Several sentences (`"wp_store. wp_pures."`) run one by one in commit mode: a failure names
        the failing sentence (`chain`), and the ones before it stay committed."""
        return _dumps(server.proof_step(session, tactic, mode=mode, select=select or None, budget=budget))

    def proof_state(
        session: str, step: int = -1, select: str = "", mode: str = "full", budget: int = DEFAULT_STATE_BUDGET,
        diff_only: bool = True, relevance: bool = False,
    ) -> str:
        """Render the goal at a step (default: current) under a token budget; it says what it elided.

        Diff-only by default: what changed since you last looked, plus a manifest of what did
        not.  `select` (e.g. "HP,H*,spatial,mentions:γ,head:WP") always shows what it names,
        with its implicit arguments; `mode` is full | folded | summary | hash-only.  Hidden
        coercions are spelled out (`↳ with coercions`) and equalities carry `[= at T]`."""
        return _dumps(server.proof_state(
            session, step=None if step < 0 else step, select=select or None, mode=mode, budget=budget,
            diff_only=diff_only, relevance=relevance,
        ))

    def proof_trace(
        file: str, lemma: str, script: list[str] | None = None, incremental: bool = True, events: str = "near",
    ) -> str:
        """Replay a script (default: the lemma's own proof) tactic by tactic; returns the ledger event log and a session.

        On a failure, `failure` (and `where`) has the failing `sentence`, its `line`/`column` in the
        file (default script only), the error, a diagnosis and the goal it was applied to; its
        `step` is the number `proof_state` uses (0 = root, k = after the k-th sentence).  After an
        edit, only the sentences from the first changed one rerun (`replayed_from`, `saved_ms`);
        `incremental=false` forces a full run.  `events` is near (default: the ledger events of the
        last steps before the end or the failure) | all | none; proof_ledger(session, "events") has
        the whole log."""
        return _dumps(server.proof_trace(file, lemma, script, incremental=incremental, events=events))

    def proof_ledger(session: str, query: str, hyp: str = "", step: int = -1) -> str:
        """Ask the resource ledger: where did a hypothesis go, what consumed it, what is still live, what was never used.

        `query` is one of where_did_it_go | blame | leftovers | unused_at_qed | events; `hyp` is
        required for the first two; `blame` takes the failing `step` (default: the step that failed)."""
        return _dumps(server.proof_ledger(session, query, hyp=hyp or None, step=None if step < 0 else step))

    def proof_try(session: str, tactics: list[str]) -> str:
        """Run up to 20 candidate tactics speculatively from the current state and report which survive.

        Each surviving row says how many goals it leaves and, when it changes them, lists them in
        order with their shapes -- a side goal is often what decides between two survivors.  A failed
        row that is a near variant of a survivor says how they differ (`vs_survivor`)."""
        return _dumps(server.proof_try(session, tactics))

    def proof_destruct(session: str, hyp: str, spec: dict[str, Any] | None = None, apply: bool = False) -> str:
        """Compile the iDestruct pattern for a hypothesis from its connective structure -- never hand-write one.

        Without `spec` the pattern is synthesised; with `spec` ({"names": [...], "pure": [...],
        "intuit": [...], "binders": [...]}, names may nest) it is compiled from your intent.
        `apply` runs it and returns the new goal, or a diagnosis of exactly where it diverged."""
        return _dumps(server.proof_destruct(session, hyp, spec=spec, apply=apply))

    def premise_search(session: str, pattern: str = "", query: str = "", scope: str = "") -> str:
        """Search for lemmas *at this goal* instead of guessing a name.

        `pattern` is a term pattern ("_ ↦ _"), `query` whitespace-separated name substrings
        ("add_comm -assoc"), `scope` a module path; falls back to a source grep."""
        return _dumps(server.premise_search(session, pattern=pattern or None, query=query or None, scope=scope or None))

    def notation_resolve(session: str, token: str) -> str:
        """What a notation means at this state, what it unfolds to, and which IPM tactics apply to it."""
        return _dumps(server.notation_resolve(session, token))

    def verify_node(file: str, lemma: str, body: str, plan: str = "") -> str:
        """Run the deterministic gate on a proof body: the same check `pcp check` and the scheduler run.

        `body` is the tactic script only (a Proof./Qed. wrapper is tolerated); `plan` is a
        path to a plan .v of child statements, relative to the workspace."""
        return _dumps(server.verify_node(file, lemma, body, plan=plan or None))

    def proof_close(session: str) -> str:
        """Close a session you are done with: frees its slot and removes its scratch twin when no other session uses it."""
        return _dumps(server.proof_close(session))

    def proof_expect(session: str, expected: str, hyps: dict[str, str] | None = None, strict: bool = True) -> str:
        """Assert the goal's shape before relying on it, e.g. "WP ! #(l +ₗ 1) {{ v, Φ v }}".

        `expected` is the conclusion, or a whole goal with `"H" : P` lines and the `---∗`
        separator; `_` and `?x` are holes (a repeated ?x must be the same term).  Rocq elaborates
        it in the current state and checks unification and syntactic equality; a mismatch
        reports the minimal differing subterms and their path.  `hyps` maps hypothesis names to
        expected props; `strict=false` accepts a match up to conversion.  Never moves the session."""
        return _dumps(server.proof_expect(session, expected, hyps=hyps or None, strict=strict))

    def proof_inv(session: str, inv: str, apply: bool = False) -> str:
        """Generate the iInv tactic that opens an invariant from its definition -- never hand-write one.

        `inv` is the invariant hypothesis ("Hinv") or a predicate/namespace it mentions.  The
        body is unfolded in the current state; `>` goes exactly on the conjuncts Rocq proves
        Timeless, pure conjuncts become `>%H`, names are fresh.  The tactic is checked
        speculatively; `apply` runs it."""
        return _dumps(server.proof_inv(session, inv, apply=apply))

    def diagnosis_feedback(diagnosis_id: str, correct: bool = False, note: str = "", actual: str = "") -> str:
        """Tell pcp whether a failure's diagnosis named the right repair class; call it when it was wrong.

        `diagnosis_id` is from the failed result; `actual` is the class that did work, one of
        bullet, rewrite-before-frame, check-lemma-premise, fix-pattern, fix-intro-pattern,
        missing-hypothesis, fix-apply, close-goal, mask, wp-next-step, goal-shape, unknown."""
        return _dumps(server.diagnosis_feedback(diagnosis_id, correct=correct, note=note, actual=actual or None))

    fns = {
        fn.__name__: fn
        for fn in (
            proof_open, proof_step, proof_state, proof_trace, proof_ledger, proof_try, proof_destruct,
            premise_search, notation_resolve, verify_node, proof_close, proof_expect, proof_inv,
            diagnosis_feedback,
        )
    }
    assert tuple(fns) == TOOLS, "tool_functions must register exactly pcp.mcp.names.TOOLS, in order"
    return fns


def make_mcp(name: str = MCP_SERVER_NAME) -> Any:
    """An MCP server object for whichever SDK generation is installed.

    ``FastMCP`` (mcp 1.x) became ``MCPServer`` (mcp 2.x) with the same decorator shape.
    ``import mcp`` succeeds on both, so only constructing the server proves anything --
    ``pcp doctor`` calls this for that reason.  ``serverInfo.version`` is set to ours
    when the installed SDK accepts it, so a client's "connected to pcp" line names a
    real, bumpable version instead of the SDK's blank default.
    """
    try:
        from mcp.server.mcpserver import MCPServer  # mcp >= 2

        return MCPServer(name, version=__version__)
    except ImportError:
        pass
    try:
        from mcp.server.fastmcp import FastMCP  # type: ignore[attr-defined]  # mcp < 2

        try:
            return FastMCP(name, version=__version__)
        except TypeError:
            return FastMCP(name)  # older mcp<2 releases had no `version` kwarg
    except ImportError as exc:
        raise ToolchainError(NO_SDK_MESSAGE) from exc


def served_tool_names(mcp: Any) -> list[str]:
    """The names an MCP server object will list, on either SDK generation."""
    manager = getattr(mcp, "_tool_manager", None)
    if manager is not None and hasattr(manager, "list_tools"):
        return [t.name for t in manager.list_tools()]
    import anyio

    return [t.name for t in anyio.run(mcp.list_tools)]


def register(server: PcpServer, mcp: Any) -> Any:
    """Attach every tool to ``mcp`` and check the served list is exactly :data:`TOOLS`."""
    for name, fn in tool_functions(server).items():
        mcp.tool(name=name, description=inspect.getdoc(fn))(fn)
    served = served_tool_names(mcp)
    if served != list(TOOLS):
        raise AssertionError(f"served tools {served} != {list(TOOLS)}")
    return mcp


def build_server(
    workspace: str | Path, *, pool_size: int = 2, coq_root: str | Path | None = None
) -> tuple[PcpServer, Any]:
    """The implementations plus the MCP server they are registered on."""
    server = PcpServer(workspace, pool_size=pool_size, coq_root=coq_root)
    return server, register(server, make_mcp(MCP_SERVER_NAME))


# ----------------------------------------------------------------- stdio entry


class ParentWatch(threading.Thread):
    """Die with the client, without ``PR_SET_PDEATHSIG`` (ARCHITECTURE.md 6).

    A stdio server notices its client leaving as EOF on stdin -- only if it is ever
    back in the read loop; one server sat inside a runaway petanque call and outlived
    its worker by hours.  The death signal is bound to the *thread* that set it and
    would fire whenever an anyio worker thread exited, so instead a thread polls
    ``getppid``: reparenting to init (1) or to a subreaper -- any change from the
    original parent -- means the client is gone.
    """

    def __init__(self, on_orphan: Callable[[], None], *, interval_s: float = PARENT_WATCH_INTERVAL_S) -> None:
        super().__init__(name="pcp-parent-watch", daemon=True)
        self.on_orphan = on_orphan
        self.interval_s = interval_s
        self.original = os.getppid()
        self.fired = False

    @staticmethod
    def orphaned(original: int) -> bool:
        ppid = os.getppid()
        return ppid == 1 or ppid != original

    def run(self) -> None:
        while not self.fired:
            time.sleep(self.interval_s)
            if self.orphaned(self.original):
                self.fired = True
                self.on_orphan()


def run_stdio(workspace: Path, *, pool_size: int = 2) -> int:
    """Serve the tools over MCP stdio; 0 ok, 2 no SDK, 1 the server crashed.

    Nothing but the protocol goes to stdout: a stray ``print`` desyncs the client into
    reporting the server as simply "failed".  All logging goes to stderr.
    """
    if os.getppid() == 1:
        return 0
    logging.basicConfig(stream=sys.stderr, level=logging.WARNING, format="pcp mcp: %(levelname)s %(message)s")
    try:
        server, mcp = build_server(workspace, pool_size=pool_size)
    except ToolchainError as exc:
        print(str(exc), file=sys.stderr)
        return 2

    def on_orphan() -> None:
        server.terminate()
        os._exit(0)

    ParentWatch(on_orphan).start()
    try:
        mcp.run()
    except Exception as exc:  # noqa: BLE001 -- report on stderr, never on stdout
        print(f"pcp mcp failed: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1
    finally:
        server.close()
    return 0
