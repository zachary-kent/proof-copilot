"""The MCP tool surface: transport-free, locked, and honest about lost state (PLAN.md 7).

Ten tools behind a hard cap (:data:`pcp.mcp.names.TOOLS`).  The implementations live on
:class:`PcpServer`, which knows nothing about MCP, so the model, the CLI, the tests and
the ablation harness call exactly the same code -- an ablation over a different code
path measures nothing (PLAN.md 13).  :func:`register` is the mechanical adapter onto
whichever ``mcp`` SDK generation is installed.

Why it is locked: the ``mcp`` SDK runs synchronous tools on worker threads and a
client issues independent tool calls in parallel.  v1 minted duplicate session ids and
interleaved ``proof_step``/``proof_try`` on one session (ARCHITECTURE.md 8, "state sent
to the wrong process").  Here the session table is mutated under one lock and every
session carries its own lock, so two calls on one session serialise while two sessions
pinned to two ``pet`` processes proceed concurrently.

Why a "lost" shape exists: a process that died or restarted is a *transport* fact, not
a wrong tactic (PLAN.md 4.4).  Any tool that meets a ``StateError`` answers
``{"ok": false, "lost": true, "action": "call proof_open again"}`` and never presents
it as a tactic failure.  Every tool answers JSON for every input: a ``PcpError`` is an
``{"error": ...}`` object and an unexpected exception is logged to stderr and returned
as ``{"error": "<Type>: <msg>"}`` -- the server never dies from one bad call.

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

from pcp.errors import PcpError, StateError, ToolchainError, UsageError
from pcp.mcp.names import MAX_TOOLS, MCP_SERVER_NAME, TOOLS
from pcp.rocq.assemble import Development, parse_plan
from pcp.rocq.body import strip_proof_wrapper
from pcp.rocq.decls import find_block
from pcp.state.diagnose import diagnose
from pcp.state.ipm.model import IrisGoal, Step
from pcp.state.ipm.pattern import DestructSpec, compile_auto, compile_spec
from pcp.state.ipm.reflect import REQUIRE, Reflector, build_idump, env_with_idump
from pcp.state.ipm.skeleton import parse_skeleton
from pcp.state.ledger.diff import attach
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
from pcp.state.pool import SessionPool
from pcp.state.render import Rendered, render_goal
from pcp.state.search import notation_resolve, premise_search
from pcp.state.session import ProofSession
from pcp.state.trace import Trace, Tracer
from pcp.util.io import read_text
from pcp.util.proc import kill_tree

assert len(TOOLS) <= MAX_TOOLS, "the tool surface is capped (PLAN.md 7)"

_log = logging.getLogger("pcp.mcp")

LOST_ACTION = "call proof_open again"
#: petanque caps a speculative fan-out at about twenty states (PLAN.md 7).
MAX_TRY = 20
DEFAULT_STEP_BUDGET = 3000
DEFAULT_STATE_BUDGET = 4000
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


def _guard(*, lost: bool) -> Callable[[Callable[..., dict[str, Any]]], Callable[..., dict[str, Any]]]:
    """Every tool answers a JSON object, whatever happens (see the module docstring)."""

    def deco(fn: Callable[..., dict[str, Any]]) -> Callable[..., dict[str, Any]]:
        @functools.wraps(fn)
        def wrapper(self: PcpServer, *args: Any, **kwargs: Any) -> dict[str, Any]:
            try:
                return fn(self, *args, **kwargs)
            except StateError as exc:
                if lost:
                    return {"ok": False, "error": str(exc), "lost": True, "action": LOST_ACTION}
                return {"error": str(exc)}
            except PcpError as exc:
                return {"error": str(exc)}
            except Exception as exc:  # noqa: BLE001 -- the server never dies from one bad call
                _log.exception("tool %s failed", fn.__name__)
                return {"error": f"{type(exc).__name__}: {exc}"}

        return wrapper

    return deco


def default_blame_step(trace: Trace) -> int:
    """The step ``blame`` asks about when none is given: the failed one, else the next one.

    Steps are numbered ``0..n``; v1 defaulted to ``len(steps)`` even when the trace had
    stopped at a failure, so the report named a step that never ran.
    """
    if trace.failed_at is not None:
        return trace.failed_at
    return trace.final.step + 1 if trace.final is not None else 0


# --------------------------------------------------------------------- server


class PcpServer:
    """The tool implementations.  Thread-safe; every method returns a JSON-shaped dict."""

    def __init__(self, workspace: str | Path, *, pool_size: int = 2, coq_root: str | Path | None = None) -> None:
        self.workspace = Path(workspace).resolve()
        self.pool_size = pool_size
        #: Where ``IDump.vo`` is built for ``reflect=True``.  Absolute, under the
        #: workspace by default -- never relative to the process's cwd (legacy bug).
        self.coq_root = Path(coq_root).resolve() if coq_root is not None else self.workspace / ".pcp" / "coq"
        self.pool = SessionPool(self.workspace, size=pool_size)
        self._reflect_pool: SessionPool | None = None
        self._reflect_lock = threading.Lock()
        self._lock = threading.RLock()
        self._sessions: dict[str, SessionRecord] = {}
        self._n = 0

    # -- lifecycle -------------------------------------------------------------
    def close(self) -> None:
        """Stop every petanque process, waiting for in-flight calls.  Idempotent."""
        self.pool.close()
        with self._reflect_lock:
            if self._reflect_pool is not None:
                self._reflect_pool.close()

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
        with self._reflect_lock:
            return [self.pool] + ([self._reflect_pool] if self._reflect_pool is not None else [])

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
        with self._lock:
            self._n += 1
            rec = SessionRecord(f"s{self._n}", session, tracer, reflector)
            self._sessions[rec.id] = rec
            return rec

    def _resolve(self, file: str | Path) -> Path:
        p = Path(file).expanduser()
        return p.resolve() if p.is_absolute() else (self.workspace / p).resolve()

    def _pool_for(self, *, reflect: bool) -> SessionPool:
        """The reflect pool spawns its processes with ``IDump`` on the load path.

        A ``pet`` captures its environment at spawn, so ``reflect`` cannot be switched on
        for a process that is already running (legacy bug: ``os.environ`` was patched
        after the fact and ``Require Import pcp.IDump`` failed inside ``start``).  Hence a
        second pool whose every process is born with the right env; it costs nothing
        until the first ``reflect=True``.
        """
        if not reflect:
            return self.pool
        with self._reflect_lock:
            if self._reflect_pool is None:
                build_idump(self.coq_root)
                env = env_with_idump(dict(os.environ), self.coq_root)
                self._reflect_pool = SessionPool(self.workspace, size=self.pool_size, env=env)
            return self._reflect_pool

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
    ) -> list[Rendered]:
        """One budgeted render per goal, diffed positionally against ``prev`` (PLAN.md 5).

        Positional: goal ``i`` against the previous goal ``i``; a goal with no
        counterpart renders in full.  v1 diffed every goal against ``prev[0]``.
        """
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
                )
            )
        return out

    @staticmethod
    def _diagnose(tactic: str, error: str | None, before: list[IrisGoal]) -> str:
        """Diagnosis by construction, against the goal the tactic was applied to."""
        return diagnose(tactic, error or "", before[0] if before else None)

    # -- state and trace --------------------------------------------------------
    @_guard(lost=False)
    def proof_open(self, file: str, lemma: str, *, reflect: bool = False, fast: bool = True) -> dict[str, Any]:
        path = self._resolve(file)
        if not path.is_file():
            raise UsageError(f"{file}: no such file (resolved against {self.workspace})")
        pool = self._pool_for(reflect=reflect)
        session = pool.open(path, lemma, pre_commands=REQUIRE if reflect else None, stub_prefix=fast)
        reflector = Reflector(session) if reflect else None
        tracer = attach(Tracer(session, reflector=reflector))
        goals = tracer.start()  # outside the table lock: `petanque/start` takes seconds
        rec = self._register(session, tracer, reflector)
        rec.seen_step = 0
        return {
            "session": rec.id,
            "state_id": rec.trace.steps[0].state_id,
            "goal": [r.text for r in self._render(rec, goals, diff_only=False)],
        }

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
        with rec.lock:
            before = rec.final_goals
            if mode == "speculative":
                result = rec.session.run(tactic, commit=False)
                return {
                    "ok": result.ok,
                    "error": result.error,
                    "loop_of": rec.tracer.step_number(result.loop_of),
                    # Only a failure gets a diagnosis: v1 attached the apply/leftover
                    # paragraphs to successes too and misled the model.
                    "diagnosis": "" if result.ok else self._diagnose(tactic, result.error, before),
                }
            step = rec.tracer.step(tactic)
            if not step.ok:
                return {"ok": False, "error": step.error, "diagnosis": self._diagnose(tactic, step.error, before)}
            rendered = self._render(rec, step.goals, prev=before, select=select, budget=budget)
            rec.seen_step = step.step
            return {
                "ok": True,
                "state_id": step.state_id,
                "proof_finished": rec.trace.finished,
                "loop_of": step.loop_of,
                "ledger": [e.to_json() for e in rec.trace.events_at(step.step)],
                "goal": [r.text for r in rendered],
            }

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
                return {"error": f"no step {step}"}
            prev = self._baseline(rec, target, explicit=step is not None) if diff_only else None
            rendered = self._render(
                rec, target.goals, prev=prev, select=select, mode=mode, budget=budget,
                diff_only=diff_only, relevance=relevance,
            )
            rec.seen_step = target.step
            out: dict[str, Any] = {"step": target.step, "goals": [r.text for r in rendered]}
            elided = [h for r in rendered for h in r.elided]
            if elided:
                out["elided"] = elided
            if not target.ok:
                # A failed step records the goals *before* the tactic; say so rather
                # than let the model believe the tactic applied (legacy bug).
                out["ok"] = False
                out["error"] = target.error
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
    def proof_trace(self, file: str, lemma: str, script: list[str] | None = None) -> dict[str, Any]:
        path = self._resolve(file)
        if not path.is_file():
            raise UsageError(f"{file}: no such file (resolved against {self.workspace})")
        tactics = list(script) if script is not None else None
        if tactics is None:
            block = find_block(read_text(path), lemma)
            if block is None or not block.has_proof:
                return {"error": f"{file}: {lemma} has no proof; pass a script"}
            tactics = block.tactics()
        opened = self.proof_open(file, lemma)
        if "error" in opened:
            return opened
        rec = self.record(opened["session"])
        with rec.lock:
            trace = rec.tracer.run_script(tactics)
            return {
                "session": rec.id,
                "steps": len(trace.steps),
                "finished": trace.finished,
                "error": trace.error,
                "events": [e.render() for e in trace.events],
            }

    @_guard(lost=True)
    def proof_ledger(
        self, session: str, query: str, *, hyp: str | None = None, step: int | None = None
    ) -> dict[str, Any]:
        rec = self.record(session)
        with rec.lock:
            trace: Any = rec.trace  # the queries take anything with .steps/.events (TraceLike)
            if query in ("where_did_it_go", "blame") and not hyp:
                return {"error": "hyp is required"}
            if query == "where_did_it_go":
                return {"answer": render_provenance(where_did_it_go(trace, str(hyp)))}
            if query == "blame":
                at = step if step is not None else default_blame_step(trace)
                return {"answer": render_blame(blame(trace, at, str(hyp)))}
            if query == "leftovers":
                hyps = leftovers(trace, step)
                return {"answer": render_leftovers(hyps), "count": len(hyps)}
            if query == "unused_at_qed":
                return {"answer": render_unused(unused_at_qed(trace))}
            if query == "events":
                return {"answer": render_events(trace.events)}
            return {"error": f"unknown query {query!r}; one of {', '.join(LEDGER_QUERIES)}"}

    @_guard(lost=True)
    def proof_try(self, session: str, tactics: list[str]) -> dict[str, Any]:
        """Speculative fan-out: near-free on a flat-rate tier, so spend it (PLAN.md 7)."""
        rec = self.record(session)
        batch = [str(t) for t in list(tactics)[:MAX_TRY]]
        with rec.lock:
            results = rec.session.try_many(batch)
        return {
            "survivors": [t for t, r in zip(batch, results, strict=True) if r.ok],
            "results": [
                {
                    "tactic": t,
                    "ok": r.ok,
                    "error": (r.error or "")[:300],
                    "proof_finished": r.proof_finished,
                    "state_id": r.state_id,
                }
                for t, r in zip(batch, results, strict=True)
            ],
        }

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
        with rec.lock:
            before = rec.final_goals
            goal = before[0] if before else None
            if goal is None:
                return {"error": "no goal"}
            h = goal.by_id(hyp)
            if h is None:
                return {"error": f'no hypothesis named "{hyp}"', "available": [x.id for x in goal.ipm_hyps]}
            skel = parse_skeleton(h.prop)
            if spec is not None:
                if not isinstance(spec, dict):
                    raise UsageError("spec must be a JSON object: {names, pure, intuit, binders}")
                d = compile_spec(DestructSpec.from_json(spec), skel)
            else:
                d = compile_auto(skel, hyp, taken=[x.id for x in goal.all_hyps if x.id != hyp])
            tactic = d.idestruct(hyp)
            out: dict[str, Any] = {
                "tactic": tactic,
                "pattern": d.pattern_text,
                "binders": list(d.binders),
                "skeleton": skel.render(),
            }
            if not apply:
                return out
            step = rec.tracer.step(tactic)
            out["ok"] = step.ok
            out["error"] = step.error
            if step.ok:
                out["goal"] = [r.text for r in self._render(rec, step.goals, prev=before)]
                rec.seen_step = step.step
            else:
                # The real error, diagnosed against the goal it was applied to -- v1
                # aligned the compiled pattern with the skeleton it came from (a tautology).
                out["diagnosis"] = self._diagnose(tactic, step.error, before)
            return out

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
        with rec.lock:
            result = premise_search(
                rec.session, pattern=pattern or "", query=query or "", scope=scope or "", roots=[self.workspace]
            )
        return {"answer": result.answer, "count": result.count}

    @_guard(lost=True)
    def notation_resolve(self, session: str, token: str) -> dict[str, Any]:
        rec = self.record(session)
        with rec.lock:
            return {"answer": notation_resolve(rec.session, token)}

    # -- integrity --------------------------------------------------------------
    @_guard(lost=False)
    def verify_node(self, file: str, lemma: str, body: str, *, plan: str | None = None) -> dict[str, Any]:
        """The deterministic gate as a tool (PLAN.md 8.7): the same ``Gate.run`` the scheduler runs.

        Statements-only prefix (sound: ``Qed`` is opaque) so a call costs seconds, not a
        full recompile; the plan path is resolved against the workspace, not the cwd.
        """
        from pcp.orch.gate import Gate  # lazy: pcp-state never needs the orchestrator

        path = self._resolve(file)
        if not path.is_file():
            raise UsageError(f"{file}: no such file (resolved against {self.workspace})")
        nodes = parse_plan(read_text(self._resolve(plan))) if plan else []
        result = Gate(Development(path)).run(
            lemma, nodes, target_body=strip_proof_wrapper(body), truncate=True, stub_prefix=True
        )
        return {"ok": result.ok, "report": result.render(), "assumptions": result.assumptions}


# ------------------------------------------------------------------ MCP adapter


def _dumps(obj: Any) -> str:
    return json.dumps(obj, default=str, ensure_ascii=False)


def tool_functions(server: PcpServer) -> dict[str, Callable[..., str]]:
    """The ten tools as plain functions returning JSON strings, keyed by name.

    Their docstrings are the descriptions the model reads; the ``""``/``-1`` sentinels
    exist because MCP clients send every optional argument.
    """

    def proof_open(file: str, lemma: str, reflect: bool = False, fast: bool = True) -> str:
        """Open a lemma for stepping; returns a session id and its Iris proof state, per hypothesis.

        `file` is relative to the workspace.  `fast` (default) elaborates only the statements
        before the lemma -- other proofs cannot affect its goal -- and is seconds instead of
        minutes.  `reflect` reads hypotheses through the Ltac2 dump (exact, layout-independent)."""
        return _dumps(server.proof_open(file, lemma, reflect=reflect, fast=fast))

    def proof_step(session: str, tactic: str, mode: str = "commit", select: str = "", budget: int = DEFAULT_STEP_BUDGET) -> str:
        """Run one tactic sentence from the current state and see exactly what changed: no file edit, no recompile.

        `mode="speculative"` does not move the session.  A failure comes back with a structured
        diagnosis (pattern/prop alignment, apply mismatch, leftover resources) -- read it before
        retrying.  `loop_of` names an earlier step whose state this one repeats."""
        return _dumps(server.proof_step(session, tactic, mode=mode, select=select or None, budget=budget))

    def proof_state(
        session: str, step: int = -1, select: str = "", mode: str = "full", budget: int = DEFAULT_STATE_BUDGET,
        diff_only: bool = True, relevance: bool = False,
    ) -> str:
        """Render the goal at a step (default: current) under a token budget; it says what it elided.

        Diff-only by default: what changed since you last looked, plus a manifest of what did
        not.  `select` (e.g. "HP,H*,spatial,mentions:γ,head:WP") always shows what it names;
        `mode` is full | folded | summary | hash-only."""
        return _dumps(server.proof_state(
            session, step=None if step < 0 else step, select=select or None, mode=mode, budget=budget,
            diff_only=diff_only, relevance=relevance,
        ))

    def proof_trace(file: str, lemma: str, script: list[str] | None = None) -> str:
        """Replay a script (default: the lemma's own proof) tactic by tactic; returns the ledger event log and a session."""
        return _dumps(server.proof_trace(file, lemma, script))

    def proof_ledger(session: str, query: str, hyp: str = "", step: int = -1) -> str:
        """Ask the resource ledger: where did a hypothesis go, what consumed it, what is still live, what was never used.

        `query` is one of where_did_it_go | blame | leftovers | unused_at_qed | events; `hyp` is
        required for the first two; `blame` takes the failing `step` (default: the step that failed)."""
        return _dumps(server.proof_ledger(session, query, hyp=hyp or None, step=None if step < 0 else step))

    def proof_try(session: str, tactics: list[str]) -> str:
        """Run up to 20 candidate tactics speculatively from the current state and report which survive."""
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

    fns = {
        fn.__name__: fn
        for fn in (
            proof_open, proof_step, proof_state, proof_trace, proof_ledger, proof_try, proof_destruct,
            premise_search, notation_resolve, verify_node,
        )
    }
    assert tuple(fns) == TOOLS, "tool_functions must register exactly pcp.mcp.names.TOOLS, in order"
    return fns


def make_mcp(name: str = MCP_SERVER_NAME) -> Any:
    """An MCP server object for whichever SDK generation is installed.

    ``FastMCP`` (mcp 1.x) became ``MCPServer`` (mcp 2.x) with the same decorator shape.
    ``import mcp`` succeeds on both, so only constructing the server proves anything --
    ``pcp doctor`` calls this for that reason.
    """
    try:
        from mcp.server.mcpserver import MCPServer  # mcp >= 2

        return MCPServer(name)
    except ImportError:
        pass
    try:
        from mcp.server.fastmcp import FastMCP  # type: ignore[attr-defined]  # mcp < 2

        return FastMCP(name)
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
    fired whenever an anyio worker thread exited (the v1 critical bug), so instead a
    thread polls ``getppid``: reparenting to init (1) or to a subreaper -- any change
    from the original parent -- means the client is gone.
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
