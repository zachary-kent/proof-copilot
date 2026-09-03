"""The MCP tool surface (PLAN.md 7).

Keep it small.  Every tool is a place the model can get lost, and every tool needs an
ablation showing it earns its context (PLAN.md 13).  There is a hard cap here, and
adding a tool means deleting one or justifying it with a measurement.

**Deliberately not tools:** ``prove_this_lemma``, ``fix_this_proof``.  Those are agent
jobs.  A tool that tries to be an agent is a tool you cannot ablate.
"""

from __future__ import annotations

import contextlib
import json
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from pcp.core.digest import PropStore
from pcp.core.ipm.model import IrisGoal
from pcp.core.ipm.pattern import DestructSpec, align, compile_auto, compile_spec
from pcp.core.ipm.skeleton import parse_skeleton
from pcp.core.ledger.query import LedgerQuery
from pcp.core.render import RenderOptions, render_goal
from pcp.core.search import grep_sources, notation_resolve, premise_search
from pcp.core.session import ProofSession, SessionPool
from pcp.core.trace import Tracer

#: The cap from PLAN.md 14 ("hard cap on tool count").  Raising it is a decision,
#: not an accident, so it is asserted at import time.
MAX_TOOLS = 12


@dataclass
class Session:
    """One open proof, plus everything derived from it."""

    id: str
    tracer: Tracer
    store: PropStore

    @property
    def trace(self):
        return self.tracer.trace


class PcpServer:
    """The tool implementations, independent of the MCP transport.

    Kept transport-free so the CLI, the tests and the eval harness call exactly what
    the model calls -- an ablation over a different code path measures nothing.
    """

    def __init__(self, workspace: Path) -> None:
        self.workspace = Path(workspace).resolve()
        self.pool = SessionPool(self.workspace, size=2)
        self.sessions: dict[str, Session] = {}
        self._n = 0

    def close(self) -> None:
        self.pool.close()

    # -- state and trace ---------------------------------------------------
    def proof_open(
        self, file: str, lemma: str, *, reflect: bool = False, fast: bool = True
    ) -> dict[str, Any]:
        """Open a lemma for stepping.

        ``fast`` opens a statements-only twin of the file.  `petanque/start` has to
        elaborate everything before the theorem, and on a real development that is
        minutes of *other people's proof automation* -- none of which can affect the
        goal state, because `Qed` proofs are opaque.  Measured on a 1123-line file:
        23.5 s -> 3.1 s cold, and 0.1 s once the pool has the document cached.
        """
        pre = None
        if reflect:
            from pcp.core.ipm.reflect import build_idump, coqpath_with

            root = Path(".pcp/coq").resolve()
            build_idump(root)
            os.environ["COQPATH"] = coqpath_with(root)
            os.environ["ROCQPATH"] = os.environ["COQPATH"]
            pre = "Require Import pcp.IDump."
        session = ProofSession(
            self.pool, self._resolve(file), lemma, pre_commands=pre, stub_prefix=fast
        )
        tracer = Tracer(session)
        tracer.start()
        self._n += 1
        sid = f"s{self._n}"
        self.sessions[sid] = Session(id=sid, tracer=tracer, store=tracer.trace.store)
        return {
            "session": sid,
            "state_id": tracer.trace.steps[0].state_id,
            "goal": self._render(sid, tracer.trace.steps[0].goals),
        }

    def proof_step(
        self,
        session: str,
        tactic: str,
        *,
        mode: str = "commit",
        select: str | None = None,
        budget: int = 3000,
    ) -> dict[str, Any]:
        s = self._session(session)
        if mode == "speculative":
            result = s.tracer.session.run(tactic, commit=False)
            return {
                "ok": result.ok,
                "error": result.error,
                "loop_of": result.loop_of,
                "diagnosis": self._diagnose(s, tactic, result.error),
            }
        before = s.trace.steps[-1].goals if s.trace.steps else []
        step = s.tracer.step(tactic)
        if not step.ok:
            return {
                "ok": False,
                "error": step.error,
                # Pattern diagnosis is not opt-in: any failing pattern-bearing tactic
                # comes back with the alignment report by construction (PLAN.md 7).
                "diagnosis": self._diagnose(s, tactic, step.error, goals=before),
            }
        events = [e.to_json() for e in s.trace.events if e.step == step.step]
        return {
            "ok": True,
            "state_id": step.state_id,
            "proof_finished": s.trace.finished,
            "ledger": events,
            "goal": self._render(session, step.goals, select=select, budget=budget),
        }

    def proof_state(
        self,
        session: str,
        *,
        step: int | None = None,
        select: str | None = None,
        mode: str = "full",
        budget: int = 4000,
        diff_only: bool = True,
        relevance: bool = False,
    ) -> dict[str, Any]:
        s = self._session(session)
        target = s.trace.step_at(step) if step is not None else s.trace.final
        if target is None:
            return {"error": f"no step {step}"}
        previous = s.trace.step_at(target.step - 1) if diff_only and target.step else None
        opts = RenderOptions(
            select=select, mode=mode, budget=budget, diff_only=diff_only, relevance=relevance
        )
        renders = [
            render_goal(
                g,
                previous=previous.goals[0] if previous and previous.goals else None,
                options=opts,
                store=s.store,
            ).text
            for g in target.goals
        ]
        return {"step": target.step, "goals": renders}

    def proof_trace(self, file: str, lemma: str, script: list[str] | None = None) -> dict[str, Any]:
        from pcp.core.vernac import find_block

        path = self._resolve(file)
        tactics = script
        if tactics is None:
            block = find_block(path.read_text(encoding="utf-8"), lemma)
            if block is None or not block.has_proof:
                return {"error": f"{file}: {lemma} has no proof; pass a script"}
            tactics = block.tactics()
        opened = self.proof_open(file, lemma)
        s = self._session(opened["session"])
        s.tracer.run_script(tactics)
        return {
            "session": s.id,
            "steps": len(s.trace.steps),
            "finished": s.trace.finished,
            "error": s.trace.error,
            "events": [e.render() for e in s.trace.events],
        }

    def proof_ledger(self, session: str, query: str, *, hyp: str | None = None, step: int | None = None) -> dict[str, Any]:
        s = self._session(session)
        q = LedgerQuery(s.trace)
        if query == "where_did_it_go":
            if not hyp:
                return {"error": "hyp is required"}
            return {"answer": q.where_did_it_go(hyp).render()}
        if query == "blame":
            if not hyp:
                return {"error": "hyp is required"}
            return {"answer": q.blame(step if step is not None else len(s.trace.steps), hyp).render()}
        if query == "leftovers":
            hyps = q.leftovers(step)
            return {
                "answer": "the spatial context is empty"
                if not hyps
                else "\n".join(f'"{h.id}" : {h.prop}' for h in hyps),
                "count": len(hyps),
            }
        if query == "unused_at_qed":
            return {"answer": ", ".join(q.unused_at_qed()) or "every resource was consumed"}
        if query == "events":
            return {"answer": "\n".join(e.render() for e in s.trace.events)}
        return {"error": f"unknown query {query!r}"}

    def proof_try(self, session: str, tactics: list[str]) -> dict[str, Any]:
        """Speculative fan-out from one state.  Very high value per token.

        Surplus subscription window is exactly what to spend here: near-free on a
        flat-rate tier, expensive on a metered API.
        """
        s = self._session(session)
        results = s.tracer.session.try_many(tactics[:20])
        return {
            "survivors": [t for t, r in zip(tactics, results) if r.ok],
            "results": [
                {
                    "tactic": t,
                    "ok": r.ok,
                    "error": (r.error or "")[:300],
                    "proof_finished": r.proof_finished,
                    "state_id": r.state.st if r.state else None,
                }
                for t, r in zip(tactics, results)
            ],
        }

    def proof_destruct(
        self,
        session: str,
        hyp: str,
        *,
        spec: dict[str, Any] | None = None,
        auto: bool = True,
        apply: bool = False,
    ) -> dict[str, Any]:
        """Structured destructuring: intent in, syntax out (PLAN.md 7).

        No model hand-assembles a nested pattern string; the compiler does it from
        the prop's connective skeleton, and on failure the aligner says exactly where
        the pattern and the object diverge.
        """
        s = self._session(session)
        goal = s.trace.final.goals[0] if s.trace.final and s.trace.final.goals else None
        if goal is None:
            return {"error": "no goal"}
        h = goal.by_id(hyp)
        if h is None:
            return {"error": f'no hypothesis named "{hyp}"', "available": [x.id for x in goal.ipm_hyps]}
        skel = parse_skeleton(h.prop)
        d = compile_spec(DestructSpec(**spec), skel) if spec else compile_auto(skel, hyp)
        tactic = d.idestruct(hyp)
        out: dict[str, Any] = {
            "tactic": tactic,
            "pattern": d.pattern_text,
            "binders": d.binders,
            "skeleton": skel.render(),
        }
        if apply:
            step = s.tracer.step(tactic)
            out["ok"] = step.ok
            out["error"] = step.error
            if step.ok:
                out["goal"] = self._render(session, step.goals)
            else:
                out["diagnosis"] = align(d.pattern, skel, binders=d.binders).render()
        return out

    # -- search ------------------------------------------------------------
    def premise_search(
        self,
        session: str,
        *,
        pattern: str | None = None,
        query: str | None = None,
        scope: str | None = None,
    ) -> dict[str, Any]:
        s = self._session(session)
        result = premise_search(s.tracer.session, pattern=pattern, query=query, scope=scope)
        if not result.premises:
            fallback = grep_sources([self.workspace], pattern or query or "")
            result.premises.extend(fallback.premises)
            result.queries.extend(fallback.queries)
        return {"answer": result.render(), "count": len(result.premises)}

    def notation_resolve(self, session: str, token: str) -> dict[str, Any]:
        s = self._session(session)
        return {"answer": notation_resolve(s.tracer.session, token).render()}

    # -- integrity ---------------------------------------------------------
    def verify_node(self, file: str, lemma: str, body: str, *, plan: str | None = None) -> dict[str, Any]:
        """The deterministic gate, callable as a tool (PLAN.md 8.7)."""
        from pcp.orch.assemble import Development, parse_plan
        from pcp.orch.gate import Gate

        dev = Development(self._resolve(file))
        specs = parse_plan(Path(plan).read_text(encoding="utf-8")) if plan else []
        result = Gate(dev).run(lemma, specs, target_body=body)
        return {"ok": result.ok, "report": result.render(), "assumptions": result.assumptions}

    # -- helpers -----------------------------------------------------------
    def _session(self, sid: str) -> Session:
        if sid not in self.sessions:
            raise KeyError(f"no session {sid!r}; call proof_open first")
        return self.sessions[sid]

    def _resolve(self, file: str) -> Path:
        p = Path(file)
        return p if p.is_absolute() else (self.workspace / p)

    def _render(
        self, session: str, goals: list[IrisGoal], *, select: str | None = None, budget: int = 3000
    ) -> list[str]:
        s = self._session(session)
        opts = RenderOptions(select=select, budget=budget, diff_only=False)
        return [render_goal(g, options=opts, store=s.store).text for g in goals]

    def _diagnose(self, s: Session, tactic: str, error: str | None, goals: list[IrisGoal] | None = None) -> str:
        """Structured diagnosis on error, produced by construction, not on request."""
        from pcp.mcp.diagnose import diagnose

        current = goals if goals is not None else (s.trace.final.goals if s.trace.final else [])
        return diagnose(tactic, error or "", current[0] if current else None)


# --------------------------------------------------------------------------- MCP

TOOLS = [
    ("proof_open", "Open a lemma; returns a session and the initial IPM state."),
    ("proof_step", "Run one tactic (commit | speculative); returns the ledger delta and a budgeted state."),
    ("proof_state", "Budgeted, per-hypothesis render of a traced state."),
    ("proof_trace", "Replay a whole proof script and return the ledger event log."),
    ("proof_ledger", "where_did_it_go | blame | leftovers | unused_at_qed | events."),
    ("proof_try", "Speculative fan-out: run N candidate tactics from one state, report which survive."),
    ("proof_destruct", "Compile an iDestruct/iIntros pattern from the prop's skeleton, or diagnose one."),
    ("premise_search", "Search / SearchPattern at the current state, with a source-grep fallback."),
    ("notation_resolve", "What a notation means, what it unfolds to, which IPM tactics apply."),
    ("verify_node", "Run the deterministic integrity gate on a proof body."),
]
assert len(TOOLS) <= MAX_TOOLS, "tool-surface cap exceeded; delete one or justify it with an ablation"


class MCPUnavailable(RuntimeError):
    pass


def make_mcp(name: str = "pcp"):
    """Construct an MCP server across SDK generations.

    The SDK renamed ``FastMCP`` to ``MCPServer`` in 2.x while keeping the shape of
    the decorator API.  Importing the bare ``mcp`` package succeeds either way, which
    is why a version check on the package alone is worthless -- and why this used to
    fail only at the moment a worker actually needed a tool.
    """
    try:
        from mcp.server.mcpserver import MCPServer  # mcp >= 2

        return MCPServer(name)
    except ImportError:
        pass
    try:
        from mcp.server.fastmcp import FastMCP  # mcp < 2

        return FastMCP(name)
    except ImportError as exc:
        raise MCPUnavailable(
            "no usable MCP server API found. Install it with "
            "pip install 'proof-copilot[mcp]' (mcp 1.x or 2.x both work)."
        ) from exc


def build_server(workspace: Path):
    """Wire the tool implementations onto an MCP server and return both."""
    server = PcpServer(workspace)
    mcp = _register(server, make_mcp("pcp"))
    return server, mcp


def _die_with_client() -> None:
    """Ask the kernel to kill this server when the client that spawned it dies.

    A stdio MCP server should notice its client leaving as EOF on stdin -- but only
    if it is ever back in the read loop. One server sat blocked inside a runaway
    petanque call, never returned, and outlived its worker by hours while that call
    grew to 372 GB. EOF cannot help a process that is not reading, so the lifetime
    has to be enforced from outside the loop.

    `PR_SET_PDEATHSIG` is set on *ourselves*, which needs no cooperation from the
    client that spawned us. The immediate `getppid` check closes the race where the
    parent died before we got here.
    """
    import ctypes
    import os
    import signal

    with contextlib.suppress(Exception):
        ctypes.CDLL("libc.so.6", use_errno=True).prctl(1, signal.SIGTERM)  # PR_SET_PDEATHSIG
    if os.getppid() == 1:  # already orphaned
        raise SystemExit(0)


def run_stdio(workspace: Path) -> int:
    """Serve the tools over MCP stdio.

    Nothing may be written to stdout here except the protocol itself: stdio MCP
    multiplexes the JSON-RPC stream over it, and a stray `print` desyncs the client
    into reporting the server as simply "failed".
    """
    _die_with_client()
    try:
        server, mcp = build_server(workspace)
    except MCPUnavailable as exc:
        print(str(exc), file=sys.stderr)
        return 2
    try:
        mcp.run()
    except Exception as exc:  # noqa: BLE001 -- report on stderr, never on stdout
        print(f"pcp mcp failed: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1
    finally:
        server.close()
    return 0


def _register(server: "PcpServer", mcp):
    """Attach every tool in :data:`TOOLS` to ``mcp``."""

    @mcp.tool()
    def proof_open(file: str, lemma: str, reflect: bool = False, fast: bool = True) -> str:
        """Open a lemma for stepping. Returns a session id and the initial IPM state.

        `fast` (default) skips elaborating the other proofs in the file, which cannot
        affect this goal; pass false only if you need the file exactly as written."""
        return json.dumps(server.proof_open(file, lemma, reflect=reflect, fast=fast), default=str)

    @mcp.tool()
    def proof_step(session: str, tactic: str, mode: str = "commit", select: str = "", budget: int = 3000) -> str:
        """Run one tactic. `speculative` does not move the session. Failures come back
        with a structured diagnosis, including pattern/prop alignment."""
        return json.dumps(server.proof_step(session, tactic, mode=mode, select=select or None, budget=budget), default=str)

    @mcp.tool()
    def proof_state(session: str, step: int = -1, select: str = "", mode: str = "full",
                    budget: int = 4000, diff_only: bool = True, relevance: bool = False) -> str:
        """Budgeted per-hypothesis render. Every render reports what it elided."""
        return json.dumps(
            server.proof_state(session, step=None if step < 0 else step, select=select or None,
                               mode=mode, budget=budget, diff_only=diff_only, relevance=relevance),
            default=str,
        )

    @mcp.tool()
    def proof_trace(file: str, lemma: str, script: list[str] | None = None) -> str:
        """Replay a proof script tactic by tactic and return the resource-ledger log."""
        return json.dumps(server.proof_trace(file, lemma, script), default=str)

    @mcp.tool()
    def proof_ledger(session: str, query: str, hyp: str = "", step: int = -1) -> str:
        """Ask where a hypothesis went, what consumed it, what is left, or what was never used."""
        return json.dumps(
            server.proof_ledger(session, query, hyp=hyp or None, step=None if step < 0 else step), default=str
        )

    @mcp.tool()
    def proof_try(session: str, tactics: list[str]) -> str:
        """Run up to 20 candidate tactics speculatively from the current state."""
        return json.dumps(server.proof_try(session, tactics), default=str)

    @mcp.tool()
    def proof_destruct(session: str, hyp: str, spec: dict | None = None, apply: bool = False) -> str:
        """Compile the iDestruct pattern for a hypothesis from its connective skeleton."""
        return json.dumps(server.proof_destruct(session, hyp, spec=spec, apply=apply), default=str)

    @mcp.tool()
    def premise_search(session: str, pattern: str = "", query: str = "", scope: str = "") -> str:
        """Search for lemmas at the current proof state, with a source-grep fallback."""
        return json.dumps(
            server.premise_search(session, pattern=pattern or None, query=query or None, scope=scope or None),
            default=str,
        )

    @mcp.tool()
    def notation_resolve(session: str, token: str) -> str:
        """Explain a notation: what it means, what it unfolds to, which tactics apply."""
        return json.dumps(server.notation_resolve(session, token), default=str)

    @mcp.tool()
    def verify_node(file: str, lemma: str, body: str, plan: str = "") -> str:
        """Run the deterministic integrity gate on a proof body."""
        return json.dumps(server.verify_node(file, lemma, body, plan=plan or None), default=str)

    return mcp
