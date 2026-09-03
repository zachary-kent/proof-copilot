"""Frontier dispatch, gating, retry, escalation (PLAN.md 8.9, 8.11, 11).

The scheduling rules that are not negotiable:

* **The whole frontier goes at once.**  Every statement ``frozen@e`` with an ``open``
  proof is dispatchable now; graph depth never gates dispatch.
* **Cheap-tier concurrency is always maximal.**  In-flight worker count defaults to
  the ceiling the rate window and the session pool allow.  Budgets bound cost;
  concurrency is never the knob you turn down, because unused window capacity
  expires worthless.
* **No model ever reviews a success.**  A gated ``qed`` is final.
* **One evidence-informed retry**, then escalate.  Not a loop.
* **It never wedges.**  Every node terminates in one of three shapes within its
  budget; a hung worker is a timeout-and-requeue, and a crash resumes from SQLite.
"""

from __future__ import annotations

import asyncio
import os
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Sequence

from pcp.orch.assemble import Development, NodeSpec
from pcp.orch.gate import Gate, GateResult
from pcp.orch.graph import Budget, Graph, Node
from pcp.orch.packet import build_packet
from pcp.orch.runners.base import NodePayload, NodeResult, Runner

DEFAULT_NODE_SECONDS = 900.0


def default_concurrency() -> int:
    """The ceiling, not a comfortable number.

    Bounded by cores because the real ceiling downstream is Rocq: a pet-server with
    Iris loaded costs 1-2 GB RSS and runs tactics serially, and each gate check
    forks a `coqc`.
    """
    return max(4, min(32, (os.cpu_count() or 4)))


@dataclass
class NodeOutcome:
    node_id: str
    name: str
    status: str            # qed | stuck | contested | error
    gate: GateResult | None = None
    evidence: str = ""
    attempts: int = 0
    elapsed_s: float = 0.0
    proof: str = ""
    requests: list[dict[str, str]] = field(default_factory=list)

    def one_line(self) -> str:
        if self.status == "qed":
            return f"qed       {self.name}  ({self.elapsed_s:.0f}s, {self.attempts} attempt(s))"
        head = {"stuck": "stuck    ", "contested": "contested", "error": "error    "}.get(self.status, self.status)
        reason = " ".join(self.evidence.split())[:100]
        return f"{head} {self.name}  {reason}"


@dataclass
class RunReport:
    """The end-of-run summary.  It fits on one screen; the dashboard is optional."""

    outcomes: list[NodeOutcome] = field(default_factory=list)
    elapsed_s: float = 0.0
    dispatched: int = 0
    gate_failures: int = 0

    def by_status(self, status: str) -> list[NodeOutcome]:
        return [o for o in self.outcomes if o.status == status]

    def render(self) -> str:
        qed = self.by_status("qed")
        stuck = self.by_status("stuck")
        contested = self.by_status("contested")
        errored = self.by_status("error")
        lines = [
            f"{len(qed)} qed · {len(stuck)} stuck · {len(contested)} contested"
            + (f" · {len(errored)} error" if errored else "")
            + f"   ({self.elapsed_s:.0f}s, {self.dispatched} dispatches)"
        ]
        for group in (qed, stuck, contested, errored):
            lines.extend("  " + o.one_line() for o in group)
        return "\n".join(lines)


class Scheduler:
    """Dispatches the frontier, gates every return, retries once with evidence."""

    def __init__(
        self,
        graph: Graph,
        dev: Development,
        runner: Runner,
        *,
        anchor: str,
        gate: Gate | None = None,
        workroot: Path = Path(".pcp/work"),
        concurrency: int | None = None,
        node_seconds: float = DEFAULT_NODE_SECONDS,
        max_attempts: int = 2,
        skills: Sequence[str] = (),
        state_tools: Sequence[str] = (),
        library: Sequence[Path] = (),
        check_command: str = "pcp check",
        on_event: Callable[[str, dict[str, Any]], None] | None = None,
        recorder: Any = None,
        corpus: str = "",
    ) -> None:
        self.graph = graph
        self.dev = dev
        self.runner = runner
        #: The declaration in the file that anchors every assembly -- the user's root.
        self.anchor = anchor
        self.gate = gate or Gate(dev)
        self.workroot = Path(workroot)
        self.workroot.mkdir(parents=True, exist_ok=True)
        self.concurrency = concurrency or default_concurrency()
        self.node_seconds = node_seconds
        self.max_attempts = max_attempts
        self.skills = list(skills)
        self.state_tools = list(state_tools)
        self.library = [Path(p) for p in library]
        self.check_command = check_command
        self.on_event = on_event
        #: When set, every attempt leaves a durable record for failure analysis.
        self.recorder = recorder
        self.corpus = corpus
        self._sem = asyncio.Semaphore(self.concurrency)
        self._gate_lock = asyncio.Semaphore(self.concurrency)

    # -- assembly context --------------------------------------------------
    def specs(self, *, target: str | None = None, target_body: str | None = None) -> list[NodeSpec]:
        """Every planned obligation, as it should appear in an assembly.

        Proved nodes carry their body; everything else is an ``Admitted`` stub, which
        is what makes the whole frontier dispatchable at once regardless of where a
        node sits in the graph.  ``target``/``target_body`` substitute the body under
        test without disturbing the rest.
        """
        out: list[NodeSpec] = []
        for n in self.graph.nodes():
            if n.rank == "root" or n.proof_status == "attic":
                continue
            if self.dev.block(n.name):
                continue  # already in the file; not an injected obligation
            body = target_body if (target is not None and n.name == target) else n.body
            out.append(NodeSpec(name=n.name, statement=n.statement, body=body, mockable=n.mockable))
        return out

    # -- one node ----------------------------------------------------------
    async def run_node(self, node: Node) -> NodeOutcome:
        started = time.perf_counter()
        # A resumed node carries the evidence its last run produced, so even its
        # first attempt here is evidence-informed rather than a blind repeat.
        evidence = node.evidence or ""
        outcome = NodeOutcome(node_id=node.id, name=node.name, status="stuck")
        for attempt in range(1, self.max_attempts + 1):
            async with self._sem:
                result, gate_result = await self._attempt(node, attempt, evidence)
            outcome.attempts = attempt
            outcome.gate = gate_result
            outcome.requests = [r.to_json() for r in result.requests]
            if result.status == "qed" and gate_result is not None and gate_result.ok:
                self.graph.set_proof_status(node.id, "gated", body=result.proof)
                outcome.status = "qed"
                outcome.proof = result.proof
                break
            if result.status == "contested":
                self.graph.set_proof_status(node.id, "contested", evidence=result.evidence)
                outcome.status = "contested"
                outcome.evidence = result.evidence
                break
            # Failure path: assemble the evidence the retry will actually use.
            evidence = _failure_evidence(result, gate_result)
            outcome.evidence = evidence
            outcome.status = "error" if result.status == "error" else "stuck"
            if result.status == "error":
                # A missing binary or an unauthenticated window is not a proof
                # failure; retrying it just burns the node's budget.
                break
        if outcome.status in ("stuck", "error"):
            self.graph.set_proof_status(node.id, "stuck", evidence=outcome.evidence)
        outcome.elapsed_s = time.perf_counter() - started
        self._emit("node.done", {"node": node.id, "status": outcome.status})
        return outcome

    async def _attempt(self, node: Node, attempt: int, evidence: str) -> tuple[NodeResult, GateResult | None]:
        siblings = self.specs(target=node.name, target_body="admit." if node.name != self.anchor else None)
        packet = build_packet(
            self.graph,
            node,
            self.dev,
            siblings,
            anchor=self.anchor,
            root=self.workroot,
            evidence=evidence,
            attempt=attempt,
            skills=self.skills,
            state_tools=self.state_tools,
            check_command=self.check_command,
            library=self.library,
        )
        payload = NodePayload(
            node_id=node.id,
            name=node.name,
            statement=node.statement,
            file=str(self.dev.path),
            workdir=packet.workdir,
            scratch_file=self.dev.path.name,
            intent=node.intent,
            siblings=[(s.name, s.statement) for s in siblings],
            evidence=evidence,
            budget_seconds=node.budget.seconds or self.node_seconds,
            attempt=attempt,
        )
        self.graph.set_proof_status(node.id, "claimed")
        attempt_id = self.graph.start_attempt(node.id, runner=self.runner.name, owner=node.owner)
        self._emit("node.dispatched", {"node": node.id, "attempt": attempt})

        result = await self.runner.run_node(payload)

        gate_result: GateResult | None = None
        if result.status == "qed" and result.proof.strip():
            is_anchor = node.name == self.anchor
            specs = self.specs(
                target=None if is_anchor else node.name,
                target_body=None if is_anchor else result.proof,
            )
            async with self._gate_lock:
                gate_result = await asyncio.to_thread(
                    _gate_call,
                    self.gate,
                    self.anchor,
                    specs,
                    result.proof if is_anchor else None,
                    node.name,
                )
            if not gate_result.ok:
                # A worker that says `qed` and does not gate is a failed attempt, not
                # a success to be argued about.  No model reads this; the gate did.
                result.status = "stuck"
        self.graph.finish_attempt(
            attempt_id,
            model=str((result.trace or {}).get("model", "")),
            status=result.status,
            evidence=result.evidence,
            body=result.proof or None,
            gate=gate_result.to_json() if gate_result else {},
            cost=result.cost,
            requests=[r.to_json() for r in result.requests],
        )
        if self.recorder is not None:
            self._record(node, attempt, result, gate_result, packet.workdir)
        return result, gate_result

    def _record(self, node: Node, attempt: int, result: NodeResult, gate: GateResult | None, workdir: Path) -> None:
        from pcp.orch.record import AttemptRecord

        self.recorder.write(
            AttemptRecord(
                run_id=self.recorder.run_id,
                node=node.id,
                lemma=node.name,
                attempt=attempt,
                runner=self.runner.name,
                status=result.status,
                solved=result.status == "qed" and gate is not None and gate.ok,
                elapsed_s=result.elapsed_s,
                cost=result.cost,
                evidence=result.evidence,
                gate_report=gate.render() if gate else "",
                compile_output=(gate.compile_output[-8000:] if gate else ""),
                gate_checks=(gate.to_json()["checks"] if gate else []),
                proof=result.proof,
                requests=[r.to_json() for r in result.requests],
                corpus=self.corpus,
                trace=result.trace,
            ),
            workdir=workdir,
            transcript=result.raw,
        )

    # -- the frontier ------------------------------------------------------
    async def run(self) -> RunReport:
        started = time.perf_counter()
        report = RunReport()
        frontier = self.graph.frontier()
        # `non-mockable` nodes genuinely block their dependents, so they go first and
        # alone; everything else goes out together.
        blocking = [n for n in frontier if not n.mockable]
        parallel = [n for n in frontier if n.mockable]

        for node in blocking:
            report.outcomes.append(await self.run_node(node))
            report.dispatched += 1

        if parallel:
            results = await asyncio.gather(*(self.run_node(n) for n in parallel))
            report.outcomes.extend(results)
            report.dispatched += len(parallel)

        report.gate_failures = sum(1 for o in report.outcomes if o.gate is not None and not o.gate.ok)
        report.elapsed_s = time.perf_counter() - started
        return report

    def _emit(self, kind: str, payload: dict[str, Any]) -> None:
        rest = {k: v for k, v in payload.items() if k != "node"}
        self.graph.emit(kind, payload.get("node"), **rest)
        if self.on_event:
            self.on_event(kind, payload)


def _gate_call(gate: Gate, anchor: str, specs: list[NodeSpec], anchor_body: str | None, target: str) -> GateResult:
    # Per-node checks stub the rest of the development's proofs.  On a real Iris
    # file that is the difference between seconds and minutes, and it is sound for
    # a *per-node* check: `Qed` proofs are opaque, so this proof can depend only on
    # its siblings' statements, never on their bodies.  Integration re-checks
    # everything for real.
    return gate.run(
        anchor, specs, target_body=anchor_body, target=target, truncate=True, stub_prefix=True
    )


def _failure_evidence(result: NodeResult, gate: GateResult | None) -> str:
    """Everything the retry needs, and nothing it does not.

    Model judgment is a failure-path resource and it is bounded even there: the one
    retry gets the gate's own words, not a re-derivation of them.
    """
    parts: list[str] = []
    if result.evidence:
        parts.append(result.evidence.strip())
    if gate is not None and not gate.ok:
        parts.append(gate.render())
    if not parts and result.raw:
        parts.append(result.raw[-1500:])
    return "\n\n".join(parts)[:6000]


def split_budget(total: Budget, nodes: int) -> Budget:
    """Geometric split: children get fractions of the parent's budget (PLAN.md 8.2)."""
    return total.split(max(1, nodes))
