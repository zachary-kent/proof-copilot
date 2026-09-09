"""Frontier dispatch, gating, retry, isolation (PLAN.md 8.1, 8.9, 8.11, 11).

The rules that are not negotiable:

* **The whole frontier goes at once.**  Every statement ``frozen@e`` with an ``open``
  proof is dispatchable now; graph depth never gates dispatch.  Non-mockable nodes
  genuinely block their dependents, so they go first and alone.
* **Cheap-tier concurrency is always maximal.**  The semaphore defaults to the
  machine ceiling; budgets bound cost, concurrency is never the knob you turn down.
* **No model ever reviews a success.**  A gated ``qed`` is final.
* **One evidence-informed retry**, then stop.  The retry carries the worker's own
  evidence, the gate's own words and the recovered partial body.  A ``stuck`` that
  asks for an **amendment** (PLAN.md 8.5: the invariant lacks a fact) is a verdict
  on the design, not on the attempt: the retry is not spent against the same
  design; it happens after the amendment is applied, with the change as evidence.
* **It never wedges.**  Every node terminates in one of the three shapes; every
  exception inside a node -- a runner raising, a sqlite error -- becomes an
  ``error`` outcome for *that node* and the others finish (ARCHITECTURE.md 8, "one
  exception wedging the whole frontier"); a runner that never returns is cut off
  at the deadline plus a grace period by the scheduler itself; and a recorder that
  fails never costs the attempt it was recording (a gated proof was once parked
  ``stuck`` over an ``OSError`` from the record directory).  Only a
  ``BaseException`` (Ctrl-C, a simulated crash) aborts the run, the way a real crash
  would; resume handles what it leaves behind.
* **Attempts are bounded across runs.**  A node's budget is ``max_attempts`` per
  statement epoch, counted from the graph's attempt rows -- re-running ``pcp prove``
  in a loop no longer buys a hopeless node two fresh workers per invocation.
* **An outage is not a result** (PLAN.md 11: unused window expires worthless).  An
  ``error`` that :func:`pcp.orch.outage.detect_outage` recognises -- a revoked login,
  a usage window, an unreachable provider -- charges nothing and parks nothing: the
  run *pauses* (one pause, every dispatcher waits on it, in-flight attempts run on),
  probes until the provider answers, and re-dispatches the affected nodes.  Only an
  exhausted wait parks them, ``stuck`` with the outage as evidence, and the run still
  reaches its report.
"""

from __future__ import annotations

import asyncio
import os
import sys
import time
import traceback
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from pcp.orch.gate import Gate, GateResult
from pcp.orch.graph import Graph
from pcp.orch.model import PROVED_STATUSES, Node
from pcp.orch.outage import Outage, PausePolicy, ProviderPause, detect_outage, format_wait, provider_probe
from pcp.orch.packet import attempt_dir, build_packet
from pcp.orch.protocol import AMENDED_MARKER, AmendmentRequest, NodePayload, NodeResult, Runner, read_result
from pcp.rocq.assemble import Development, NodeSpec
from pcp.rocq.body import is_placeholder
from pcp.util.io import json_load
from pcp.util.text import one_line

DEFAULT_NODE_SECONDS = 900.0
#: How long past ``node_seconds`` a runner may take to return before the scheduler
#: cancels the attempt itself: a process-group kill plus a reap should take seconds.
DEADLINE_GRACE_S = 30.0
#: The retry packet shows at most 4000 chars of evidence, so the worker's own prose
#: is clipped first: the gate's words are the part that must survive.
EVIDENCE_LIMIT = 6000
WORKER_EVIDENCE_LIMIT = 2500
TRACEBACK_TAIL = 1500
#: Outage pauses one node may go through in one run before it is parked: a provider
#: that answers the probe and fails the next attempt is flapping, and the node's
#: attempt budget is not the bound (outage rows are never charged).
MAX_OUTAGE_RETRIES = 3


def default_concurrency() -> int:
    """The ceiling, not a comfortable number: bounded by cores because the real
    ceiling downstream is Rocq (each gate check forks a ``coqc``)."""
    return max(4, min(32, (os.cpu_count() or 4)))


# ------------------------------------------------------------------ assembly context


@dataclass(frozen=True)
class AssemblyContext:
    """Everything an assembly needs besides the bodies, carried as one value.

    The packet, the gate, revalidation and integration all assemble the same
    development with the same anchor and the same extra preamble; keeping them in
    one object is what makes "computed and dropped" impossible (ARCHITECTURE.md 8,
    "dead documented features": the plan preamble was parsed and never used).
    """

    dev: Development
    anchor: str
    #: The plan's own preamble (extra ``Require`` lines), inserted into every assembly.
    preamble: str = ""
    #: The design brief shown to provers (``""`` under ``--brief spec-only``).
    design: str = ""

    def siblings(self, graph: Graph, *, exclude: str | None = None) -> list[NodeSpec]:
        return siblings_of(graph, self.dev, exclude=exclude)

    def gate(self, **kw: Any) -> Gate:
        return Gate(self.dev, **kw)


def siblings_of(graph: Graph, dev: Development, *, exclude: str | None = None) -> list[NodeSpec]:
    """Every obligation as it appears in an assembly (contract §5.1).

    Non-root, non-attic nodes not declared in the file, in plan order.  A node
    contributes its body **only while proved**: the graph clears a body on every
    reopen, and the assertion below is the one place that promise is checked, because
    a stale body injected as a proved sibling once broke every other worker's gate.
    """
    out: list[NodeSpec] = []
    for n in graph.nodes():
        if n.rank == "root" or n.proof_status == "attic" or n.name == exclude:
            continue
        if dev.block(n.name) is not None:
            continue  # declared in the file: not an injected obligation
        proved = n.proof_status in PROVED_STATUSES
        assert proved or n.body is None, f"{n.name} is {n.proof_status} but still carries a body"
        out.append(NodeSpec(n.name, n.statement, n.body if proved else None, n.mockable, n.transparent))
    return out


#: Evidence prefix of a node parked without an attempt because a non-mockable sibling
#: is unproved; the amendment path reopens such nodes when that sibling reopens.
BLOCKED_PREFIX = "blocked: non-mockable obligation(s)"


def attempts_spent(graph: Graph, node: Node) -> int:
    """Prover attempts charged to ``node`` at its current statement epoch.

    An ``error`` row is never charged: a missing binary or a gate that could not
    run is not the node's fault.  A ``claimed`` row left by a crash *is* -- the
    worker ran.
    """
    return sum(
        1
        for row in graph.attempts_for(node.id)
        if row.get("role", "prover") == "prover"
        and int(row.get("epoch", 0)) == node.epoch
        and row.get("status") != "error"
    )


def repin_edges(graph: Graph, node_id_: str) -> None:
    """A proof just checked against its dependencies' *current* statements: pin its
    demand edges there.  A proof is of a specific statement epoch and integration
    requires every edge current (PLAN.md 8.1), so whoever records or re-checks a
    proof re-pins -- otherwise the first epoch bump blocked integration for good."""
    for dst, pinned, kind in graph.deps(node_id_):
        target = graph.get(dst)
        if target is not None and target.epoch != pinned:
            graph.add_edge(node_id_, dst, kind=kind)


def ensure_edge(graph: Graph, src: str, dst: str, *, kind: str = "uses") -> None:
    """Add a demand edge only if it is missing.  A restated obligation keeps its
    dependents' pins where their proofs were checked -- ``add_edge`` on an existing
    edge re-pins it to the new epoch and hides exactly the staleness integration
    must see."""
    if not any(d == dst and k == kind for d, _pinned, k in graph.deps(src)):
        graph.add_edge(src, dst, kind=kind)


def last_partial(graph: Graph, node: Node, *, workroot: str | Path | None = None) -> str:
    """The body the last prover attempt at this epoch left behind (a recovered
    partial or a gate-rejected proof), so a resumed node's first attempt starts where
    the previous run stopped rather than from ``admit.`` -- exactly what an in-run
    retry gets.  When no row carries a body and ``workroot`` is given, the latest
    attempt's own directory is read: a worker killed with the process left its work
    in the scratch file, not in a row."""
    rows = [
        row for row in graph.attempts_for(node.id)
        if int(row.get("epoch", -1)) == node.epoch and row.get("role", "prover") == "prover"
    ]
    for row in reversed(rows):
        if row.get("body"):
            return str(row["body"])
    if workroot is not None and rows:
        return partial_in_attempt_dir(workroot, node, int(rows[-1]["id"]))
    return ""


def partial_in_attempt_dir(workroot: str | Path, node: Node, attempt_id: int) -> str:
    """The target's body as the worker left it in ``<workroot>/<node>/a<id>/``, or
    ``""`` (no directory, nothing written, or the untouched placeholder).  Reads the
    attempt's own ``pcp-node.json`` for the scratch file name, so a designed or staged
    development is read under the name the packet gave it."""
    workdir = attempt_dir(workroot, node.id, attempt_id)
    if not workdir.is_dir():
        return ""
    scratch = Path(node.file).name if node.file else None
    meta = workdir / "pcp-node.json"
    if meta.exists():
        try:
            scratch = str(json_load(meta).get("scratch") or scratch)
        except (ValueError, OSError, AttributeError):
            pass
    try:
        result = read_result(workdir, "", target=node.name, scratch_file=scratch)
    except OSError:
        return ""
    body = result.proof.strip()
    return "" if not body or is_placeholder(body) else body


# ------------------------------------------------------------------ outcomes


@dataclass
class NodeOutcome:
    node_id: str
    name: str
    status: str  # qed | stuck | contested | error
    gate: GateResult | None = None
    evidence: str = ""
    attempts: int = 0
    elapsed_s: float = 0.0
    proof: str = ""
    #: Lemma requests only (``why_it_failed`` reads them as "the lemmas it was missing").
    requests: list[dict[str, str]] = field(default_factory=list)
    #: Definition changes the prover asked for, ``requester`` filled.
    amendments: list[AmendmentRequest] = field(default_factory=list)
    #: Parked ``stuck`` for the approver after ``review_after`` failed attempts, with
    #: budget left: the amendment path adjudicates it before anything retries it.
    review: bool = False

    def one_line(self) -> str:
        if self.status == "qed":
            return f"qed       {self.name}  ({self.elapsed_s:.0f}s, {self.attempts} attempt(s))"
        head = {"stuck": "stuck    ", "contested": "contested", "error": "error    "}.get(self.status, self.status)
        asked = f"  [asks: {', '.join(a.describe() for a in self.amendments)[:60]}]" if self.amendments else ""
        review = "  [for review]" if self.review else ""
        return f"{head} {self.name}  {one_line(self.evidence, 100)[:100]}{asked}{review}"

    def to_json(self) -> dict[str, Any]:
        return {
            "node": self.node_id,
            "name": self.name,
            "status": self.status,
            "attempts": self.attempts,
            "elapsed_s": self.elapsed_s,
            "evidence": self.evidence,
            "requests": list(self.requests),
            "amendments": [a.to_json() for a in self.amendments],
            "review": self.review,
        }


@dataclass
class RunReport:
    """The end-of-run summary.  It fits on one screen; the dashboard is optional."""

    outcomes: list[NodeOutcome] = field(default_factory=list)
    elapsed_s: float = 0.0
    #: Attempts dispatched (not nodes): three nodes with six attempts is six.
    dispatched: int = 0
    #: Attempts whose gate failed, across every attempt.
    gate_failures: int = 0

    def by_status(self, status: str) -> list[NodeOutcome]:
        return [o for o in self.outcomes if o.status == status]

    def amendments(self) -> list[AmendmentRequest]:
        """Every distinct amendment the provers asked for, in outcome order, deduped by
        :meth:`AmendmentRequest.key` (two provers hitting the same missing fact is one
        change; the first requester is credited)."""
        seen: set[str] = set()
        out: list[AmendmentRequest] = []
        for o in self.outcomes:
            for a in o.amendments:
                if a.key() in seen:
                    continue
                seen.add(a.key())
                out.append(a)
        return out

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

    def to_json(self) -> dict[str, Any]:
        return {
            "elapsed_s": self.elapsed_s,
            "dispatched": self.dispatched,
            "gate_failures": self.gate_failures,
            "outcomes": [o.to_json() for o in self.outcomes],
        }

    @classmethod
    def combined(cls, reports: Iterable[RunReport]) -> RunReport:
        """Several dispatch rounds as one report: the latest outcome per node wins,
        the counters add up.  Design revisions re-dispatch; the user sees one run."""
        latest: dict[str, NodeOutcome] = {}
        out = cls()
        for report in reports:
            for o in report.outcomes:
                latest[o.node_id] = o
            out.elapsed_s += report.elapsed_s
            out.dispatched += report.dispatched
            out.gate_failures += report.gate_failures
        out.outcomes = list(latest.values())
        return out


def failure_evidence(result: NodeResult, gate: GateResult | None) -> str:
    """What the retry sees: the worker's evidence, then the gate's own words.

    The worker's prose is clipped so the ``gate: FAIL`` block and the compiler tail
    survive the packet's own limit; a 4000-character complaint used to push the one
    thing the retry needed out of the window.
    """
    parts: list[str] = []
    if result.evidence.strip():
        parts.append(result.evidence.strip()[:WORKER_EVIDENCE_LIMIT])
    if gate is not None and not gate.ok:
        parts.append(gate.render())
    if not parts and result.raw:
        parts.append(result.raw[-1500:])
    return "\n\n".join(parts)[:EVIDENCE_LIMIT]


# ------------------------------------------------------------------ the scheduler


class Scheduler:
    """Dispatches the frontier, gates every return, retries with evidence, isolates."""

    def __init__(
        self,
        graph: Graph,
        dev: Development,
        runner: Runner,
        *,
        anchor: str,
        gate: Gate | None = None,
        workroot: str | Path,
        concurrency: int | None = None,
        node_seconds: float = DEFAULT_NODE_SECONDS,
        max_attempts: int = 2,
        skills: Sequence[str] = (),
        state_tools: Sequence[str] = (),
        library: Sequence[Path] = (),
        check_command: str = "pcp check",
        recorder: Any = None,
        corpus: str = "",
        design_brief: str = "",
        index_path: str | Path | None = None,
        round: int = 1,
        on_event: Callable[[str, dict[str, Any]], None] | None = None,
        preamble: str = "",
        deadline_grace_s: float = DEADLINE_GRACE_S,
        amendments: bool = True,
        pause: PausePolicy | ProviderPause | None = None,
        probe: Callable[[], Any] | None = None,
        review_after: int = 0,
        reviewed: Callable[[Node], bool] | None = None,
    ) -> None:
        self.graph = graph
        self.context = AssemblyContext(dev, anchor, preamble, design_brief)
        self.runner = runner
        self.gate = gate or Gate(dev)
        self.workroot = Path(workroot)
        self.concurrency = concurrency or default_concurrency()
        #: The per-attempt clock.  Always this; the run budget's seconds are the
        #: run's, not the worker's (bug class "configuration accepted but ignored").
        self.node_seconds = float(node_seconds)
        self.deadline_grace_s = float(deadline_grace_s)
        self.max_attempts = max(1, int(max_attempts))
        #: After this many failed prover attempts at an epoch (0: never), a node with
        #: budget left is parked ``stuck`` for the approver instead of retried: PLAN.md
        #: 8.9 treats a twice-escalated node as a statement problem, and a verdict costs
        #: seconds where an attempt costs the node's clock.  ``reviewed(node)`` says the
        #: epoch already had its verdict, so the remaining budget is spent normally.
        self.review_after = max(0, int(review_after))
        self.reviewed = reviewed or (lambda _node: False)
        self.skills = list(skills)
        self.state_tools = list(state_tools)
        self.library = [Path(p) for p in library]
        self.check_command = check_command
        self.recorder = recorder
        self.corpus = corpus
        self.index_path = Path(index_path) if index_path is not None else None
        self.round = int(round)
        self.on_event = on_event
        #: Whether a ``stuck`` that asks for an amendment ends the retry loop (the
        #: amendment path will reopen the node).  Off under ``--amendments 0``: the
        #: request is still recorded, but nothing will act on it, so the retry runs.
        self.amendments = bool(amendments)
        self._sem = asyncio.Semaphore(self.concurrency)
        #: The run's one provider pause (module docstring).  ``None``: an outage is an
        #: ``error`` outcome as before -- direct users of the scheduler opt in; ``pcp
        #: prove`` always passes one, disabled by ``--pause-hours 0``.
        self.pause: ProviderPause | None = None
        if isinstance(pause, ProviderPause):
            self.pause = pause
        elif isinstance(pause, PausePolicy) and pause.active:
            self.pause = ProviderPause(pause, probe or provider_probe(runner), on_wait=self._say, on_event=self._pause_event)

    @property
    def dev(self) -> Development:
        return self.context.dev

    @property
    def anchor(self) -> str:
        return self.context.anchor

    def siblings(self) -> list[NodeSpec]:
        return self.context.siblings(self.graph)

    # -- the frontier ------------------------------------------------------
    async def run(self) -> RunReport:
        started = time.perf_counter()
        report = RunReport()
        frontier = self.graph.frontier()
        blocking = [n for n in frontier if not n.mockable]
        parallel = [n for n in frontier if n.mockable]
        for node in blocking:
            self._add(report, await self._isolated(node))
        if parallel:
            results = await asyncio.gather(*(self._isolated(n) for n in parallel), return_exceptions=True)
            crash: BaseException | None = None
            for node, res in zip(parallel, results, strict=True):
                if isinstance(res, NodeOutcome):
                    self._add(report, res)
                elif isinstance(res, Exception):
                    self._add(report, self._crashed(node, res))  # the second net
                elif isinstance(res, BaseException):
                    crash = res
            if crash is not None:
                raise crash
        report.elapsed_s = time.perf_counter() - started
        return report

    def _add(self, report: RunReport, outcome: NodeOutcome) -> None:
        report.outcomes.append(outcome)
        report.dispatched += outcome.attempts
        report.gate_failures += getattr(outcome, "_gate_failures", 0)

    async def _isolated(self, node: Node) -> NodeOutcome:
        try:
            return await self.run_node(node)
        except asyncio.CancelledError:
            raise
        except Exception as exc:  # noqa: BLE001 -- the whole point: one node, not the run
            return self._crashed(node, exc)

    def _crashed(self, node: Node, exc: BaseException) -> NodeOutcome:
        tail = "".join(traceback.format_exception(type(exc), exc, exc.__traceback__))[-TRACEBACK_TAIL:]
        evidence = (
            "the orchestrator failed while running this node (not the worker's fault): "
            f"{type(exc).__name__}: {exc}\n{tail}"
        )
        outcome = NodeOutcome(node.id, node.name, "error", evidence=evidence)
        try:
            self._park(node, evidence)
            self._emit("node.done", node=node.id, status="error", crashed=True)
        except Exception:  # noqa: BLE001 -- the graph itself is broken; the report still says so
            pass
        return outcome

    def _park(self, node: Node, evidence: str) -> None:
        """Leave ``node`` ``stuck`` with ``evidence`` without dispatching it.

        The lattice has no ``open -> stuck`` edge (a node is stuck *after* a claim),
        so an undispatched verdict claims and releases in one breath.
        """
        current = self.graph.get(node.id)
        if current is None:
            return
        if current.proof_status == "open":
            self.graph.set_proof_status(node.id, "claimed")
            current = self.graph.get(node.id)
        if current is not None and current.proof_status == "claimed":
            self.graph.set_proof_status(node.id, "stuck", evidence=evidence)

    def _wants_review(self, node: Node, failed: int, *, first: bool = False) -> bool:
        """``failed`` prover attempts at this epoch have failed and budget remains: hand
        the node to the approver before spending more (only once per epoch).  Not on the
        first attempt of a dispatch right after an amendment reopened the node at its own
        epoch: the retry against the strengthened design comes first, and the review
        reads *its* failure."""
        if not self.review_after or failed < self.review_after or self.reviewed(node):
            return False
        return not (first and (node.evidence or "").startswith(AMENDED_MARKER))

    # -- one node ----------------------------------------------------------
    async def run_node(self, node: Node) -> NodeOutcome:
        started = time.perf_counter()
        outcome = NodeOutcome(node.id, node.name, "stuck")
        spent = attempts_spent(self.graph, node)
        remaining = self.max_attempts - spent
        if remaining <= 0:
            outcome.evidence = f"attempt budget spent ({spent}); raise --attempts or revise the statement"
            if self._wants_review(node, spent, first=True):
                outcome.review = True
                outcome.evidence = node.evidence or outcome.evidence
                self._emit("node.for_review", node=node.id, attempts=spent)
            self._park(node, outcome.evidence)
            outcome.elapsed_s = time.perf_counter() - started
            self._emit("node.done", node=node.id, status=outcome.status)
            return outcome
        blockers = [s.name for s in self.siblings() if not s.mockable and s.body is None and s.name != node.name]
        if blockers:
            outcome.evidence = (
                f"{BLOCKED_PREFIX} " + ", ".join(blockers)
                + " are unproved and cannot be stubbed into this node's file"
            )
            self._park(node, outcome.evidence)
            outcome.elapsed_s = time.perf_counter() - started
            self._emit("node.done", node=node.id, status=outcome.status)
            return outcome

        # A resumed node carries the evidence its last run produced and the body it
        # left behind, so even its first attempt here is evidence-informed rather
        # than a blind repeat from `admit.`.
        evidence = node.evidence or ""
        previous_body = last_partial(self.graph, node, workroot=self.workroot) if evidence else ""
        gate_failures = 0
        stays_open = False
        i = 0
        outages = 0
        while True:
            # Review is checked before the budget: with `--attempts 2 --review-after 2`
            # the second failure is what sends the node to the approver.
            if self._wants_review(node, spent + i, first=i == 0):
                outcome.review = True
                outcome.evidence = outcome.evidence or evidence or f"{spent + i} attempt(s) failed at this epoch"
                self._emit("node.for_review", node=node.id, attempts=spent + i)
                break
            if i >= remaining:
                break
            if self.pause is not None:
                await self.pause.wait_if_paused()
            attempt_no = spent + i + 1
            async with self._sem:
                result, gate_result = await self._attempt(node, attempt_no, evidence, previous_body)
            outage = self._outage_of(result)
            if outage is not None:
                # Not the node's attempt and not its fault: the row stays ``error``
                # (uncharged), the node goes back to ``open``, and the run pauses.
                outages += 1
                self.graph.set_proof_status(node.id, "open")
                if outages <= MAX_OUTAGE_RETRIES and await self._hold(outage, node):
                    continue
                outcome.status = "error"
                outcome.evidence = self._outage_evidence(outage, outages)
                break
            i += 1
            outcome.attempts = i
            outcome.gate = gate_result
            outcome.requests = [r.to_json() for r in result.requests]
            outcome.amendments = requested_amendments(node, result)
            if gate_result is not None and not gate_result.ok:
                gate_failures += 1
            if result.status == "qed" and gate_result is not None and gate_result.ok:
                self.graph.record_proof(node.id, result.proof)
                repin_edges(self.graph, node.id)
                outcome.status, outcome.proof, outcome.evidence = "qed", result.proof, ""
                break
            if result.status == "contested":
                self.graph.set_proof_status(node.id, "contested", evidence=result.evidence)
                outcome.status, outcome.evidence = "contested", result.evidence
                break
            if self.amendments and outcome.amendments and result.status == "stuck":
                # The prover says the design lacks a fact.  Retrying against the same
                # design spends the attempt on the same wall; the amendment path
                # reopens this node with the change as evidence (module docstring).
                outcome.evidence = failure_evidence(result, gate_result)
                self._emit("node.asked_amendment", node=node.id, amendments=[a.to_json() for a in outcome.amendments])
                break
            if gate_result is not None and gate_result.infrastructure:
                # The gate could not run: not the worker's fault, not charged, and
                # the node stays open for a run on a machine whose coqc works.
                outcome.status, outcome.evidence = "error", result.evidence
                self.graph.set_proof_status(node.id, "open")
                stays_open = True
                break
            evidence = failure_evidence(result, gate_result)
            previous_body = result.proof
            outcome.evidence = evidence
            outcome.status = "error" if result.status == "error" else "stuck"
            if result.status == "error":
                break  # infrastructure: retrying burns the budget on nothing
        if outcome.status in ("stuck", "error") and not stays_open:
            self._park(node, outcome.evidence)
        outcome.elapsed_s = time.perf_counter() - started
        outcome._gate_failures = gate_failures  # type: ignore[attr-defined]
        self._emit("node.done", node=node.id, status=outcome.status)
        return outcome

    async def _attempt(
        self, node: Node, attempt_no: int, evidence: str, previous_body: str
    ) -> tuple[NodeResult, GateResult | None]:
        """One attempt: fresh packet, runner, gate, durable row, record."""
        self.graph.set_proof_status(node.id, "claimed")
        attempt_id = self.graph.start_attempt(
            node.id, runner=self.runner.name, owner=node.owner, role="prover", round=self.round
        )
        try:
            siblings = self.siblings()
            packet = build_packet(
                self.graph, node, self.dev, siblings,
                anchor=self.anchor, root=self.workroot, attempt_id=attempt_id,
                evidence=evidence, attempt=attempt_no, skills=self.skills,
                state_tools=self.state_tools, check_command=self.check_command,
                library=self.library, design=self.context.design, previous_body=previous_body,
                index_path=self.index_path, extra_preamble=self.context.preamble,
            )
            payload = NodePayload(
                node_id=node.id, name=node.name, statement=node.statement,
                file=str(self.dev.path), workdir=packet.workdir, scratch_file=self.dev.path.name,
                intent=node.intent, siblings=[(s.name, s.statement) for s in siblings],
                evidence=evidence, budget_seconds=self.node_seconds, attempt=attempt_no,
                skills=self.skills, check_command=self.check_command,
            )
            self._emit("node.dispatched", node=node.id, attempt=attempt_no, attempt_id=attempt_id)
            result = await self._run_with_deadline(node, payload)
            gate_result = await self._gate_if_qed(node, result)
            self.graph.finish_attempt(
                attempt_id,
                status=result.status,
                evidence=result.evidence,
                body=result.proof or None,
                gate=gate_result.to_json() if gate_result else {},
                cost=result.cost,
                requests=requests_json(node, result),
                model=result.model,
            )
        except Exception as exc:
            # Never leave a row claimed: whatever else happens, the store says why.
            try:
                self.graph.finish_attempt(attempt_id, status="error", evidence=f"orchestrator failure: {type(exc).__name__}: {exc}")
            except Exception:  # noqa: BLE001
                pass
            raise
        if self.recorder is not None:
            try:
                self._record(node, attempt_no, attempt_id, result, gate_result, packet.workdir)
            except Exception as exc:  # noqa: BLE001 -- a record is *about* the attempt; it never costs it
                self._emit("record.failed", node=node.id, attempt_id=attempt_id, error=f"{type(exc).__name__}: {exc}")
        return result, gate_result

    # -- the provider pause ------------------------------------------------
    def _outage_of(self, result: NodeResult) -> Outage | None:
        """An outage this scheduler will pause for; ``None`` keeps the old behaviour
        (no pause configured, an ``error`` that is not an outage, a missing CLI)."""
        if self.pause is None or not self.pause.enabled:
            return None
        outage = detect_outage(result)
        return outage if outage is not None and outage.retryable else None

    async def _hold(self, outage: Outage, node: Node) -> bool:
        assert self.pause is not None
        self._log(f"{node.name}: provider outage ({outage.describe()}); pausing the run")
        return await self.pause.hold(outage)

    def _outage_evidence(self, outage: Outage, outages: int) -> str:
        assert self.pause is not None
        waited = self.pause.last_wait_s if self.pause.exhausted is not None else self.pause.waited_s
        note = f"provider outage: {outage.detail} (waited {format_wait(waited)}"
        if self.pause.exhausted is None and outages > MAX_OUTAGE_RETRIES:
            note += f"; {outages} consecutive attempts failed with a provider outage"
        return note + ")"

    def _pause_event(self, kind: str, payload: dict[str, Any]) -> None:
        """``run.paused`` / ``run.resumed`` / ``run.pause_exhausted``: a graph event
        (under no node: the pause is the run's) and the ``on_event`` callback."""
        self.graph.emit(kind, None, **payload)
        self._log(f"{kind}: {payload}")
        if self.on_event:
            self.on_event(kind, {"node": None, **payload})

    def _say(self, message: str) -> None:
        """A pause status line: the operator's terminal, the record's ``run.log``,
        and ``on_event`` for a dashboard -- never a graph event per probe."""
        print(message, file=sys.stderr, flush=True)
        self._log(message)
        if self.on_event:
            self.on_event("run.waiting", {"node": None, "message": message})

    def _log(self, line: str) -> None:
        log = getattr(self.recorder, "log", None)
        if callable(log):
            try:
                log(line)
            except Exception:  # noqa: BLE001 -- a log line never costs the run
                pass

    async def _run_with_deadline(self, node: Node, payload: NodePayload) -> NodeResult:
        """The runner enforces the clock; this is the backstop for one that does not.

        A runner that never returned used to wedge the run with the node ``claimed``
        forever (review finding).  Past the deadline plus the grace period the
        attempt is cancelled -- a subprocess runner kills its process group on
        cancellation -- and whatever the worker left in its directory is read back:
        a complete answer keeps its own status, anything else is a deadline ``stuck``
        with the partial, exactly the shape a runner's own kill produces.
        """
        limit = self.node_seconds + self.deadline_grace_s
        try:
            return await asyncio.wait_for(self.runner.run_node(payload), timeout=limit)
        except TimeoutError:
            pass
        partial = read_result(Path(payload.workdir), "", target=node.name, scratch_file=payload.scratch_file)
        note = (
            f"worker exceeded its {self.node_seconds:.0f}s deadline and the runner did not stop it; "
            f"the scheduler killed the attempt after {limit:.0f}s"
        )
        if partial.status in ("qed", "contested"):
            partial.evidence, partial.timed_out = _join(partial.evidence, note), True
            return partial
        if partial.proof.strip():
            note += f"; recovered a {len(partial.proof.strip().splitlines())}-line partial proof"
        return NodeResult(status="stuck", proof=partial.proof, evidence=note, timed_out=True)

    async def _gate_if_qed(self, node: Node, result: NodeResult) -> GateResult | None:
        """Decide a ``qed``: empty body -> stuck; gate -> gated / stuck / error."""
        if result.status != "qed":
            return None
        if not result.proof.strip():
            result.status = "stuck"
            result.evidence = _join(result.evidence, "the worker answered qed with an empty proof body")
            return None
        gate_result = await asyncio.to_thread(self._gate, node, result.proof)
        if gate_result.infrastructure:
            result.status = "error"
            result.evidence = _join(
                result.evidence,
                "the gate could not run, so this proof is unverified and the attempt is not charged to the node:\n"
                + gate_result.render(),
            )
        elif not gate_result.ok:
            # A worker that says `qed` and does not gate is a failed attempt, not a
            # success to be argued about.  No model reads this; the gate did.
            result.status = "stuck"
        return gate_result

    def _gate(self, node: Node, proof: str) -> GateResult:
        is_anchor = node.name == self.anchor
        specs = [s.with_body(proof) if s.name == node.name else s for s in self.siblings()]
        if not is_anchor and all(s.name != node.name for s in specs):
            specs.append(NodeSpec(node.name, node.statement, proof, node.mockable, node.transparent))
        return self.gate.run(
            self.anchor, specs,
            target=node.name, target_body=proof if is_anchor else None,
            truncate=True, stub_prefix=True, extra_preamble=self.context.preamble,
        )

    def _record(
        self, node: Node, attempt_no: int, attempt_id: int, result: NodeResult,
        gate: GateResult | None, workdir: Path,
    ) -> None:
        from pcp.orch.record import AttemptRecord

        self.recorder.write(
            AttemptRecord(
                run_id=self.recorder.run_id,
                node=node.id,
                lemma=node.name,
                attempt=attempt_no,
                runner=self.runner.name,
                status=result.status,
                solved=result.status == "qed" and gate is not None and gate.ok,
                elapsed_s=result.elapsed_s,
                cost=dict(result.cost),
                evidence=result.evidence,
                gate_report=gate.render() if gate else "",
                compile_output=gate.compile_output if gate else "",
                gate_checks=(gate.to_json()["checks"] if gate else []),
                proof=result.proof,
                requests=requests_json(node, result),
                corpus=self.corpus,
                trace=dict(result.trace),
                attempt_id=attempt_id,
                round=self.round,
                exit_code=result.exit_code,
            ),
            workdir=workdir,
            transcript=result.raw,
        )

    def _emit(self, kind: str, *, node: str | None = None, **payload: Any) -> None:
        self.graph.emit(kind, node, **payload)
        if self.on_event:
            self.on_event(kind, {"node": node, **payload})


def requested_amendments(node: Node, result: NodeResult) -> list[AmendmentRequest]:
    """The result's amendments with the requester filled in.  A ``qed`` asks for
    nothing: a proof that went through did not need the design changed."""
    if result.status == "qed":
        return []
    out: list[AmendmentRequest] = []
    for a in result.amendments:
        if not a.requester:
            a.requester = node.name
        out.append(a)
    return out


def requests_json(node: Node, result: NodeResult) -> list[dict[str, str]]:
    """Both request kinds, kind-tagged, as the attempt row and the record store them."""
    return [r.to_json() for r in result.requests] + [a.to_json() for a in requested_amendments(node, result)]


def _join(*parts: str) -> str:
    return "; ".join(p.strip() for p in parts if p and p.strip())


__all__ = [
    "DEADLINE_GRACE_S",
    "DEFAULT_NODE_SECONDS",
    "MAX_OUTAGE_RETRIES",
    "AssemblyContext",
    "NodeOutcome",
    "PausePolicy",
    "ProviderPause",
    "RunReport",
    "Scheduler",
    "BLOCKED_PREFIX",
    "attempts_spent",
    "default_concurrency",
    "ensure_edge",
    "failure_evidence",
    "last_partial",
    "partial_in_attempt_dir",
    "repin_edges",
    "requested_amendments",
    "requests_json",
    "siblings_of",
]
