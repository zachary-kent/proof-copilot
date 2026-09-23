"""Crash-resume (PLAN.md 8.11: "resumed after a crash picks up from the SQLite graph").

A run always resumes from the graph; ``--fresh`` is what starts over.  Three rules:

* ``claimed`` (a worker was in flight when the process died) reopens -- unless an
  attempt row already holds a body the gate accepted, in which case the proof is
  *salvaged* and no worker is spent;
* ``stuck`` reopens only while attempts remain at this epoch, so re-running
  ``pcp prove`` in a loop cannot buy a hopeless node two fresh workers per run;
* ``contested`` stays: it is a statement question for the human.

Two things a crash must not lose: a body is salvaged only when it was gated *for
this statement epoch* -- a node reopened by a revision then dispatched may carry an
older gate-passing row for the statement it used to be, which must not mark it
``gated``; and a node
reopened after dying between ``finish_attempt`` and ``set_proof_status`` carries
that attempt's evidence, so its next attempt is evidence-informed rather than a
blind repeat.

A third (ARCHITECTURE.md §10): **work in flight is recovered, not lost**.  The
worker that died with the process left its partial proof in the attempt directory
(``<workroot>/<node>/a<attempt>/``, the scratch file named by ``pcp-node.json``).
That body becomes the row's ``body`` and the node's evidence says so, so the next
packet carries it under "Your previous attempt's proof (partial)" exactly as an
in-run retry would; and the row itself is closed ``stuck`` ("interrupted by a
crash") -- a ``claimed`` row is a live worker, and there is none.  A decomposer or
approver round left ``claimed`` is closed the same way.

And the development a resumed run proves against is the one the graph recorded --
the designed copy after a design round, the staged copy under ``--brief spec-only``
-- never the original file the design was applied *to*.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any

from pcp.orch.gate import GateResult
from pcp.orch.graph import Graph
from pcp.orch.model import Node, node_id
from pcp.orch.protocol import NodeResult
from pcp.orch.schedule import attempts_spent, failure_evidence, partial_in_attempt_dir, repin_edges
from pcp.rocq.assemble import Development

if TYPE_CHECKING:
    from pcp.orch.prove import ProveConfig

DESIGNED_FILE_META = "designed_file"
#: What a node reopened with a recovered partial is told (its packet quotes it).
RESUMED_NOTE = "resumed after a crash; a partial proof from the interrupted attempt is in your file"
#: How an attempt row a crash left ``claimed`` is closed.
INTERRUPTED_NOTE = "interrupted by a crash"
#: Roles whose rounds are closed ``stuck`` when found ``claimed`` (no partial to keep).
ROUND_ROLES: frozenset[str] = frozenset({"decomposer", "approver"})


@dataclass
class ResumeReport:
    """What a resume did: the ``run.resumed`` event's payload."""

    reopened: list[str] = field(default_factory=list)
    salvaged: list[str] = field(default_factory=list)
    #: Nodes whose interrupted attempt left a partial proof now carried forward.
    recovered_partials: list[str] = field(default_factory=list)
    #: Attempt ids a crash left ``claimed`` and this resume closed.
    interrupted: list[int] = field(default_factory=list)

    @property
    def any(self) -> bool:
        return bool(self.reopened or self.salvaged or self.recovered_partials or self.interrupted)

    def to_json(self) -> dict[str, Any]:
        return {
            "reopened": list(self.reopened), "salvaged": list(self.salvaged),
            "recovered_partials": list(self.recovered_partials), "interrupted": list(self.interrupted),
        }


def reopen_incomplete(graph: Graph, *, max_attempts: int, workroot: str | Path | None = None) -> list[str]:
    """Make a resumed run pick up where the last one stopped (module docstring);
    returns the reopened names.  :func:`resume_incomplete` is the same operation with
    the full report."""
    return resume_incomplete(graph, max_attempts=max_attempts, workroot=workroot).reopened


def resume_incomplete(graph: Graph, *, max_attempts: int, workroot: str | Path | None = None) -> ResumeReport:
    """Reopen, salvage, and recover in-flight work (module docstring)."""
    report = ResumeReport()
    for node in graph.nodes():
        report.interrupted += close_interrupted_rounds(graph, node)
        if node.statement_status != "frozen":
            continue
        if node.proof_status == "claimed":
            body = salvageable_body(graph, node)
            if body is not None:
                graph.record_proof(node.id, body)
                repin_edges(graph, node.id)
                graph.emit("proof.salvaged", node.id, name=node.name)
                report.salvaged.append(node.name)
                _close_claimed_prover_rows(graph, node, workroot=None, report=report)
                continue
            prior = last_evidence(graph, node)
            partial = _close_claimed_prover_rows(graph, node, workroot=workroot, report=report)
            evidence = prior
            if partial:
                evidence = "\n\n".join(p for p in (RESUMED_NOTE, prior) if p)
                report.recovered_partials.append(node.name)
                graph.emit("proof.recovered", node.id, name=node.name, lines=len(partial.splitlines()))
            graph.set_proof_status(node.id, "open", evidence=evidence)
            report.reopened.append(node.name)
        elif node.proof_status == "stuck" and attempts_spent(graph, node) < max_attempts:
            graph.set_proof_status(node.id, "open")
            report.reopened.append(node.name)
    return report


def recover_in_flight(graph: Graph, node: Node, *, workroot: str | Path | None) -> str:
    """The partial body the interrupted prover attempt left in its directory (``""``
    when none), read through the attempt's own ``pcp-node.json``.  Only rows at the
    node's current epoch are consulted: an older epoch's partial is a proof of a
    statement that no longer exists."""
    partial = ""
    for row in graph.attempts_for(node.id):
        if row.get("status") != "claimed" or row.get("role", "prover") != "prover":
            continue
        if int(row.get("epoch", -1)) != node.epoch or workroot is None:
            continue
        found = partial_in_attempt_dir(workroot, node, int(row["id"]))
        if found:
            partial = found
    return partial


def _close_claimed_prover_rows(graph: Graph, node: Node, *, workroot: str | Path | None, report: ResumeReport) -> str:
    """Close every prover row a crash left ``claimed``, keeping the partial (if any)
    in the row so :func:`pcp.orch.schedule.last_partial` finds it.  Returns the
    partial recovered at the current epoch."""
    partial = recover_in_flight(graph, node, workroot=workroot)
    for row in graph.attempts_for(node.id):
        if row.get("status") != "claimed" or row.get("role", "prover") != "prover":
            continue
        current = int(row.get("epoch", -1)) == node.epoch
        graph.finish_attempt(int(row["id"]), status="stuck", evidence=INTERRUPTED_NOTE, body=partial or None if current else None)
        report.interrupted.append(int(row["id"]))
    return partial


def close_interrupted_rounds(graph: Graph, node: Node) -> list[int]:
    """Decomposer and approver rows left ``claimed`` by a crash are closed ``stuck``
    (``INTERRUPTED_NOTE``): the round counts (``design_rounds_used`` reads its round
    number either way) and nothing stays "in flight" forever."""
    closed: list[int] = []
    for row in graph.attempts_for(node.id):
        if row.get("status") == "claimed" and row.get("role") in ROUND_ROLES:
            graph.finish_attempt(int(row["id"]), status="stuck", evidence=INTERRUPTED_NOTE)
            closed.append(int(row["id"]))
    return closed


def salvageable_body(graph: Graph, node: Node) -> str | None:
    """The latest body the gate accepted for ``node`` *at its current epoch*."""
    for row in reversed(graph.attempts_for(node.id)):
        if int(row.get("epoch", -1)) != node.epoch or row.get("status") != "qed" or not row.get("body"):
            continue
        gate = _gate_json(row)
        if gate is not None and gate.get("ok") is True:
            return str(row["body"])
    return None


def last_evidence(graph: Graph, node: Node) -> str:
    """What the last finished prover attempt at this epoch reported, in the shape
    the scheduler's own retry would have seen (worker evidence, then the gate)."""
    for row in reversed(graph.attempts_for(node.id)):
        if int(row.get("epoch", -1)) != node.epoch or row.get("finished") is None or row.get("role", "prover") != "prover":
            continue
        gate = _gate_json(row)
        result = NodeResult(status=str(row.get("status") or "stuck"), evidence=str(row.get("evidence") or ""))
        return failure_evidence(result, GateResult.from_json(gate) if gate else None) or node.evidence or ""
    return node.evidence or ""


def _gate_json(row: dict[str, Any]) -> dict[str, Any] | None:
    try:
        gate = json.loads(row.get("gate") or "{}")
    except json.JSONDecodeError:
        return None
    return gate if isinstance(gate, dict) and gate else None


def resume_development(cfg: ProveConfig, graph: Graph, *, contract: Any | None = None) -> Development:
    """The development this run proves against: designed > staged > original."""
    designed = graph.get_meta(DESIGNED_FILE_META)
    if designed and Path(designed).exists():
        return Development(designed)
    if cfg.brief == "spec-only":
        from pcp.orch.prove.design import stage_spec_only

        return stage_spec_only(cfg, node_id(cfg.target), contract=contract)
    return Development(cfg.file)


__all__ = [
    "DESIGNED_FILE_META",
    "INTERRUPTED_NOTE",
    "RESUMED_NOTE",
    "ResumeReport",
    "close_interrupted_rounds",
    "last_evidence",
    "recover_in_flight",
    "reopen_incomplete",
    "resume_development",
    "resume_incomplete",
    "salvageable_body",
]
