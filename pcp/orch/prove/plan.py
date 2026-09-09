"""Planning and freezing: the plan file becomes frozen nodes (PLAN.md 8.11 step 1).

The user is the root decomposer: they state the children in a ``.v`` and the
statements freeze immediately, with only the free sentinels.  What the freeze
guarantees here, by construction rather than by later cleanup:

* the root is inserted **first**, so a plan that restates it can never collide with
  it (the legacy build crashed with an ``IntegrityError`` on a fresh graph);
* a child that restates the root, a declaration already in the file, or another
  child is a *blocking* sentinel hit and is not inserted -- it would otherwise be
  frozen, dispatched and demanded by integration forever;
* the graph is reconciled with the plan **by statement hash**, not by name: an
  edited child is re-frozen at ``epoch+1`` with its body cleared, a removed child is
  retired, and a child whose plan now carries a proof is gated first;
* a plan-supplied ``Qed`` body is **gated** before it enters the graph.  A human
  vouches for the *statements*; the kernel still checks the proofs.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any

from pcp.errors import ToolchainError, UsageError
from pcp.orch.gate import Gate
from pcp.orch.graph import Graph
from pcp.orch.model import PROVED_STATUSES, Node, node_id
from pcp.orch.schedule import ensure_edge, repin_edges
from pcp.orch.sentinels import SentinelHit, SentinelReport, body_hash, run_free_sentinels
from pcp.rocq.assemble import Development, NodeSpec, parse_plan, plan_preamble
from pcp.rocq.decls import THEOREM_HEADS
from pcp.rocq.statement import statement_hash
from pcp.util.io import read_text

if TYPE_CHECKING:
    from pcp.orch.prove import ProveConfig

ROOT_ORDERING = 1_000_000


@dataclass
class PlanContext:
    dev: Development
    specs: list[NodeSpec] = field(default_factory=list)
    preamble: str = ""


def plan_nodes(cfg: ProveConfig) -> PlanContext:
    """Read the development and the plan; the target must be declared in the file."""
    if not Path(cfg.file).exists():
        raise UsageError(f"{cfg.file}: no such file")
    dev = Development(cfg.file)
    if dev.block(cfg.target) is None:
        raise UsageError(f"{cfg.file}: no declaration named {cfg.target!r}")
    specs: list[NodeSpec] = []
    preamble = ""
    if cfg.plan is not None:
        if not Path(cfg.plan).exists():
            raise UsageError(f"{cfg.plan}: no such plan file")
        text = read_text(cfg.plan)
        specs = parse_plan(text)
        preamble = plan_preamble(text).strip()
    return PlanContext(dev=dev, specs=specs, preamble=preamble)


def plan_sentinels(plan: PlanContext, target: str) -> SentinelReport:
    """The free sentinels over the plan, plus the two name-level blocks a hash cannot
    see: a child named like the root, or like any declaration already in the file."""
    dev = plan.dev
    root_block = dev.require_block(target)
    known: dict[str, str] = {}
    for b in dev.blocks:
        if b.name and b.head in THEOREM_HEADS:
            known[statement_hash(b.statement)] = b.name
            known[body_hash(b.statement)] = b.name
    known[statement_hash(root_block.statement)] = target
    known[body_hash(root_block.statement)] = target
    specs: Any = plan.specs  # frozen dataclasses satisfy the sentinel protocol at runtime
    report = run_free_sentinels(specs, existing_hashes=known, root_statement=root_block.statement)
    declared = set(dev.names())
    for spec in plan.specs:
        if spec.name == target:
            report.hits.append(SentinelHit("reduction sentinel", spec.name, "the plan restates the root itself", blocking=True))
        elif spec.name in declared:
            report.hits.append(SentinelHit(
                "duplicate declaration", spec.name,
                "already declared in the file; use it, do not restate it as an obligation", blocking=True,
            ))
    return report


def build_graph(
    cfg: ProveConfig,
    plan: PlanContext,
    *,
    whitelist: Iterable[str] = (),
) -> tuple[Graph, Node, SentinelReport]:
    """Create or resume the graph and reconcile it with the plan (module docstring)."""
    graph = Graph(cfg.graph_path)
    try:
        root = _ensure_root(cfg, graph, plan)
        sentinels = plan_sentinels(plan, cfg.target)
        blocked = {h.node for h in sentinels.blocking}
        wanted = {s.name for s in plan.specs}
        for i, spec in enumerate(plan.specs):
            if spec.name in blocked:
                continue
            _reconcile_child(cfg, graph, plan, root, spec, i, whitelist=whitelist)
        if plan.specs or cfg.plan is not None:
            _retire_dropped(graph, root, wanted)
    except BaseException:
        graph.close()
        raise
    return graph, graph.require(root.id), sentinels


def _ensure_root(cfg: ProveConfig, graph: Graph, plan: PlanContext) -> Node:
    block = plan.dev.require_block(cfg.target)
    root = graph.by_name(cfg.target)
    if root is None:
        return graph.add_node(
            Node(
                id=node_id(cfg.target),
                name=cfg.target,
                statement=block.statement,
                rank="root",
                statement_status="frozen",
                owner="human",
                intent=cfg.intent,
                budget=cfg.budget,
                file=str(cfg.file),
                is_glue=True,
                ordering=ROOT_ORDERING,
                transparent=block.ender == "Defined",
            )
        )
    if root.statement_hash != statement_hash(block.statement):
        # The user edited the root itself: a new statement is a new epoch, and the old
        # proof (if any) is of the old statement.
        root = graph.update(
            root.id, statement=block.statement, statement_hash=statement_hash(block.statement),
            epoch=root.epoch + 1, proof_status="open", body=None, role="human",
        )
        graph.emit("plan.restated", root.id, epoch=root.epoch, name=root.name)
    return root


def _reconcile_child(
    cfg: ProveConfig, graph: Graph, plan: PlanContext, root: Node, spec: NodeSpec, index: int, *, whitelist: Iterable[str]
) -> None:
    child_budget = cfg.budget.split(max(1, len(plan.specs)))
    existing = graph.by_name(spec.name)
    new_hash = statement_hash(spec.statement)
    if existing is None:
        body = spec.body
        if body is not None:
            _gate_plan_body(plan, cfg.target, spec, whitelist=whitelist)
        node = graph.add_node(
            Node(
                id=node_id(spec.name),
                name=spec.name,
                statement=spec.statement.strip(),
                rank="local",
                parent=root.id,
                depth=1,
                statement_status="frozen",
                proof_status="gated" if body is not None else "open",
                body=body,
                mockable=spec.mockable,
                transparent=spec.transparent,
                owner="human",
                intent=cfg.intent,
                budget=child_budget,
                file=str(cfg.file),
                ordering=index,
            )
        )
        graph.add_edge(root.id, node.id)
        return
    if existing.statement_hash != new_hash:
        # Restated: a new statement is a new epoch; the old body proved the old one.
        graph.update(
            existing.id, statement=spec.statement.strip(), statement_hash=new_hash,
            epoch=existing.epoch + 1, proof_status="open", body=None,
            transparent=spec.transparent, ordering=index, role="human",
        )
        graph.emit("plan.restated", existing.id, epoch=existing.epoch + 1, name=existing.name)
        ensure_edge(graph, root.id, existing.id)  # the root's pin stays where its proof was checked
        existing = graph.require(existing.id)
    elif existing.proof_status == "attic":
        graph.set_proof_status(existing.id, "open", role="human")
        graph.emit("plan.revived", existing.id, round_of=root.id)
        existing = graph.require(existing.id)
    if spec.body is not None and existing.proof_status not in PROVED_STATUSES:
        # The plan now carries a proof for a child that has none: gate it, take it.
        _gate_plan_body(plan, cfg.target, spec, whitelist=whitelist)
        if existing.proof_status == "open":
            graph.set_proof_status(existing.id, "claimed")
        graph.record_proof(existing.id, spec.body)
        repin_edges(graph, existing.id)
        graph.emit("plan.proof_taken", existing.id, name=existing.name)


def _gate_plan_body(plan: PlanContext, anchor: str, spec: NodeSpec, *, whitelist: Iterable[str]) -> None:
    """A plan-supplied proof is checked the way a worker's would be, before it enters
    the graph as ``gated`` -- the legacy build trusted it, and a bad plan body then
    broke every child's packet and gate (bugs-pipeline: prove.py:188)."""
    gate = Gate(plan.dev, extra_whitelist=tuple(whitelist))
    others = [NodeSpec(s.name, s.statement, None, s.mockable, s.transparent) for s in plan.specs if s.name != spec.name]
    result = gate.run(
        anchor, [*others, spec], target=spec.name, target_body=None,
        truncate=True, stub_prefix=True, extra_preamble=plan.preamble,
    )
    if result.infrastructure:
        failed = next((c.detail for c in result.checks if not c.ok and not c.advisory), "the gate could not run")
        raise ToolchainError(f"cannot gate the plan's proof of `{spec.name}`: {failed}")
    if not result.ok:
        first = next((f"{c.name}: {c.detail}" for c in result.failures), "gate failed")
        raise UsageError(f"the plan's proof of `{spec.name}` does not pass the gate: {first}")


def _retire_dropped(graph: Graph, root: Node, wanted: set[str]) -> None:
    """Children in the graph the plan no longer states go to the attic if unproved;
    proved ones stay because the root's proof may cite them."""
    retired: list[str] = []
    for node in graph.nodes(parent=root.id):
        if node.name in wanted or node.proof_status == "attic" or node.proof_status in PROVED_STATUSES:
            continue
        if node.owner != "human":
            continue  # decomposer children are the decomposer's to retire
        graph.set_proof_status(node.id, "attic", role="human")
        retired.append(node.name)
    if retired:
        graph.emit("plan.retired", root.id, retired=retired)


def has_children(graph: Graph, root: Node) -> bool:
    return any(n.id != root.id and n.proof_status != "attic" for n in graph.nodes())


__all__ = ["PlanContext", "build_graph", "has_children", "plan_nodes", "plan_sentinels"]
