"""The amendment lattice (PLAN.md 8.5): two rungs built, the rest designed.

    refute      proof of `stmt → False`         auto-accept, dependents tainted
    iso         shim `old ⊣⊢ new`               auto-accept, dependents untouched
    strengthen  shim `new ⊢ old`                auto-accept, dependents untouched
    weaken      prose rationale -- no shim can exist   AUDIT

Built: machine-checked :func:`refute` (a counterexample gated in the frozen
environment, with the statement's binders kept so the probe can typecheck at all),
:func:`taint` along the two channels, the deterministic :func:`impact_of` /
:func:`audit_rung` routing, and :func:`replay_first` salvage.  Unbuilt, on purpose,
until measured amendment traffic justifies them: quorum plumbing, shims and their
TTLs, auditor routing, the ``weaken`` vote -- :func:`propose` records where an
amendment *would* go and :func:`apply_amendment` applies one a human accepted.

Everything except :func:`replay_first` (which resume uses) is behind
``config.flag("amendment_lattice")`` and refuses to run with the flag off.

**Definition amendments** (the daily-loop route, no flag): a prover asks for a
conjunct the invariant lacks, the orchestrator applies it to the *definition* and
replays every proof.  The statement-invalidation channel then needs two things the
refutation path does not: :func:`mentions_definition` looks through one level of
definitions (a node stating ``is_lock`` is invalidated when ``lock_inv``, which
``is_lock`` unfolds to, changes), and :func:`reopen_for_amendment` moves the nodes
that failed *against the old definition* -- ``contested`` and ``stuck`` included --
back to ``open`` at ``epoch+1`` with what changed as their evidence.  ``contested ->
open`` is a human-only move in the lattice; this is the human's delegate (the
approver's verdict, or a machine-checked strengthening) acting, so the write is made
under ``role="human"`` on purpose and says so in the event.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Literal

from pcp.errors import UsageError
from pcp.orch.gate import CHECK_STUBS, Gate
from pcp.orch.graph import Graph
from pcp.orch.model import PROVED_STATUSES, Node
from pcp.orch.protocol import AMENDED_MARKER
from pcp.rocq.assemble import Development, NodeSpec
from pcp.rocq.lexer import identifiers, strip_comments
from pcp.rocq.statement import split_head, statement_binders, statement_hash

AmendClass = Literal["refute", "iso", "strengthen", "weaken"]
Rung = Literal["deterministic", "one-auditor", "quorum", "human"]

FLAG = "amendment_lattice"
AUTO_ACCEPT: tuple[AmendClass, ...] = ("refute", "iso", "strengthen")
#: Everyday Iris plumbing, pre-cleared: a `weaken` whose only additions are
#: typeclass constraints the impact replay discharges at every use site.
PRECLEARED_PREFIXES = ("inG ", "Countable ", "EqDecision ", "Inhabited ", "heapGS", "invGS", "!")
#: Heads whose body a statement can mention a definition *through* (one level).
DEFINITION_HEADS: tuple[str, ...] = (
    "Definition", "Fixpoint", "CoFixpoint", "Notation", "Let", "Instance", "Record", "Class",
    "Inductive", "CoInductive", "Variant",
)


def require_flag(config: Any | None) -> None:
    on = config is not None and bool(getattr(config, "flag", lambda *_: False)(FLAG))
    if not on:
        raise UsageError(
            f"the amendment lattice is off (config flag `{FLAG}`); only human edits and "
            "replay-first salvage are on the daily loop"
        )


@dataclass
class ImpactReport:
    """What an amendment costs, computed rather than argued (PLAN.md 8.5)."""

    node: str
    reopened: list[str] = field(default_factory=list)
    statement_invalidated: list[str] = field(default_factory=list)
    new_obligations: list[tuple[str, str]] = field(default_factory=list)
    discharged_automatically: list[str] = field(default_factory=list)
    residue: list[str] = field(default_factory=list)

    def size(self) -> int:
        return len(self.reopened) + len(self.statement_invalidated) + len(self.residue)

    def render(self) -> str:
        lines = [f"impact of amending `{self.node}`:"]
        lines.append(f"  proofs re-opened:        {len(self.reopened)} {', '.join(self.reopened[:8])}")
        lines.append(
            f"  statements invalidated:  {len(self.statement_invalidated)} {', '.join(self.statement_invalidated[:8])}"
        )
        if self.new_obligations:
            lines.append("  new obligations at use sites:")
            lines.extend(f"    {site}: {ob}" for site, ob in self.new_obligations[:12])
        if self.discharged_automatically:
            lines.append(f"  automation discharges:   {', '.join(self.discharged_automatically[:8])}")
        if self.residue:
            lines.append(f"  residue (real work):     {', '.join(self.residue[:8])}")
        return "\n".join(lines)

    def to_json(self) -> dict[str, Any]:
        return {
            "node": self.node, "reopened": list(self.reopened),
            "statement_invalidated": list(self.statement_invalidated),
            "new_obligations": [list(x) for x in self.new_obligations],
            "discharged_automatically": list(self.discharged_automatically),
            "residue": list(self.residue),
        }


@dataclass
class Amendment:
    node: str
    klass: AmendClass
    statement: str
    rationale: str = ""
    evidence: str = ""
    status: str = "proposed"  # proposed | accepted | rejected
    impact: ImpactReport | None = None
    rung: Rung = "deterministic"

    def auto_acceptable(self) -> bool:
        return self.klass in AUTO_ACCEPT

    def to_json(self) -> dict[str, Any]:
        return {
            "node": self.node, "klass": self.klass, "statement": self.statement,
            "rationale": self.rationale, "evidence": self.evidence, "status": self.status,
            "impact": self.impact.to_json() if self.impact else None, "rung": self.rung,
        }


# ------------------------------------------------------------------ classification


def classify(old: str, new: str) -> AmendClass:
    """A heuristic first guess; the *evidence* (shim or counterexample) decides.
    More explicit binder groups is a ``weaken`` (a hypothesis was added)."""
    if statement_hash(old) == statement_hash(new):
        return "iso"
    if len(statement_binders(new)) > len(statement_binders(old)):
        return "weaken"
    return "strengthen"


def precleared(added: list[str]) -> bool:
    return bool(added) and all(a.strip().startswith(PRECLEARED_PREFIXES) for a in added)


def audit_rung(node: Node, amendment: Amendment, impact: ImpactReport) -> Rung:
    """Blast radius picks the rung; audit is a ladder climbed only as needed."""
    if amendment.auto_acceptable():
        return "deterministic"
    if node.rank == "root":
        return "human"
    if node.rank == "interface":
        return "quorum" if impact.size() > 6 else "one-auditor"
    return "one-auditor" if impact.size() else "deterministic"


def mentions(statement: str, name: str) -> bool:
    """Whether ``statement`` refers to ``name`` as an identifier -- ``inv`` is not a
    reference in ``invariant_holds``."""
    return name in identifiers(strip_comments(statement))


def impact_of(graph: Graph, node: Node) -> ImpactReport:
    """Pure graph arithmetic over the transitive dependents, on two channels:
    statement-invalidation (the dependent's statement mentions the node) and
    proof-invalidation (only its proof did)."""
    report = ImpactReport(node=node.name)
    for dep_id in graph.transitive_dependents(node.id):
        dep = graph.get(dep_id)
        if dep is None:
            continue
        if mentions(dep.statement, node.name):
            report.statement_invalidated.append(dep.name)
        else:
            report.reopened.append(dep.name)
    return report


def mentions_definition(dev: Development, statement: str, definition: str) -> bool:
    """Whether ``statement`` depends on ``definition``: directly, or through one other
    definition whose body mentions it.

    One level, deliberately: ``is_lock γ lk R`` unfolds to ``inv N (lock_inv γ lk R)``
    and a change to ``lock_inv`` changes what ``is_lock`` means, but chasing the whole
    closure would reopen every statement in the file for every amendment and turn
    the incremental route back into the full revision it replaces.
    """
    if mentions(statement, definition):
        return True
    for block in dev.blocks:
        if not block.name or block.name == definition or block.head not in DEFINITION_HEADS:
            continue
        if mentions(block.statement, definition) and mentions(statement, block.name):
            return True
    return False


def statement_invalidated(graph: Graph, dev: Development, definition: str) -> list[Node]:
    """Non-root, non-attic nodes whose statement (one level deep) mentions the amended
    definition -- the statement-invalidation channel of PLAN.md 8.5 for a definition
    rather than a lemma.  The root is the caller's: ``revalidate`` replays it."""
    return [
        n for n in graph.nodes()
        if n.rank != "root" and n.proof_status != "attic" and mentions_definition(dev, n.statement, definition)
    ]


def reopen_for_amendment(graph: Graph, nodes: list[Node], *, definition: str, detail: str) -> list[str]:
    """Every listed node -> ``open`` at ``epoch+1``, body cleared, ``detail`` as its
    evidence (prefixed :data:`AMENDED_MARKER` so the retry packet says exactly what
    changed).  Returns the names, in order; the root is included when listed; only
    the attic is left alone.

    Written as ``role="human"``: ``contested -> open`` is adjudication and no model
    may perform it (PLAN.md 8.1), and this call *is* the adjudication being carried
    out -- an approver's verdict or a machine-checked strengthening standing in for
    the human's edit.  The epoch bump is what grants the fresh attempts: attempts are
    counted per statement epoch (``schedule.attempts_spent``).
    """
    evidence = detail.strip() if detail.strip().startswith(AMENDED_MARKER) else f"{AMENDED_MARKER} {detail.strip()}"
    reopened: list[str] = []
    with graph.transaction():
        for listed in nodes:
            node = graph.require(listed.id)
            if node.proof_status == "attic":
                continue
            graph.update(node.id, proof_status="open", epoch=node.epoch + 1, evidence=evidence, role="human")
            if node.body is not None:
                graph.clear_body(node.id, role="human")
            graph.emit(
                "node.reopened_by_amendment", node.id, definition=definition, from_status=node.proof_status,
                from_epoch=node.epoch, to_epoch=node.epoch + 1, role="human", detail=evidence[:400],
            )
            reopened.append(node.name)
    return reopened


# ------------------------------------------------------------------ the built rungs


def refutation_statement(statement: str) -> str:
    """``Lemma X__refutation <binders> : (<prop>) -> False.`` -- the binders are kept,
    because a proposition with unbound variables cannot typecheck, so without them no
    refutation could ever check."""
    head, binders, ty = split_head(statement)
    if not head:
        raise UsageError("cannot refute a statement with no top-level colon")
    words = head.split()
    name = words[-1]
    prop = ty.strip()
    if prop.endswith("."):
        prop = prop[:-1].rstrip()
    probe = f"{name}__refutation"
    return f"Lemma {probe}{(' ' + binders) if binders else ''} : ({prop}) -> False."


def _anchor_and_siblings(graph: Graph, dev: Development, node: Node) -> tuple[str, list[NodeSpec]]:
    """Anchor at the file's root declaration (the node itself when it is in the file),
    every other obligation stubbed or proved as the graph says."""
    root = next((n for n in graph.nodes() if n.rank == "root"), None)
    anchor = node.name if dev.block(node.name) is not None else (root.name if root else "")
    if not anchor or dev.block(anchor) is None:
        raise UsageError(f"{dev.path}: no declaration anchors `{node.name}`")
    siblings = [
        NodeSpec(n.name, n.statement, n.body if n.proof_status in PROVED_STATUSES else None, n.mockable, n.transparent)
        for n in graph.nodes()
        if n.name != anchor and n.proof_status != "attic" and dev.block(n.name) is None
    ]
    return anchor, siblings


def refute(
    graph: Graph, dev: Development, gate: Gate, node: Node, *, counterexample: str, config: Any | None = None,
    preamble: str = "",
) -> Amendment:
    """Machine-checked refutation: ``stmt → False`` gated in the frozen environment.

    Auto-accepted when it checks and rests on no admitted stub (a refutation that
    needs an unproved sibling is not machine-checked).  A refuted fixed root is a
    legitimate research outcome: evidence, not failure.
    """
    require_flag(config)
    anchor, siblings = _anchor_and_siblings(graph, dev, node)
    probe_name = f"{node.name}__refutation"
    probe = NodeSpec(probe_name, refutation_statement(node.statement), counterexample)
    result = gate.run(
        anchor, [*siblings, probe], target=probe_name, target_body=None,
        truncate=True, stub_prefix=True, extra_preamble=preamble,
    )
    leaning = next((c.detail for c in result.checks if c.name == CHECK_STUBS and c.detail), "")
    amendment = Amendment(node=node.name, klass="refute", statement=node.statement, evidence=counterexample)
    if result.ok and not leaning:
        amendment.status = "accepted"
        graph.update(node.id, statement_status="refuted", role="human")
        graph.emit("statement.refuted", node.id, evidence=counterexample[:400])
        taint(graph, node, config=config)
    else:
        amendment.status = "rejected"
        amendment.rationale = (
            "the refutation rests on admitted stubs: " + leaning if result.ok
            else "the refutation does not check:\n" + result.render()
        )
    return amendment


def taint(graph: Graph, node: Node, *, config: Any | None = None) -> list[str]:
    """Propagate a refutation along the two channels (PLAN.md 8.5)."""
    require_flag(config)
    tainted: list[str] = []
    for dep_id in graph.transitive_dependents(node.id):
        dep = graph.get(dep_id)
        if dep is None:
            continue
        if mentions(dep.statement, node.name):
            graph.update(dep.id, statement_status="proposed", proof_status="open", body=None, role="human")
        else:
            graph.update(dep.id, proof_status="open", body=None, role="human")
        tainted.append(dep.name)
    graph.emit("statement.tainted", node.id, dependents=tainted)
    return tainted


def propose(graph: Graph, node: Node, amendment: Amendment, *, config: Any | None = None) -> Amendment:
    """Compute where an amendment belongs on the audit ladder and record it."""
    require_flag(config)
    amendment.impact = impact_of(graph, node)
    amendment.rung = audit_rung(node, amendment, amendment.impact)
    graph.emit(
        "amendment.proposed", node.id, klass=amendment.klass, rung=amendment.rung,
        from_epoch=node.epoch, to_epoch=node.epoch + 1, impact=amendment.impact.to_json(),
    )
    return amendment


def apply_amendment(graph: Graph, node: Node, amendment: Amendment, *, config: Any | None = None) -> Node | None:
    """Bump the epoch.  Dependents' pinned edges go stale, which is the whole point."""
    require_flag(config)
    if amendment.status != "accepted":
        return None
    current = graph.require(node.id)
    updated = graph.update(
        node.id,
        statement=amendment.statement,
        statement_hash=statement_hash(amendment.statement),
        epoch=current.epoch + 1,
        statement_status="frozen",
        proof_status="open",
        body=None,
        role="human",
    )
    graph.emit("statement.amended", node.id, klass=amendment.klass, epoch=current.epoch + 1)
    return updated


def replay_first(graph: Graph, dev: Development, gate: Gate, root: Node, node: Node, *, preamble: str = "") -> bool:
    """Salvage before dispatch (PLAN.md 8.5): replay every recorded body, newest
    first, against the current development; the first that gates is recorded.
    Deterministic and nearly free next to a worker."""
    bodies = [str(a["body"]) for a in graph.attempts_for(node.id) if a.get("body")]
    if not bodies:
        return False
    is_anchor = dev.block(node.name) is not None
    anchor = node.name if is_anchor else root.name
    siblings = [
        NodeSpec(n.name, n.statement, n.body if n.proof_status in PROVED_STATUSES else None, n.mockable, n.transparent)
        for n in graph.nodes()
        if n.id != node.id and n.name != anchor and n.proof_status != "attic" and dev.block(n.name) is None
    ]
    for body in reversed(bodies):
        specs = siblings if is_anchor else [*siblings, NodeSpec(node.name, node.statement, body, node.mockable, node.transparent)]
        result = gate.run(
            anchor, specs, target=node.name, target_body=body if is_anchor else None,
            truncate=True, stub_prefix=True, extra_preamble=preamble,
        )
        if result.ok:
            current = graph.require(node.id)
            if current.proof_status == "open":
                graph.set_proof_status(node.id, "claimed")
            graph.record_proof(node.id, body)
            graph.emit("proof.replayed", node.id)
            return True
    return False


__all__ = [
    "AMENDED_MARKER",
    "AUTO_ACCEPT",
    "DEFINITION_HEADS",
    "FLAG",
    "Amendment",
    "ImpactReport",
    "apply_amendment",
    "audit_rung",
    "classify",
    "impact_of",
    "mentions",
    "mentions_definition",
    "precleared",
    "propose",
    "refutation_statement",
    "refute",
    "reopen_for_amendment",
    "replay_first",
    "require_flag",
    "statement_invalidated",
    "taint",
]
