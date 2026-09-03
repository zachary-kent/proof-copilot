"""The amendment lattice (PLAN.md 8.5).

A frozen statement changes only through a typed amendment, and the crucial
observation is that **three of the four classes are machine-checkable**, so scarce
audit attention concentrates on the fourth.

    refute      proof of `stmt → False`         auto-accept, dependents tainted
    iso         shim `old ⊣⊢ new`               auto-accept, dependents untouched
    strengthen  shim `new ⊢ old`                auto-accept, dependents untouched
    weaken      prose rationale -- no shim can exist   AUDIT

`weaken` is the class the observed failure lives in: hypotheses added to make proofs
go through.  Its obligation does not vanish, it *moves* -- every added hypothesis
must now be discharged at every use site -- so before any vote the graph computes a
deterministic **impact report** and "just add a hypothesis" stops looking free.

Two rungs are built, per the plan's own phasing: machine-checked ``refute`` and human
edit.  Quorum plumbing, shim TTLs and audit routing stay on paper until measured
amendment traffic justifies them; the routing decision is computed here so that when
they are built there is somewhere to put them.
"""

from __future__ import annotations

import time
from dataclasses import dataclass, field
from typing import Literal

from pcp.orch.assemble import Development, NodeSpec
from pcp.orch.gate import Gate
from pcp.orch.graph import Graph, Node
from pcp.orch.hashing import statement_hash

AmendClass = Literal["refute", "iso", "strengthen", "weaken"]
Rung = Literal["deterministic", "one-auditor", "quorum", "human"]

AUTO_ACCEPT: tuple[AmendClass, ...] = ("refute", "iso", "strengthen")

#: Everyday Iris plumbing, pre-cleared: a `weaken` whose only additions are typeclass
#: constraints the impact replay discharges automatically at every use site.
_PRECLEARED_PREFIXES = ("inG ", "Countable ", "EqDecision ", "Inhabited ", "heapGS", "invGS", "!")


@dataclass
class ImpactReport:
    """What a `weaken` actually costs, computed rather than argued.

    Auditors vote with the true cost in hand: which dependents re-open, which new
    obligations appear at which call sites, and which of those automation already
    discharges.
    """

    node: str
    reopened: list[str] = field(default_factory=list)
    statement_invalidated: list[str] = field(default_factory=list)
    new_obligations: list[tuple[str, str]] = field(default_factory=list)
    discharged_automatically: list[str] = field(default_factory=list)
    residue: list[str] = field(default_factory=list)

    def render(self) -> str:
        lines = [f"impact of amending `{self.node}`:"]
        lines.append(f"  proofs re-opened:        {len(self.reopened)} {', '.join(self.reopened[:8])}")
        lines.append(
            f"  statements invalidated:  {len(self.statement_invalidated)} "
            f"{', '.join(self.statement_invalidated[:8])}"
        )
        if self.new_obligations:
            lines.append("  new obligations at use sites:")
            for site, obligation in self.new_obligations[:12]:
                lines.append(f"    {site}: {obligation}")
        if self.discharged_automatically:
            lines.append(f"  automation discharges:   {', '.join(self.discharged_automatically[:8])}")
        if self.residue:
            lines.append(f"  residue (real work):     {', '.join(self.residue[:8])}")
        return "\n".join(lines)

    def size(self) -> int:
        return len(self.reopened) + len(self.statement_invalidated) + len(self.residue)


@dataclass
class Amendment:
    node: str
    klass: AmendClass
    statement: str
    rationale: str = ""
    evidence: str = ""
    status: str = "proposed"
    impact: ImpactReport | None = None
    rung: Rung = "deterministic"

    def auto_acceptable(self) -> bool:
        return self.klass in AUTO_ACCEPT


def classify(old: str, new: str) -> AmendClass:
    """A heuristic first guess; the *evidence* is what actually decides.

    ``iso`` and ``strengthen`` are proved by a shim, ``refute`` by a counterexample.
    Anything with no shim and no counterexample is ``weaken`` by definition, which is
    why that class is the one that costs an audit.
    """
    if statement_hash(old) == statement_hash(new):
        return "iso"
    if _binder_count(new) > _binder_count(old):
        return "weaken"
    return "strengthen"


def _binder_count(statement: str) -> int:
    from pcp.orch.assemble import statement_binders

    return len(statement_binders(statement))


def precleared(added: list[str]) -> bool:
    """Typeclass plumbing additions are pre-cleared (PLAN.md 8.5, last paragraph)."""
    return bool(added) and all(a.strip().startswith(_PRECLEARED_PREFIXES) for a in added)


def audit_rung(graph: Graph, node: Node, amendment: Amendment, impact: ImpactReport) -> Rung:
    """Blast radius picks the rung; audit is a ladder climbed only as needed."""
    if amendment.auto_acceptable():
        return "deterministic"
    if node.rank == "root":
        return "human"
    if node.rank == "interface":
        return "quorum" if impact.size() > 6 else "one-auditor"
    return "one-auditor" if impact.size() else "deterministic"


def impact_of(graph: Graph, node: Node) -> ImpactReport:
    """Deterministic blast-radius computation -- pure graph arithmetic."""
    report = ImpactReport(node=node.name)
    for dependent_id in graph.transitive_dependents(node.id):
        dep = graph.get(dependent_id)
        if dep is None:
            continue
        # Two mechanically distinguishable channels (PLAN.md 8.5, Falsification
        # propagation): proof-invalidation re-opens a proof; statement-invalidation
        # means the dependent's statement no longer means anything.
        if node.name in dep.statement:
            report.statement_invalidated.append(dep.name)
        else:
            report.reopened.append(dep.name)
    return report


def refute(
    graph: Graph,
    dev: Development,
    gate: Gate,
    node: Node,
    *,
    counterexample: str,
) -> Amendment:
    """Machine-checked refutation: a proof of `stmt → False` in the frozen environment.

    Auto-accepted when it checks, because there is nothing for a model to judge.  A
    refuted fixed root is a legitimate research outcome and the pipeline treats it as
    a success mode: it returns evidence, not failure.
    """
    from pcp.orch.assemble import NodeSpec as _NodeSpec

    probe_name = f"{node.name}__refutation"
    probe = _NodeSpec(
        name=probe_name,
        statement=f"Lemma {probe_name} : ({_proposition(node.statement)}) -> False.",
        body=counterexample,
    )
    siblings = [
        NodeSpec(name=n.name, statement=n.statement, body=n.body)
        for n in graph.nodes()
        if n.id != node.id and not dev.block(n.name)
    ]
    result = gate.run(node.name, siblings + [probe], target_body=None, target=node.name)
    amendment = Amendment(
        node=node.name,
        klass="refute",
        statement=node.statement,
        evidence=counterexample,
        status="accepted" if result.ok else "rejected",
    )
    if result.ok:
        graph.update(node.id, statement_status="refuted")
        graph.emit("statement.refuted", node.id, evidence=counterexample[:400])
        taint(graph, node)
    else:
        amendment.rationale = "the refutation does not check:\n" + result.render()
    return amendment


def taint(graph: Graph, node: Node) -> list[str]:
    """Propagate a refutation to transitive dependents along the two channels."""
    tainted: list[str] = []
    for dependent_id in graph.transitive_dependents(node.id):
        dep = graph.get(dependent_id)
        if dep is None:
            continue
        if node.name in dep.statement:
            graph.update(dep.id, statement_status="proposed", proof_status="open", body=None)
        else:
            graph.update(dep.id, proof_status="open", body=None)
        tainted.append(dep.name)
    graph.emit("statement.tainted", node.id, dependents=tainted)
    return tainted


def propose(graph: Graph, node: Node, amendment: Amendment) -> Amendment:
    """Record an amendment and compute where it belongs on the audit ladder."""
    amendment.impact = impact_of(graph, node)
    amendment.rung = audit_rung(graph, node, amendment, amendment.impact)
    graph.db.execute(
        "INSERT INTO amendments(node, from_epoch, to_epoch, klass, status, rationale, evidence, impact, "
        "statement, created_at) VALUES(?,?,?,?,?,?,?,?,?,?)",
        (
            node.id, node.epoch, node.epoch + 1, amendment.klass, amendment.status,
            amendment.rationale, amendment.evidence, amendment.impact.render(),
            amendment.statement, time.time(),
        ),
    )
    graph.db.commit()
    graph.emit("amendment.proposed", node.id, klass=amendment.klass, rung=amendment.rung)
    return amendment


def apply_amendment(graph: Graph, node: Node, amendment: Amendment) -> Node | None:
    """Bump the epoch.  Dependents' pinned edges go stale, which is the whole point."""
    if amendment.status != "accepted":
        return None
    updated = graph.update(
        node.id,
        statement=amendment.statement,
        statement_hash=statement_hash(amendment.statement),
        epoch=node.epoch + 1,
        statement_status="frozen",
        proof_status="open",
        body=None,
    )
    graph.emit("statement.amended", node.id, klass=amendment.klass, epoch=node.epoch + 1)
    return updated


def replay_first(graph: Graph, dev: Development, gate: Gate, node: Node) -> bool:
    """Salvage before dispatch (PLAN.md 8.5, Falsification propagation).

    On any re-opening, replay the old proof script against the new epoch before
    spending a worker on it.  After small amendments most proofs survive verbatim,
    and replay is deterministic and nearly free.
    """
    attempts = graph.attempts_for(node.id)
    bodies = [a["body"] for a in attempts if a.get("body")]
    if not bodies:
        return False
    siblings = [
        NodeSpec(name=n.name, statement=n.statement, body=n.body)
        for n in graph.nodes()
        if n.id != node.id and not dev.block(n.name)
    ]
    for body in reversed(bodies):
        is_anchor = bool(dev.block(node.name))
        specs = siblings if is_anchor else siblings + [NodeSpec(node.name, node.statement, body)]
        result = gate.run(
            node.name if is_anchor else _anchor_of(dev, graph),
            specs,
            target_body=body if is_anchor else None,
            target=node.name,
        )
        if result.ok:
            graph.set_proof_status(node.id, "gated", body=body)
            graph.emit("proof.replayed", node.id)
            return True
    return False


def _anchor_of(dev: Development, graph: Graph) -> str:
    for n in graph.nodes():
        if n.rank == "root":
            return n.name
    return dev.blocks[0].name if dev.blocks else ""


def _proposition(statement: str) -> str:
    """The proposition part of `Lemma name binders : P.` -- everything after the colon."""
    body = statement.strip().rstrip(".")
    idx = body.find(":")
    depth = 0
    for i, ch in enumerate(body):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0 and not body.startswith("::", i):
            idx = i
            break
    return body[idx + 1 :].strip()
