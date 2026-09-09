"""Shared helpers for the pipeline tests: a plain (Iris-free) development, a plan, a
scripted gate that needs no compiler, and a graph builder."""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from pcp.orch.gate import CHECK_COMPILES, Check, GateResult
from pcp.orch.graph import Graph
from pcp.orch.model import Budget, Node, node_id
from pcp.orch.runners.mock import WRONG_PROOF
from pcp.rocq.assemble import Development

PLAIN_SOURCE = """(* a plain development, no Iris *)
Set Default Proof Using "Type".

Lemma helper (P Q : Prop) : P -> Q -> Q.
Proof.
  intros _ H. exact H.
Qed.

Lemma root (P Q : Prop) : P -> Q -> P.
Proof.
Admitted.
"""

PLAN_SOURCE = """(* the user's plan *)
Lemma c1 (P : Prop) : P -> P.
Proof. Admitted.

Lemma c2 (Q : Prop) : Q -> Q.
Proof. Admitted.
"""

ANSWERS = {"c1": "intros H. exact H.", "c2": "intros H. exact H.", "root": "intros H _. exact H."}


def write_plain(tmp_path: Path, *, source: str = PLAIN_SOURCE, plan: str | None = PLAN_SOURCE) -> tuple[Path, Path | None]:
    corpus = tmp_path / "corpus"
    corpus.mkdir(parents=True, exist_ok=True)
    dev = corpus / "Plain.v"
    dev.write_text(source, encoding="utf-8")
    (corpus / "_CoqProject").write_text("-Q . plain\n", encoding="utf-8")
    plan_path = None
    if plan is not None:
        plan_path = corpus / "plan.v"
        plan_path.write_text(plan, encoding="utf-8")
    return dev, plan_path


def plain_cfg(tmp_path: Path, **kw: Any):
    from pcp.orch.prove import ProveConfig

    dev, plan = write_plain(tmp_path, plan=kw.pop("plan_source", PLAN_SOURCE))
    defaults: dict[str, Any] = dict(
        file=dev, target="root", plan=plan, graph_path=tmp_path / "graph.db", workroot=tmp_path / "work",
        node_seconds=60, budget=Budget(requests=50, seconds=1800), run_lock=False,
    )
    defaults.update(kw)
    return ProveConfig(**defaults)


def build_plain_graph(tmp_path: Path, *, names: tuple[str, ...] = ("c1", "c2"), **node_kw: Any) -> tuple[Graph, Node, Development]:
    """A frozen root with frozen children, no plan file involved."""
    dev_path, _ = write_plain(tmp_path, plan=None)
    dev = Development(dev_path)
    graph = Graph(tmp_path / "graph.db")
    root = graph.add_node(Node(
        id=node_id("root"), name="root", statement=dev.require_block("root").statement, rank="root",
        statement_status="frozen", owner="human", is_glue=True, ordering=1_000_000, file=str(dev_path),
    ))
    for i, name in enumerate(names):
        kw = dict(node_kw)
        child = graph.add_node(Node(
            id=node_id(name), name=name, statement=f"Lemma {name} (P : Prop) : P -> P.", rank="local",
            parent=root.id, depth=1, statement_status="frozen", owner="human", ordering=i, file=str(dev_path), **kw,
        ))
        graph.add_edge(root.id, child.id)
    return graph, root, dev


@dataclass
class FakeGate:
    """Decides like the gate would, without a compiler: the mock's wrong proof fails,
    anything containing ``reject`` fails, everything else passes."""

    reject: tuple[str, ...] = ()
    infrastructure: bool = False
    calls: list[dict[str, Any]] = field(default_factory=list)

    def run(self, anchor: str, nodes: list, *, target: str | None = None, target_body: str | None = None, **kw: Any) -> GateResult:
        target = target or anchor
        body = target_body if target == anchor else next((s.body for s in nodes if s.name == target), "")
        body = body or ""
        self.calls.append({"anchor": anchor, "target": target, "body": body, **kw})
        if self.infrastructure:
            return GateResult(ok=False, checks=[Check(CHECK_COMPILES, False, "gate could not run: no coqc on PATH")], infrastructure=True)
        ok = WRONG_PROOF not in body and not any(r in body for r in self.reject)
        detail = "" if ok else "Error: The reference wrong_proof_from_mock was not found in the current environment."
        return GateResult(ok=ok, checks=[Check(CHECK_COMPILES, ok, detail)], assembled="(* assembled *)", compile_output=detail)

    def run_design(self, *a: Any, **kw: Any) -> GateResult:
        return GateResult(ok=True, checks=[])
