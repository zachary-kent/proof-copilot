"""Integration and export (PLAN.md 8.2, 8.7, 13).

A plan *integrates* only when its glue ``Qed``s -- here the glue is the root itself,
proved from children that must by then be proved rather than admitted -- and the
whole file compiles with ``Print Assumptions ⊆ whitelist``.  The gate's own axiom
check is the oracle: no stricter "no assumptions at all" rule is re-derived here to
refuse developments the gate accepted.

The solution export is the artifact a ladder rung hands forward.  Its header is
computed from the *artifact* (``Admitted`` blocks found by the declaration parser,
``Proof.``-less ones included), never only from the graph, and it says
``INCOMPLETE`` / ``PARTIAL`` / ``COMPLETE`` so nothing downstream reads an admit as
a result.
"""

from __future__ import annotations

from collections.abc import Sequence
from pathlib import Path
from typing import Any

from pcp.orch.gate import Gate
from pcp.orch.graph import Graph
from pcp.orch.model import PROVED_STATUSES, Node
from pcp.rocq.assemble import Development, NodeSpec
from pcp.rocq.decls import parse_blocks
from pcp.util.io import atomic_write_text, copy_if_exists, ensure_dir


def obligations(graph: Graph, dev: Development) -> list[Node]:
    """Every non-root, non-attic node not declared in the file, in plan order."""
    return [
        n for n in graph.nodes()
        if n.rank != "root" and n.proof_status != "attic" and dev.block(n.name) is None
    ]


def stale_demands(graph: Graph, nodes: Sequence[Node]) -> list[tuple[Node, str, int, int]]:
    """``(node, dependency id, pinned epoch, current epoch)`` for every demand edge
    pinned behind its dependency's statement epoch (PLAN.md 8.1)."""
    return [(n, dst, pinned, now) for n in nodes for dst, pinned, now in graph.stale_edges(n.id)]


def integrate(graph: Graph, dev: Development, gate: Gate, root: Node, *, preamble: str = "") -> tuple[bool, str]:
    """Completion has a machine oracle: ``Qed`` plus a clean ``Print Assumptions``,
    with every demand edge current -- a proof checked against an obligation's
    earlier statement is not a proof of the plan.  The status writes are one
    transaction, so a crash between them cannot leave half a plan ``integrated``."""
    nodes = obligations(graph, dev)
    missing = [n.name for n in nodes if not (n.body and n.proof_status in PROVED_STATUSES)]
    if missing:
        return False, f"{len(missing)} obligation(s) still open: {', '.join(missing[:6])}"
    root_now = graph.require(root.id)
    if not root_now.body or root_now.proof_status not in PROVED_STATUSES:
        return False, f"the root `{root.name}` is not proved yet"
    stale = stale_demands(graph, [*nodes, root_now])
    if stale:
        node, dst, pinned, now = stale[0]
        dep = graph.get(dst)
        return False, (
            f"{len(stale)} demand edge(s) are stale: `{node.name}` was proved against "
            f"`{dep.name if dep else dst}`@{pinned}, which is now @{now}; that proof must be re-checked first"
        )
    specs = [NodeSpec(n.name, n.statement, n.body, n.mockable, n.transparent) for n in nodes]
    result = gate.run(
        root.name, specs, target_body=root_now.body,
        # Per-node checks truncate for speed; integration compiles the whole file.
        truncate=False, check_assumptions=True, extra_preamble=preamble,
    )
    if result.infrastructure:
        return False, "the integration gate could not run:\n" + result.render()
    if not result.ok:
        return False, "the integration gate failed:\n" + result.render()
    with graph.transaction():
        for n in nodes:
            graph.set_proof_status(n.id, "integrated")
        graph.set_proof_status(root.id, "integrated")
    return True, ""


def export_solution(
    recorder: Any, graph: Graph, dev: Development, root: Node, *, integrated: bool, preamble: str = ""
) -> Path | None:
    """Write what the run produced, finished or not, into ``<record>/solution/``."""
    if recorder is None:
        return None
    nodes = obligations(graph, dev)
    root_now = graph.require(root.id)
    specs = [
        NodeSpec(n.name, n.statement, n.body if n.proof_status in PROVED_STATUSES else None, n.mockable, n.transparent)
        for n in nodes
    ]
    root_body = root_now.body if root_now.proof_status in PROVED_STATUSES else None
    text = dev.assemble(root.name, specs, anchor_body=root_body, truncate=False, extra_preamble=preamble).text
    proved = sorted(s.name for s in specs if s.body is not None) + ([root.name] if root_body else [])
    open_ = sorted(s.name for s in specs if s.body is None) + ([] if root_body else [root.name])
    admitted = sorted(b.name for b in parse_blocks(text) if b.admitted and b.name)
    out_dir = ensure_dir(Path(recorder.root) / "solution")
    target = out_dir / dev.path.name
    atomic_write_text(target, solution_header(root.name, integrated, proved, open_, admitted) + text)
    copy_if_exists(dev.path.parent / "_CoqProject", out_dir / "_CoqProject")
    return target


def solution_header(
    root_name: str, integrated: bool, proved: Sequence[str], open_: Sequence[str], admitted: Sequence[str] = ()
) -> str:
    """The three-way verdict.  ``integrated`` is a claim about the root alone; the
    file's remaining admits are a second claim, and the strong word is reserved for
    when both hold.  An obligation already listed as open is not repeated under
    ADMITTED, and neither is the root."""
    admitted = [n for n in admitted if n != root_name and n not in open_]
    if not integrated:
        verdict = f"INCOMPLETE: `{root_name}` did not integrate. Anything still `Admitted` below is unproved."
    elif admitted:
        verdict = (
            f"PARTIAL: `{root_name}` Qeds and its `Print Assumptions` is clean, but "
            f"{len(admitted)} other specification(s) in this file are still `Admitted`."
        )
    else:
        verdict = f"COMPLETE: `{root_name}` Qeds and `Print Assumptions` is clean."
    return "\n".join([
        "(* Produced by proof-copilot. This is machine-generated work, not a reference.",
        f"   {verdict}",
        f"   proved: {', '.join(proved) or 'nothing'}",
        f"   open:   {', '.join(open_) or 'nothing'}",
        f"   ADMITTED (unproved) in this file: {', '.join(admitted) or 'nothing'}",
        " *)",
        "",
    ])


__all__ = ["export_solution", "integrate", "obligations", "solution_header", "stale_demands"]
