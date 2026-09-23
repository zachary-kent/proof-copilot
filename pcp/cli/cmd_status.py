"""``pcp status`` and ``pcp handoff`` (contract §1.3, §1.4).

Both open the graph read-only: a wrong ``--graph`` path is an error, never a freshly
created empty database that a later ``pcp prove`` would resume from.
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any

from pcp.cli.common import absolute
from pcp.errors import UsageError
from pcp.orch.graph import Graph
from pcp.orch.model import Node
from pcp.util.io import atomic_write_text, json_dumps
from pcp.util.paths import resolve_from

STATUS_ORDER = ("integrated", "gated", "qed", "claimed", "open", "stuck", "contested", "attic")
MARKS = {"integrated": "✓", "gated": "✓", "stuck": "✗", "contested": "?", "claimed": "…"}


def _open(path: Path) -> Graph:
    graph_path = absolute(path)
    assert graph_path is not None
    if not graph_path.exists():
        raise UsageError(f"no graph at {graph_path}")
    return Graph.open_readonly(graph_path)


def node_json(n: Node) -> dict[str, Any]:
    return {
        "id": n.id, "name": n.name, "rank": n.rank, "epoch": n.epoch,
        "statement_status": n.statement_status, "proof_status": n.proof_status,
        "attempts": n.attempts, "evidence": n.evidence,
    }


def render_status(graph: Graph) -> str:
    nodes = graph.nodes()
    summary = graph.summary()
    lines = [" · ".join(f"{summary[k]} {k}" for k in STATUS_ORDER if k in summary) or "empty graph", ""]
    for n in nodes:
        mark = MARKS.get(n.proof_status, "·")
        lines.append(f" {mark} {n.name:32} {n.proof_status:11} {n.statement_status:9} epoch {n.epoch} attempts {n.attempts}")
        if n.evidence and n.proof_status in ("stuck", "contested"):
            lines.append(f"     {' '.join(n.evidence.split())[:150]}")
    return "\n".join(lines)


def cmd_status(args: argparse.Namespace) -> int:
    graph_path = absolute(args.graph)
    if args.missing_ok and graph_path is not None and not graph_path.exists():
        # A project that has never run `pcp prove` is a normal state for a caller that
        # only reports (the Claude Code plugin's status command), not an error.
        print(f"no pcp run in this project yet (no graph at {graph_path}); start one with `pcp prove`")
        return 0
    graph = _open(args.graph)
    try:
        if args.json:
            print(json_dumps({"summary": graph.summary(), "nodes": [node_json(n) for n in graph.nodes()]}))
        else:
            print(render_status(graph))
    finally:
        graph.close()
    return 0


def cmd_handoff(args: argparse.Namespace) -> int:
    from pcp.orch.handoff import render_handoff

    graph = _open(args.graph)
    try:
        node = graph.get(args.node) or graph.by_name(args.node)
        if node is None:
            raise UsageError(f"no node {args.node!r} in {graph.path}")
        text = render_handoff(graph, node)
    finally:
        graph.close()
    out = absolute(args.out) if args.out is not None else resolve_from(f"{node.name}_handoff.v")
    assert out is not None
    atomic_write_text(out, text)
    print(f"wrote {out}")
    return 0
