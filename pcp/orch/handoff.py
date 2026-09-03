"""`pcp handoff` -- a stuck node lands in your editor, not in a report (PLAN.md 8.11).

Emits a `.v` carrying the frozen statement, the best partial script, and the blame
trace as comments.  The point is that the human's next move is `coqc` on a file, not
reading a status page and reconstructing the state by hand.
"""

from __future__ import annotations

import json
import textwrap
from typing import Any

from pcp.orch.graph import Graph, Node


def render_handoff(graph: Graph, node: Node) -> str:
    attempts = graph.attempts_for(node.id)
    best = _best_partial(attempts)
    lines: list[str] = []
    lines.append(f"(* {node.name} -- handed off from pcp *)")
    lines.append("(*")
    lines.append(f"   node          {node.id}")
    lines.append(f"   status        {node.proof_status} (statement {node.statement_status}@{node.epoch})")
    lines.append(f"   attempts      {node.attempts}")
    lines.append(f"   source        {node.file}")
    if node.intent:
        lines.append("   intent")
        lines.extend("     " + l for l in textwrap.wrap(node.intent, 88))
    lines.append("*)")
    lines.append("")

    if node.evidence:
        lines.append("(* Why it stopped:")
        lines.extend("   " + l for l in node.evidence.strip().splitlines()[:60])
        lines.append("*)")
        lines.append("")

    deps = graph.deps(node.id)
    if deps:
        lines.append("(* Depends on (pinned epochs): *)")
        for dst, epoch, kind in deps:
            target = graph.get(dst)
            name = target.name if target else dst
            lines.append(f"(*   {name} @{epoch} [{kind}] *)")
        lines.append("")

    requests = _requests(attempts)
    if requests:
        lines.append("(* Lemmas the workers asked for (not created -- requests route through")
        lines.append("   the statement pipeline before anyone proves them): *)")
        for req in requests:
            lines.append(f"(*   {req.get('statement', '').strip()} *)")
            if req.get("rationale"):
                lines.append(f"(*     because: {req['rationale'].strip()} *)")
        lines.append("")

    lines.append(node.statement.strip())
    lines.append("Proof.")
    if best:
        lines.append("  (* best partial script from the attempts above *)")
        lines.extend("  " + l for l in best.strip().splitlines())
    else:
        lines.append("  (* no partial script survived; start from the statement *)")
    lines.append("Admitted.")
    lines.append("")
    return "\n".join(lines)


def _best_partial(attempts: list[dict[str, Any]]) -> str | None:
    """The longest body any attempt produced -- the most progress that survived."""
    bodies = [a.get("body") for a in attempts if a.get("body")]
    if not bodies:
        return None
    return max(bodies, key=len)


def _requests(attempts: list[dict[str, Any]]) -> list[dict[str, str]]:
    out: list[dict[str, str]] = []
    for a in attempts:
        try:
            out.extend(json.loads(a.get("requests") or "[]"))
        except json.JSONDecodeError:
            continue
    return out
