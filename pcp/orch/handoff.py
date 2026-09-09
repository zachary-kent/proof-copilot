"""``pcp handoff`` -- a stuck node lands in your editor, not in a report (PLAN.md 8.11).

Emits a ``.v`` carrying the frozen statement, the best partial script, and the blame
trace as comments, in the layout of contract §1.4.  Everything quoted inside a
comment is escaped (``*)`` and ``(*`` cannot terminate or nest it), and the partial
script is chosen among bodies that *are* proof bodies -- a gate-rejected hostile body
never lands in the user's editor just because it was the longest.
"""

from __future__ import annotations

import json
import textwrap
from typing import Any

from pcp.orch.graph import Graph
from pcp.orch.model import Node
from pcp.rocq.body import is_placeholder, validate_body

EVIDENCE_LINES = 60


def comment_safe(text: str) -> str:
    """Make ``text`` safe inside a Rocq comment: no ``*)`` / ``(*`` survive."""
    return text.replace("*)", "* )").replace("(*", "( *")


def render_handoff(graph: Graph, node: Node) -> str:
    attempts = graph.attempts_for(node.id)
    best = best_partial(node, attempts)
    lines: list[str] = []
    lines.append(f"(* {comment_safe(node.name)} -- handed off from pcp *)")
    lines.append("(*")
    lines.append(f"   node          {node.id}")
    lines.append(f"   status        {node.proof_status} (statement {node.statement_status}@{node.epoch})")
    lines.append(f"   attempts      {node.attempts}")
    lines.append(f"   source        {comment_safe(node.file)}")
    if node.intent:
        lines.append("   intent")
        lines.extend("     " + ln for ln in textwrap.wrap(comment_safe(node.intent), 88))
    lines.append("*)")
    lines.append("")

    if node.evidence:
        lines.append("(* Why it stopped:")
        lines.extend("   " + ln for ln in comment_safe(node.evidence.strip()).splitlines()[:EVIDENCE_LINES])
        lines.append("*)")
        lines.append("")

    deps = graph.deps(node.id)
    if deps:
        lines.append("(* Depends on (pinned epochs): *)")
        for dst, epoch, kind in deps:
            target = graph.get(dst)
            name = target.name if target else dst
            lines.append(f"(*   {comment_safe(name)} @{epoch} [{comment_safe(kind)}] *)")
        lines.append("")

    requests = collect_requests(attempts)
    if requests:
        lines.append("(* Lemmas the workers asked for (not created -- requests route through")
        lines.append("   the statement pipeline before anyone proves them): *)")
        for req in requests:
            lines.append(f"(*   {comment_safe(req.get('statement', '').strip())} *)")
            if req.get("rationale"):
                lines.append(f"(*     because: {comment_safe(str(req['rationale']).strip())} *)")
        lines.append("")

    lines.append(node.statement.strip())
    lines.append("Proof.")
    if best:
        lines.append("  (* best partial script from the attempts above *)")
        lines.extend("  " + ln for ln in best.strip().splitlines())
    else:
        lines.append("  (* no partial script survived; start from the statement *)")
    lines.append("Admitted.")
    lines.append("")
    return "\n".join(lines)


def best_partial(node: Node, attempts: list[dict[str, Any]]) -> str | None:
    """The longest body that is structurally a proof body: the node's own gated body
    first, then any attempt's, never a placeholder and never a body that would not
    even pass the static gate."""
    candidates: list[str] = []
    if node.body and not is_placeholder(node.body):
        candidates.append(node.body)
    for a in attempts:
        body = a.get("body")
        if body and not is_placeholder(body) and not validate_body(body):
            candidates.append(str(body))
    if not candidates:
        return None
    return max(candidates, key=len)


def collect_requests(attempts: list[dict[str, Any]]) -> list[dict[str, str]]:
    """Every lemma request any attempt filed (bad JSON and non-objects skipped)."""
    out: list[dict[str, str]] = []
    for a in attempts:
        raw = a.get("requests")
        if isinstance(raw, list):
            items: Any = raw
        else:
            try:
                items = json.loads(raw or "[]")
            except (json.JSONDecodeError, TypeError):
                continue
        if not isinstance(items, list):
            continue
        for req in items:
            if isinstance(req, dict) and str(req.get("statement", "")).strip():
                out.append({"statement": str(req["statement"]), "rationale": str(req.get("rationale", "") or "")})
    return out
