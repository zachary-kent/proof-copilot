"""`AtomicRunner` -- deferred, not cut (PLAN.md 11).

Atomic is strong on the generic parts (parallel stages, bounded repair loops,
resumability, approval gates, multi-provider routing) but its DAG is **authored and
acyclic**, and this graph is discovered at runtime and has renegotiation cycles.  The
audit's recommendation was to drop it outright; it stays on the list only for the
case where durable checkpoints and gates start to mattering more than the cycles.

Deliberately unimplemented.  A stub that pretends to work is worse than one that
says what it would take -- and this module exists so the decision is recorded next to
the code rather than only in the plan.
"""

from __future__ import annotations

from dataclasses import dataclass

from pcp.orch.runners.base import NodePayload, NodeResult

NOTE = (
    "AtomicRunner is deferred (PLAN.md 11). Atomic's DAG is authored and acyclic; "
    "this graph is discovered at runtime and carries renegotiation cycles. Revisit "
    "only if durable checkpoints and cross-provider routing start to matter more "
    "than the cycles do. Requires Node >= 22.19."
)


@dataclass
class AtomicRunner:
    name: str = "atomic"

    def available(self) -> bool:
        return False

    async def run_node(self, node: NodePayload) -> NodeResult:
        return NodeResult(status="error", evidence=NOTE)
