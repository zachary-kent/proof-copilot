"""A runner with no model behind it (PLAN.md 8.11, the permanent canary).

The canary is one golden end-to-end run that executes in CI and before every
release, and it cannot depend on a provider being reachable, authenticated, or in a
good mood.  This runner replays scripted answers, so the canary tests *the loop* --
dispatch, gating, retry, resume, reporting -- which is the part that is not allowed
to break.
"""

from __future__ import annotations

import asyncio
import time
from dataclasses import dataclass, field
from typing import Callable

from pcp.orch.runners.base import NodePayload, NodeResult


@dataclass
class MockRunner:
    """Answers from a table, optionally with a delay and a scripted first failure."""

    answers: dict[str, str] = field(default_factory=dict)
    #: Nodes that fail on their first attempt and succeed on the retry, so the
    #: evidence-informed retry path is exercised rather than assumed.
    fail_first: set[str] = field(default_factory=set)
    delay: float = 0.0
    name: str = "mock"
    on_dispatch: Callable[[NodePayload], None] | None = None

    def available(self) -> bool:
        return True

    async def run_node(self, node: NodePayload) -> NodeResult:
        started = time.perf_counter()
        if self.on_dispatch:
            self.on_dispatch(node)
        if self.delay:
            await asyncio.sleep(self.delay)
        if node.name in self.fail_first and node.attempt == 1:
            return NodeResult(
                status="stuck",
                evidence="mock: scripted first-attempt failure",
                elapsed_s=time.perf_counter() - started,
            )
        proof = self.answers.get(node.name)
        if proof is None:
            return NodeResult(
                status="stuck",
                evidence=f"mock: no scripted answer for {node.name}",
                elapsed_s=time.perf_counter() - started,
            )
        return NodeResult(
            status="qed",
            proof=proof,
            cost={"requests": 1},
            elapsed_s=time.perf_counter() - started,
        )
