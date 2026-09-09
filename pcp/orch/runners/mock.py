"""A runner with no model behind it (PLAN.md 8.11, the permanent canary).

The canary is one golden end-to-end run that executes in CI and before every
release, and it cannot depend on a provider being reachable, authenticated, or in a
good mood.  This runner replays scripted answers, so the canary tests *the loop* --
dispatch, gating, retry, resume, reporting -- which is the part that must not break.

It answers the way a real worker does: by writing ``answer.json`` into the attempt's
directory and letting :func:`read_result` read it back, so the packet/answer path is
exercised rather than bypassed.
"""

from __future__ import annotations

import asyncio
from collections.abc import Callable, Iterable, Mapping
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from pcp.orch.protocol import ANSWER_FILE, NodePayload, NodeResult, read_result
from pcp.util.io import ensure_dir, json_dump

#: An unbound identifier: compiles nowhere, so the gate rejects it for a reason the
#: retry evidence can name.
WRONG_PROOF = "exact wrong_proof_from_mock."


@dataclass
class MockRunner:
    """Answers from a table, optionally with a delay and scripted first failures."""

    answers: Mapping[str, str] | None = None
    #: Nodes whose first attempt returns a wrong proof, so the evidence-informed retry
    #: path is exercised rather than assumed.
    fail_first: Iterable[str] = field(default_factory=set, kw_only=True)
    on_dispatch: Callable[[NodePayload], None] | None = field(default=None, kw_only=True)
    #: Per-node status override (``contested``/``stuck``/``error``) instead of a proof.
    statuses: Mapping[str, str] | None = field(default=None, kw_only=True)
    delay_s: float = field(default=0.0, kw_only=True)
    #: Nodes whose attempt raises, to test that the scheduler isolates a bad runner.
    raise_for: Iterable[str] = field(default_factory=set, kw_only=True)
    name: str = field(default="mock", kw_only=True)

    def __post_init__(self) -> None:
        self.answers = dict(self.answers or {})
        self.fail_first = set(self.fail_first)
        self.statuses = dict(self.statuses or {})
        self.raise_for = set(self.raise_for)

    def available(self) -> bool:
        return True

    def scripted_answer(self, node: NodePayload) -> dict[str, Any]:
        """What this worker writes to ``answer.json`` for ``node``."""
        answers: dict[str, str] = dict(self.answers or {})
        statuses: dict[str, str] = dict(self.statuses or {})
        status = statuses.get(node.name)
        if status is not None and status != "qed":
            return {"status": status, "evidence": f"mock: scripted {status} for {node.name}"}
        if node.name in self.fail_first and node.attempt == 1:
            return {"status": "qed", "proof": WRONG_PROOF, "evidence": "mock: scripted first-attempt failure"}
        proof = answers.get(node.name)
        if proof is None:
            return {"status": "stuck", "evidence": f"mock: no scripted answer for {node.name}"}
        return {"status": "qed", "proof": proof}

    async def run_node(self, node: NodePayload) -> NodeResult:
        if node.name in self.raise_for:
            raise RuntimeError(f"mock: scripted crash for {node.name}")
        if self.on_dispatch:
            self.on_dispatch(node)
        if self.delay_s:
            await asyncio.sleep(self.delay_s)
        loop = asyncio.get_running_loop()
        started = loop.time()
        workdir = ensure_dir(Path(node.workdir))
        answer = self.scripted_answer(node)
        if answer["status"] == "error":
            # Infrastructure failures never come through answer.json (a worker cannot
            # claim one; ``read_answer_file`` maps the word to ``stuck``), so the
            # mock returns it the way a runner does: directly, with nothing written.
            result = NodeResult(status="error", evidence=str(answer.get("evidence", "")), exit_code=1)
        else:
            json_dump(workdir / ANSWER_FILE, answer)
            result = read_result(workdir, "", target=node.name, scratch_file=node.scratch_file)
        result.elapsed_s = loop.time() - started
        result.cost = {"requests": 1, "seconds": result.elapsed_s}
        if result.exit_code is None:
            result.exit_code = 0
        result.trace = {"model": "mock", "turns": 1, "final_text": "", "tool_calls": []}
        return result
