"""`DirectAPIRunner` -- the API, with no harness in the way (PLAN.md 11).

Its job is the eval harness (PLAN.md 13), where a harness between the model and the
tools would confound every ablation.  It is deliberately the *last* runner in
priority order: metered tokens are the scarce resource, and the flat-rate window is
the workhorse.
"""

from __future__ import annotations

import asyncio
import os
import time
from dataclasses import dataclass, field

from pcp.orch.runners.base import NodePayload, NodeResult, read_result, strip_proof_wrapper

DEFAULT_MODEL = "claude-sonnet-5"


@dataclass
class DirectAPIRunner:
    """One Messages API call per attempt.  No tools, no loop: prompt in, proof out."""

    model: str = DEFAULT_MODEL
    max_tokens: int = 8000
    name: str = "direct"
    api_key_env: str = "ANTHROPIC_API_KEY"
    system: str = ""
    extra: dict = field(default_factory=dict)

    def available(self) -> bool:
        if not os.environ.get(self.api_key_env):
            return False
        try:
            import anthropic  # noqa: F401
        except ImportError:
            return False
        return True

    async def run_node(self, node: NodePayload) -> NodeResult:
        started = time.perf_counter()
        if not self.available():
            return NodeResult(
                status="error",
                evidence=f"{self.api_key_env} is unset or the anthropic SDK is missing",
                elapsed_s=time.perf_counter() - started,
            )
        import anthropic

        client = anthropic.AsyncAnthropic()
        prompt = (node.workdir / "TASK.md").read_text(encoding="utf-8")
        try:
            message = await asyncio.wait_for(
                client.messages.create(
                    model=self.model,
                    max_tokens=self.max_tokens,
                    system=self.system or _DEFAULT_SYSTEM,
                    messages=[{"role": "user", "content": prompt}],
                    **self.extra,
                ),
                timeout=node.budget_seconds,
            )
        except asyncio.TimeoutError:
            return NodeResult(status="stuck", evidence="API call exceeded the node deadline",
                              elapsed_s=time.perf_counter() - started)
        except Exception as exc:  # noqa: BLE001 -- a provider error is a node failure, not a crash
            return NodeResult(status="error", evidence=f"{type(exc).__name__}: {exc}",
                              elapsed_s=time.perf_counter() - started)

        text = "".join(block.text for block in message.content if getattr(block, "type", "") == "text")
        result = read_result(node.workdir, text)
        result.proof = strip_proof_wrapper(result.proof) if result.proof else ""
        result.elapsed_s = time.perf_counter() - started
        result.cost = {
            "requests": 1,
            "tokens": message.usage.input_tokens + message.usage.output_tokens,
            "seconds": result.elapsed_s,
        }
        return result


_DEFAULT_SYSTEM = (
    "You are proving one Rocq/Iris lemma. Reply with the proof body only, inside a "
    "```coq fence, with no Proof. or Qed. wrapper. Do not restate the lemma and do "
    "not modify it. If you cannot prove it, say STUCK and explain what blocked you."
)
