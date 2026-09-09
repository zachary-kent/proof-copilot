"""``DirectAPIRunner`` -- the Messages API with no harness in the way (PLAN.md 11).

Its job is the eval harness (PLAN.md 13), where a harness between the model and the
tools would confound every ablation.  It is deliberately the *last* runner in
priority order: metered tokens are the scarce resource; the flat-rate window is the
workhorse.  It never writes files, so with per-attempt directories it can never read
a stale answer either.
"""

from __future__ import annotations

import asyncio
from dataclasses import dataclass

from pcp.config.env import ANTHROPIC_API_KEY, api_key
from pcp.orch.protocol import NodePayload, NodeResult, read_result
from pcp.orch.runners.cli import has_answer
from pcp.orch.runners.stream import WorkerTrace
from pcp.util.io import read_text
from pcp.util.text import one_line

DEFAULT_MODEL = "claude-sonnet-5"

_DEFAULT_SYSTEM = (
    "You are proving one Rocq/Iris lemma. Reply with the proof body only, inside a "
    "```coq fence, with no Proof. or Qed. wrapper. Do not restate the lemma and do "
    "not modify it. If you cannot prove it, say STUCK and explain what blocked you."
)


@dataclass
class DirectAPIRunner:
    """One Messages API call per attempt.  No tools, no loop: prompt in, proof out."""

    model: str = DEFAULT_MODEL
    max_tokens: int = 8000
    effort: str | None = None
    name: str = "direct"
    system: str = ""

    def available(self) -> bool:
        if not api_key("anthropic"):
            return False
        try:
            import anthropic  # noqa: F401
        except ImportError:
            return False
        return True

    def login_hint(self) -> str:
        return f"set {ANTHROPIC_API_KEY}"

    async def run_node(self, node: NodePayload) -> NodeResult:
        if not self.available():
            return NodeResult(status="error", evidence=f"{ANTHROPIC_API_KEY} is unset or the anthropic SDK is missing")
        try:
            prompt = read_text(node.prompt_path)
        except OSError as exc:
            return NodeResult(status="error", evidence=f"the packet has no {node.prompt_file}: {exc}")
        import anthropic

        kwargs: dict = {
            "model": self.model,
            "max_tokens": self.max_tokens,
            "system": self.system or _DEFAULT_SYSTEM,
            "messages": [{"role": "user", "content": prompt}],
        }
        if self.effort:
            kwargs["output_config"] = {"effort": self.effort}
        loop = asyncio.get_running_loop()
        started = loop.time()
        try:
            # The client is closed on exit, so an eval at concurrency 8 does not leak
            # a connection pool per attempt; a deadline cancels the request with it.
            async with anthropic.AsyncAnthropic() as client:
                message = await asyncio.wait_for(client.messages.create(**kwargs), timeout=node.budget_seconds)
        except TimeoutError:
            elapsed = loop.time() - started
            return NodeResult(
                status="stuck",
                evidence=f"worker exceeded its {node.budget_seconds:.0f}s deadline and was killed; the API call returned nothing before the kill",
                elapsed_s=elapsed,
                timed_out=True,
                cost={"requests": 1, "seconds": elapsed},
            )
        except Exception as exc:  # noqa: BLE001 -- a provider error is a node failure, not a crash
            elapsed = loop.time() - started
            return NodeResult(
                status="error",
                evidence=f"provider error: {type(exc).__name__}: {one_line(str(exc), 400)}",
                elapsed_s=elapsed,
                cost={"requests": 1, "seconds": elapsed},
            )
        elapsed = loop.time() - started
        text = "".join(getattr(block, "text", "") for block in message.content if getattr(block, "type", "") == "text")
        usage = message.usage
        trace = WorkerTrace(
            format="direct",
            turns=1,
            input_tokens=int(getattr(usage, "input_tokens", 0) or 0),
            output_tokens=int(getattr(usage, "output_tokens", 0) or 0),
            cache_read_tokens=int(getattr(usage, "cache_read_input_tokens", 0) or 0),
            cache_creation_tokens=int(getattr(usage, "cache_creation_input_tokens", 0) or 0),
            final_text=text,
            model=str(getattr(message, "model", "") or self.model),
            events=1,
        )
        result = read_result(node.workdir, text, target=node.name, scratch_file=node.scratch_file)
        stop = getattr(message, "stop_reason", None)
        if stop == "refusal":
            result = NodeResult(status="stuck", evidence="the model refused the request (stop_reason refusal)")
        elif stop == "max_tokens" and not has_answer(node.workdir, text):
            result.evidence = "; ".join(
                p for p in (result.evidence, f"the reply was cut off at max_tokens={self.max_tokens} (stop_reason max_tokens)") if p
            )
        result.raw = text
        result.elapsed_s = elapsed
        result.trace = trace.to_json()
        result.cost = {
            "requests": 1,
            "tokens": trace.total_tokens,
            "input_tokens": trace.input_tokens,
            "output_tokens": trace.output_tokens,
            "cache_read_tokens": trace.cache_read_tokens,
            "seconds": elapsed,
        }
        return result
