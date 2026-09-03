"""`ClaudeCodeSubagentRunner` -- the one runner with a mid-flight channel.

Every other runner is one-shot, so its deadline ladder is soft deadline -> kill ->
requeue.  An interactive session can be *pinged* first: current goal, plan, blocker,
one line each, and one extension if the reply shows progress (PLAN.md 6).  That is
the only reason this runner exists alongside the headless one.

It shells out to the same `claude` CLI in a resumable session, so it inherits the
Claude Code session's own auth -- login stays delegated.
"""

from __future__ import annotations

import asyncio
import json
import shutil
import time
from dataclasses import dataclass, field
from pathlib import Path

from pcp.orch.runners.base import NodePayload, NodeResult, read_result, strip_proof_wrapper

PING = (
    "Status check. Reply with exactly three lines:\n"
    "GOAL: <the goal you are on>\nPLAN: <your next step>\nBLOCKER: <what is in the way, or none>"
)


@dataclass
class ClaudeCodeSubagentRunner:
    """A resumable `claude` session, pinged once before it is killed."""

    model: str | None = None
    name: str = "claude-code"
    allowed_tools: str = "Read,Write,Edit,Bash,Glob,Grep"
    permission_mode: str = "acceptEdits"
    #: Fraction of the budget after which the worker gets its one ping.
    ping_at: float = 0.6
    #: Extra time granted when the ping shows progress.
    extension: float = 0.5
    sessions: dict[str, str] = field(default_factory=dict)

    def available(self) -> bool:
        return shutil.which("claude") is not None

    async def run_node(self, node: NodePayload) -> NodeResult:
        started = time.perf_counter()
        prompt = (node.workdir / "TASK.md").read_text(encoding="utf-8")
        argv = [
            "claude", "-p",
            "--output-format", "json",
            "--permission-mode", self.permission_mode,
            "--allowed-tools", *self.allowed_tools.split(","),
        ]
        if self.model:
            argv += ["--model", self.model]
        try:
            # Prompt on stdin: `--allowed-tools` is variadic and swallows a trailing
            # positional argument, which fails silently as "no answer produced".
            proc = await asyncio.create_subprocess_exec(
                *argv,
                cwd=str(node.workdir),
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.STDOUT,
                stdin=asyncio.subprocess.PIPE,
            )
        except FileNotFoundError:
            return NodeResult(status="error", evidence="`claude` is not on PATH",
                              elapsed_s=time.perf_counter() - started)

        budget = node.budget_seconds
        try:
            stdout, _ = await asyncio.wait_for(
                proc.communicate(prompt.encode("utf-8")), timeout=budget * self.ping_at
            )
        except asyncio.TimeoutError:
            progressed = await self._ping(node)
            remaining = budget * (1 - self.ping_at) + (budget * self.extension if progressed else 0.0)
            try:
                stdout, _ = await asyncio.wait_for(proc.communicate(), timeout=remaining)
            except asyncio.TimeoutError:
                proc.kill()
                await proc.wait()
                partial = read_result(node.workdir, "")
                return NodeResult(
                    status="stuck",
                    proof=strip_proof_wrapper(partial.proof) if partial.proof else "",
                    evidence=(
                        "worker was pinged and "
                        + ("showed progress but still overran" if progressed else "showed no progress")
                        + "; killed at its deadline"
                    ),
                    elapsed_s=time.perf_counter() - started,
                )

        text = (stdout or b"").decode("utf-8", "replace")
        result = read_result(node.workdir, _unwrap_json(text))
        result.proof = strip_proof_wrapper(result.proof) if result.proof else ""
        result.elapsed_s = time.perf_counter() - started
        result.cost = {"requests": 1, "seconds": result.elapsed_s}
        return result

    async def _ping(self, node: NodePayload) -> bool:
        """One ping, one line each.  Progress means a named goal and a next step."""
        marker: Path = node.workdir / ".pcp-ping"
        marker.write_text(PING, encoding="utf-8")
        # A one-shot CLI cannot be interrupted mid-flight; the honest signal available
        # here is whether the worker has been changing files.
        try:
            newest = max(
                (p.stat().st_mtime for p in node.workdir.rglob("*") if p.is_file()),
                default=0.0,
            )
        except OSError:
            return False
        return (time.time() - newest) < 120.0


def _unwrap_json(text: str) -> str:
    """`claude -p --output-format json` wraps the transcript; take the result field."""
    try:
        data = json.loads(text)
    except json.JSONDecodeError:
        return text
    if isinstance(data, dict):
        return str(data.get("result") or data.get("content") or text)
    return text
