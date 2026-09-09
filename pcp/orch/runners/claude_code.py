"""``ClaudeCodeSubagentRunner`` -- ``claude -p --output-format json``.

PLAN.md 6 wants an *interactive* runner with a mid-flight channel: ping once (goal,
plan, blocker), extend once if the reply shows progress.  That ladder is **not
implementable for a one-shot CLI** -- ``claude -p`` reads one prompt, runs to
completion and prints once at exit; there is no second prompt without ``--resume``,
and resuming *after* a kill is a new attempt, not a ping.  The legacy runner faked it:
it wrote a marker file the process never read and measured the marker's own mtime as
"progress", so every worker got the extension and the evidence lied about a ping
(bugs 3-4 in the runner audit).  This version does not pretend.  The runner gets the
whole budget in ONE ``run_async`` call (no cancelled ``communicate()`` that drops the
buffered output) and is otherwise the headless runner with the single-object output
format, which is what an operator inside a Claude Code session gets for free.

A real mid-flight channel needs a session that accepts a second message; when that
exists, it belongs here.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass, field

from pcp.mcp.config import MCP_CONFIG_FILE
from pcp.orch.runners.cli import CLAUDE_LOGIN_HINT, DEFAULT_ALLOWED_TOOLS, CLIRunner, claude_argv


@dataclass
class ClaudeCodeSubagentRunner(CLIRunner):
    """``claude -p --output-format json`` with ``--strict-mcp-config`` (contract 3.3)."""

    allowed_tools: tuple[str, ...] = DEFAULT_ALLOWED_TOOLS
    permission_mode: str = "acceptEdits"
    mcp_tools: tuple[str, ...] = ()
    mcp_config: str = MCP_CONFIG_FILE
    effort: str | None = None
    extra_args: tuple[str, ...] = field(default_factory=tuple)

    def __post_init__(self) -> None:
        self.name = "claude-code"
        self.binary = "claude"
        self.stream = "json"
        self.login = self.login or CLAUDE_LOGIN_HINT
        self.allowed_tools = _tuple(self.allowed_tools)
        self.mcp_tools = _tuple(self.mcp_tools)
        self.extra_args = _tuple(self.extra_args)
        if not self.argv:
            self.argv = claude_argv(
                output_format="json",
                allowed_tools=self.allowed_tools,
                permission_mode=self.permission_mode,
                mcp_tools=self.mcp_tools or None,
                mcp_config=self.mcp_config,
                model=self.model,
                effort=self.effort,
                extra_args=self.extra_args,
            )
        super().__post_init__()


def _tuple(value: str | Sequence[str] | None) -> tuple[str, ...]:
    if value is None:
        return ()
    if isinstance(value, str):
        return tuple(t.strip() for t in value.split(",") if t.strip())
    return tuple(str(v) for v in value)
