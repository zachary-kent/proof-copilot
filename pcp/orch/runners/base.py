"""The one runner factory: ``RunnerSpec`` -> ``Runner`` (PLAN.md 11).

"Own the graph, rent the runner."  Running one node attempt is commodity, so it sits
behind the :class:`pcp.orch.protocol.Runner` protocol and is built *here only*.  The
legacy tree plumbed options per runner by keyword, and four of them were silently
dropped on the way (an ``--effort`` that never reached codex, tools baked into one
runner for every rung).  A :class:`RunnerSpec` names every option once, and
:func:`build_runner` refuses -- with ``UsageError`` -- any option the chosen runner
would ignore, instead of pretending it applied (ARCHITECTURE.md 8, "runner options
silently dropped").
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field, fields
from typing import TYPE_CHECKING, Any

from pcp.config.providers import RUNNER_PROVIDER
from pcp.config.schema import EFFORT_LEVELS
from pcp.errors import UsageError
from pcp.mcp.config import MCP_CONFIG_FILE
from pcp.mcp.names import STATE_TOOLS
from pcp.orch.protocol import Runner
from pcp.orch.runners.cli import (
    CLAUDE_LOGIN_HINT,
    CODEX_LOGIN_HINT,
    DECOMPOSER_TOOLS,
    DEFAULT_ALLOWED_TOOLS,
    PERMISSION_MODES,
    CLIRunner,
    claude_headless_runner,
    codex_cli_runner,
    decomposer_runner,
)

if TYPE_CHECKING:
    from pcp.orch.runners.sandbox import Sandbox

__all__ = [
    "DECOMPOSER_TOOLS",
    "DEFAULT_ALLOWED_TOOLS",
    "LOGIN_DELEGATED",
    "PERMISSION_MODES",
    "RUNNER_NAMES",
    "RunnerSpec",
    "build_runner",
    "decomposer_runner",
    "doctor_lines",
    "login_hint",
    "provider_for",
]

RUNNER_NAMES: tuple[str, ...] = ("codex", "claude", "claude-code", "direct", "mock")
#: ``auto`` probes these in order: the flat-rate workhorse first, metered last.
AUTO_ORDER: tuple[str, ...] = ("codex", "claude", "claude-code", "direct")

LOGIN_DELEGATED = (
    "Login is delegated: run `codex login` or Claude Code's `/login` yourself. "
    "Inside a Claude Code session, `! codex login` runs it without leaving the session."
)

#: Which spec fields each runner honours.  Anything else requested is refused.
_SUPPORTS: dict[str, frozenset[str]] = {
    "codex": frozenset({"model", "sandbox", "extra_args"}),
    "claude": frozenset({"model", "effort", "permission_mode", "mcp_tools", "mcp_config", "sandbox", "allowed_tools", "extra_args"}),
    "claude-code": frozenset({"model", "effort", "permission_mode", "mcp_tools", "mcp_config", "sandbox", "allowed_tools", "extra_args"}),
    "direct": frozenset({"model", "effort"}),
    "mock": frozenset({"answers"}),
}

_FLAGS: dict[str, str] = {
    "model": "--model",
    "effort": "--effort",
    "permission_mode": "the permission mode",
    "mcp_tools": "--state-tools",
    "mcp_config": "the MCP config path",
    "sandbox": "--sandbox",
    "allowed_tools": "the tool allowlist",
    "extra_args": "extra runner arguments",
    "answers": "scripted answers",
}


@dataclass(frozen=True)
class RunnerSpec:
    """Everything the CLI decided about how to run a node, in one immutable value."""

    runner: str
    model: str | None = None
    effort: str | None = None
    permission_mode: str | None = None
    mcp_tools: tuple[str, ...] = ()
    mcp_config: str = MCP_CONFIG_FILE
    sandbox: Sandbox | None = None
    allowed_tools: tuple[str, ...] | None = None
    extra_args: tuple[str, ...] = ()
    #: ``mock`` only: proof body by node name.
    answers: Mapping[str, str] | None = field(default=None, hash=False)

    def __post_init__(self) -> None:
        object.__setattr__(self, "mcp_tools", _tuple(self.mcp_tools) or ())
        object.__setattr__(self, "extra_args", _tuple(self.extra_args) or ())
        if self.allowed_tools is not None:
            object.__setattr__(self, "allowed_tools", _tuple(self.allowed_tools))
        if self.runner not in RUNNER_NAMES:
            raise UsageError(f"unknown runner {self.runner!r}; choose from {', '.join(RUNNER_NAMES)}")
        if self.effort is not None and self.effort not in EFFORT_LEVELS:
            raise UsageError(f"unknown effort {self.effort!r}; one of {', '.join(EFFORT_LEVELS)}")
        if self.permission_mode is not None and self.permission_mode not in PERMISSION_MODES:
            raise UsageError(f"unknown permission mode {self.permission_mode!r}; one of {', '.join(PERMISSION_MODES)}")
        unknown = [t for t in self.mcp_tools if t not in STATE_TOOLS]
        if unknown:
            raise UsageError(f"unknown state tool(s): {', '.join(unknown)}. Choose from: {', '.join(STATE_TOOLS)}")

    def requested(self) -> list[str]:
        """The option names set to something other than their default."""
        out: list[str] = []
        for f in fields(self):
            if f.name == "runner":
                continue
            value = getattr(self, f.name)
            if f.name in ("mcp_tools", "extra_args"):
                if value:
                    out.append(f.name)
            elif value is not None and value != f.default:
                out.append(f.name)
        return out

    def to_json(self) -> dict[str, Any]:
        return {
            "runner": self.runner,
            "model": self.model,
            "effort": self.effort,
            "permission_mode": self.permission_mode,
            "mcp_tools": list(self.mcp_tools),
            "mcp_config": self.mcp_config,
            "sandbox": self.sandbox is not None,
            "allowed_tools": list(self.allowed_tools) if self.allowed_tools is not None else None,
            "extra_args": list(self.extra_args),
        }


def _tuple(value: str | Sequence[str] | None) -> tuple[str, ...] | None:
    if value is None:
        return None
    if isinstance(value, str):
        return tuple(t.strip() for t in value.split(",") if t.strip())
    return tuple(str(v) for v in value)


def provider_for(name: str) -> str:
    try:
        return RUNNER_PROVIDER[name]
    except KeyError:
        raise UsageError(f"unknown runner {name!r}; choose from {', '.join(RUNNER_NAMES)}") from None


def login_hint(name: str) -> str:
    provider = provider_for(name)
    if provider == "codex":
        return CODEX_LOGIN_HINT
    if name == "direct":
        return "set ANTHROPIC_API_KEY"
    if provider == "anthropic":
        return CLAUDE_LOGIN_HINT
    return "no login needed"


def build_runner(spec: RunnerSpec) -> Runner:
    """The only factory.  Refuses any option the runner would ignore."""
    ignored = sorted(set(spec.requested()) - _SUPPORTS[spec.runner])
    if ignored:
        what = ", ".join(_FLAGS.get(o, o) for o in ignored)
        others = ", ".join(r for r in RUNNER_NAMES if all(o in _SUPPORTS[r] for o in ignored)) or "no runner"
        raise UsageError(f"runner `{spec.runner}` ignores {what}; drop it, or choose a runner that supports it ({others})")
    runner: Any
    if spec.runner == "codex":
        runner = codex_cli_runner(spec.model, extra_args=spec.extra_args)
    elif spec.runner == "claude":
        runner = claude_headless_runner(
            spec.model,
            allowed_tools=spec.allowed_tools,
            permission_mode=spec.permission_mode or "acceptEdits",
            mcp_tools=spec.mcp_tools or None,
            mcp_config=spec.mcp_config,
            effort=spec.effort,
            extra_args=spec.extra_args,
        )
    elif spec.runner == "claude-code":
        from pcp.orch.runners.claude_code import ClaudeCodeSubagentRunner

        runner = ClaudeCodeSubagentRunner(
            model=spec.model,
            allowed_tools=spec.allowed_tools if spec.allowed_tools is not None else DEFAULT_ALLOWED_TOOLS,
            permission_mode=spec.permission_mode or "acceptEdits",
            mcp_tools=spec.mcp_tools,
            mcp_config=spec.mcp_config,
            effort=spec.effort,
            extra_args=spec.extra_args,
        )
    elif spec.runner == "direct":
        from pcp.orch.runners.direct import DEFAULT_MODEL, DirectAPIRunner

        runner = DirectAPIRunner(model=spec.model or DEFAULT_MODEL, effort=spec.effort)
    else:
        from pcp.orch.runners.mock import MockRunner

        runner = MockRunner(spec.answers)
    if spec.sandbox is not None:
        from pcp.orch.runners.sandbox import SandboxedRunner

        runner = SandboxedRunner(runner, spec.sandbox)
    return runner


def doctor_lines() -> list[str]:
    """The ``pcp doctor`` runner section (contract 1.15): one line per runner."""
    lines: list[str] = []
    for name in AUTO_ORDER:
        runner = build_runner(RunnerSpec(name))
        mark = "ok" if runner.available() else "— unavailable"
        lines.append(f"  {runner.name:24} {mark}")
    return lines


def is_subprocess_runner(runner: Any) -> bool:
    return isinstance(runner, CLIRunner) or hasattr(runner, "argv")
