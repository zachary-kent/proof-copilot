"""Provider detection and role -> (provider, model) resolution (PLAN.md 11).

**Login is delegated, never implemented.**  Each provider's CLI owns its auth flow; pcp
only checks and prints the command to run when a window is unauthenticated.
"""

from __future__ import annotations

import os
import shutil
from dataclasses import dataclass
from typing import TYPE_CHECKING

from pcp.config.schema import EFFORT_LEVELS, ROLES, Tiers

if TYPE_CHECKING:
    from pcp.config.schema import Config

#: How each provider is detected.
PROVIDER_BINARIES = {"codex": "codex", "anthropic": "claude"}

#: Per-provider role defaults, applied only for providers actually present.  The prover
#: tier prefers the flat-rate workhorse; the judgement roles do not.
PROVIDER_DEFAULTS: dict[str, dict[str, str]] = {
    "codex": {"prover": "luna"},
    "anthropic": {
        "decomposer": "claude-fable-5",
        "prover": "claude-sonnet-5",
        "auditor": "claude-opus-5",
    },
}

#: Default effort per role.  The decomposer thinks hardest because a bad decomposition
#: is the most expensive error in the pipeline.
ROLE_EFFORT: dict[str, str] = {"decomposer": "xhigh", "prover": "medium", "auditor": "high"}

#: Which provider each role prefers when several are installed.
ROLE_PROVIDER_ORDER: dict[str, tuple[str, ...]] = {
    "prover": ("codex", "anthropic"),
    "decomposer": ("anthropic", "codex"),
    "auditor": ("anthropic", "codex"),
}

#: Which runner names talk to which provider.
RUNNER_PROVIDER: dict[str, str] = {
    "codex": "codex",
    "claude": "anthropic",
    "claude-code": "anthropic",
    "direct": "anthropic",
    "mock": "mock",
}


def detect_providers() -> list[str]:
    """Providers whose CLI (or API key) is actually on this machine."""
    found = [name for name, binary in PROVIDER_BINARIES.items() if shutil.which(binary)]
    if os.environ.get("ANTHROPIC_API_KEY") and "anthropic" not in found:
        found.append("anthropic")
    return found


def default_tiers(detected: list[str] | None = None) -> Tiers:
    """Role bindings for the providers that are present, in preference order."""
    available = detected if detected is not None else detect_providers()
    tiers = Tiers()
    for role in ROLES:
        for provider in ROLE_PROVIDER_ORDER[role]:
            if provider in available:
                model = PROVIDER_DEFAULTS.get(provider, {}).get(role)
                if model:
                    getattr(tiers, role).append(f"{provider}/{model}")
    return tiers


@dataclass(frozen=True)
class Binding:
    role: str
    provider: str
    model: str

    @property
    def spec(self) -> str:
        return f"{self.provider}/{self.model}"


def parse_spec(spec: str) -> tuple[str | None, str]:
    """``provider/model`` -> (provider, model); a bare model has provider ``None``."""
    provider, sep, model = spec.partition("/")
    if not sep:
        return None, spec
    return provider, model


def resolve(role: str, config: Config, *, provider: str | None = None) -> Binding | None:
    """The first tier entry for ``role`` -- restricted to ``provider`` when given.

    The tier is an ordered preference list, so with ``provider`` set the *first entry
    for that provider* wins, not the first entry overall.  ``None`` means nothing is
    configured for that provider and the caller should use its default -- and say so.
    """
    for entry in config.tiers.for_role(role):
        p, model = parse_spec(entry)
        if not p or not model:
            continue
        if provider is not None and p != provider:
            continue
        return Binding(role=role, provider=p, model=model)
    return None


def resolve_effort(role: str, config: Config) -> str:
    level = config.effort.get(role) or ROLE_EFFORT.get(role, "medium")
    return level if level in EFFORT_LEVELS else "medium"


def describe_bindings(config: Config) -> str:
    detected = detect_providers()
    lines = [f"providers detected: {', '.join(detected) or 'none'}"]
    for role in ROLES:
        binding = resolve(role, config)
        spec = binding.spec if binding else "— provider default"
        lines.append(f"  {role:11} {spec:<32} effort {resolve_effort(role, config)}")
    return "\n".join(lines)
