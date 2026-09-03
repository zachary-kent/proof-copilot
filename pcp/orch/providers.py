"""Model access: tiers, provider profiles, login methods (PLAN.md 11).

Model access is a first-class config concern.  Roles bind to tiers, tiers bind to
provider profiles, and each profile carries its own login method -- because the
auditor ladder needs mixed model families on day one, and mixed families are only
real if a second provider is a config line rather than an integration project.

**Login is delegated, never implemented.**  Each provider's CLI owns its auth flow;
pcp only *checks*, and prints the command to run when a window is unauthenticated.

**Secrets hygiene.**  Credentials live in the keychain or a 0600 file outside the
repo -- never in the graph DB, the traces, or a context packet.  Traces become
training data later, and nothing secret may ever enter them.
"""

from __future__ import annotations

import os
import tomllib
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

DEFAULT_CONFIG = Path(".pcp/config.toml")

#: Keys that must never be read out of config into anything durable.
SECRET_KEYS = ("api_key", "token", "secret", "password")


@dataclass
class Provider:
    name: str
    auth: str = "subscription"      # subscription | api-key | sdk | none
    endpoint: str | None = None
    login_command: str | None = None

    def login_hint(self) -> str:
        if self.login_command:
            return self.login_command
        return {
            "subscription": f"{self.name} login",
            "api-key": f"set {self.name.upper()}_API_KEY",
            "sdk": "configure ambient cloud credentials",
            "none": "no login needed",
        }.get(self.auth, "see the provider's documentation")


#: How each provider is detected, and what it is good for.
PROVIDER_BINARIES = {"codex": "codex", "anthropic": "claude"}

#: Per-provider role defaults, applied only for providers actually present.
#:
#: They encode the third economics rule: metered frontier tokens buy only what cheap
#: models are structurally wrong for -- decomposition, adjudication, absorbed
#: escalations -- and never bookkeeping or review.  So the *prover* tier prefers the
#: flat-rate workhorse and the *decomposer* and *auditor* tiers do not.
PROVIDER_DEFAULTS: dict[str, dict[str, str]] = {
    "codex": {"prover": "luna"},
    "anthropic": {
        "decomposer": "claude-fable-5",
        "prover": "claude-sonnet-5",
        "auditor": "claude-opus-5",
    },
}

#: Reasonable effort per role.
#:
#: The decomposer and the auditor make *judgements* -- what the invariant should be,
#: whether a weakening is acceptable -- and those are exactly the calls PLAN.md 11
#: says metered frontier capacity is for.  A bad decomposition is also the most
#: expensive error in the pipeline: it is discovered only after the children's budget
#: has been spent, so thinking harder there is cheap by comparison.  Provers grind
#: tactics in bulk, where the same spend buys more attempts than it buys thinking.
ROLE_EFFORT: dict[str, str] = {
    "decomposer": "xhigh",
    "prover": "medium",
    "auditor": "high",
}

#: Accepted by the provider CLI; ordered.
EFFORT_LEVELS = ("low", "medium", "high", "xhigh", "max")


#: Which provider each role prefers when several are installed.  Provers go to the
#: flat-rate tier first; the roles that need judgement do not.
ROLE_PROVIDER_ORDER: dict[str, tuple[str, ...]] = {
    "prover": ("codex", "anthropic"),
    "decomposer": ("anthropic", "codex"),
    "auditor": ("anthropic", "codex"),
}


def detect_providers() -> list[str]:
    """Providers whose CLI is actually on this machine."""
    import shutil

    found = [name for name, binary in PROVIDER_BINARIES.items() if shutil.which(binary)]
    if os.environ.get("ANTHROPIC_API_KEY") and "anthropic" not in found:
        found.append("anthropic")
    return found


def default_tiers(detected: list[str] | None = None) -> "Tiers":
    """Sensible role bindings for the providers that are present.

    Hardcoding `codex/luna` on a machine with no `codex` produced a tier that
    silently resolved to nothing; deriving the defaults from what is installed makes
    the fallback visible instead.
    """
    available = detected if detected is not None else detect_providers()
    tiers = Tiers(decomposer=[], prover=[], auditor=[])
    for role in ("decomposer", "prover", "auditor"):
        for provider in ROLE_PROVIDER_ORDER[role]:
            if provider not in available:
                continue
            model = PROVIDER_DEFAULTS.get(provider, {}).get(role)
            if model:
                getattr(tiers, role).append(f"{provider}/{model}")
    return tiers


@dataclass
class Tiers:
    """Roles bind to tiers; a tier is an ordered preference list."""

    decomposer: list[str] = field(default_factory=list)
    prover: list[str] = field(default_factory=list)
    auditor: list[str] = field(default_factory=list)


@dataclass
class Config:
    tiers: Tiers = field(default_factory=lambda: default_tiers())
    providers: dict[str, Provider] = field(default_factory=dict)
    concurrency: int | None = None
    #: Per-role effort, overriding :data:`ROLE_EFFORT`.
    effort: dict[str, str] = field(default_factory=dict)
    axiom_whitelist: list[str] = field(default_factory=list)
    #: Speculative features are off by default and are not allowed to break the
    #: canary (PLAN.md 8.11).
    flags: dict[str, bool] = field(default_factory=dict)

    def flag(self, name: str, default: bool = False) -> bool:
        return bool(self.flags.get(name, default))


DEFAULT_FLAGS = {
    "recursive_decomposition": False,   # depth > 1 (PLAN.md 8.2)
    "or_nodes": False,                  # alternative plans raced under split budgets
    "strict_no_gap": False,             # glue must Qed before children dispatch
    "amendment_lattice": False,         # beyond refute + human edit
    "vacuity_probes": False,            # costs a Rocq compile per statement
    "sketch_compiler": False,           # CSL mode (PLAN.md 9)
    "state_layer": False,               # wire pcp-state into worker packets
    "epsilon_spot_check": False,        # defaults to zero in the daily loop
}


def load(path: Path | str = DEFAULT_CONFIG) -> Config:
    """Precedence: an explicit config file overrides the detected defaults."""
    cfg = Config(flags=dict(DEFAULT_FLAGS))
    p = Path(path)
    if not p.exists():
        return cfg
    data: dict[str, Any] = tomllib.loads(p.read_text(encoding="utf-8"))
    tiers = data.get("tiers", {})
    cfg.tiers = Tiers(
        decomposer=_as_list(tiers.get("decomposer", cfg.tiers.decomposer)),
        prover=_as_list(tiers.get("prover", cfg.tiers.prover)),
        auditor=_as_list(tiers.get("auditor", cfg.tiers.auditor)),
    )
    for name, spec in (data.get("providers") or {}).items():
        _reject_secrets(name, spec)
        cfg.providers[name] = Provider(
            name=name,
            auth=spec.get("auth", "subscription"),
            endpoint=spec.get("endpoint"),
            login_command=spec.get("login_command"),
        )
    cfg.concurrency = data.get("concurrency")
    for role, level in (data.get("effort") or {}).items():
        if level not in EFFORT_LEVELS:
            raise SystemExit(
                f"{p}: effort for {role!r} is {level!r}; expected one of "
                + ", ".join(EFFORT_LEVELS)
            )
        cfg.effort[role] = level
    cfg.axiom_whitelist = _as_list(data.get("axiom_whitelist", []))
    cfg.flags.update({k: bool(v) for k, v in (data.get("flags") or {}).items()})
    return cfg


def _as_list(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value]
    return list(value or [])


def _reject_secrets(provider: str, spec: dict[str, Any]) -> None:
    """Config is committed; credentials are not.  Fail loudly rather than leak."""
    for key in spec:
        if any(marker in key.lower() for marker in SECRET_KEYS):
            raise SystemExit(
                f".pcp/config.toml: provider {provider!r} carries {key!r}. Credentials "
                "belong in the keychain or a 0600 file outside the repo -- never in "
                "config, the graph DB, traces, or context packets."
            )


@dataclass(frozen=True)
class Binding:
    """A resolved role -> (provider, model) choice."""

    role: str
    provider: str
    model: str

    @property
    def spec(self) -> str:
        return f"{self.provider}/{self.model}"


def resolve_effort(role: str, config: Config | None = None) -> str:
    """Effort for a role: configured, else the sensible default for that job."""
    cfg = config or load()
    return cfg.effort.get(role) or ROLE_EFFORT.get(role, "medium")


def describe_bindings(config: Config | None = None) -> str:
    cfg = config or load()
    detected = detect_providers()
    lines = [f"providers detected: {', '.join(detected) or 'none'}"]
    for role in ("decomposer", "prover", "auditor"):
        binding = resolve(role, cfg)
        spec = binding.spec if binding else "— provider default"
        lines.append(f"  {role:11} {spec:<32} effort {resolve_effort(role, cfg)}")
    return "\n".join(lines)


def resolve(role: str, config: Config | None = None) -> Binding | None:
    """Which model should play ``role``.

    PLAN.md 11 binds roles to tiers and tiers to providers, and the point of writing
    it down is that the binding is then *visible*: a run whose decomposer silently
    inherited whatever the CLI defaults to cannot be compared with one that did not.
    Returns ``None`` when nothing is configured, so the caller can fall back to the
    provider's own default -- and say so.
    """
    cfg = config or load()
    entries = {
        "decomposer": cfg.tiers.decomposer,
        "prover": cfg.tiers.prover,
        "auditor": cfg.tiers.auditor,
    }.get(role, [])
    for entry in entries:
        provider, _, model = entry.partition("/")
        if model:
            return Binding(role=role, provider=provider, model=model)
    return None


def env_credential(provider: str) -> str | None:
    return os.environ.get(f"{provider.upper()}_API_KEY")


EXAMPLE_CONFIG = """\
# .pcp/config.toml -- model access, one line per provider.

[tiers]
decomposer = "anthropic/claude-fable-5"
prover     = ["codex/luna", "anthropic/claude-sonnet-5"]   # flat-rate workhorse first
auditor    = ["anthropic/claude-opus-5", "google/gemini-3-pro"]  # mixed families

[providers.anthropic]
auth = "subscription"        # OAuth device flow; or "api-key"

[providers.codex]
auth = "subscription"        # a 20x plan: near-zero marginal cost, budget in requests/window

[providers.local]
auth = "none"
endpoint = "http://localhost:11434"

[effort]
# Judgement roles think; the bulk tactic tier spends its budget on attempts instead.
# A bad decomposition is the most expensive error there is, so it gets the most.
decomposer = "xhigh"
prover     = "medium"
auditor    = "high"

[flags]
# Speculative machinery is off by default and may not break the canary.
recursive_decomposition = false
or_nodes = false
strict_no_gap = false
"""
