"""Read ``.pcp/config.toml``.  Credentials are refused, never read."""

from __future__ import annotations

import tomllib
from pathlib import Path
from typing import Any

from pcp.config.flags import DEFAULT_FLAGS
from pcp.config.providers import default_tiers
from pcp.config.schema import Config, Provider, Tiers
from pcp.errors import UsageError

DEFAULT_CONFIG = Path(".pcp/config.toml")

#: Keys that must never be read out of config into anything durable.
SECRET_KEYS = ("api_key", "token", "secret", "password")


def load(path: Path | str | None = None, *, base: Path | None = None) -> Config:
    """Load the config file (default ``.pcp/config.toml`` under ``base``/cwd).

    A missing file yields the detected defaults.  An explicit file overrides them.
    """
    p = Path(path) if path is not None else DEFAULT_CONFIG
    if not p.is_absolute() and base is not None:
        p = base / p
    cfg = Config(tiers=default_tiers(), flags=dict(DEFAULT_FLAGS))
    if not p.exists():
        return cfg
    try:
        data: dict[str, Any] = tomllib.loads(p.read_text(encoding="utf-8"))
    except tomllib.TOMLDecodeError as exc:
        raise UsageError(f"{p}: not valid TOML: {exc}") from None
    tiers = data.get("tiers") or {}
    cfg.tiers = Tiers(
        decomposer=_as_list(tiers.get("decomposer", cfg.tiers.decomposer)),
        prover=_as_list(tiers.get("prover", cfg.tiers.prover)),
        auditor=_as_list(tiers.get("auditor", cfg.tiers.auditor)),
    )
    for name, spec in (data.get("providers") or {}).items():
        _reject_secrets(p, name, spec)
        cfg.providers[name] = Provider(
            name=name,
            auth=str(spec.get("auth", "subscription")),
            endpoint=spec.get("endpoint"),
            login_command=spec.get("login_command"),
        )
    if data.get("concurrency") is not None:
        cfg.concurrency = int(data["concurrency"])
    cfg.effort = {str(k): str(v) for k, v in (data.get("effort") or {}).items()}
    cfg.axiom_whitelist = _as_list(data.get("axiom_whitelist", []))
    cfg.flags.update({str(k): bool(v) for k, v in (data.get("flags") or {}).items()})
    cfg.source = str(p)
    cfg.validate()
    return cfg


def _as_list(value: Any) -> list[str]:
    if value is None:
        return []
    if isinstance(value, str):
        return [value]
    return [str(v) for v in value]


def _reject_secrets(path: Path, provider: str, spec: dict[str, Any]) -> None:
    """Config is committed; credentials are not.  Fail loudly rather than leak."""
    for key in spec:
        if any(marker in key.lower() for marker in SECRET_KEYS):
            raise UsageError(
                f"{path}: provider {provider!r} carries {key!r}. Credentials belong in the "
                "keychain or a 0600 file outside the repo -- never in config, the graph DB, "
                "traces, or context packets."
            )


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

# concurrency = 8
# axiom_whitelist = ["Classical_Prop.classic"]

[flags]
# Speculative machinery is off by default and may not break the canary.
recursive_decomposition = false
"""
