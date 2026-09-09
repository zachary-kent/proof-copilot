"""The configuration model (PLAN.md 11): roles bind to tiers, tiers to providers."""

from __future__ import annotations

from dataclasses import dataclass, field

from pcp.config.flags import DEFAULT_FLAGS
from pcp.errors import UsageError

ROLES = ("decomposer", "prover", "auditor")

#: Accepted by the provider CLIs; ordered.
EFFORT_LEVELS = ("low", "medium", "high", "xhigh", "max")


@dataclass(frozen=True)
class Provider:
    name: str
    auth: str = "subscription"  # subscription | api-key | sdk | none
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


@dataclass
class Tiers:
    """Roles bind to tiers; a tier is an ordered preference list of ``provider/model``."""

    decomposer: list[str] = field(default_factory=list)
    prover: list[str] = field(default_factory=list)
    auditor: list[str] = field(default_factory=list)

    def for_role(self, role: str) -> list[str]:
        if role not in ROLES:
            raise UsageError(f"unknown role {role!r}; one of {', '.join(ROLES)}")
        return list(getattr(self, role))


@dataclass
class Config:
    tiers: Tiers = field(default_factory=Tiers)
    providers: dict[str, Provider] = field(default_factory=dict)
    #: Worker concurrency; ``None`` means the machine ceiling.
    concurrency: int | None = None
    #: Per-role effort, overriding the role defaults.
    effort: dict[str, str] = field(default_factory=dict)
    #: Extra axioms the gate accepts, on top of the built-in whitelist.
    axiom_whitelist: list[str] = field(default_factory=list)
    flags: dict[str, bool] = field(default_factory=lambda: dict(DEFAULT_FLAGS))
    #: Where this configuration came from, for reports.
    source: str = "detected defaults"

    def flag(self, name: str, default: bool = False) -> bool:
        return bool(self.flags.get(name, default))

    def validate(self) -> None:
        for role, level in self.effort.items():
            if role not in ROLES:
                raise UsageError(f"config: effort names unknown role {role!r}")
            if level not in EFFORT_LEVELS:
                raise UsageError(
                    f"config: effort for {role!r} is {level!r}; expected one of " + ", ".join(EFFORT_LEVELS)
                )
        if self.concurrency is not None and self.concurrency < 1:
            raise UsageError("config: concurrency must be >= 1")
        for name in self.flags:
            if name not in DEFAULT_FLAGS:
                raise UsageError(f"config: unknown flag {name!r}; known: " + ", ".join(DEFAULT_FLAGS))
