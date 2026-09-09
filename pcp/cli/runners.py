"""Runner selection for ``pcp prove`` (PLAN.md 11; contract §1.1).

One place decides which runner runs, which model it gets, and what it is allowed to
ignore -- and it decides in that order.  ``--runner auto`` honours the configured
tier's provider preference; a ``provider/model`` flag is validated against the
runner *actually chosen* (the legacy CLI checked it against a hard-coded
``anthropic`` before choosing, so ``--runner codex --prover-model codex/luna`` was
refused); and every option reaches the runner through :class:`RunnerSpec`, whose
factory refuses what the runner would ignore, so ``--state-tools --runner codex``
fails loudly instead of recording an ablation arm that never had its tools.
"""

from __future__ import annotations

import argparse
import functools
from collections.abc import Callable, Sequence
from pathlib import Path
from typing import Any

from pcp.cli.common import absolute
from pcp.config.providers import parse_spec, resolve, resolve_effort
from pcp.config.schema import Config
from pcp.errors import UsageError
from pcp.mcp.names import parse_state_tools
from pcp.orch.protocol import Runner
from pcp.orch.runners.base import (
    AUTO_ORDER,
    RUNNER_NAMES,
    RunnerSpec,
    build_runner,
    decomposer_runner,
    is_subprocess_runner,
    provider_for,
)
from pcp.util.paths import repo_root

__all__ = [
    "NO_RUNNER",
    "effort_for",
    "library_dirs",
    "model_for",
    "pick_auto",
    "sandbox_for",
    "select_approver",
    "select_decomposer",
    "select_runner",
    "state_tools_for",
]

NO_RUNNER = (
    "no runner is available. Install one of `codex` or `claude`, or set "
    "ANTHROPIC_API_KEY for --runner direct. `pcp doctor` shows what is missing."
)
#: Runners whose CLI takes an effort level; the others get none unless asked.
EFFORT_RUNNERS = ("claude", "claude-code", "direct")
PERMISSION_RUNNERS = ("claude", "claude-code")
DEFAULT_SOURCE_NOTE = "built-in default for the providers detected on this machine"
#: The approver answers yes/no on one conjunct; ``xhigh`` is for designs (PLAN.md 8.5).
APPROVER_EFFORT = "medium"


def state_tools_for(args: argparse.Namespace) -> list[str]:
    value = getattr(args, "state_tools", None)
    return parse_state_tools(value) if value is not None else []


def library_dirs(values: Sequence[str] | None) -> list[Path]:
    """``--library`` directories, absolute; each must exist (an accidental library is
    indistinguishable from a leak, so the default stays "nothing")."""
    out: list[Path] = []
    for value in values or []:
        path = absolute(value)
        assert path is not None
        if not path.exists():
            raise UsageError(f"--library {value}: no such path")
        out.append(path)
    return out


def pick_auto(cfg: Config, role: str) -> str:
    """``AUTO_ORDER`` restricted to the providers the role's tier names, first
    available; else the first available at all."""
    preferred = {parse_spec(e)[0] for e in cfg.tiers.for_role(role)}
    ordered = [r for r in AUTO_ORDER if provider_for(r) in preferred] + [r for r in AUTO_ORDER if provider_for(r) not in preferred]
    for name in ordered:
        if build_runner(RunnerSpec(name)).available():
            return name
    raise UsageError(NO_RUNNER)


def model_for(role: str, cfg: Config, provider: str, *, flag: str | None, flag_name: str) -> tuple[str | None, str | None]:
    """The model for ``role`` under ``provider``, and the note to print about it.

    An explicit flag wins and is validated against the chosen runner's provider.
    Otherwise the tier's first entry *for that provider* applies; a tier that only
    binds another provider falls back to the provider default and says so.
    """
    if flag:
        p, model = parse_spec(flag)
        if p is not None and p != provider:
            raise UsageError(
                f"{flag_name} names provider {p!r}, but this run uses {provider!r}. "
                f"Pass a {provider} model, or change the runner."
            )
        return model, None
    if provider == "mock":
        return None, None
    binding = resolve(role, cfg, provider=provider)
    if binding is not None:
        source = cfg.source if Path(cfg.source).exists() else DEFAULT_SOURCE_NOTE
        return binding.model, f"{role}: {binding.spec} (from {source})"
    other = resolve(role, cfg)
    if other is not None:
        return None, f"{role}: config binds {other.spec}, but this run uses {provider}; falling back to the provider default"
    return None, None


def effort_for(role: str, cfg: Config, runner: str, *, flag: str | None) -> str | None:
    """An explicit flag always reaches the spec (and fails loudly if ignored); the
    config/role default reaches only runners that take one."""
    if flag:
        return flag
    return resolve_effort(role, cfg) if runner in EFFORT_RUNNERS else None


def sandbox_for(
    args: argparse.Namespace, runner_name: str, *, corpus_dir: Path, library: Sequence[Path]
) -> Any:
    """The bubblewrap policy for a benchmark run (contract §1.1, §3.4)."""
    from pcp.orch.runners import sandbox as sb

    if not is_subprocess_runner(build_runner(RunnerSpec(runner_name))):
        raise UsageError(
            f"--sandbox needs a subprocess runner; {runner_name} runs in-process. "
            "Use --runner codex or --runner claude."
        )
    if not sb.available():
        raise UsageError("--sandbox needs bubblewrap (`bwrap`); install it or drop --sandbox")
    reference = absolute(getattr(args, "reference", None))
    return sb.Sandbox.for_benchmark(
        repo_root(), reference=reference, corpus_dir=corpus_dir, library=list(library),
        provider=provider_for(runner_name),
    )


def select_runner(
    args: argparse.Namespace,
    cfg: Config,
    *,
    role: str = "prover",
    corpus_dir: Path | None = None,
    library: Sequence[Path] = (),
) -> tuple[Runner, list[str]]:
    """Choose, bind, build (module docstring).  Returns the runner and the stderr notes."""
    name = getattr(args, "runner", "auto") or "auto"
    if name != "auto" and name not in RUNNER_NAMES:
        raise UsageError(f"unknown runner {name!r}; choose from {', '.join(RUNNER_NAMES)}")
    chosen = pick_auto(cfg, role) if name == "auto" else name
    provider = provider_for(chosen)
    notes: list[str] = []
    flag = getattr(args, "prover_model", None) or getattr(args, "model", None)
    model, note = model_for(role, cfg, provider, flag=flag, flag_name="--prover-model")
    if note:
        notes.append(note)
    effort = effort_for(role, cfg, chosen, flag=getattr(args, "prover_effort", None))
    sandbox = None
    if getattr(args, "sandbox", False):
        sandbox = sandbox_for(args, chosen, corpus_dir=corpus_dir or Path(args.file).resolve().parent, library=library)
    permission = None
    if chosen in PERMISSION_RUNNERS:
        permission = "bypassPermissions" if sandbox is not None else "acceptEdits"
    spec = RunnerSpec(
        runner=chosen,
        model=model,
        effort=effort,
        permission_mode=permission,
        mcp_tools=tuple(state_tools_for(args)),
        sandbox=sandbox,
    )
    runner = build_runner(spec)
    if name == "auto" and not runner.available():
        raise UsageError(NO_RUNNER)
    return runner, notes


def select_decomposer(
    args: argparse.Namespace,
    cfg: Config,
    *,
    corpus_dir: Path,
    library: Sequence[Path] = (),
    sandbox_factory: Callable[[], Any] | None = None,
) -> tuple[Runner, list[str]]:
    """The decomposer: ``claude -p`` with ``Read Glob Grep`` only (contract §3.5)."""
    notes: list[str] = []
    flag = getattr(args, "decomposer", None)
    model, note = model_for("decomposer", cfg, "anthropic", flag=flag, flag_name="--decomposer")
    if note and not flag:
        notes.append(note)
    effort = getattr(args, "decomposer_effort", None) or resolve_effort("decomposer", cfg)
    factory = sandbox_factory
    if factory is None and getattr(args, "sandbox", False):
        factory = functools.partial(sandbox_for, args, "claude", corpus_dir=corpus_dir, library=library)
    runner = decomposer_runner(model, effort=effort, sandbox_factory=factory)
    notes.append(
        f"decomposer: {getattr(runner, 'name', '?')} (read-only)"
        + ("" if model else "  [no model pinned -- using the provider default]")
    )
    return runner, notes


def select_approver(
    args: argparse.Namespace,
    cfg: Config,
    *,
    corpus_dir: Path,
    library: Sequence[Path] = (),
    sandbox_factory: Callable[[], Any] | None = None,
) -> Runner:
    """The approver: the decomposer's runner -- same model, same ``Read Glob Grep``
    allowlist, same sandbox -- at ``--approver-effort`` (default :data:`APPROVER_EFFORT`).

    An amendment verdict or a contest adjudication is a short, decisive round on one
    definition; running it at the design effort would make the incremental route
    cost what the full revision costs.  The model follows ``--decomposer``: the
    approver is the decomposer's delegate, not a third role with its own tier.
    """
    flag = getattr(args, "decomposer", None)
    model, _note = model_for("decomposer", cfg, "anthropic", flag=flag, flag_name="--decomposer")
    effort = getattr(args, "approver_effort", None) or APPROVER_EFFORT
    factory = sandbox_factory
    if factory is None and getattr(args, "sandbox", False):
        factory = functools.partial(sandbox_for, args, "claude", corpus_dir=corpus_dir, library=library)
    return decomposer_runner(model, effort=effort, sandbox_factory=factory)
