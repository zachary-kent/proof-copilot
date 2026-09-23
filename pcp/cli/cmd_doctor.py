"""``pcp doctor``, ``pcp models``, ``pcp docs`` -- the environment, not a proof."""

from __future__ import annotations

import argparse
import importlib.util
import os
from pathlib import Path

from pcp.cli.common import absolute, err
from pcp.config import env as penv
from pcp.config.load import DEFAULT_CONFIG, EXAMPLE_CONFIG, load
from pcp.config.providers import describe_bindings
from pcp.errors import UsageError


def _config(args: argparse.Namespace):
    path = getattr(args, "config", None)
    return load(absolute(path) if path else None)


def cmd_models(args: argparse.Namespace) -> int:
    if args.example:
        print(EXAMPLE_CONFIG)
        return 0
    cfg = _config(args)
    print(describe_bindings(cfg))
    print(f"\nsource: {cfg.source}")
    print(
        "override per run with --decomposer / --prover-model, or pin them in "
        f'{DEFAULT_CONFIG} ([tiers] decomposer = "anthropic/claude-fable-5").'
    )
    return 0


def cmd_doctor(args: argparse.Namespace) -> int:
    from pcp.cli.cmd_setup import check_pins, pins_summary
    from pcp.util.assets import check_assets, pins_path

    ok = True
    prefix = penv.switch_prefix()
    print(f"toolchain (pinned: {pins_summary()})")
    print(f"  {'opam switch':24} {penv.opam_switch()} at {prefix or f'{penv.opam_root()} — missing (`pcp setup`)'}")
    for label, value in (
        ("coqc / rocq", penv.coqc_binary()),
        ("pet (stdio petanque)", penv.pet_binary()),
        ("pet-server (socket)", penv.pet_server_binary()),
        ("bwrap (sandbox)", penv.bwrap_binary()),
    ):
        print(f"  {label:24} {value or '— missing'}")
        if label == "coqc / rocq" and not value:
            ok = False
    for var in (penv.COQPATH, penv.ROCQPATH):
        print(f"  {var:24} {os.environ.get(var, '— unset')}")
    roots = penv.library_roots()
    print(f"  {'library roots':24} {', '.join(str(r) for r in roots) or '— none'}")

    print(f"\npins ({pins_path()})")
    for check in check_pins():
        mark = "ok" if check.ok else "— MISMATCH" if check.installed else "— missing"
        print(f"  {check.name:24} {check.installed or '—'} (pinned {check.pinned})  {mark}")
        if not check.ok:
            ok = False

    print("\npackaged assets")
    for rel, problem in check_assets():
        print(f"  {rel:24} {'ok' if problem is None else '— ' + problem}")
        if problem is not None:
            ok = False

    print("\nlibraries")
    if importlib.util.find_spec("pytanque") is not None:
        print("  pytanque                 ok")
    else:
        print("  pytanque                 — missing (pip install 'pytanque @ git+https://github.com/LLM4Rocq/pytanque@4092b1238b56468fdc1b3d100e078791c9690fd4')")
    try:
        from pcp.mcp.server import make_mcp

        make_mcp("probe")
        print("  mcp server API           ok")
    except Exception as exc:  # noqa: BLE001 -- report, do not crash the doctor
        print(f"  mcp server API           — unusable ({exc})")

    print("\nmodels by role")
    for line in describe_bindings(_config(args)).splitlines():
        print("  " + line)

    print("\nrunners")
    from pcp.orch.runners.base import RUNNER_NAMES, RunnerSpec, build_runner

    for name in RUNNER_NAMES:
        if name == "mock":
            continue
        try:
            runner = build_runner(RunnerSpec(runner=name))
            mark = "ok" if runner.available() else "— unavailable"
        except Exception as exc:  # noqa: BLE001
            mark = f"— unavailable ({exc})"
        print(f"  {name:24} {mark}")
    print(
        "\nLogin is delegated: run `codex login` or Claude Code's `/login` yourself. "
        "Inside a Claude Code session, `! codex login` runs it without leaving the session."
    )
    if not ok:
        err(
            "\nRun `pcp setup` to build or repair the pinned switch (`pcp setup --dry-run` shows what it "
            'would do). pcp finds the switch itself; `eval "$(pcp env)"` also puts rocq/coqc on your '
            "shell's PATH. A missing packaged asset means a broken install: reinstall proof-copilot."
        )
    return 0 if ok else 1


def cmd_docs(args: argparse.Namespace) -> int:
    from pcp.rocq.library import build_index

    roots = penv.library_roots()
    if not roots:
        raise UsageError("no Rocq library root found; set ROCQPATH")
    out = absolute(args.out) or Path(".pcp/docs/index.txt").resolve()
    n, found = build_index(out, libraries=tuple(args.libraries), roots=roots)
    print(f"{n} declarations from {', '.join(found or args.libraries)} → {out}")
    return 0
