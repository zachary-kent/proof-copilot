"""The layering contract (docs/ARCHITECTURE.md 1), as a test.

The daily loop must run where the only Rocq binary is ``coqc``: ``pcp.orch`` must not
import the state layer or petanque.  And pcp-state outlives any orchestration
framework: it must not import ``pcp.orch``.  Claims like these rot silently, so they
are tests.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

PROBE = """
import importlib, sys
for m in {imports!r}:
    importlib.import_module(m)
leaked = sorted(m for m in sys.modules if any(m == f or m.startswith(f + '.') for f in {forbidden!r}))
print(",".join(leaked))
"""


def _leaks(imports: list[str], forbidden: list[str]) -> list[str]:
    proc = subprocess.run(
        [sys.executable, "-c", PROBE.format(imports=imports, forbidden=forbidden)],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr
    return [m for m in proc.stdout.strip().split(",") if m]


def test_orch_does_not_import_the_state_layer() -> None:
    leaked = _leaks(
        [
            "pcp.orch.prove", "pcp.orch.gate", "pcp.orch.schedule", "pcp.orch.graph",
            "pcp.orch.runners.cli", "pcp.orch.runners.mock", "pcp.orch.packet", "pcp.orch.record",
        ],
        ["pytanque", "pcp.state", "pcp.mcp.server"],
    )
    assert not leaked, "the daily loop imported the state layer: " + ", ".join(leaked)


def test_state_layer_does_not_import_the_orchestrator() -> None:
    leaked = _leaks(
        ["pcp.state.trace", "pcp.state.render", "pcp.state.ledger.query", "pcp.state.session", "pcp.state.explain"],
        ["pcp.orch", "pcp.cli", "pcp.dash"],
    )
    assert not leaked, "pcp-state imported pcp-orch: " + ", ".join(leaked)


def test_rocq_layer_is_toolchain_free() -> None:
    leaked = _leaks(
        ["pcp.rocq.lexer", "pcp.rocq.decls", "pcp.rocq.body", "pcp.rocq.assemble", "pcp.rocq.project", "pcp.rocq.assumptions"],
        ["pytanque", "pcp.state", "pcp.orch", "pcp.mcp"],
    )
    assert not leaked, "pcp.rocq imported an upper layer: " + ", ".join(leaked)


def test_util_and_config_are_stdlib_only() -> None:
    leaked = _leaks(
        ["pcp.util.proc", "pcp.util.io", "pcp.util.locks", "pcp.config.load", "pcp.config.providers"],
        ["pcp.rocq", "pcp.state", "pcp.orch", "pcp.mcp", "pytanque"],
    )
    assert not leaked, "pcp.util/config imported an upper layer: " + ", ".join(leaked)


def test_cli_imports_nothing_until_a_command_runs() -> None:
    leaked = _leaks(["pcp.cli.main"], ["pcp.state", "pcp.orch", "pytanque", "pcp.mcp.server"])
    assert not leaked, "pcp.cli.main eagerly imported: " + ", ".join(leaked)


def test_no_raw_subprocess_outside_proc_and_petanque() -> None:
    """Rule 1: subprocesses go through pcp.util.proc (petanque owns its pet)."""
    offenders = []
    for path in (ROOT / "pcp").rglob("*.py"):
        rel = path.relative_to(ROOT).as_posix()
        if rel in ("pcp/util/proc.py", "pcp/state/petanque.py"):
            continue
        text = path.read_text(encoding="utf-8")
        if "subprocess.Popen(" in text or "subprocess.run(" in text or "create_subprocess_exec(" in text:
            offenders.append(rel)
    assert not offenders, "raw subprocess use outside pcp.util.proc: " + ", ".join(offenders)


def test_no_systemexit_outside_the_cli() -> None:
    """Rule 5: library code raises PcpError; only the CLI maps to exit codes."""
    offenders = []
    for path in (ROOT / "pcp").rglob("*.py"):
        rel = path.relative_to(ROOT).as_posix()
        if rel.startswith("pcp/cli/"):
            continue
        text = path.read_text(encoding="utf-8")
        if "raise SystemExit" in text or "sys.exit(" in text:
            offenders.append(rel)
    assert not offenders, "SystemExit outside pcp.cli: " + ", ".join(offenders)
