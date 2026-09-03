"""The daily loop must not depend on the state layer (PLAN.md 8.11).

"Non-dependencies, by design: ... and no pcp-state at all: day-one workers ride
rocq-mcp or plain `coqc` feedback, and the state layer (Phases 2-4) upgrades their
solve rate rather than gating the loop."

That is a load-bearing claim -- it is why Phase 1 could ship before Phase 2 -- and
claims like it rot silently.  So it is a test: `pcp prove` must import and run on a
machine where the only Rocq binary is `coqc` and petanque does not exist.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

#: Modules whose presence would mean the loop had acquired a petanque dependency.
FORBIDDEN = ("pytanque", "pcp.core.session", "pcp.core.trace", "pcp.core.ipm", "pcp.core.ledger")

PROBE = """
import sys
import pcp.orch.prove
import pcp.orch.gate
import pcp.orch.schedule
import pcp.orch.graph
import pcp.orch.runners.cli
import pcp.orch.runners.mock
leaked = [m for m in {forbidden!r} if m in sys.modules]
print(",".join(leaked))
"""


def test_daily_loop_does_not_import_the_state_layer() -> None:
    proc = subprocess.run(
        [sys.executable, "-c", PROBE.format(forbidden=FORBIDDEN)],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    leaked = [m for m in proc.stdout.strip().split(",") if m]
    assert not leaked, (
        "the daily loop imported the state layer: "
        + ", ".join(leaked)
        + " -- Phase 1 must run with coqc alone"
    )


def test_state_layer_does_not_import_the_orchestrator() -> None:
    """The other direction too: pcp-state outlives any orchestration framework."""
    proc = subprocess.run(
        [
            sys.executable,
            "-c",
            "import sys, pcp.core.trace, pcp.core.render, pcp.core.ledger.query;"
            "print(','.join(m for m in sys.modules if m.startswith('pcp.orch')))",
        ],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    leaked = [m for m in proc.stdout.strip().split(",") if m]
    assert not leaked, "pcp-state imported pcp-orch: " + ", ".join(leaked)


def test_the_gate_needs_only_coqc() -> None:
    """The gate shells out to `coqc`; it must not reach for petanque."""
    import inspect

    from pcp.orch import gate

    source = inspect.getsource(gate)
    assert "pytanque" not in source
    assert "pet-server" not in source
