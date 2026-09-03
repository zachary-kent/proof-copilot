"""The MCP tool surface (PLAN.md 7), exercised through the same code the model calls.

The implementations are kept transport-free on purpose: an ablation that measures a
different code path from the one the model uses measures nothing.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from tests.conftest import needs_petanque, needs_rocq


def test_the_tool_surface_stays_small() -> None:
    """Every tool is a place the model can get lost, and every tool needs an
    ablation showing it earns its context."""
    from pcp.mcp.server import MAX_TOOLS, TOOLS

    assert len(TOOLS) <= MAX_TOOLS
    names = [n for n, _ in TOOLS]
    assert len(names) == len(set(names))
    # Deliberately not tools: a tool that tries to be an agent cannot be ablated.
    assert "prove_this_lemma" not in names
    assert "fix_this_proof" not in names


def test_pattern_diagnosis_is_produced_by_construction_not_on_request() -> None:
    from pcp.core.ipm.parse import parse_goal
    from pcp.mcp.diagnose import diagnose

    goal = parse_goal('  "H" : l ↦ v ∗ P\n--------------------------------------∗\n  Q')
    report = diagnose('iDestruct "H" as "[H1|H2]".', "Error: cannot destruct", goal)
    assert "disjunction" in report
    assert "a pattern that fits: [H1 H2]" in report


def test_a_malformed_pattern_gets_a_fitting_one_rather_than_a_parser_error() -> None:
    from pcp.core.ipm.parse import parse_goal
    from pcp.mcp.diagnose import diagnose

    goal = parse_goal('  "H" : l ↦ v ∗ P\n--------------------------------------∗\n  Q')
    report = diagnose('iDestruct "H" as "[H1 H2".', "Error", goal)
    assert "does not parse" in report and "[H1 H2]" in report


def test_leftover_spatial_is_named_when_a_closing_tactic_fails() -> None:
    """Failure mode #2: `iFrame` / `done` fails and the error does not say why."""
    from pcp.core.ipm.parse import parse_goal
    from pcp.mcp.diagnose import diagnose

    goal = parse_goal('  "Hl" : l ↦ v\n  "HQ" : Q\n--------------------------------------∗\n  P')
    report = diagnose("iFrame.", "Error: cannot solve", goal)
    assert "spatial context is not empty" in report
    assert '"Hl"' in report and '"HQ"' in report


@needs_petanque
@needs_rocq
class TestAgainstRocq:
    @pytest.fixture(scope="class")
    def server(self, scratch_dir: Path):
        from pcp.mcp.server import PcpServer

        s = PcpServer(scratch_dir)
        yield s
        s.close()

    def test_open_step_and_ledger(self, server) -> None:
        opened = server.proof_open("Blame.v", "premature_consumption")
        sid = opened["session"]
        assert "spatial" in opened["goal"][0] or "⊢" in opened["goal"][0]

        step = server.proof_step(sid, 'iIntros "[[HP HQ] HR]".')
        assert step["ok"]
        assert [e["kind"] for e in step["ledger"]].count("Intro") == 3

        left = server.proof_ledger(sid, "leftovers")
        assert left["count"] == 3

        server.proof_step(sid, "iFrame.")
        where = server.proof_ledger(sid, "where_did_it_go", hyp="HP")
        assert "step 1" in where["answer"]

    def test_speculative_fan_out(self, server) -> None:
        sid = server.proof_open("Basic.v", "sep_comm")["session"]
        out = server.proof_try(sid, ['iIntros "[HP HQ]".', "reflexivity.", "lia."])
        assert out["survivors"] == ['iIntros "[HP HQ]".']
        # Speculation must not move the session.
        assert server.proof_step(sid, 'iIntros "[HP HQ]".')["ok"]

    def test_destruct_compiles_and_applies(self, server) -> None:
        sid = server.proof_open("Basic.v", "exists_pure")["session"]
        server.proof_step(sid, 'iIntros "H".')
        out = server.proof_destruct(sid, "H", apply=True)
        assert out["ok"], out
        assert out["binders"] == ["n"]
        assert "%" in out["pattern"]

    def test_a_failing_pattern_bearing_tactic_returns_the_alignment_report(self, server) -> None:
        sid = server.proof_open("Basic.v", "destruct_nested")["session"]
        out = server.proof_step(sid, 'iIntros "[HP|HQ]".')
        assert not out["ok"]
        assert "mismatch" in out["diagnosis"] or "disjunction" in out["diagnosis"]

    def test_premise_search_finds_real_iris_lemmas(self, server) -> None:
        sid = server.proof_open("Basic.v", "load_twice")["session"]
        out = server.premise_search(sid, query="pointsto")
        assert out["count"] > 0, out["answer"]

    def test_verify_node_is_the_same_gate(self, server) -> None:
        good = server.verify_node("Basic.v", "sep_comm", 'iIntros "[HP HQ]". iFrame.')
        assert good["ok"]
        bad = server.verify_node("Basic.v", "sep_comm", "admit.")
        assert not bad["ok"]


# ------------------------------------------------------------- the server itself

def test_the_server_builds_and_serves_exactly_the_declared_tools(tmp_path: Path) -> None:
    """This is the test that was missing.

    `import mcp` succeeds on both SDK generations, so a package-level check reported
    the server healthy while it could not start at all: the SDK renamed `FastMCP` to
    `MCPServer` in 2.x, and the failure surfaced only when a worker asked for a tool.
    """
    import asyncio

    from pcp.mcp.server import TOOLS, build_server

    server, mcp = build_server(tmp_path)
    try:
        served = sorted(t.name for t in asyncio.run(mcp.list_tools()))
    finally:
        server.close()
    assert served == sorted(name for name, _ in TOOLS)


def test_every_served_tool_has_a_description(tmp_path: Path) -> None:
    """A tool the model cannot understand is a tool it will not use."""
    import asyncio

    from pcp.mcp.server import build_server

    server, mcp = build_server(tmp_path)
    try:
        tools = asyncio.run(mcp.list_tools())
    finally:
        server.close()
    for tool in tools:
        assert (tool.description or "").strip(), f"{tool.name} has no description"


# ------------------------------------------------------------------- the wiring

def test_mcp_tool_names_are_namespaced_for_the_allowlist() -> None:
    from pcp.orch.runners.cli import mcp_tool_name

    assert mcp_tool_name("proof_ledger") == "mcp__pcp__proof_ledger"
    assert mcp_tool_name("mcp__pcp__proof_try") == "mcp__pcp__proof_try"


def test_granting_tools_changes_the_worker_s_argv() -> None:
    """An ablation rung is only real if the worker's CLI is told about its tools."""
    from pcp.orch.runners.cli import claude_headless_runner

    plain = claude_headless_runner()
    assert "--mcp-config" not in plain.argv
    assert not [a for a in plain.argv if a.startswith("mcp__")]

    granted = claude_headless_runner(mcp_tools=["proof_ledger", "premise_search"])
    assert "--mcp-config" in granted.argv
    # Strict, so the operator's own servers cannot leak into a measurement.
    assert "--strict-mcp-config" in granted.argv
    assert "mcp__pcp__proof_ledger" in granted.argv
    assert "mcp__pcp__premise_search" in granted.argv


def test_the_mcp_config_points_at_this_pcp(tmp_path: Path) -> None:
    import json as _json

    from pcp.orch.runners.cli import MCP_SERVER_NAME, write_mcp_config

    path = write_mcp_config(tmp_path)
    config = _json.loads(path.read_text(encoding="utf-8"))
    server = config["mcpServers"][MCP_SERVER_NAME]
    assert server["command"] == "pcp"
    assert server["args"][:2] == ["mcp", "--workspace"]


def test_the_ladder_grants_strictly_more_at_each_rung() -> None:
    """The ladder only attributes a delta if each rung adds exactly one capability."""
    import sys
    from pathlib import Path as _P

    sys.path.insert(0, str(_P(__file__).resolve().parents[1]))
    from eval.ablations import LADDER, ORDER

    previous: set[str] = set()
    for name in ORDER:
        tools = set(LADDER[name].tools)
        assert previous <= tools, f"{name} drops a tool the previous rung had"
        previous = tools
    assert LADDER["baseline"].tools == []
    assert "proof_try" in LADDER["speculative"].tools


def test_petanque_gets_a_hard_memory_ceiling() -> None:
    """`rss_cap_mb` is only checked *between* calls, so one runaway tactic is
    unbounded -- Rocq's `Timeout` bounds time, not memory. An orphaned session
    reached 372 GB before anyone noticed. The ceiling has to be enforced by the OS
    so it binds inside the call."""
    from pcp.core.session import DEFAULT_MEM_LIMIT_MB, DEFAULT_RSS_CAP_MB, _pet_wrapper_dir

    assert DEFAULT_MEM_LIMIT_MB > DEFAULT_RSS_CAP_MB, (
        "the hard ceiling must sit above the soft cap, so the graceful restart is "
        "what normally fires and this is only the backstop"
    )
    wrapper = _pet_wrapper_dir(DEFAULT_MEM_LIMIT_MB) / "pet"
    text = wrapper.read_text(encoding="utf-8")
    assert f"ulimit -v {DEFAULT_MEM_LIMIT_MB * 1024}" in text
    assert text.rstrip().endswith('"$@"')
    assert wrapper.stat().st_mode & 0o111, "the wrapper must be executable"


def test_the_wrapper_ties_petanque_to_its_parent_when_it_can() -> None:
    """An orphan keeps its whole Rocq heap; one outlived its run by hours."""
    import shutil

    from pcp.core.session import DEFAULT_MEM_LIMIT_MB, _pet_wrapper_dir

    text = (_pet_wrapper_dir(DEFAULT_MEM_LIMIT_MB) / "pet").read_text(encoding="utf-8")
    if shutil.which("setpriv"):
        assert "--pdeathsig KILL" in text
    # Either way the address-space limit is applied before handing over.
    assert text.index("ulimit -v") < text.index("exec ")


def test_the_mcp_server_asks_to_die_with_its_client() -> None:
    """EOF on stdin cannot help a server blocked inside a runaway call."""
    import inspect

    from pcp.mcp import server

    assert "PR_SET_PDEATHSIG" in inspect.getsource(server._die_with_client)
    assert "_die_with_client()" in inspect.getsource(server.run_stdio)
