"""The CLI surface, including the worker-facing `pcp check`."""

from __future__ import annotations

import json
import subprocess
import sys

import pytest
from pathlib import Path

from tests.conftest import needs_rocq

ROOT = Path(__file__).resolve().parents[1]


def run(*args: str, cwd: Path | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, "-m", "pcp.cli.main", *args],
        cwd=str(cwd or ROOT),
        capture_output=True,
        text=True,
    )


def test_help_and_version() -> None:
    assert run("--version").returncode == 0
    assert "prove" in run("--help").stdout


def test_doctor_reports_what_is_missing() -> None:
    proc = run("doctor")
    assert "toolchain" in proc.stdout and "runners" in proc.stdout
    # Login is delegated, never implemented -- the doctor says so rather than
    # offering to log in.
    assert "Login is delegated" in proc.stdout


def test_destruct_compiles_a_pattern_offline() -> None:
    proc = run("destruct", "∃ γ, own γ (◯ n) ∗ ⌜n = 3⌝")
    assert proc.returncode == 0
    assert 'iDestruct "H" as (γ) "[H1 %H2]"' in proc.stdout


def test_destruct_diagnoses_a_bad_pattern_offline() -> None:
    proc = run("destruct", "l ↦ v ∗ P", "--pattern", "[H1|H2]")
    assert proc.returncode == 1
    assert "disjunction" in proc.stdout
    assert "a pattern that fits: [H1 H2]" in proc.stdout


def test_sketch_compiles_to_a_plan(tmp_path: Path, canary_dir: Path) -> None:
    out = tmp_path / "plan.v"
    proc = run("sketch", str(canary_dir / "counter.sketch"), "--out", str(out))
    assert proc.returncode == 0, proc.stderr
    text = out.read_text(encoding="utf-8")
    # Every invariant owes an inhabitation witness, as a node not a note.
    assert "Lemma Icount_alloc" in text
    assert "Lemma incr_glue_load_cmpxchg" in text
    assert "commit point" in proc.stdout


@needs_rocq
def test_prove_and_status_and_handoff(tmp_path: Path, canary_dir: Path) -> None:
    """The three commands the daily loop actually needs, driven as a user would."""
    graph = tmp_path / "graph.db"
    work = tmp_path / "work"
    proc = run(
        "prove", str(canary_dir / "Canary.v"), "canary_main",
        "--plan", str(canary_dir / "plan.v"),
        "--runner", "mock", "--graph", str(graph), "--workroot", str(work),
    )
    # The mock runner has no scripted answers here, so nothing proves -- but the loop
    # must terminate cleanly and report three stuck nodes rather than wedging.
    assert proc.returncode == 1
    assert "3 stuck" in proc.stdout

    status = run("status", "--graph", str(graph), "--json")
    assert status.returncode == 0
    data = json.loads(status.stdout)
    assert data["summary"] == {"stuck": 3}
    assert {n["name"] for n in data["nodes"]} == {"canary_main", "canary_swap", "canary_assoc"}

    out = tmp_path / "h.v"
    handoff = run("handoff", "canary_swap", "--graph", str(graph), "-o", str(out))
    assert handoff.returncode == 0
    assert "Lemma canary_swap" in out.read_text(encoding="utf-8")


@needs_rocq
def test_pcp_check_is_what_the_worker_runs(tmp_path: Path, canary_dir: Path) -> None:
    """"It compiled for me" and "it passed the gate" must be the same sentence."""
    graph = tmp_path / "graph.db"
    work = tmp_path / "work"
    run(
        "prove", str(canary_dir / "Canary.v"), "canary_main",
        "--plan", str(canary_dir / "plan.v"),
        "--runner", "mock", "--graph", str(graph), "--workroot", str(work),
    )
    workdir = work / "canary_swap"
    assert (workdir / "pcp-node.json").exists()
    # The packet must not list the node itself as an available lemma.
    task = (workdir / "TASK.md").read_text(encoding="utf-8")
    assert "`canary_swap` (" not in task

    good = tmp_path / "good.v"
    good.write_text('iIntros "[HA HB]". iFrame.', encoding="utf-8")
    ok = run("check", "--body", str(good), cwd=workdir)
    assert ok.returncode == 0, ok.stdout + ok.stderr
    assert "gate: PASS" in ok.stdout

    bad = tmp_path / "bad.v"
    bad.write_text('iIntros "[HA HB]". done.', encoding="utf-8")
    fail = run("check", "--body", str(bad), cwd=workdir)
    assert fail.returncode == 1
    assert "gate: FAIL" in fail.stdout


@needs_rocq
def test_pcp_check_refuses_outside_a_node_directory(tmp_path: Path) -> None:
    proc = run("check", cwd=tmp_path)
    assert proc.returncode == 2
    assert "pcp-node.json" in proc.stderr


def test_a_model_flag_accepts_the_form_pcp_models_prints() -> None:
    """`pcp models` prints `anthropic/claude-opus-5`; the flag must take that.

    Passed through verbatim it reached `claude --model anthropic/claude-opus-5`,
    which is rejected -- and the run died at the first decomposition with "no JSON
    object to read", which reads like a decomposer fault rather than a bad flag.
    """
    from pcp.cli.main import _model_flag

    assert _model_flag("anthropic/claude-opus-5", "--decomposer") == "claude-opus-5"
    assert _model_flag("claude-opus-5", "--decomposer") == "claude-opus-5"
    assert _model_flag(None, "--decomposer") is None


def test_a_model_flag_refuses_another_provider() -> None:
    from pcp.cli.main import _model_flag

    with pytest.raises(SystemExit) as exc:
        _model_flag("codex/luna", "--prover-model")
    assert "codex" in str(exc.value)


def test_an_explained_abort_exits_1_rather_than_crashing(tmp_path) -> None:
    """`SystemExit("message")` is how this codebase aborts with an explanation.

    `int()` on it raised ValueError, so the explanation was buried under a traceback.
    """
    import subprocess
    import sys as _sys

    src = tmp_path / "T.v"
    src.write_text("Lemma t : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    proc = subprocess.run(
        [_sys.executable, "-m", "pcp.cli.main", "prove", str(src), "t",
         "--prover-model", "codex/luna", "--no-orchestration"],
        capture_output=True, text=True,
    )
    assert proc.returncode == 1, proc.stderr
    assert "codex" in proc.stderr
    assert "Traceback" not in proc.stderr


def test_the_control_arm_does_not_inherit_the_operator_s_mcp_servers() -> None:
    """`--strict-mcp-config` means "only servers from --mcp-config", so with none
    named it means none at all -- and it must go on in *both* arms.

    Passing it only when tools were granted meant the tools-off arm loaded whatever
    MCP config happened to sit in the operator's home. A benchmark run recorded
    `mcp_servers=[{'name': 'claude.ai Google Drive', 'status': 'needs-auth'}]` in
    every worker. Inert there, but an ablation whose control arm varies by machine
    measures the machine.
    """
    from pcp.orch.runners.cli import claude_headless_runner

    off = claude_headless_runner("m").argv
    assert "--strict-mcp-config" in off
    assert "--mcp-config" not in off, "nothing to load in the control arm"

    on = claude_headless_runner("m", mcp_tools=["proof_open"]).argv
    assert "--strict-mcp-config" in on
    assert on[on.index("--mcp-config") + 1] == ".mcp.json"
    assert "mcp__pcp__proof_open" in on


def test_state_tools_resolve_to_a_named_set() -> None:
    """What "tools on" meant has to be recoverable from the source, not from
    whatever the server happened to register that day."""
    import pcp.cli.main as cli

    assert cli._state_tools(None) == []
    assert cli._state_tools("all") == list(cli.STATE_TOOLS)
    assert cli._state_tools("proof_open,proof_try") == ["proof_open", "proof_try"]
    with pytest.raises(SystemExit) as exc:
        cli._state_tools("proof_open,teleport")
    assert "teleport" in str(exc.value)


def test_the_mcp_config_is_written_per_node(tmp_path) -> None:
    """Rooted in the node's own workdir, so one worker's proof sessions cannot
    reach another's scratch even though they share a binary."""
    import json

    from pcp.orch.assemble import Development
    from pcp.orch.graph import Node
    from pcp.orch.packet import build_packet

    src = tmp_path / "Dev.v"
    src.write_text("Lemma a : True.\nProof.\nAdmitted.\n")
    dev = Development(src)
    node = Node(id="a", name="a", statement="Lemma a : True.", parent=None)

    plain = build_packet(None, node, dev, [], anchor="a", root=tmp_path / "off")
    assert not (plain.workdir / ".mcp.json").exists()

    withtools = build_packet(None, node, dev, [], anchor="a", root=tmp_path / "on",
                            state_tools=["proof_open"])
    cfg = json.loads((withtools.workdir / ".mcp.json").read_text())
    server = cfg["mcpServers"]["pcp"]
    assert server["args"][:2] == ["mcp", "--workspace"]
    assert server["args"][2] == str(withtools.workdir)


def test_a_killed_worker_keeps_the_output_it_streamed(tmp_path) -> None:
    """A deadline must not destroy the only evidence of what the worker did.

    Two of three rungs on the 2026-09-01 design ladder died on a decomposer deadline.
    Because stdout was collected with `communicate()`, which returns nothing unless
    the process exits, every byte the worker had streamed was discarded at the kill:
    the records read `trace: {}` with an empty transcript and no cost, so a worker
    thinking hard for an hour looked exactly like one hung on its first token.  The
    usual recovery -- read what the worker wrote to disk -- cannot help a decomposer,
    which is read-only by construction.
    """
    import asyncio
    from pcp.orch.runners.base import NodePayload
    from pcp.orch.runners.cli import CLIRunner

    (tmp_path / "TASK.md").write_text("go", encoding="utf-8")
    # Emit a well-formed stream event, then hang well past the deadline.
    event = (
        '{"type":"assistant","message":{"content":[{"type":"text","text":"partial thought"}]}}'
    )
    runner = CLIRunner(
        argv=["python3", "-c",
              f"import sys,time; print({event!r}, flush=True); time.sleep(60)"],
        name="probe", binary="python3", stream_json=True,
    )
    node = NodePayload(node_id="n", name="n", statement="", file="f.v",
                       workdir=tmp_path, budget_seconds=1.5)
    result = asyncio.run(runner.run_node(node))

    assert result.status == "stuck"
    assert "deadline" in result.evidence
    assert result.trace, "the stream captured before the kill must survive it"
    assert "no output at all" not in result.evidence
    assert "bytes of output before the kill" in result.evidence


def test_a_silent_worker_is_reported_as_silent(tmp_path) -> None:
    """The other half: distinguishing 'worked but slow' from 'never said anything'."""
    import asyncio
    from pcp.orch.runners.base import NodePayload
    from pcp.orch.runners.cli import CLIRunner

    (tmp_path / "TASK.md").write_text("go", encoding="utf-8")
    runner = CLIRunner(
        argv=["python3", "-c", "import time; time.sleep(60)"],
        name="probe", binary="python3", stream_json=True,
    )
    node = NodePayload(node_id="n", name="n", statement="", file="f.v",
                       workdir=tmp_path, budget_seconds=1.5)
    result = asyncio.run(runner.run_node(node))

    assert result.status == "stuck"
    assert "the worker produced no output at all before the kill" in result.evidence
