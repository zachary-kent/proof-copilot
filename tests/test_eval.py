"""eval/harness.py and eval/ablations.py: the held-out-lemma harness on the prove pipeline.

Most harness guarantees hold by construction -- a runner per arm, a task directory
removed before the task starts, a record subtree per arm and task, the packet written
by ``pcp prove`` itself; the rest have a test named after them below (error
accounting, holdouts reported rather than skipped, recording that can be switched off).
"""

from __future__ import annotations

import json
import shutil
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from eval.ablations import LADDER, ORDER, Ablation, deltas, describe  # noqa: E402
from eval.harness import (  # noqa: E402
    ArmPaths,
    Metrics,
    Outcome,
    Task,
    arm_runner,
    arm_spec,
    collect_benchmark,
    collect_tasks,
    main,
    run_arm,
    task_config,
)
from pcp.config.load import load  # noqa: E402
from pcp.errors import UsageError  # noqa: E402
from pcp.orch.runners.mock import MockRunner  # noqa: E402
from pcp.rocq.decls import find_block  # noqa: E402
from tests.conftest import needs_rocq  # noqa: E402

CANARY_MAIN = 'iIntros "[HP [HQ HR]]". iFrame.'


def _canary_library(tmp_path: Path, canary_dir: Path) -> Path:
    """A copy of the canary corpus posing as an installed library: the real one is
    never written to, and ``canary_main`` still carries its ``Qed`` proof."""
    lib = tmp_path / "lib"
    lib.mkdir()
    for name in ("Canary.v", "_CoqProject"):
        shutil.copy(canary_dir / name, lib / name)
    return lib


def _canary_task(tmp_path: Path, canary_dir: Path) -> Task:
    tasks = collect_tasks(_canary_library(tmp_path, canary_dir), "*.v", limit=5)
    assert [t.lemma for t in tasks] == ["canary_main"]
    return tasks[0]


# ------------------------------------------------------------------ the ablation ladder


def test_every_rung_is_a_strict_superset_of_the_one_before() -> None:
    previous: Ablation | None = None
    for name in ORDER:
        arm = LADDER[name]
        if previous is not None:
            assert set(previous.tools) < set(arm.tools) or (set(previous.tools) == set(arm.tools) and arm.skill != previous.skill)
            assert not previous.skill or arm.skill == previous.skill
        previous = arm
    assert LADDER["baseline"].tools == ()
    assert "proof_try" in LADDER["speculative"].tools and "proof_try" not in LADDER["retrieval"].tools
    assert LADDER["ledger"].skill == "prover.md" and LADDER["goal-dump"].skill == ""
    text = describe()
    assert "+proof_ledger" in text and "+skill prover.md" in text and "+proof_try" in text


def test_an_ablation_refuses_an_unknown_tool() -> None:
    with pytest.raises(ValueError, match="unknown state tool"):
        Ablation("bogus", ("proof_open", "proof_teleport"))


def test_deltas_give_a_verdict_per_rung_and_none_for_an_arm_that_only_errored() -> None:
    rows = [
        {"ablation": "baseline", "n": 4, "measured": 4, "solve_rate": 0.25},
        {"ablation": "goal-dump", "n": 4, "measured": 4, "solve_rate": 0.5},
        {"ablation": "ledger", "n": 4, "measured": 0, "solve_rate": 0.0},
        {"ablation": "retrieval", "n": 4, "measured": 4, "solve_rate": 0.5},
    ]
    lines = deltas(rows).splitlines()
    assert lines[0].split() == ["baseline", "25.0%"]
    assert "(+25.0 pt)  earns its context" in lines[1]
    assert "n/a" in lines[2] and "errored" in lines[2]
    # Compared against the last *measured* arm, not the errored one.
    assert "(+0.0 pt)  DOES NOT EARN ITS CONTEXT -- delete it" in lines[3]


# ------------------------------------------------------------------ one runner per arm


def test_the_control_arm_runner_carries_no_mcp_grant_and_the_ledger_arm_does() -> None:
    """The runner is a function of the arm alone, never the union of every arm's tools,
    so the baseline's argv has no ``--mcp-config`` and no ``mcp__pcp__*``."""
    cfg = load(None)
    control, _ = arm_spec("claude", LADDER["baseline"], cfg=cfg)
    assert control.mcp_tools == ()
    runner, _ = arm_runner("claude", LADDER["baseline"], cfg=cfg)
    assert "--mcp-config" not in runner.argv
    assert not any(a.startswith("mcp__pcp__") for a in runner.argv)
    assert "--strict-mcp-config" in runner.argv

    ledger, _ = arm_spec("claude", LADDER["ledger"], cfg=cfg)
    assert ledger.mcp_tools == LADDER["ledger"].tools
    runner, _ = arm_runner("claude", LADDER["ledger"], cfg=cfg)
    assert "--mcp-config" in runner.argv
    granted = [a for a in runner.argv if a.startswith("mcp__pcp__")]
    assert granted == [f"mcp__pcp__{t}" for t in LADDER["ledger"].tools]
    assert "mcp__pcp__proof_try" not in granted


def test_a_runner_that_cannot_honour_the_grant_is_refused_not_run_without_it() -> None:
    with pytest.raises(UsageError, match="ignores --state-tools"):
        arm_runner("codex", LADDER["ledger"], cfg=load(None))
    with pytest.raises(UsageError, match="unknown runner"):
        arm_runner("teleport", LADDER["baseline"], cfg=load(None))


def test_the_mock_arm_keeps_its_grant_in_the_packet(tmp_path: Path, canary_dir: Path) -> None:
    """The mock has no command line; its grant is ``ProveConfig.state_tools``, which
    is what makes ``pcp prove`` describe and wire the tools in the packet."""
    spec, _ = arm_spec("mock", LADDER["ledger"], cfg=load(None), answers={"canary_main": CANARY_MAIN})
    assert spec.mcp_tools == () and spec.answers == {"canary_main": CANARY_MAIN}
    task = _canary_task(tmp_path, canary_dir)
    cfg = task_config(task, LADDER["ledger"], ArmPaths(tmp_path / "work"), timeout=30)
    assert list(cfg.state_tools) == list(LADDER["ledger"].tools)
    assert cfg.skills and cfg.skills[0].startswith("# Prover")
    assert cfg.max_attempts == 1 and cfg.require_orchestration is False and cfg.plan is None
    assert cfg.node_seconds == 30


# ------------------------------------------------------------------ tasks


def test_collect_benchmark_reads_every_holdout_of_a_design_rung(bench_dir: Path) -> None:
    tasks = collect_benchmark(bench_dir / "rwcas_design")
    assert [t.lemma for t in tasks] == ["new_rwcas_spec", "read_spec", "write_spec"]
    assert all(t.held_out and t.file.name == "Rwcas.v" for t in tasks)
    assert next(t for t in tasks if t.lemma == "write_spec").reference_tactics == 119
    assert tasks[0].statement.startswith("Lemma new_rwcas_spec")
    assert len({t.key for t in tasks}) == 3


def test_a_holdout_the_corpus_file_does_not_have_is_reported_not_silently_skipped(tmp_path: Path, bench_dir: Path, capsys) -> None:
    """A missing holdout is reported; ``n`` never shrinks without a word."""
    corpus = tmp_path / "corpus"
    shutil.copytree(bench_dir / "rwcas_design", corpus)
    meta = json.loads((corpus / "bench.json").read_text())
    meta["holdout"].append({"name": "ghost_spec", "anonymised": "ghost_spec", "tactics": 3})
    meta["holdout"].append({"name": "is_rwcas_persistent", "anonymised": "is_rwcas_persistent", "tactics": 1})
    (corpus / "bench.json").write_text(json.dumps(meta))
    tasks = collect_benchmark(corpus)
    assert [t.lemma for t in tasks] == ["new_rwcas_spec", "read_spec", "write_spec"]
    err = capsys.readouterr().err
    assert "'ghost_spec' is not declared" in err and "skipped" in err
    assert "'is_rwcas_persistent' is not Admitted" in err


def test_collect_tasks_holds_out_a_qed_proof_into_a_copy_and_leaves_the_library_alone(tmp_path: Path, canary_dir: Path) -> None:
    lib = _canary_library(tmp_path, canary_dir)
    before = (lib / "Canary.v").read_text()
    tasks = collect_tasks(lib, "*.v", limit=5)
    assert [t.lemma for t in tasks] == ["canary_main"]
    task = tasks[0]
    assert not task.held_out and task.reference_body.strip() == CANARY_MAIN and task.reference_tactics == 2
    copy = task.materialise(tmp_path / "dest")
    assert copy == tmp_path / "dest" / "Canary.v" and (tmp_path / "dest" / "_CoqProject").exists()
    block = find_block(copy.read_text(), "canary_main")
    assert block is not None and block.admitted and block.statement == task.statement
    assert (lib / "Canary.v").read_text() == before, "the library must never be modified"
    assert collect_tasks(lib, "*.v", limit=0) == []


# ------------------------------------------------------------------ metrics


def test_metrics_count_errors_separately_and_keep_them_out_of_the_rate() -> None:
    """A missing binary is not an unsolved lemma."""
    m = Metrics(ablation="ledger")
    m.add(Outcome(file="a.v", lemma="a", status="qed", solved=True, tokens=100, tool_calls=4, checks=2, elapsed_s=10, dollars=0.5))
    m.add(Outcome(file="a.v", lemma="b", status="stuck", error="Unable to unify"))
    m.add(Outcome(file="a.v", lemma="c", status="error", infrastructure=True, error="claude is not on PATH"))
    assert (m.n, m.measured, m.solved, m.errors) == (3, 2, 1, 1)
    assert m.solve_rate == 0.5
    line = m.render()
    assert line.startswith("ledger         solve 1/2 (50%)  tokens/solved 100  tools/solved 4.0  checks/solved 2.0  wall/solved 10s  $0.50")
    assert line.endswith("  error 1")
    data = m.to_json()
    assert {"ablation", "n", "measured", "solved", "errors", "solve_rate", "tokens_per_solved", "tool_calls_per_solved", "wall_per_solved", "outcomes"} <= set(data)
    assert data["errors"] == 1 and data["outcomes"][2]["infrastructure"] is True
    back = Metrics.from_json(json.loads(json.dumps(data)))
    assert (back.n, back.solved, back.errors) == (3, 1, 1) and back.outcomes[0].solved
    clean = Metrics(ablation="baseline")
    assert "error" not in clean.render() and clean.solve_rate == 0.0


# ------------------------------------------------------------------ running arms


def test_a_task_directory_is_fresh_per_run_and_a_crashing_runner_is_an_error_outcome(tmp_path: Path, canary_dir: Path) -> None:
    """Nothing an earlier run left can be scored."""
    task = _canary_task(tmp_path, canary_dir)
    paths = ArmPaths(workroot=tmp_path / "work" / "baseline")
    stale = paths.task_root(task) / "work" / "stale" / "answer.json"
    stale.parent.mkdir(parents=True)
    stale.write_text('{"status": "qed", "proof": "admit."}')
    runner = MockRunner(answers={"canary_main": CANARY_MAIN}, raise_for={"canary_main"})
    metrics = run_arm_sync([task], LADDER["baseline"], runner, paths, timeout=30)
    assert not stale.exists()
    assert (metrics.n, metrics.errors, metrics.measured, metrics.solved) == (1, 1, 0, 0)
    out = metrics.outcomes[0]
    assert out.status == "error" and out.infrastructure and not out.solved
    assert "scripted crash" in out.error
    assert "error 1" in metrics.render()
    assert "n/a" in deltas([metrics])


def run_arm_sync(tasks, arm, runner, paths, **kw) -> Metrics:
    import asyncio

    return asyncio.run(run_arm(tasks, arm, runner, paths, concurrency=2, **kw))


def test_no_tasks_and_an_unknown_ablation_exit_2(tmp_path: Path, canary_dir: Path) -> None:
    empty = tmp_path / "empty"
    empty.mkdir()
    assert main(["--root", str(empty), "--files", "*.v", "--no-record", "--workroot", str(tmp_path / "w")]) == 2
    lib = _canary_library(tmp_path, canary_dir)
    assert main(["--root", str(lib), "--files", "*.v", "--ablations", "baseline,teleport", "--no-record"]) == 2


@needs_rocq
def test_two_arms_on_the_canary_produce_two_record_runs_and_distinct_packets(tmp_path: Path, canary_dir: Path, capsys) -> None:
    lib = _canary_library(tmp_path, canary_dir)
    answers = tmp_path / "answers.json"
    answers.write_text(json.dumps({"canary_main": CANARY_MAIN}))
    record, workroot, out = tmp_path / "records", tmp_path / "work", tmp_path / "results.json"
    code = main([
        "--root", str(lib), "--files", "*.v", "--runner", "mock", "--mock-answers", str(answers),
        "--ablations", "baseline,goal-dump", "--workroot", str(workroot), "--record", str(record),
        "--out", str(out), "--timeout", "120", "--concurrency", "2",
    ])
    captured = capsys.readouterr()
    assert code == 0, captured.err
    runs = sorted(p.name for p in record.iterdir())
    assert len(runs) == 2 and runs[0].endswith("-baseline") and runs[1].endswith("-goal-dump")

    data = json.loads(out.read_text())
    assert set(data) == {"runner", "results"} and data["runner"] == "mock"
    assert [r["ablation"] for r in data["results"]] == ["baseline", "goal-dump"]
    for r in data["results"]:
        assert (r["n"], r["solved"], r["errors"]) == (1, 1, 0) and r["solve_rate"] == 1.0
        assert r["outcomes"][0]["status"] == "qed" and r["outcomes"][0]["integrated"] is True
        assert r["outcomes"][0]["record"].startswith(str(record))
    assert "baseline       solve 1/1 (100%)" in captured.out
    assert "goal-dump      solve 1/1 (100%)" in captured.out
    assert "earns its context" in captured.out or "DOES NOT EARN" in captured.out
    assert "1/1 solved" in captured.out  # the failure summary per arm

    # The two arms ran different packets: only the tools arm names its tools.
    packets = {name: next((record / name).rglob("TASK.md")).read_text() for name in runs}
    assert "mcp__pcp__proof_open" not in packets[runs[0]]
    assert "mcp__pcp__proof_open" in packets[runs[1]]
    records = [json.loads(p.read_text()) for p in record.rglob("record.json")]
    assert len(records) == 2 and all(r["solved"] and r["runner"] == "mock" for r in records)
    # A second run into the same workroot starts from nothing: the graphs are fresh.
    graphs = list(workroot.rglob("graph.db"))
    assert len(graphs) == 2
