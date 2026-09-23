"""eval/ladder.py: the design-rung ladder.

Nothing here runs ``pcp prove`` or a provider: the rung launcher is replaced by a
``python -c`` stand-in, and preflight's machine probes are switched off.  Outages are
decided from records, never sniffed from log text
(``test_outage_is_decided_from_records_not_log_text``).
"""

from __future__ import annotations

import json
import shlex
import shutil
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from eval.ladder import (  # noqa: E402
    DEFAULT_PATHS,
    LADDER,
    Paths,
    Rung,
    _assert_library_is_clean,
    budget_problem,
    library_for,
    main,
    outage_of,
    preflight,
    publish,
    run_rung,
    rung_argv,
    select_rungs,
    tag_for,
)
from pcp.errors import UsageError  # noqa: E402
from pcp.orch.prove.integrate import solution_header  # noqa: E402
from pcp.orch.record import AttemptRecord, Recorder  # noqa: E402

ROW_KEYS = {"outage", "rung", "root", "exit", "timed_out", "elapsed_s", "record", "log", "published", "tail", "brief"}


def _launcher(code: str) -> list[str]:
    """A stand-in for ``python -u -m pcp.cli.main``: the rung's flags land in argv."""
    return [sys.executable, "-c", code]


def _paths(tmp_path: Path, bench_dir: Path, rungs: tuple[str, ...] = ("rwcas_design", "seqlock_design", "seqlock_wf_design")) -> Paths:
    """A private repo root holding copies of the design corpora."""
    paths = Paths(tmp_path / "repo")
    for name in rungs:
        shutil.copytree(bench_dir / name, paths.corpus / name)
    return paths


def _record(status: str, evidence: str, **kw) -> AttemptRecord:
    base = dict(run_id="r", node="n", lemma="fc23_spec", attempt=1, runner="claude", status=status, solved=False, evidence=evidence)
    base.update(kw)
    return AttemptRecord(**base)


# ------------------------------------------------------------------ rungs


def test_every_checked_in_design_rung_parses_and_roots_at_its_largest_holdout(bench_dir: Path) -> None:
    for rung in LADDER:
        assert rung.is_design_rung, rung.name
        bench = json.loads((bench_dir / rung.name / "bench.json").read_text())
        biggest = max(bench["holdout"], key=lambda h: h["tactics"])
        assert rung.root_lemma == biggest["anonymised"]
        assert rung.file.suffix == ".v" and "__pcp" not in rung.file.stem
    assert LADDER[0].root_lemma == "write_spec"
    assert {r.root_lemma for r in LADDER[1:]} == {"x34_spec", "fc50_spec"}
    assert preflight(list(LADDER), probes=False) == []


def test_preflight_refuses_a_proof_rung_and_a_missing_corpus_without_a_traceback() -> None:
    problems = preflight([Rung("rwcas", 900, 1800), Rung("nowhere", 900, 1800)], probes=False)
    assert len(problems) == 2
    assert problems[0].startswith("rwcas: the design is GIVEN here")
    assert problems[1].startswith("nowhere: no corpus at")


def test_preflight_budget_arithmetic() -> None:
    assert budget_problem(Rung("x", node_seconds=1800, decomposer_seconds=5400)) == ""
    assert budget_problem(Rung("x", node_seconds=2700, decomposer_seconds=5400)) == ""
    assert "cannot fit a revision" in budget_problem(Rung("x", node_seconds=2701, decomposer_seconds=5400))
    assert "9000s > wall 8000s" in budget_problem(Rung("x", node_seconds=1800, decomposer_seconds=5400, wall_seconds=8000))
    for rung in LADDER:
        assert budget_problem(rung) == "", rung.name


def test_only_refuses_an_unknown_rung_and_keeps_ladder_order() -> None:
    assert [r.name for r in select_rungs(["seqlock_design", "rwcas_design"])] == ["rwcas_design", "seqlock_design"]
    with pytest.raises(UsageError, match="no such rung"):
        select_rungs(["rwcas_design", "seqlock_desgin"])
    assert main(["--only", "nope", "--dry-run"]) == 2


# ------------------------------------------------------------------ the argv


def test_dry_run_spec_only_carries_no_library_and_says_so(capsys) -> None:
    assert main(["--dry-run", "--brief", "spec-only"]) == 0
    lines = capsys.readouterr().out.strip().splitlines()
    assert len(lines) == len(LADDER)
    for line, rung in zip(lines, LADDER, strict=True):
        argv = shlex.split(line)
        assert "--library" not in argv
        assert argv[argv.index("--brief") + 1] == "spec-only"
        assert argv[argv.index("--corpus") + 1] == rung.name
        assert {"--sandbox", "--fresh", "--state-tools"} <= set(argv)
        assert argv[argv.index("--node-seconds") + 1] == f"{rung.node_seconds:g}"
        assert argv[argv.index("--decomposer-seconds") + 1] == f"{rung.decomposer_seconds:g}"
        assert argv[argv.index("prove") + 2] == rung.root_lemma


def test_rung_argv_refuses_a_library_under_spec_only_and_passes_models_through(tmp_path: Path) -> None:
    rung = LADDER[0]
    with pytest.raises(UsageError, match="no --library is allowed"):
        rung_argv(rung, stamp="t", brief="spec-only", library=[tmp_path])
    argv = rung_argv(
        rung, stamp="t", brief="full", library=[tmp_path], runner="claude", decomposer="claude-opus-5",
        prover_model="claude-sonnet-5", extra=["--prover-effort", "high"],
    )
    tag = tag_for("t", rung.name)
    assert argv[argv.index("--library") + 1] == str(tmp_path)
    assert argv[argv.index("--decomposer") + 1] == "claude-opus-5"
    assert argv[argv.index("--prover-model") + 1] == "claude-sonnet-5"
    assert argv[argv.index("--runner") + 1] == "claude"
    assert argv[-2:] == ["--prover-effort", "high"]
    assert argv[argv.index("--graph") + 1] == str(DEFAULT_PATHS.graph(tag))
    assert argv[argv.index("--record") + 1] == str(DEFAULT_PATHS.record(tag))
    assert argv[argv.index("--reference") + 1] == str(DEFAULT_PATHS.reference / rung.name)


def test_the_carry_is_every_earlier_rung_published_plus_the_paper(tmp_path: Path, bench_dir: Path) -> None:
    paths = _paths(tmp_path, bench_dir)
    (paths.paper).mkdir(parents=True)
    (paths.paper / "README.md").write_text("# Big Atomics\n")
    solved = paths.solved("rwcas_design")
    solved.mkdir(parents=True)
    (solved / "Rwcas.v").write_text(solution_header("write_spec", True, ["write_spec"], []) + "Lemma x : True. Proof. exact I. Qed.\n")
    third = LADDER[2]
    assert library_for(third, paths) == [solved, paths.paper]
    assert library_for(third, paths, paper=False) == [solved]
    assert library_for(third, paths, carry=False) == [paths.paper]
    assert library_for(third, paths, brief="spec-only") == []
    # A rung published by *this* invocation wins over a stale earlier publication,
    # and a rung between two selected ones is not skipped.
    fresh = {"rwcas_design": tmp_path / "fresh_rwcas", "seqlock_design": tmp_path / "fresh_seqlock"}
    assert library_for(third, paths, fresh=fresh) == [fresh["rwcas_design"], fresh["seqlock_design"], paths.paper]
    assert library_for(LADDER[0], paths) == [paths.paper]


# ------------------------------------------------------------------ the boundary


def test_assert_library_is_clean_refuses_an_unheaded_v_and_any_corpus_or_reference_path(tmp_path: Path, bench_dir: Path) -> None:
    paths = _paths(tmp_path, bench_dir, ("rwcas_design",))
    good = tmp_path / "lib" / "solved" / "rwcas_design"
    good.mkdir(parents=True)
    (good / "Rwcas.v").write_text(solution_header("write_spec", False, [], ["write_spec"]) + "Lemma x : True. Admitted.\n")
    _assert_library_is_clean([good], paths.forbidden)
    bad = tmp_path / "lib" / "leak"
    bad.mkdir()
    (bad / "Answer.v").write_text("(* the reference proof *)\nLemma x : True. Proof. exact I. Qed.\n")
    with pytest.raises(UsageError, match="was not produced by a run"):
        _assert_library_is_clean([good, bad], paths.forbidden)
    with pytest.raises(UsageError, match="is inside"):
        _assert_library_is_clean([paths.corpus / "rwcas_design"], paths.forbidden)
    with pytest.raises(UsageError, match="is inside"):
        _assert_library_is_clean([paths.reference / "rwcas_design" / "deeper"], paths.forbidden)
    with pytest.raises(UsageError, match="is inside"):
        _assert_library_is_clean([DEFAULT_PATHS.corpus / "rwcas"])


def test_publish_copies_the_latest_solution_and_reads_the_verdict_negative_first(tmp_path: Path, bench_dir: Path) -> None:
    paths = _paths(tmp_path, bench_dir, ("rwcas_design",))
    rung = LADDER[0]
    record = paths.record("ladder_t_rwcas_design")
    assert publish(rung, record, paths) is None
    for run_id, header in (("r1", solution_header("write_spec", False, [], ["write_spec"])), ("r2", solution_header("write_spec", True, ["write_spec"], []))):
        solution = record / run_id / "solution"
        solution.mkdir(parents=True)
        (solution / "Rwcas.v").write_text(header + "(* body *)\n")
        (solution / "_CoqProject").write_text("-Q . bench\n")
    dest = publish(rung, record, paths)
    assert dest == paths.solved("rwcas_design")
    readme = (dest / "README.md").read_text()
    assert readme.startswith("# `rwcas_design`, as this system solved it (complete)")
    assert "write_spec" in readme and (dest / "_CoqProject").exists()
    # The library it produced passes the boundary check it will be subjected to.
    _assert_library_is_clean([dest], paths.forbidden)
    shutil.rmtree(record / "r2")
    dest = publish(rung, record, paths)
    assert "(incomplete)" in (dest / "README.md").read_text()


# ------------------------------------------------------------------ outages


def test_outage_is_decided_from_records_not_log_text(tmp_path: Path, bench_dir: Path) -> None:
    """Structured signals only: a log tail that quotes ``bwrap:`` is not an outage, and
    a run whose every attempt is a ``runner-error`` is one even when nothing in the log
    says so."""
    # Every recorded attempt failed underneath the worker: an outage.
    down = tmp_path / "down"
    Recorder(down, run_id="r1").write(_record("error", "claude is not on PATH or could not be started"))
    Recorder(down, run_id="r1").write(_record("error", "Failed to authenticate", lemma="x22_spec"))
    verdict = outage_of(exit_code=1, timed_out=False, spawn_error="", record_dir=down)
    assert verdict.startswith("every attempt failed with runner-error")
    # One ordinary proof failure among them: the rung ran.
    Recorder(down, run_id="r1").write(_record("stuck", "Error: Unable to unify a with b", lemma="cec21_spec"))
    assert outage_of(exit_code=1, timed_out=False, spawn_error="", record_dir=down) == ""
    # Exit status is a signal; a wall kill and a clean exit never are.
    assert outage_of(exit_code=0, timed_out=False, spawn_error="", record_dir=down) == ""
    assert outage_of(exit_code=-9, timed_out=True, spawn_error="", record_dir=tmp_path / "none") == ""
    # Exit 2 is a refusal only when nothing was recorded: a run that spent its design
    # rounds and exited 2 has records and is a result.
    assert outage_of(exit_code=2, timed_out=False, spawn_error="", record_dir=down) == ""
    assert "usage error" in outage_of(exit_code=2, timed_out=False, spawn_error="", record_dir=tmp_path / "none")
    assert "before any attempt" in outage_of(exit_code=1, timed_out=False, spawn_error="", record_dir=tmp_path / "none")
    assert "could not be started" in outage_of(exit_code=None, timed_out=False, spawn_error="python: no such file", record_dir=down)

    # A rung whose log shouts every outage marker but whose records are ordinary failures.
    paths = _paths(tmp_path, bench_dir, ("rwcas_design",))
    rung = LADDER[0]
    tag = tag_for("t", rung.name)
    Recorder(paths.record(tag), run_id="r1").write(_record("stuck", "Error: Unable to unify a with b"))
    noisy = _launcher(
        "import sys; print('bwrap: setting up uid map: Permission denied'); "
        "print('access token has been revoked; is not on PATH; could not run at all'); sys.exit(1)"
    )
    row = run_rung(rung, paths, stamp="t", launcher=noisy)
    assert row["outage"] == "" and row["exit"] == 1
    assert "bwrap:" in row["tail"], "the text was there and was ignored"


def test_a_run_that_spent_its_design_rounds_is_not_an_outage(tmp_path: Path) -> None:
    rec = Recorder(tmp_path / "rec")
    rec.write(AttemptRecord(run_id=rec.run_id, node="root", lemma="root", attempt=1, runner="claude", status="stuck",
                            solved=False, elapsed_s=900.0, evidence="decomposition rejected: child 'x' has no statement"),
              suffix="decompose")
    assert outage_of(exit_code=2, timed_out=False, spawn_error="", record_dir=tmp_path / "rec") == ""
    assert outage_of(exit_code=1, timed_out=False, spawn_error="", record_dir=tmp_path / "rec") == ""
    assert "refused to start" in outage_of(exit_code=2, timed_out=False, spawn_error="", record_dir=tmp_path / "nothing")


def test_run_rung_writes_a_live_log_and_the_summary_row(tmp_path: Path, bench_dir: Path) -> None:
    paths = _paths(tmp_path, bench_dir, ("rwcas_design",))
    rung = LADDER[0]
    row = run_rung(rung, paths, stamp="t", brief="spec-only", launcher=_launcher("import sys; print('argv:', sys.argv); sys.exit(0)"))
    assert set(row) == ROW_KEYS
    assert (row["rung"], row["root"], row["exit"], row["timed_out"], row["published"], row["brief"]) == ("rwcas_design", "write_spec", 0, False, None, "spec-only")
    assert row["outage"] == "" and row["elapsed_s"] >= 0
    log = Path(row["log"])
    assert log == paths.log(tag_for("t", "rwcas_design"))
    text = log.read_text()
    assert text.splitlines()[1] == "# brief: spec-only, library: none"
    assert "'--brief', 'spec-only'" in text and "--library" not in row["tail"]
    assert Path(row["record"]) == paths.record(tag_for("t", "rwcas_design"))


def test_run_rung_kills_the_process_group_at_the_wall(tmp_path: Path, bench_dir: Path) -> None:
    paths = _paths(tmp_path, bench_dir, ("rwcas_design",))
    rung = Rung("rwcas_design", 1800, 5400, wall_seconds=1.0, corpus_root=paths.corpus)
    row = run_rung(rung, paths, stamp="t", launcher=_launcher("import time; print('working', flush=True); time.sleep(30)"))
    assert row["timed_out"] and row["outage"] == "" and row["exit"] != 0
    assert "working" in row["tail"]


# ------------------------------------------------------------------ main


def test_main_stops_on_an_outage_and_keeps_the_rows_it_has(tmp_path: Path, bench_dir: Path, capsys) -> None:
    paths = _paths(tmp_path, bench_dir)
    code = main(
        ["--skip-preflight", "--stamp", "t", "--no-paper", "--brief", "spec-only"],
        paths=paths, launcher=_launcher("import sys; sys.exit(1)"),
    )
    out = capsys.readouterr().out
    assert code == 1
    assert "STOPPING: rwcas_design could not run" in out
    assert "--only rwcas_design seqlock_design seqlock_wf_design" in out
    rows = json.loads(paths.summary("t").read_text())
    assert [r["rung"] for r in rows] == ["rwcas_design"] and rows[0]["outage"]
    assert "[OUT ] rwcas_design" in out


def test_main_runs_every_rung_and_exits_zero_iff_all_did(tmp_path: Path, bench_dir: Path, capsys) -> None:
    paths = _paths(tmp_path, bench_dir)
    code = main(
        ["--skip-preflight", "--stamp", "t", "--brief", "spec-only", "--", "--prover-effort", "high"],
        paths=paths, launcher=_launcher("import sys; print(sys.argv); sys.exit(0)"),
    )
    out = capsys.readouterr().out
    assert code == 0
    rows = json.loads(paths.summary("t").read_text())
    assert [r["rung"] for r in rows] == [r.name for r in LADDER]
    assert all(r["exit"] == 0 and r["outage"] == "" and r["brief"] == "spec-only" and r["published"] is None for r in rows)
    for rung in LADDER:
        text = paths.log(tag_for("t", rung.name)).read_text()
        assert "# brief: spec-only, library: none" in text
        assert "'--library'" not in text and "'--prover-effort', 'high'" in text
    assert out.count("[ok  ]") == 3
    assert not paths.library.exists(), "spec-only publishes nothing"
