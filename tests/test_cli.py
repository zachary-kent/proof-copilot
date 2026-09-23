"""The CLI surface: prove/check/status/handoff/failures, driven as a user would."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

import pytest

from pcp.config.schema import Config, Tiers
from pcp.errors import UsageError
from tests._orch_fixtures import write_plain
from tests.conftest import needs_rocq

ROOT = Path(__file__).resolve().parents[1]
CANARY = ROOT / "eval" / "corpus" / "canary"


def run(*args: str, cwd: Path | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, "-m", "pcp.cli.main", *args],
        cwd=str(cwd or ROOT), capture_output=True, text=True, check=False,
    )


def prove_mock(tmp_path: Path, *extra: str, corpus: Path = CANARY, target: str = "canary_main") -> subprocess.CompletedProcess:
    return run(
        "prove", str(corpus / (corpus.name.capitalize() + ".v") if corpus == CANARY else corpus / "Plain.v"), target,
        "--plan", str(corpus / "plan.v"), "--runner", "mock",
        "--graph", str(tmp_path / "graph.db"), "--workroot", str(tmp_path / "work"), *extra,
        cwd=tmp_path,
    )


def attempt_dir(tmp_path: Path, node: str) -> Path:
    """Attempt ids are global, so a node's first attempt dir is not always ``a1``."""
    return sorted((tmp_path / "work" / node).glob("a*"), key=lambda p: int(p.name[1:]))[0]


def test_help_and_version():
    from pcp import __version__

    assert run("--version").stdout.strip() == f"pcp {__version__}"
    assert "prove" in run("--help").stdout
    assert run().returncode == 1


def test_prove_with_an_unanswering_mock_terminates_with_three_stuck(tmp_path):
    proc = prove_mock(tmp_path)
    assert proc.returncode == 1, proc.stderr
    assert "3 stuck" in proc.stdout and "not integrated" in proc.stdout
    assert "runner: mock" in proc.stderr
    assert (tmp_path / "graph.db").exists()
    # The JSON shape is the contract's.
    proc = prove_mock(tmp_path, "--json", "--attempts", "3")
    data = json.loads(proc.stdout)
    assert set(data) == {"integrated", "detail", "elapsed_s", "outcomes", "sentinels", "amendments"}
    assert data["integrated"] is False and {o["status"] for o in data["outcomes"]} == {"stuck"}


def test_status_and_handoff_on_a_canary_graph(tmp_path):
    prove_mock(tmp_path)
    graph = tmp_path / "graph.db"
    status = run("status", "--graph", str(graph), "--json", cwd=tmp_path)
    assert status.returncode == 0, status.stderr
    data = json.loads(status.stdout)
    assert data["summary"] == {"stuck": 3}
    assert {n["name"] for n in data["nodes"]} == {"canary_main", "canary_swap", "canary_assoc"}
    text = run("status", "--graph", str(graph), cwd=tmp_path).stdout
    assert text.splitlines()[0] == "3 stuck" and " ✗ canary_swap" in text
    out = tmp_path / "h.v"
    handoff = run("handoff", "canary_swap", "--graph", str(graph), "-o", str(out), cwd=tmp_path)
    assert handoff.returncode == 0 and handoff.stdout.strip() == f"wrote {out}"
    assert "Lemma canary_swap" in out.read_text() and out.read_text().rstrip().endswith("Admitted.")
    missing = run("status", "--graph", str(tmp_path / "nope.db"), cwd=tmp_path)
    assert missing.returncode == 2 and "no graph at" in missing.stderr
    assert not (tmp_path / "nope.db").exists(), "a wrong path never creates a graph"
    unknown = run("handoff", "nobody", "--graph", str(graph), cwd=tmp_path)
    assert unknown.returncode == 2 and "no node 'nobody'" in unknown.stderr


def test_fresh_after_a_bad_flag_leaves_the_graph_untouched(tmp_path):
    prove_mock(tmp_path)
    graph = tmp_path / "graph.db"
    before = graph.stat().st_mtime_ns
    proc = prove_mock(tmp_path, "--fresh", "--library", str(tmp_path / "typo"))
    assert proc.returncode == 2 and "--library" in proc.stderr and "no such path" in proc.stderr
    assert graph.exists() and graph.stat().st_mtime_ns == before and (tmp_path / "work").exists()
    ok = prove_mock(tmp_path, "--fresh")
    assert ok.returncode == 1 and "3 stuck" in ok.stdout
    assert not (tmp_path / "graph.db-wal").exists() or True


def test_state_tools_with_codex_are_refused_loudly(tmp_path):
    proc = prove_mock(tmp_path, "--runner", "codex", "--state-tools")
    assert proc.returncode == 2
    assert "ignores --state-tools" in proc.stderr and "Traceback" not in proc.stderr
    bad = prove_mock(tmp_path, "--state-tools", "proof_open,teleport")
    assert bad.returncode == 2 and "teleport" in bad.stderr
    unknown = prove_mock(tmp_path, "--runner", "warp")
    assert unknown.returncode == 2 and "unknown runner 'warp'" in unknown.stderr


def test_provider_model_validation_happens_after_runner_selection(tmp_path):
    from pcp.cli.runners import model_for, select_runner

    proc = prove_mock(tmp_path, "--prover-model", "codex/luna")
    assert proc.returncode == 2 and "names provider 'codex', but this run uses 'mock'" in proc.stderr
    cfg = Config(tiers=Tiers(prover=["codex/luna", "anthropic/claude-sonnet-5"]))
    assert model_for("prover", cfg, "codex", flag="codex/luna", flag_name="--prover-model") == ("luna", None)
    assert model_for("prover", cfg, "anthropic", flag=None, flag_name="--prover-model")[0] == "claude-sonnet-5"
    binding, note = model_for("prover", cfg, "codex", flag=None, flag_name="--prover-model")
    assert binding == "luna" and "built-in default" in note
    only_codex = Config(tiers=Tiers(prover=["codex/luna"]))
    assert model_for("prover", only_codex, "anthropic", flag=None, flag_name="--prover-model") == (
        None, "prover: config binds codex/luna, but this run uses anthropic; falling back to the provider default")
    with pytest.raises(UsageError, match="names provider 'anthropic', but this run uses 'codex'"):
        model_for("prover", cfg, "codex", flag="anthropic/x", flag_name="--prover-model")
    args = argparse.Namespace(runner="codex", prover_model="codex/luna", model=None, prover_effort=None, sandbox=False, state_tools=None, file=str(CANARY / "Canary.v"))
    runner, notes = select_runner(args, cfg)
    assert runner.name == "codex:luna" and notes == []
    with pytest.raises(UsageError, match="ignores --effort"):
        select_runner(argparse.Namespace(runner="codex", prover_model=None, model=None, prover_effort="xhigh", sandbox=False, state_tools=None, file="x"), cfg)
    with pytest.raises(UsageError, match="subprocess runner"):
        select_runner(argparse.Namespace(runner="mock", prover_model=None, model=None, prover_effort=None, sandbox=True, state_tools=None, reference=None, file=str(CANARY / "Canary.v")), cfg)


def test_auto_prefers_the_configured_tiers_provider(monkeypatch):
    from pcp.cli import runners as r

    monkeypatch.setattr(r, "build_runner", lambda spec: type("R", (), {"available": lambda self: spec.runner in ("codex", "claude"), "name": spec.runner})())
    assert r.pick_auto(Config(tiers=Tiers(prover=["anthropic/claude-sonnet-5"])), "prover") == "claude"
    assert r.pick_auto(Config(tiers=Tiers(prover=["codex/luna"])), "prover") == "codex"
    assert r.pick_auto(Config(tiers=Tiers(prover=["local/x"])), "prover") == "codex", "first available otherwise"
    monkeypatch.setattr(r, "build_runner", lambda spec: type("R", (), {"available": lambda self: False, "name": spec.runner})())
    with pytest.raises(UsageError, match="no runner is available"):
        r.pick_auto(Config(), "prover")


def test_failures_on_a_recorded_run(tmp_path):
    proc = prove_mock(tmp_path, "--record", str(tmp_path / "rec"), "--corpus", "canary")
    assert proc.returncode == 1 and "records:" in proc.stdout
    run_dir = next((tmp_path / "rec").iterdir())
    assert (run_dir / "solution" / "Canary.v").exists()
    assert "INCOMPLETE" in (run_dir / "solution" / "Canary.v").read_text()[:400]
    report = run("failures", str(run_dir), cwd=tmp_path)
    assert report.returncode == 0 and "0/6 solved" in report.stdout and "protocol-violation" in report.stdout
    as_json = json.loads(run("failures", str(run_dir), "--json", cwd=tmp_path).stdout)
    assert as_json["total"] == 6 and as_json["solved"] == 0
    klass = run("failures", str(run_dir), "--class", "protocol-violation", cwd=tmp_path)
    assert klass.returncode == 0 and "6 record(s) in class protocol-violation" in klass.stdout
    assert run("failures", str(run_dir), "--class", "nope", cwd=tmp_path).returncode == 2
    assert run("failures", str(tmp_path / "empty"), cwd=tmp_path).returncode == 2


def test_check_outside_a_node_directory_is_refused(tmp_path):
    proc = run("check", cwd=tmp_path)
    assert proc.returncode == 2 and "pcp-node.json" in proc.stderr


def test_orchestration_required_without_a_plan_is_a_usage_error(tmp_path):
    dev, _ = write_plain(tmp_path, plan=None)
    proc = run("prove", str(dev), "root", "--runner", "mock", "--graph", str(tmp_path / "g.db"),
               "--workroot", str(tmp_path / "w"), "--no-orchestration", cwd=tmp_path)
    assert proc.returncode == 1 and "1 stuck" in proc.stdout, proc.stderr
    missing = run("prove", str(tmp_path / "nope.v"), "root", "--runner", "mock", cwd=tmp_path)
    assert missing.returncode == 2 and "no such file" in missing.stderr


@needs_rocq
def test_pcp_check_is_what_the_worker_runs(tmp_path):
    proc = prove_mock(tmp_path)
    assert proc.returncode == 1, proc.stderr
    workdir = attempt_dir(tmp_path, "canary_swap")
    assert (workdir / "pcp-node.json").exists()
    task = (workdir / "TASK.md").read_text(encoding="utf-8")
    assert "`canary_swap` (" not in task

    good = tmp_path / "good.v"
    good.write_text('iIntros "[HA HB]". iFrame.', encoding="utf-8")
    ok = run("check", "--body", str(good), cwd=workdir)
    assert ok.returncode == 0, ok.stdout + ok.stderr
    assert "gate: PASS" in ok.stdout
    also = run("check", str(good), cwd=workdir)
    assert also.returncode == 0
    as_json = json.loads(run("check", str(good), "--json", cwd=workdir).stdout)
    assert as_json["ok"] is True and "canary_swap" in as_json["assumptions"]

    bad = tmp_path / "bad.v"
    bad.write_text('iIntros "[HA HB]". done.', encoding="utf-8")
    fail = run("check", "--body", str(bad), cwd=workdir)
    assert fail.returncode == 1
    assert "gate: FAIL" in fail.stdout and "what to do:" in fail.stdout and "compiles (coqc)" in fail.stdout

    admit = tmp_path / "admit.v"
    admit.write_text("admit.", encoding="utf-8")
    static = run("check", "--body", str(admit), "--diagnose", cwd=workdir)
    assert static.returncode == 1 and "Your body contains an admit" in static.stdout
    assert "diagnosis" not in static.stdout.lower() or "no diagnosis" not in static.stdout

    # With no body argument the scratch file's own body is checked (still `admit.`).
    scratch = run("check", "--dir", str(workdir), cwd=tmp_path)
    assert scratch.returncode == 1 and "gate: FAIL" in scratch.stdout
    elsewhere = run("check", "--dir", str(workdir), "--body", str(good), "--full", "--unused-premises", cwd=tmp_path)
    assert elsewhere.returncode == 0 and "unused-premise report" in elsewhere.stdout


@needs_rocq
def test_pcp_check_on_the_root_node_and_the_design_mode(tmp_path):
    prove_mock(tmp_path)
    workdir = attempt_dir(tmp_path, "canary_main")
    main = tmp_path / "main.v"
    main.write_text('iIntros "[HP [HQ HR]]". iFrame.', encoding="utf-8")
    ok = run("check", "--body", str(main), cwd=workdir)
    assert ok.returncode == 0, ok.stdout
    design = run("check", "--design", cwd=workdir)
    assert "contract:" in design.stdout and design.returncode in (0, 1)


# ---------------------------------------------------------------- init / env / setup / doctor


def test_init_writes_the_example_config_and_ignores_run_state_but_not_the_config(tmp_path):
    from pcp.config.load import EXAMPLE_CONFIG, load

    (tmp_path / ".git").mkdir()
    (tmp_path / ".gitignore").write_text("*.vo")
    done = run("init", cwd=tmp_path)
    assert done.returncode == 0, done.stderr
    config = tmp_path / ".pcp" / "config.toml"
    assert config.read_text() == EXAMPLE_CONFIG and load(config).source == str(config)
    inner = (tmp_path / ".pcp" / ".gitignore").read_text().splitlines()
    assert "*" in inner and "!config.toml" in inner and "!.gitignore" in inner
    assert (tmp_path / ".gitignore").read_text() == "*.vo", "the project's .gitignore is not touched"
    assert "note:" not in done.stdout
    config.write_text("# mine\n")
    again = run("init", cwd=tmp_path)
    assert again.returncode == 2 and "--force" in again.stderr and config.read_text() == "# mine\n"
    forced = run("init", "--force", cwd=tmp_path)
    assert forced.returncode == 0 and config.read_text() == EXAMPLE_CONFIG
    assert (tmp_path / ".pcp" / ".gitignore").read_text().splitlines() == inner, "idempotent"


def test_init_force_preserves_an_existing_configs_mode(tmp_path):
    import os

    (tmp_path / ".git").mkdir()
    config = tmp_path / ".pcp" / "config.toml"
    config.parent.mkdir()
    config.write_text("# mine\n")
    config.chmod(0o640)
    forced = run("init", "--force", cwd=tmp_path)
    assert forced.returncode == 0
    assert os.stat(config).st_mode & 0o777 == 0o640


def test_init_notes_a_project_gitignore_that_hides_the_config(tmp_path):
    (tmp_path / ".git").mkdir()
    (tmp_path / ".gitignore").write_text(".pcp/\n")
    done = run("init", cwd=tmp_path)
    assert done.returncode == 0 and "will not be tracked" in done.stdout


def test_init_outside_git_writes_only_under_pcp(tmp_path):
    project = tmp_path / "p"
    project.mkdir()
    done = run("init", str(project), cwd=tmp_path)
    assert done.returncode == 0 and (project / ".pcp" / "config.toml").exists()
    assert not (project / ".gitignore").exists()


def test_env_prints_evalable_exports_for_the_switch(tmp_path):
    import os

    prefix = tmp_path / "opam" / "pcp"
    (prefix / "bin").mkdir(parents=True)
    (prefix / "lib" / "coq" / "user-contrib").mkdir(parents=True)
    env = {**os.environ, "OPAMROOT": str(tmp_path / "opam"), "PATH": "/usr/bin:/bin"}
    env.pop("PCP_OPAM_SWITCH", None)
    done = subprocess.run([sys.executable, "-m", "pcp.cli.main", "env"], cwd=str(tmp_path), env=env,
                          capture_output=True, text=True, check=False)
    assert done.returncode == 0, done.stderr
    # What `eval "$(pcp env)"` does, in a clean sh: the switch's bin is first on PATH.
    shell = subprocess.run(["/bin/sh", "-c", done.stdout + '\nprintf "%s\\n%s\\n%s" "$PATH" "$ROCQPATH" "$PCP_OPAM_SWITCH"'],
                           env={"PATH": "/usr/bin:/bin", "HOME": str(tmp_path)}, capture_output=True, text=True, check=False)
    path, rocqpath, switch = shell.stdout.splitlines()
    assert path.split(":")[0] == str(prefix / "bin")
    assert rocqpath == str(prefix / "lib" / "coq" / "user-contrib") and switch == "pcp"
    missing = subprocess.run([sys.executable, "-m", "pcp.cli.main", "env", "--switch", "nope"], cwd=str(tmp_path), env=env,
                             capture_output=True, text=True, check=False)
    assert missing.returncode == 1 and missing.stdout == "" and "pcp setup" in missing.stderr


def test_setup_dry_run_names_the_script_the_pins_and_the_switch(tmp_path):
    import os

    env = {**os.environ, "OPAMROOT": str(tmp_path / "opam")}
    done = subprocess.run([sys.executable, "-m", "pcp.cli.main", "setup", "--dry-run", "--switch", "scratch", "--jobs", "2"],
                          cwd=str(tmp_path), env=env, capture_output=True, text=True, check=False)
    assert done.returncode == 0, done.stderr
    assert "setup-toolchain.sh" in done.stdout and "toolchain.env" in done.stdout
    assert "would run: opam switch create scratch" in done.stdout and "-j 2" in done.stdout
    assert not (tmp_path / "opam").exists()


def test_doctor_reports_pins_and_packaged_assets_and_points_at_pcp_setup(tmp_path):
    import os

    env = {**os.environ, "OPAMROOT": str(tmp_path / "opam"), "PATH": "/usr/bin:/bin"}
    env.pop("PCP_COQC", None)
    done = subprocess.run([sys.executable, "-m", "pcp.cli.main", "doctor"], cwd=str(tmp_path), env=env,
                          capture_output=True, text=True, check=False)
    assert "packaged assets" in done.stdout and "skills/prover.md         ok" in done.stdout
    assert "coq/IDump.v              ok" in done.stdout and "pinned" in done.stdout
    if done.returncode != 0:
        assert "pcp setup" in done.stderr and "setup-toolchain.sh" not in done.stderr and "env.sh" not in done.stderr
