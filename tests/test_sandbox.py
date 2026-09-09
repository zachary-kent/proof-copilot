"""The bubblewrap sandbox: a pure argv builder, and real isolation where bwrap exists."""

from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path

import pytest

from pcp.config.env import SANDBOX_PASSTHROUGH
from pcp.orch.protocol import NodePayload
from pcp.orch.runners.sandbox import (
    Sandbox,
    SandboxedRunner,
    available,
    hosts_file,
    stage_credentials,
    sync_credentials,
)
from pcp.util.proc import run
from tests.conftest import needs_bwrap


def fake_home(tmp_path: Path) -> Path:
    home = tmp_path / "home"
    (home / ".claude").mkdir(parents=True)
    (home / ".claude" / ".credentials.json").write_text('{"token": "t0"}')
    (home / ".claude" / "transcript.jsonl").write_text("spoilers")
    (home / ".claude.json").write_text("{}")
    return home


def sandbox(tmp_path: Path, **kw) -> Sandbox:
    repo = tmp_path / "repo"
    (repo / ".pcp" / "reference").mkdir(parents=True)
    (repo / "eval").mkdir()
    defaults = dict(
        ro_paths=(repo,),
        masked=(repo / ".pcp", repo / "eval", repo / "does-not-exist"),
        credentials=(".claude/.credentials.json", ".claude.json"),
        network=True,
        deny_hosts=("github.com",),
        home=fake_home(tmp_path),
        root=tmp_path / "stage",
        refresh_credentials=False,
        clearenv=True,
    )
    defaults.update(kw)
    return Sandbox(**defaults)


def test_wrap_is_pure_and_clears_the_environment_to_an_allowlist(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("PCP_BWRAP", "/fake/bwrap")
    sb = sandbox(tmp_path)
    work = tmp_path / "work" / "n" / "a1"
    work.mkdir(parents=True)
    argv = ["claude", "-p", "--verbose"]
    env = {"PATH": "/x/bin", "ROCQPATH": "/r", "ANTHROPIC_API_KEY": "secret-key", "SSH_AUTH_SOCK": "/s"}
    cmd = sb.wrap(argv, workdir=work, env=env)
    assert argv == ["claude", "-p", "--verbose"], "wrap never mutates its input"
    assert sb.wrap(argv, workdir=work, env=env) == cmd, "same inputs, same command"
    assert cmd[:5] == ["/fake/bwrap", "--die-with-parent", "--new-session", "--unshare-pid", "--ro-bind"]
    assert "--unshare-net" not in cmd
    assert "--clearenv" in cmd and cmd.index("--clearenv") < cmd.index("--setenv")
    pairs = {cmd[i + 1]: cmd[i + 2] for i, a in enumerate(cmd) if a == "--setenv"}
    assert pairs == {
        "HOME": str(sb.home.resolve()), "PCP_SANDBOX": "1", "PATH": "/x/bin", "ROCQPATH": "/r",
        # the runner defaults ride along with the allowlist (spec-only ladder finding)
        "CLAUDE_CODE_MAX_OUTPUT_TOKENS": "128000",
    }
    assert "secret-key" not in cmd and "SSH_AUTH_SOCK" not in cmd
    assert set(pairs) - {"HOME", "PCP_SANDBOX"} <= set(SANDBOX_PASSTHROUGH)
    assert sb.environment(env) == pairs, "the bwrap process itself is started with exactly the allowlist"
    assert "--clearenv" not in Sandbox(clearenv=False, home=sb.home, root=sb.root, refresh_credentials=False).wrap(argv, workdir=work, env=env)
    assert cmd[-4:] == ["--", "claude", "-p", "--verbose"]
    assert cmd[cmd.index("--bind") + 1 : cmd.index("--bind") + 3] == [str(work.resolve())] * 2
    assert cmd[cmd.index("--chdir") + 1] == str(work.resolve())


def test_wrap_masks_after_binding_and_skips_masks_that_do_not_exist(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("PCP_BWRAP", "/fake/bwrap")
    sb = sandbox(tmp_path)
    cmd = sb.wrap(["x"], workdir=tmp_path, env={})
    repo = (tmp_path / "repo").resolve()
    ro_at = cmd.index(str(repo))
    mask_at = cmd.index(str(repo / ".pcp"))
    assert cmd[ro_at - 1] == "--ro-bind" and cmd[mask_at - 1] == "--tmpfs"
    assert ro_at < mask_at
    assert str(repo / "does-not-exist") not in cmd, "a mount point cannot be made inside a read-only bind"
    assert str(repo / "eval") in cmd


def test_wrap_binds_the_hosts_file_and_the_node_file_dir_back(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("PCP_BWRAP", "/fake/bwrap")
    sb = sandbox(tmp_path)
    designed = tmp_path / "repo" / ".pcp" / "work" / "n.designed"
    designed.mkdir(parents=True)
    cmd = sb.wrap(["x"], workdir=tmp_path, env={}, node_file_dir=designed)
    hosts = cmd[cmd.index("/etc/hosts") - 1]
    assert hosts.startswith(str(tmp_path / "stage" / "hosts-"))
    text = Path(hosts).read_text()
    assert "127.0.0.1 github.com" in text and "::1 github.com" in text
    assert hosts_file(("github.com",), tmp_path / "stage") == Path(hosts), "content-addressed: same deny list, same file"
    assert cmd.index(str(designed.resolve())) > cmd.index(str((tmp_path / "repo" / ".pcp").resolve()))


def test_network_off_unshares_the_net_and_needs_no_hosts_file(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("PCP_BWRAP", "/fake/bwrap")
    cmd = sandbox(tmp_path, network=False).wrap(["x"], workdir=tmp_path, env={})
    assert "--unshare-net" in cmd and "/etc/hosts" not in cmd and "resolv.conf" not in " ".join(cmd)


def test_credentials_are_staged_as_a_directory_holding_only_the_allowlist(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("PCP_BWRAP", "/fake/bwrap")
    sb = sandbox(tmp_path)
    cmd = sb.wrap(["x"], workdir=tmp_path, env={})
    home = sb.home.resolve()
    stage = cmd[cmd.index(str(home / ".claude")) - 1]
    assert stage.startswith(str(tmp_path / "stage" / "creds-"))
    assert sorted(p.name for p in Path(stage).iterdir()) == [".credentials.json"], "transcripts are not staged"
    at = cmd.index(str(home / ".claude.json"))
    assert cmd[at - 1] == "--ro-bind" and cmd[at + 1] == cmd[at], "a file in $HOME itself is bound directly"
    assert cmd.index("--tmpfs") < cmd.index(stage), "the home tmpfs comes before anything bound back into it"


def test_a_rotated_credential_reaches_the_stage(tmp_path: Path) -> None:
    home = fake_home(tmp_path)
    pairs = stage_credentials([".claude/.credentials.json"], home, root=tmp_path / "stage", refresh=False)
    host_dir, stage = pairs[0]
    assert host_dir == home / ".claude" and (stage / ".credentials.json").read_text() == '{"token": "t0"}'
    new = home / ".claude" / ".credentials.new"
    new.write_text('{"token": "t1"}')
    os.replace(new, home / ".claude" / ".credentials.json")
    assert sync_credentials() >= 1
    assert (stage / ".credentials.json").read_text() == '{"token": "t1"}'
    assert oct(stage.stat().st_mode & 0o777) == "0o700"


def test_wrap_without_bwrap_raises_a_toolchain_error(tmp_path: Path, monkeypatch) -> None:
    from pcp.errors import ToolchainError

    monkeypatch.delenv("PCP_BWRAP", raising=False)
    monkeypatch.setenv("PATH", str(tmp_path))
    with pytest.raises(ToolchainError, match="bwrap"):
        sandbox(tmp_path).wrap(["x"], workdir=tmp_path, env={})


def test_for_benchmark_masks_the_answer_subtrees_and_binds_the_corpus_back(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    corpus = repo / "eval" / "corpus" / "bench" / "rung"
    corpus.mkdir(parents=True)
    sb = Sandbox.for_benchmark(repo, reference=tmp_path / "answers", corpus_dir=corpus, library=[tmp_path / "lib"], provider="claude", home=tmp_path / "home")
    masked = set(sb.masked)
    for sub in (".pcp", ".git", "eval", "docs", "tests"):
        assert (repo.resolve() / sub) in masked
    assert (tmp_path / "answers").resolve() in masked
    assert sb.unmasked == (corpus.resolve(), (tmp_path / "lib").resolve())
    assert sb.docs_paths == (repo.resolve() / ".pcp" / "docs",)
    assert sb.credentials[0] == ".claude/.credentials.json" and sb.binaries == ("claude", "python3", "pcp")
    assert sb.network and sb.deny_hosts
    codex = Sandbox.for_benchmark(repo, provider="codex", network=False)
    assert codex.binaries[0] == "codex" and codex.credentials == (".codex/auth.json", ".codex/config.toml")


@dataclass
class Fake:
    argv: list
    name: str = "fake"
    env: dict | None = None
    seen: list = None  # type: ignore[assignment]

    def available(self) -> bool:
        return True

    async def run_node(self, node):
        from pcp.orch.protocol import NodeResult

        (self.seen if self.seen is not None else []).append((list(self.argv), self.env))
        return NodeResult(status="qed", proof="exact I.", evidence=" ".join(self.argv))


async def test_sandboxed_runner_never_mutates_the_wrapped_runner(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("PCP_BWRAP", "/fake/bwrap")
    seen: list = []
    inner = Fake(argv=["claude", "-p"], seen=seen)
    runner = SandboxedRunner(inner, sandbox(tmp_path))
    assert runner.name == "sandboxed:fake"
    work = tmp_path / "work" / "n" / "a1"
    work.mkdir(parents=True)
    node = NodePayload(node_id="n", name="n", statement="", file=str(tmp_path / "repo" / "Dev.v"), workdir=work)
    result = await runner.run_node(node)
    assert result.status == "qed"
    assert inner.argv == ["claude", "-p"] and inner.env is None, "the wrapped runner is untouched"
    argv, env = seen[0]
    assert argv[0] == "/fake/bwrap" and argv[-2:] == ["claude", "-p"]
    assert str((tmp_path / "repo").resolve()) in argv
    assert env["PCP_SANDBOX"] == "1" and set(env) <= {"HOME", "PCP_SANDBOX", *SANDBOX_PASSTHROUGH}


async def test_sandboxed_runner_refuses_an_in_process_runner(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("PCP_BWRAP", "/fake/bwrap")

    class InProcess:
        name = "direct"

        def available(self) -> bool:
            return True

        async def run_node(self, node):
            raise AssertionError("must not run")

    runner = SandboxedRunner(InProcess(), sandbox(tmp_path))
    result = await runner.run_node(NodePayload(node_id="n", name="n", statement="", file="", workdir=tmp_path))
    assert result.status == "error" and "in-process" in result.evidence


# ---------------------------------------------------------------- real bubblewrap


def real_sandbox(tmp_path: Path) -> tuple[Sandbox, Path]:
    repo = tmp_path / "repo"
    repo.mkdir()
    (repo / "README").write_text("hello")
    work = tmp_path / "work"
    work.mkdir()
    sb = Sandbox(
        ro_paths=(repo,),
        masked=(),
        credentials=(),
        binaries=("sh", "env", "ls", "touch"),
        network=False,
        home=Path.home(),
        root=tmp_path / "stage",
        refresh_credentials=False,
    )
    return sb, work


@needs_bwrap
def test_a_sandboxed_process_sees_no_secrets_and_no_home_files(tmp_path: Path) -> None:
    assert available()
    sb, work = real_sandbox(tmp_path)
    host_env = {**os.environ, "ANTHROPIC_API_KEY": "secret-xyz", "PCP_PROBE": "leak"}
    # What SandboxedRunner does: the bwrap process itself gets only the allowlist.
    out = run(sb.wrap(["/usr/bin/env"], workdir=work, env=host_env), env=sb.environment(host_env), timeout=60)
    assert out.returncode == 0, out.output
    assert "secret-xyz" not in out.stdout and "PCP_PROBE" not in out.stdout
    assert "PCP_SANDBOX=1" in out.stdout and f"HOME={Path.home()}" in out.stdout
    listing = run(sb.wrap(["/bin/sh", "-c", 'ls -A "$HOME"'], workdir=work, env=host_env), env=sb.environment(host_env), timeout=60)
    assert listing.returncode == 0 and listing.stdout.strip() == "", listing.output


@needs_bwrap
def test_a_sandboxed_write_outside_the_workdir_fails(tmp_path: Path) -> None:
    sb, work = real_sandbox(tmp_path)
    repo = (tmp_path / "repo").resolve()
    probe = run(
        sb.wrap(["/bin/sh", "-c", f"touch '{repo}/leak' 2>/dev/null && echo REPO-WRITABLE; touch ./ok && echo WORK-WRITABLE; touch /usr/leak 2>/dev/null && echo USR-WRITABLE"], workdir=work),
        env=sb.environment(),
        timeout=60,
    )
    assert "WORK-WRITABLE" in probe.stdout, probe.output
    assert "REPO-WRITABLE" not in probe.stdout and "USR-WRITABLE" not in probe.stdout
    assert (work / "ok").exists() and not (repo / "leak").exists()


# ---------------------------------------------------------------- the composed path: CLIRunner under bwrap

REPO = Path(__file__).resolve().parents[1]


def _sandboxed_cli(tmp_path: Path, body: str) -> tuple:
    import sys

    from pcp.orch.runners.cli import CLIRunner

    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    script = bin_dir / "fake_claude.py"
    script.write_text("import json, os, subprocess, sys, time\n" + body, encoding="utf-8")
    sb = Sandbox(
        ro_paths=(REPO,),
        credentials=(),
        binaries=(sys.executable,),
        network=False,
        home=Path.home(),
        root=tmp_path / "stage",
        refresh_credentials=False,
        unmasked=(bin_dir,),
    )
    work = tmp_path / "work" / "n" / "a1"
    work.mkdir(parents=True)
    (work / "TASK.md").write_text("# Prove `foo`\n")
    (work / "node.v").write_text("Lemma foo : True.\nProof.\n  admit.\nAdmitted.\n")
    inner = CLIRunner(argv=[sys.executable, str(script)], binary=sys.executable, stream="claude", name="fake")
    node = NodePayload(node_id="foo", name="foo", statement="Lemma foo : True.", file=str(work / "node.v"), workdir=work, budget_seconds=1.0)
    return SandboxedRunner(inner, sb), node


@needs_bwrap
async def test_a_sandboxed_cli_runner_answers_and_sees_no_secret(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("ANTHROPIC_API_KEY", "secret-xyz")
    runner, node = _sandboxed_cli(tmp_path, """
sys.stdin.read()
leaked = sorted(k for k in os.environ if k.endswith("_API_KEY") or k == "SSH_AUTH_SOCK")
json.dump({"status": "qed" if not leaked else "contested", "proof": "exact I.", "evidence": "leaked: " + ",".join(leaked)}, open("answer.json", "w"))
print(json.dumps({"type": "result", "subtype": "success", "num_turns": 1}))
""")
    node.budget_seconds = 60.0
    result = await runner.run_node(node)
    assert result.status == "qed", result.evidence + "\n" + result.raw
    assert result.proof == "exact I." and result.exit_code == 0
    assert (node.workdir / "answer.json").exists(), "the one writable path is the attempt dir"


@needs_bwrap
async def test_a_deadline_kill_under_bwrap_takes_the_whole_namespace(tmp_path: Path) -> None:
    import random
    import time

    marker = f"100.{random.randint(10**6, 10**7)}"
    runner, node = _sandboxed_cli(tmp_path, f"""
subprocess.Popen(["sleep", "{marker}"])
src = open("node.v").read().replace("admit.", "iIntros.")
open("node.v", "w").write(src)
print(json.dumps({{"type": "system", "subtype": "init", "model": "m", "mcp_servers": []}}), flush=True)
time.sleep(100)
""")
    started = time.perf_counter()
    result = await runner.run_node(node)
    assert result.timed_out and result.status == "stuck"
    assert result.proof == "iIntros." and "recovered a 1-line partial proof" in result.evidence
    assert time.perf_counter() - started < 15
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline and run(["pgrep", "-f", f"sleep {marker}"]).returncode == 0:
        time.sleep(0.1)
    assert run(["pgrep", "-f", f"sleep {marker}"]).returncode != 0, "the worker's child outlived the kill"
