"""The bubblewrap sandbox: a pure argv builder, and real isolation where bwrap exists."""

from __future__ import annotations

import dataclasses
import os
from collections.abc import Sequence
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
    monkeypatch.setenv("OPAMROOT", str(tmp_path / "no-opam"))  # no pinned switch to append to PATH
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


def test_the_pinned_switch_reaches_the_worker_path_after_the_operators(tmp_path: Path, monkeypatch) -> None:
    """pcp finds the switch without `pcp env`, and so does a worker's own `coqc`."""
    (tmp_path / "opam" / "pcp" / "bin").mkdir(parents=True)
    monkeypatch.setenv("OPAMROOT", str(tmp_path / "opam"))
    monkeypatch.delenv("PCP_OPAM_SWITCH", raising=False)
    env = sandbox(tmp_path).environment({"PATH": "/x/bin", "OPAMROOT": str(tmp_path / "opam")})
    assert env["PATH"] == f"/x/bin:{tmp_path / 'opam' / 'pcp' / 'bin'}"
    assert env["OPAMROOT"] == str(tmp_path / "opam"), "pcp inside resolves the same switch"


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


# ---------------------------------------------------------------- an installed pcp, a user's project


def test_a_user_project_masks_only_its_run_state(tmp_path: Path) -> None:
    """A user's docs/ and tests/ are their own; only ``.pcp`` (graph, answer key) hides,
    with the docs index bound back."""
    project = tmp_path / "proj"
    sb = Sandbox.for_benchmark(project, masks=(), home=tmp_path / "home", install=())
    assert sb.masked == (project.resolve() / ".pcp",)
    assert sb.docs_paths == (project.resolve() / ".pcp" / "docs",)


def test_for_benchmark_binds_pcps_own_install_and_the_opam_root(tmp_path: Path, monkeypatch) -> None:
    import sys

    import pcp
    from pcp.orch.runners.sandbox import install_paths

    monkeypatch.setenv("OPAMROOT", str(tmp_path / "opamroot"))
    sb = Sandbox.for_benchmark(tmp_path / "proj", home=tmp_path / "home")
    ro = set(sb.ro_paths)
    assert tmp_path / "opamroot" in ro, "the toolchain follows OPAMROOT"
    for path in (Path(sys.prefix).resolve(), Path(sys.base_prefix).resolve(), Path(pcp.__file__).parent.resolve()):
        assert path in ro or path in Path.home().resolve().parents or path == Path.home().resolve()
    assert set(install_paths()) <= ro and "pcp" in sb.binaries


def test_install_paths_never_bind_home_or_an_ancestor(monkeypatch) -> None:
    import sys

    from pcp.orch.runners.sandbox import install_paths

    home = Path.home().resolve()
    monkeypatch.setattr(sys, "prefix", str(home))
    monkeypatch.setattr(sys, "base_prefix", "/")
    paths = install_paths()
    assert home not in paths and Path("/") not in paths


def test_sandbox_for_uses_the_invocation_directory_and_checkout_masks_only_in_a_checkout(tmp_path: Path, monkeypatch) -> None:
    import argparse

    from pcp.cli import runners as cli_runners
    from pcp.orch.runners import sandbox as sb_mod

    monkeypatch.setattr(sb_mod, "available", lambda: True)
    project = tmp_path / "proj"
    project.mkdir()
    monkeypatch.chdir(project)
    args = argparse.Namespace(reference=None)
    box = cli_runners.sandbox_for(args, "claude", corpus_dir=project, library=[])
    assert project.resolve() in box.ro_paths and box.masked == (project.resolve() / ".pcp",)
    monkeypatch.chdir(REPO)
    box = cli_runners.sandbox_for(args, "claude", corpus_dir=REPO, library=[])
    assert {REPO / sub for sub in (".pcp", ".git", "eval", "docs", "tests")} <= set(box.masked)


@needs_bwrap
def test_the_running_pcp_install_works_inside_a_sandbox_of_a_user_project(tmp_path: Path) -> None:
    """The probe for a ``uv tool`` install: pcp's interpreter and package live outside
    the project (here: this venv, and for an editable install the checkout's ``pcp/``),
    so only the install binds make ``pcp`` runnable inside.  Without them it is not."""
    import sys

    project = tmp_path / "proj"
    (project / ".pcp" / "reference").mkdir(parents=True)
    (project / ".pcp" / "reference" / "answer.v").write_text("the answer")
    (project / ".pcp" / "docs").mkdir()
    (project / ".pcp" / "docs" / "index.txt").write_text("index")
    work = tmp_path / "work"
    work.mkdir()
    pcp_bin = Path(sys.prefix) / "bin" / "pcp"
    if not pcp_bin.exists():
        pytest.skip("no pcp entry point in this interpreter's prefix")
    probe = (
        f"'{pcp_bin}' --version && '{sys.executable}' -c 'import pcp.util.assets as a; a.idump_path(); a.skill_text(\"prover.md\"); print(\"ASSETS-OK\")'; "
        f"cat '{project}/.pcp/reference/answer.v' 2>/dev/null; cat '{project}/.pcp/docs/index.txt'"
    )
    import dataclasses

    box = dataclasses.replace(
        Sandbox.for_benchmark(project, masks=(), network=False, home=Path.home(), root=tmp_path / "stage", binaries=()),
        refresh_credentials=False, credentials=(),
    )
    out = run(box.wrap(["/bin/sh", "-c", probe], workdir=work), env=box.environment(), timeout=120)
    assert out.returncode == 0, out.output
    assert out.stdout.startswith("pcp ") and "ASSETS-OK" in out.stdout
    assert "the answer" not in out.stdout and "index" in out.stdout
    bare = dataclasses.replace(box, ro_paths=(project.resolve(),))
    if any(Path(sys.prefix).resolve().is_relative_to(p) for p in (Path(s) for s in ("/usr", "/opt"))):
        return  # a system interpreter is bound anyway; nothing to contrast
    missing = run(bare.wrap(["/bin/sh", "-c", f"'{pcp_bin}' --version"], workdir=work), env=bare.environment(), timeout=60)
    assert missing.returncode != 0, "pcp ran with no install binds -- the probe proves nothing"


# ---------------------------------------------------------------- mount order: a mask is never undone


_TREE = ("r", "r/a", "r/a/b", "r/a/b/c", "r/d", "r/d/e")
_KINDS = (None, "ro", "mask", "unmask", "mask+unmask")


def _policy_tree(tmp_path: Path) -> Path:
    base = tmp_path / "t"
    for node in _TREE:
        (base / node).mkdir(parents=True, exist_ok=True)
        (base / node / "f.txt").write_text(node)
    return base.resolve()


def _combo_sandbox(base: Path, combo: dict[str, str | None], tmp_path: Path) -> Sandbox:
    def pick(kind: str) -> tuple[Path, ...]:
        return tuple(base / n for n, k in combo.items() if k and kind in k.split("+"))

    return Sandbox(
        ro_paths=pick("ro"), masked=pick("mask"), unmasked=pick("unmask"), network=False, home=tmp_path / "home",
        root=tmp_path / "stage", refresh_credentials=False, clearenv=False,
    )


def _expected_visible(combo: dict[str, str | None], node: str) -> bool:
    """Most specific wins: the deepest rule on the node's ancestry decides, and a
    mask beats a bind of the same path."""
    chain = [n for n in _TREE if node == n or node.startswith(n + "/")]
    for n in sorted(chain, key=len, reverse=True):
        if combo[n]:
            return "mask" not in combo[n].split("+")
    return False


def _simulated_visible(cmd: list[str], path: Path) -> bool:
    """What bwrap would show at ``path``: the last mount on an ancestor-or-self."""
    verdict = False
    i = 0
    while i < len(cmd) and cmd[i] != "--":
        op = cmd[i]
        if op in ("--ro-bind", "--bind"):
            src, dst, i = cmd[i + 1], Path(cmd[i + 2]), i + 3
            if path == dst or dst in path.parents:
                verdict = src != "/dev/null"
        elif op in ("--tmpfs", "--proc", "--dev", "--chdir"):
            if op == "--tmpfs" and (path == Path(cmd[i + 1]) or Path(cmd[i + 1]) in path.parents):
                verdict = False
            i += 2
        elif op == "--setenv":
            i += 3
        else:
            i += 1
    return verdict


def _combos(n: int, seed: int) -> list[dict[str, str | None]]:
    import random

    rng = random.Random(seed)
    return [{node: rng.choice(_KINDS) for node in _TREE} for _ in range(n)]


def test_mount_order_never_lets_an_ancestor_bind_undo_a_mask(tmp_path: Path, monkeypatch) -> None:
    """For any mix of read-only, masked and carved-back paths, a path under a mask is
    hidden unless a bind *deeper than the mask* covers it -- whatever order the
    policy lists them in (the root carved back over its own ``.pcp`` was the leak)."""
    monkeypatch.setenv("PCP_BWRAP", "/fake/bwrap")
    base = _policy_tree(tmp_path)
    work = tmp_path / "work"
    work.mkdir()
    for combo in _combos(1500, seed=7):
        cmd = _combo_sandbox(base, combo, tmp_path).wrap(["x"], workdir=work)
        for node in _TREE:
            got = _simulated_visible(cmd, base / node / "f.txt")
            assert got == _expected_visible(combo, node), (combo, node, cmd)


def test_a_file_mask_is_blanked_not_tmpfsd(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setenv("PCP_BWRAP", "/fake/bwrap")
    answer = tmp_path / "repo" / "answer.v"
    answer.parent.mkdir()
    answer.write_text("Qed.")
    cmd = sandbox(tmp_path, masked=(answer,)).wrap(["x"], workdir=tmp_path)
    at = cmd.index(str(answer.resolve()))
    assert cmd[at - 2 : at] == ["--ro-bind", "/dev/null"]


def _visible(box: Sandbox, paths: Sequence[Path], work: Path) -> set[Path]:
    script = "; ".join(f'[ -e "{p}" ] && echo "{p}"' for p in paths) + "; true"
    out = run(box.wrap(["/bin/sh", "-c", script], workdir=work), env=box.environment(), timeout=60)
    assert out.returncode == 0, out.output
    return {Path(line) for line in out.stdout.splitlines() if line}


@needs_bwrap
def test_mount_order_property_holds_under_real_bwrap(tmp_path: Path) -> None:
    base = _policy_tree(tmp_path)
    work = tmp_path / "work"
    work.mkdir()
    for combo in _combos(12, seed=11):
        box = _combo_sandbox(base, combo, tmp_path)
        files = [base / node / "f.txt" for node in _TREE]
        seen = _visible(box, files, work)
        assert seen == {base / n / "f.txt" for n in _TREE if _expected_visible(combo, n)}, combo


# ---------------------------------------------------------------- the project root `pcp prove --sandbox` binds


def _cli_box(corpus: Path, *, reference: Path | None = None, workroot: Path | None = None) -> Sandbox:
    import argparse

    from pcp.cli import runners as cli_runners

    box = cli_runners.sandbox_for(argparse.Namespace(reference=reference, workroot=workroot), "claude", corpus_dir=corpus, library=[])
    return dataclasses.replace(box, refresh_credentials=False)


def _checkout(path: Path) -> Path:
    for sub in ("pcp", "eval/corpus/bench/X", "eval/corpus/bench/Y", ".git", "docs", "tests", ".pcp/reference"):
        (path / sub).mkdir(parents=True, exist_ok=True)
    (path / "pcp" / "__init__.py").write_text("")
    (path / "pyproject.toml").write_text("")
    (path / "eval/corpus/bench/X/F.v").write_text("Lemma x.")
    (path / "eval/corpus/bench/Y/F.v").write_text("the design variant")
    (path / ".git" / "HEAD").write_text("ref")
    (path / ".pcp/reference/answer.v").write_text("Qed.")
    return path.resolve()


@pytest.fixture
def fake_user(tmp_path: Path, monkeypatch) -> Path:
    home = tmp_path / "home"
    (home / ".claude").mkdir(parents=True)
    (home / ".claude" / "transcript.jsonl").write_text("spoilers")
    monkeypatch.setenv("HOME", str(home))
    return home.resolve()


@needs_bwrap
def test_a_file_at_the_project_root_leaves_run_state_and_the_reference_hidden(tmp_path: Path, monkeypatch, fake_user) -> None:
    """``pcp prove Foo.v L --sandbox`` at the root carves the root back as the corpus;
    that bind must not undo the ``.pcp`` mask or the ``--reference`` inside it."""
    project = tmp_path / "U"
    (project / ".pcp" / "reference").mkdir(parents=True)
    (project / ".pcp" / "eval").mkdir()
    (project / ".pcp" / "docs").mkdir()
    (project / ".pcp" / "reference" / "answer.txt").write_text("Qed.")
    (project / ".pcp" / "eval" / "r.txt").write_text("an earlier run")
    (project / ".pcp" / "docs" / "index.txt").write_text("index")
    (project / "Foo.v").write_text("Lemma foo.")
    project = project.resolve()
    monkeypatch.chdir(project)
    box = _cli_box(project, reference=project / ".pcp" / "reference")
    work = tmp_path / "work"
    work.mkdir()
    answers = [project / ".pcp/reference/answer.txt", project / ".pcp/eval/r.txt"]
    seen = _visible(box, [*answers, project / "Foo.v", project / ".pcp/docs/index.txt"], work)
    assert not seen & set(answers)
    assert {project / "Foo.v", project / ".pcp/docs/index.txt"} <= seen


def test_home_and_its_ancestors_are_refused_as_the_sandbox_root(tmp_path: Path, monkeypatch, fake_user) -> None:
    from pcp.errors import UsageError
    from pcp.orch.runners import sandbox as sb_mod

    monkeypatch.setattr(sb_mod, "available", lambda: True)
    (fake_user / "F.v").write_text("Lemma f.")
    for cwd in (fake_user, fake_user.parent, Path("/")):
        monkeypatch.chdir(cwd)
        with pytest.raises(UsageError, match="home directory or above"):
            _cli_box(fake_user)
    # A project under $HOME is fine, and $HOME's own .pcp is never taken for a project's.
    (fake_user / ".pcp").mkdir()
    (fake_user / "proj").mkdir()
    monkeypatch.chdir(fake_user / "proj")
    box = _cli_box(fake_user / "proj")
    assert fake_user / "proj" in box.ro_paths and fake_user not in box.ro_paths


def test_a_corpus_outside_the_project_is_refused_unless_pcp_staged_it(tmp_path: Path, monkeypatch, fake_user) -> None:
    from pcp.errors import UsageError
    from pcp.orch.runners import sandbox as sb_mod

    monkeypatch.setattr(sb_mod, "available", lambda: True)
    (tmp_path / "proj").mkdir()
    (tmp_path / "other").mkdir()
    monkeypatch.chdir(tmp_path / "proj")
    with pytest.raises(UsageError, match="outside the project"):
        _cli_box((tmp_path / "other").resolve())
    staged = tmp_path / "wr" / "staged"
    staged.mkdir(parents=True)
    box = _cli_box(staged.resolve(), workroot=(tmp_path / "wr").resolve())
    assert staged.resolve() in box.unmasked


@needs_bwrap
def test_a_checkout_subdirectory_still_masks_the_sibling_rungs(tmp_path: Path, monkeypatch, fake_user) -> None:
    """``cd eval && pcp prove ... --sandbox``: the root is the enclosing checkout."""
    co = _checkout(tmp_path / "co")
    monkeypatch.chdir(co / "eval")
    corpus = co / "eval/corpus/bench/X"
    box = _cli_box(corpus)
    work = tmp_path / "work"
    work.mkdir()
    secrets = [co / "eval/corpus/bench/Y/F.v", co / ".git/HEAD", co / ".pcp/reference/answer.v"]
    seen = _visible(box, [*secrets, corpus / "F.v"], work)
    assert seen == {corpus / "F.v"}


@needs_bwrap
def test_the_parent_of_a_checkout_masks_the_nested_checkouts_answers(tmp_path: Path, monkeypatch, fake_user) -> None:
    """Run from a directory holding a checkout (``~/src``): the root is that
    directory, and the nested checkout's benchmarks and run state are found and
    masked -- as is a ``.pcp`` left by an earlier run from any subdirectory."""
    parent = tmp_path / "src"
    co = _checkout(parent / "co")
    (parent / "proj" / "sub" / ".pcp").mkdir(parents=True)
    (parent / "proj" / "sub" / ".pcp" / "graph.db").write_text("old proofs")
    (parent / "proj" / "F.v").write_text("Lemma f.")
    parent = parent.resolve()
    monkeypatch.chdir(parent)
    box = _cli_box(parent / "proj")
    work = tmp_path / "work"
    work.mkdir()
    secrets = [co / "eval/corpus/bench/Y/F.v", co / ".git/HEAD", co / ".pcp/reference/answer.v", parent / "proj/sub/.pcp/graph.db"]
    seen = _visible(box, [*secrets, parent / "proj/F.v"], work)
    assert seen == {parent / "proj/F.v"}


def test_the_sandbox_root_is_the_enclosing_checkout_then_the_nearest_pcp_project(tmp_path: Path, fake_user) -> None:
    from pcp.cli.runners import sandbox_root

    co = _checkout(tmp_path / "co")
    (co / "eval" / ".pcp").mkdir()
    assert sandbox_root(co / "eval/corpus/bench/X") == co, "a checkout beats a nearer .pcp"
    proj = tmp_path / "proj"
    (proj / ".pcp").mkdir(parents=True)
    (proj / "theories" / "x").mkdir(parents=True)
    assert sandbox_root((proj / "theories" / "x").resolve()) == proj.resolve()
    (tmp_path / "bare" / "d").mkdir(parents=True)
    assert sandbox_root((tmp_path / "bare" / "d").resolve()) == (tmp_path / "bare" / "d").resolve()
