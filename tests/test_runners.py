"""CLI runners against fake CLIs: exit codes, deadlines, answers, argv contracts.

No test here calls a real ``claude`` or ``codex``; every "binary" is a script written
into the test's own directory.
"""

from __future__ import annotations

import asyncio
import json
import os
import sys
import textwrap
import time
from pathlib import Path

import pytest

from pcp.config import env as penv
from pcp.errors import UsageError
from pcp.orch.protocol import (
    ANSWER_FILE,
    MAX_WORKER_FILE_BYTES,
    NodePayload,
    read_answer_file,
    read_edited_body,
    read_result,
)
from pcp.orch.runners import cli as rcli
from pcp.orch.runners.base import (
    RUNNER_NAMES,
    RunnerSpec,
    build_runner,
    doctor_lines,
    login_hint,
    provider_for,
)
from pcp.orch.runners.claude_code import ClaudeCodeSubagentRunner
from pcp.orch.runners.cli import CLIRunner, claude_headless_runner, codex_cli_runner, decomposer_runner
from pcp.orch.runners.sandbox import Sandbox
from pcp.orch.runners.stream import parse_output
from pcp.util.proc import Streamed
from tests._orch_fixtures import bounded

PY = sys.executable
SCRATCH = "Lemma foo : True.\nProof.\n  admit.\nAdmitted.\n"

INIT = json.dumps({"type": "system", "subtype": "init", "model": "claude-test", "mcp_servers": []})
ASSISTANT = json.dumps({
    "type": "assistant",
    "message": {
        "id": "m1",
        "usage": {"input_tokens": 3, "output_tokens": 4, "cache_read_input_tokens": 10, "cache_creation_input_tokens": 1},
        "content": [{"type": "text", "text": "working"}],
    },
})
RESULT = json.dumps({
    "type": "result", "subtype": "success", "is_error": False, "num_turns": 2, "duration_ms": 1234,
    "total_cost_usd": 0.01,
    "usage": {"input_tokens": 3, "output_tokens": 4, "cache_read_input_tokens": 10, "cache_creation_input_tokens": 1},
    "result": "all done",
})


def attempt(tmp_path: Path, n: int = 1, *, budget: float = 30.0) -> NodePayload:
    """A fresh attempt directory with the packet files a runner reads."""
    workdir = tmp_path / "work" / "foo" / f"a{n}"
    workdir.mkdir(parents=True)
    (workdir / "TASK.md").write_text("# Prove `foo`\n", encoding="utf-8")
    (workdir / "node.v").write_text(SCRATCH, encoding="utf-8")
    return NodePayload(node_id="foo", name="foo", statement="Lemma foo : True.", file=str(tmp_path / "Dev.v"), workdir=workdir, budget_seconds=budget, attempt=n)


def script(tmp_path: Path, name: str, body: str) -> CLIRunner:
    path = tmp_path / name
    path.write_text("import json, os, subprocess, sys, time\n" + textwrap.dedent(body), encoding="utf-8")
    return CLIRunner(argv=[PY, str(path)], name="fake", binary=PY, stream="claude")


def _dead(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return True
    try:
        state = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[0]
    except OSError:
        return True
    return state == "Z"


# ---------------------------------------------------------------- outcomes


async def test_nonzero_exit_with_no_answer_is_an_error_not_a_worker_stuck(tmp_path: Path) -> None:
    runner = script(tmp_path, "fail.py", """
        print("Failed to authenticate: 401 OAuth access token has been revoked", flush=True)
        sys.exit(1)
    """)
    result = await runner.run_node(attempt(tmp_path))
    assert result.status == "error"
    assert result.exit_code == 1 and not result.timed_out
    assert "exited with status 1" in result.evidence and "401" in result.evidence
    assert "401 OAuth" in result.raw
    assert result.cost["seconds"] > 0 and result.cost["requests"] == 1
    assert result.trace["stderr_lines"] == ["Failed to authenticate: 401 OAuth access token has been revoked"]


async def test_exit_zero_with_answer_json_is_qed_with_the_stream_accounted(tmp_path: Path) -> None:
    runner = script(tmp_path, "ok.py", f"""
        prompt = sys.stdin.read()
        assert "Prove" in prompt, prompt
        print({INIT!r}, flush=True)
        print({ASSISTANT!r}, flush=True)
        json.dump({{"status": "qed", "proof": "Proof.\\n  exact I.\\nQed."}}, open("answer.json", "w"))
        print({RESULT!r}, flush=True)
    """)
    started = time.perf_counter()
    result = await runner.run_node(attempt(tmp_path))
    elapsed = time.perf_counter() - started
    assert result.status == "qed" and result.proof == "exact I."
    assert result.exit_code == 0 and not result.timed_out
    assert result.model == "claude-test"
    assert result.trace["turns"] == 2 and result.trace["total_tokens"] == 18
    assert result.cost["tokens"] == 18 and result.cost["dollars"] == 0.01
    assert 0 < result.cost["seconds"] <= elapsed + 0.1, "seconds is the wall clock, not duration_ms"
    assert result.cost["seconds"] != 1.234
    assert INIT in result.raw, "raw is the full stream, not a clipped tail"


async def test_the_configured_model_is_attribution_when_the_stream_is_silent(tmp_path: Path) -> None:
    runner = script(tmp_path, "quiet.py", """
        json.dump({"status": "stuck", "evidence": "no idea"}, open("answer.json", "w"))
    """)
    runner.model = "luna"
    result = await runner.run_node(attempt(tmp_path))
    assert result.status == "stuck" and result.evidence == "no idea"
    assert result.model == "luna"


async def test_deadline_kills_the_whole_tree_and_recovers_the_partial_body(tmp_path: Path) -> None:
    runner = script(tmp_path, "hang.py", f"""
        child = subprocess.Popen(["sleep", "100"])
        open("child.pid", "w").write(str(child.pid))
        print({INIT!r}, flush=True)
        print({ASSISTANT!r}, flush=True)
        src = open("node.v").read().replace("admit.", "iIntros.\\n  iSplit.")
        open("node.v", "w").write(src)
        time.sleep(100)
    """)
    node = attempt(tmp_path, budget=1.0)
    result = await runner.run_node(node)
    assert result.timed_out and result.status == "stuck"
    assert result.evidence.startswith("worker exceeded its 1s deadline and was killed; recovered a 2-line partial proof; captured ")
    assert "(1 turn(s), 0 tool call(s))" in result.evidence
    assert result.proof == "iIntros.\n  iSplit."
    assert result.trace["total_tokens"] == 18, "usage streamed before the kill is kept"
    assert result.cost["seconds"] >= 1.0
    assert INIT in result.raw
    pid = int((node.workdir / "child.pid").read_text())
    deadline = time.monotonic() + 5
    while not _dead(pid) and time.monotonic() < deadline:
        time.sleep(0.05)
    assert _dead(pid), "the worker's child survived the deadline kill"


async def test_a_complete_answer_written_before_the_kill_is_honoured(tmp_path: Path) -> None:
    runner = script(tmp_path, "late.py", """
        json.dump({"status": "qed", "proof": "exact I."}, open("answer.json", "w"))
        time.sleep(100)
    """)
    result = await runner.run_node(attempt(tmp_path, budget=1.0))
    assert result.timed_out
    assert result.status == "qed" and result.proof == "exact I."
    assert "killed at its 1s deadline after writing its answer" in result.evidence


async def test_a_silent_worker_killed_at_the_deadline_says_so(tmp_path: Path) -> None:
    runner = script(tmp_path, "mute.py", "time.sleep(100)\n")
    result = await runner.run_node(attempt(tmp_path, budget=1.0))
    assert result.status == "stuck" and result.timed_out
    assert result.evidence == "worker exceeded its 1s deadline and was killed; the worker produced no output at all before the kill"
    assert result.proof == ""


async def test_stale_files_in_another_attempt_dir_are_never_read(tmp_path: Path) -> None:
    earlier = attempt(tmp_path, 1)
    (earlier.workdir / ANSWER_FILE).write_text(json.dumps({"status": "qed", "proof": "exact I."}))
    (earlier.workdir / "proof.v").write_text("exact I.\n")
    runner = script(tmp_path, "silent.py", "sys.stdin.read()\n")
    result = await runner.run_node(attempt(tmp_path, 2))
    assert result.status == "stuck" and result.proof == ""
    assert "produced no answer.json" in result.evidence


async def test_error_max_turns_without_an_answer_is_an_error(tmp_path: Path) -> None:
    verdict = json.dumps({"type": "result", "subtype": "error_max_turns", "is_error": True, "num_turns": 9, "duration_ms": 5})
    runner = script(tmp_path, "maxturns.py", f"print({verdict!r})\n")
    result = await runner.run_node(attempt(tmp_path))
    assert result.status == "error"
    assert "error_max_turns" in result.evidence and result.exit_code == 0


async def test_error_max_turns_after_a_complete_answer_keeps_the_answer(tmp_path: Path) -> None:
    verdict = json.dumps({"type": "result", "subtype": "error_max_turns", "is_error": True, "num_turns": 9})
    runner = script(tmp_path, "maxturns2.py", f"""
        json.dump({{"status": "qed", "proof": "exact I."}}, open("answer.json", "w"))
        print({verdict!r})
    """)
    result = await runner.run_node(attempt(tmp_path))
    assert result.status == "qed" and result.proof == "exact I."
    assert "error_max_turns" in result.evidence


async def test_nonzero_exit_after_an_answer_keeps_the_answer_and_notes_the_exit(tmp_path: Path) -> None:
    runner = script(tmp_path, "answer_then_fail.py", """
        json.dump({"status": "contested", "evidence": "the statement is false for n = 0"}, open("answer.json", "w"))
        sys.exit(3)
    """)
    result = await runner.run_node(attempt(tmp_path))
    assert result.status == "contested"
    assert result.evidence == "the statement is false for n = 0; the runner exited with status 3"
    assert result.exit_code == 3


async def test_a_fenced_proof_in_the_final_text_counts_as_an_answer(tmp_path: Path) -> None:
    final = json.dumps({"type": "result", "subtype": "success", "num_turns": 1, "result": "Here you go:\n```coq\nexact I.\n```"})
    runner = script(tmp_path, "fence.py", f"print({final!r})\n")
    result = await runner.run_node(attempt(tmp_path))
    assert result.status == "qed" and result.proof == "exact I."


async def test_codex_jsonl_answers_through_the_agent_message(tmp_path: Path) -> None:
    lines = [
        json.dumps({"type": "turn.started"}),
        json.dumps({"type": "item.completed", "item": {"type": "agent_message", "text": "```coq\nexact I.\n```"}}),
        json.dumps({"type": "turn.completed", "usage": {"input_tokens": 50, "cached_input_tokens": 20, "output_tokens": 5}}),
    ]
    runner = script(tmp_path, "codex.py", "sys.stdin.read()\n" + "".join(f"print({line!r})\n" for line in lines))
    runner.stream = "codex"
    result = await runner.run_node(attempt(tmp_path))
    assert result.status == "qed" and result.proof == "exact I."
    assert result.cost["tokens"] == 75 and result.trace["turns"] == 1


async def test_claude_code_json_output_is_read_and_accounted(tmp_path: Path) -> None:
    final = json.dumps({"type": "result", "subtype": "success", "num_turns": 2, "duration_ms": 10, "total_cost_usd": 0.5, "usage": {"input_tokens": 1, "output_tokens": 2}, "result": "```coq\nexact I.\n```"})
    path = tmp_path / "cc.py"
    path.write_text(f"import sys\nsys.stdin.read()\nprint({final!r})\n")
    runner = ClaudeCodeSubagentRunner(argv=[PY, str(path)])
    result = await runner.run_node(attempt(tmp_path))
    assert result.status == "qed" and result.proof == "exact I."
    assert result.cost["dollars"] == 0.5 and result.cost["turns"] == 2 and result.cost["seconds"] > 0


async def test_a_missing_binary_is_an_error_with_the_login_hint(tmp_path: Path) -> None:
    runner = CLIRunner(argv=["/nonexistent/pcp-fake-cli", "-p"], binary="/nonexistent/pcp-fake-cli", stream="claude", login="`fake login`")
    result = await runner.run_node(attempt(tmp_path))
    assert result.status == "error"
    assert "is not on PATH" in result.evidence and "`fake login`" in result.evidence
    assert not runner.available()


async def test_a_packet_without_a_prompt_is_an_error(tmp_path: Path) -> None:
    node = attempt(tmp_path)
    (node.workdir / "TASK.md").unlink()
    runner = script(tmp_path, "never.py", "raise SystemExit(7)\n")
    result = await runner.run_node(node)
    assert result.status == "error" and "TASK.md" in result.evidence


async def test_authenticated_is_bounded_and_none_when_unknown(tmp_path: Path) -> None:
    ok = tmp_path / "auth_ok.py"
    ok.write_text("raise SystemExit(0)\n")
    assert await CLIRunner(argv=[PY], auth_check=(PY, str(ok))).authenticated() is True
    bad = tmp_path / "auth_bad.py"
    bad.write_text("raise SystemExit(1)\n")
    assert await CLIRunner(argv=[PY], auth_check=(PY, str(bad))).authenticated() is False
    assert await CLIRunner(argv=[PY], auth_check=("/nonexistent/binary",)).authenticated() is None
    assert await CLIRunner(argv=[PY]).authenticated() is None


# ---------------------------------------------------------------- argv contracts (contract 3.3)


def test_claude_headless_argv_matches_the_contract() -> None:
    assert claude_headless_runner().argv == [
        "claude", "-p", "--output-format", "stream-json", "--verbose", "--permission-mode", "acceptEdits",
        "--strict-mcp-config", "--allowed-tools", "Read", "Write", "Edit", "Bash", "Glob", "Grep",
    ]
    runner = claude_headless_runner("claude-sonnet-5", mcp_tools=["proof_open", "proof_step"], permission_mode="bypassPermissions", effort="high")
    assert runner.argv == [
        "claude", "-p", "--output-format", "stream-json", "--verbose", "--permission-mode", "bypassPermissions",
        "--strict-mcp-config", "--mcp-config", ".mcp.json", "--allowed-tools", "Read", "Write", "Edit", "Bash", "Glob", "Grep",
        "mcp__pcp__proof_open", "mcp__pcp__proof_step", "--model", "claude-sonnet-5", "--effort", "high",
    ]
    assert runner.name == "claude:claude-sonnet-5/high" and runner.stream == "claude" and runner.binary == "claude"


def test_the_control_arm_never_inherits_the_operator_s_mcp_servers() -> None:
    argv = claude_headless_runner().argv
    assert "--strict-mcp-config" in argv and "--mcp-config" not in argv


def test_codex_argv_matches_the_contract() -> None:
    assert codex_cli_runner().argv == ["codex", "exec", "--json", "--sandbox", "workspace-write", "--skip-git-repo-check", "-"]
    runner = codex_cli_runner("luna")
    assert runner.argv == ["codex", "exec", "--json", "--sandbox", "workspace-write", "--skip-git-repo-check", "--model", "luna", "-"]
    assert runner.name == "codex:luna" and runner.stream == "codex" and runner.auth_check == ("codex", "login", "status")


def test_the_decomposer_has_no_way_to_write_or_execute() -> None:
    argv = decomposer_runner("claude-opus-5", effort="xhigh").argv
    assert argv == [
        "claude", "-p", "--output-format", "stream-json", "--verbose", "--permission-mode", "acceptEdits",
        "--strict-mcp-config", "--allowed-tools", "Read", "Glob", "Grep", "--model", "claude-opus-5", "--effort", "xhigh",
    ]
    for forbidden in ("Write", "Edit", "Bash", "--mcp-config"):
        assert forbidden not in argv


def test_the_decomposer_can_be_sandboxed_from_a_sandbox_or_a_factory(tmp_path: Path) -> None:
    sandbox = Sandbox(home=tmp_path, root=tmp_path, refresh_credentials=False)
    assert decomposer_runner(sandbox_factory=sandbox).name == "sandboxed:claude:default"
    assert decomposer_runner(sandbox_factory=lambda: sandbox).name == "sandboxed:claude:default"


def test_claude_code_argv_uses_json_output_and_strict_mcp() -> None:
    runner = ClaudeCodeSubagentRunner(model="claude-sonnet-5", mcp_tools=("proof_open",), effort="low")
    assert runner.argv == [
        "claude", "-p", "--output-format", "json", "--permission-mode", "acceptEdits", "--strict-mcp-config",
        "--mcp-config", ".mcp.json", "--allowed-tools", "Read", "Write", "Edit", "Bash", "Glob", "Grep", "mcp__pcp__proof_open",
        "--model", "claude-sonnet-5", "--effort", "low",
    ]
    assert runner.name == "claude-code" and runner.stream == "json"


# ---------------------------------------------------------------- the factory


def test_build_runner_refuses_options_a_runner_would_ignore() -> None:
    with pytest.raises(UsageError, match="runner `codex` ignores --effort"):
        build_runner(RunnerSpec("codex", effort="high"))
    with pytest.raises(UsageError, match="runner `codex` ignores --state-tools"):
        build_runner(RunnerSpec("codex", mcp_tools=("proof_open",)))
    with pytest.raises(UsageError, match="runner `direct` ignores --state-tools"):
        build_runner(RunnerSpec("direct", mcp_tools=("proof_open",)))
    with pytest.raises(UsageError, match="runner `mock` ignores --model"):
        build_runner(RunnerSpec("mock", model="x"))
    with pytest.raises(UsageError, match="runner `direct` ignores --sandbox"):
        build_runner(RunnerSpec("direct", sandbox=Sandbox(refresh_credentials=False)))
    with pytest.raises(UsageError, match="runner `claude` ignores scripted answers"):
        build_runner(RunnerSpec("claude", answers={"foo": "exact I."}))


def test_build_runner_builds_each_runner_with_its_supported_options() -> None:
    claude = build_runner(RunnerSpec("claude", model="m", effort="high", permission_mode="bypassPermissions", mcp_tools=("proof_open",)))
    assert claude.name == "claude:m/high" and "--mcp-config" in claude.argv
    codex = build_runner(RunnerSpec("codex", model="luna", extra_args=("--full-auto",)))
    assert codex.argv[-3:] == ["luna", "--full-auto", "-"]
    assert build_runner(RunnerSpec("claude-code", model="m")).name == "claude-code"
    assert build_runner(RunnerSpec("direct", model="claude-opus-5", effort="max")).model == "claude-opus-5"
    assert build_runner(RunnerSpec("mock", answers={"foo": "exact I."})).answers == {"foo": "exact I."}
    sandboxed = build_runner(RunnerSpec("claude", sandbox=Sandbox(refresh_credentials=False)))
    assert sandboxed.name == "sandboxed:claude:default"


def test_runner_spec_validates_its_inputs() -> None:
    with pytest.raises(UsageError, match="unknown runner"):
        RunnerSpec("atomic")
    with pytest.raises(UsageError, match="unknown effort"):
        RunnerSpec("claude", effort="ultra")
    with pytest.raises(UsageError, match="unknown permission mode"):
        RunnerSpec("claude", permission_mode="yolo")
    with pytest.raises(UsageError, match="unknown state tool"):
        RunnerSpec("claude", mcp_tools=("proof_guess",))
    spec = RunnerSpec("claude", mcp_tools="proof_open,proof_step")
    assert spec.mcp_tools == ("proof_open", "proof_step")
    assert spec.to_json()["mcp_tools"] == ["proof_open", "proof_step"]


def test_provider_and_login_hints_cover_every_runner() -> None:
    assert [provider_for(n) for n in RUNNER_NAMES] == ["codex", "anthropic", "anthropic", "anthropic", "mock"]
    assert "codex login" in login_hint("codex")
    assert "/login" in login_hint("claude")
    assert "ANTHROPIC_API_KEY" in login_hint("direct")
    with pytest.raises(UsageError):
        provider_for("atomic")


def test_doctor_lines_name_the_four_probeable_runners() -> None:
    lines = doctor_lines()
    assert [line.split()[0] for line in lines] == ["codex:default", "claude:default", "claude-code", "direct"]
    assert all(line.rstrip().endswith(("ok", "— unavailable")) for line in lines)


# ---------------------------------------------------------------- the direct runner, against a fake SDK


class _FakeSDK:
    """Just enough of ``anthropic`` for the runner: a closable async client."""

    def __init__(self, *, text: str = "", stop: str = "end_turn", raise_exc: Exception | None = None, delay: float = 0.0) -> None:
        self.text, self.stop, self.raise_exc, self.delay = text, stop, raise_exc, delay
        self.calls: list[dict] = []
        self.closed = 0
        sdk = self

        class Messages:
            async def create(self, **kwargs):
                import asyncio
                from types import SimpleNamespace

                sdk.calls.append(kwargs)
                if sdk.raise_exc:
                    raise sdk.raise_exc
                if sdk.delay:
                    await asyncio.sleep(sdk.delay)
                usage = SimpleNamespace(input_tokens=7, output_tokens=3, cache_read_input_tokens=100, cache_creation_input_tokens=0)
                return SimpleNamespace(content=[SimpleNamespace(type="text", text=sdk.text)], usage=usage, stop_reason=sdk.stop, model="claude-sonnet-5-x")

        class AsyncAnthropic:
            def __init__(self) -> None:
                self.messages = Messages()

            async def __aenter__(self):
                return self

            async def __aexit__(self, *exc):
                sdk.closed += 1

        self.AsyncAnthropic = AsyncAnthropic


def _install_fake_sdk(monkeypatch, **kw) -> _FakeSDK:
    import types

    sdk = _FakeSDK(**kw)
    module = types.ModuleType("anthropic")
    module.AsyncAnthropic = sdk.AsyncAnthropic  # type: ignore[attr-defined]
    monkeypatch.setitem(sys.modules, "anthropic", module)
    monkeypatch.setenv("ANTHROPIC_API_KEY", "k")
    return sdk


async def test_direct_runner_reads_a_fenced_proof_and_accounts_tokens(tmp_path: Path, monkeypatch) -> None:
    from pcp.orch.runners.direct import DirectAPIRunner

    sdk = _install_fake_sdk(monkeypatch, text="Sure:\n```coq\nexact I.\n```")
    runner = DirectAPIRunner(model="claude-sonnet-5", effort="high")
    assert runner.available()
    result = await runner.run_node(attempt(tmp_path))
    assert result.status == "qed" and result.proof == "exact I."
    assert result.cost["tokens"] == 110 and result.cost["input_tokens"] == 7 and result.cost["seconds"] >= 0
    assert result.model == "claude-sonnet-5-x" and result.trace["turns"] == 1
    assert sdk.calls[0]["output_config"] == {"effort": "high"} and sdk.calls[0]["max_tokens"] == 8000
    assert sdk.closed == 1, "the client is closed per attempt"


async def test_direct_runner_reports_provider_errors_as_error(tmp_path: Path, monkeypatch) -> None:
    from pcp.orch.runners.direct import DirectAPIRunner

    _install_fake_sdk(monkeypatch, raise_exc=RuntimeError("401 invalid x-api-key"))
    result = await DirectAPIRunner().run_node(attempt(tmp_path))
    assert result.status == "error" and result.evidence.startswith("provider error: RuntimeError: 401")


async def test_direct_runner_deadline_is_a_timed_out_stuck(tmp_path: Path, monkeypatch) -> None:
    from pcp.orch.runners.direct import DirectAPIRunner

    sdk = _install_fake_sdk(monkeypatch, text="x", delay=5.0)
    result = await DirectAPIRunner().run_node(attempt(tmp_path, budget=0.2))
    assert result.status == "stuck" and result.timed_out and "exceeded its 0s deadline" in result.evidence
    assert sdk.closed == 1


async def test_direct_runner_names_a_max_tokens_truncation(tmp_path: Path, monkeypatch) -> None:
    from pcp.orch.runners.direct import DirectAPIRunner

    _install_fake_sdk(monkeypatch, text="```coq\niIntros.\n  iSplit", stop="max_tokens")
    result = await DirectAPIRunner(max_tokens=50).run_node(attempt(tmp_path))
    assert result.status == "stuck" and "max_tokens=50" in result.evidence


def test_direct_runner_is_unavailable_without_a_key(monkeypatch) -> None:
    from pcp.orch.runners.direct import DirectAPIRunner

    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    assert not DirectAPIRunner().available()


def test_every_claude_run_raises_the_cli_output_ceiling(monkeypatch, tmp_path: Path) -> None:
    """A long decomposer reply must not overrun the CLI's 64k output default: every run,
    sandboxed or not, carries the raised ceiling unless the operator set one."""
    monkeypatch.delenv(penv.CLAUDE_MAX_OUTPUT_TOKENS, raising=False)
    assert penv.with_runner_defaults({})[penv.CLAUDE_MAX_OUTPUT_TOKENS] == penv.DEFAULT_CLAUDE_MAX_OUTPUT_TOKENS
    assert penv.with_runner_defaults({penv.CLAUDE_MAX_OUTPUT_TOKENS: "9"})[penv.CLAUDE_MAX_OUTPUT_TOKENS] == "9"
    assert penv.CLAUDE_MAX_OUTPUT_TOKENS in penv.SANDBOX_PASSTHROUGH

    seen: dict[str, object] = {}

    async def fake_run_async(argv, **kw):
        seen["env"] = kw.get("env")
        return Streamed(list(argv), returncode=1)

    monkeypatch.setattr(rcli, "run_async", fake_run_async)
    runner = rcli.claude_headless_runner()
    (tmp_path / "TASK.md").write_text("x", encoding="utf-8")
    asyncio.run(rcli.run_cli(runner, NodePayload(node_id="n", name="n", statement="Lemma n : True.", file="f.v", workdir=tmp_path)))
    assert seen["env"][penv.CLAUDE_MAX_OUTPUT_TOKENS] == penv.DEFAULT_CLAUDE_MAX_OUTPUT_TOKENS
    sb = Sandbox(ro_paths=(), masked=(), credentials=(), binaries=(), home=tmp_path)
    assert sb.environment({"PATH": "/bin"})[penv.CLAUDE_MAX_OUTPUT_TOKENS] == penv.DEFAULT_CLAUDE_MAX_OUTPUT_TOKENS


# ---------------------------------------------------------------- what a worker leaves in its directory


DEEP = "[" * 100_000 + "]" * 100_000


@pytest.mark.parametrize("name", ["answer.json", "proof.v", "Dev.v", "extra.v"])
def test_a_fifo_or_device_named_like_a_worker_file_never_blocks_the_reader(tmp_path, name):
    os.mkfifo(tmp_path / name)
    r = bounded(lambda: read_result(tmp_path, "", target="t", scratch_file="Dev.v"))
    assert r.status == "stuck" and r.proof == ""
    os.unlink(tmp_path / name)
    os.symlink("/dev/zero", tmp_path / name)
    r = bounded(lambda: read_result(tmp_path, "", target="t", scratch_file="Dev.v"))
    assert r.status == "stuck"
    if name == "answer.json":
        assert "symlink" in r.evidence


def test_a_directory_named_like_a_worker_file_does_not_raise(tmp_path):
    for name in ("answer.json", "proof.v", "x.v"):
        (tmp_path / name).mkdir()
    r = read_result(tmp_path, "", target="t", scratch_file="Dev.v")
    assert r.status == "stuck" and "not a regular file" in r.evidence


def test_oversized_and_deeply_nested_answers_are_malformed_not_read(tmp_path):
    big = tmp_path / "answer.json"
    big.write_bytes(b'{"status":"qed","proof":"' + b"x" * (MAX_WORKER_FILE_BYTES + 1) + b'"}')
    r = read_answer_file(big)
    assert r.status == "stuck" and "limit" in r.evidence
    big.write_text('{"status":"qed","proof":' + DEEP + "}")
    assert read_answer_file(big).status == "stuck"
    trace = parse_output('{"type":"assistant","message":{"content":' + DEEP + "}}\n", "claude")
    assert trace.events == 0 and len(trace.stderr_lines) == 1
    (tmp_path / "Dev.v").write_text("Lemma t : True.\nProof.\n  exact I.\nQed.\n")
    assert read_edited_body(tmp_path, "t", scratch_file="Dev.v") == "exact I."
