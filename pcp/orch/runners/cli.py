"""One-shot CLI runners: ``codex exec``, ``claude -p`` (PLAN.md 11).

These are the workhorses.  The flat-rate subscription tier is reachable through the
provider's CLI login, not through a meterable API, so the cheap tier *is* a
subprocess -- and that is a feature: login is delegated, never implemented; pcp only
checks whether a window is authenticated and prints the command to run when it is not.

One-shot runners have no mid-flight channel, so their deadline ladder is soft deadline
-> kill -> requeue with the partial trace as evidence (PLAN.md 6).  The kill is a
process-*group* kill (``pcp.util.proc.run_async``), so a worker's in-flight ``coqc``,
its ``pcp mcp`` server and that server's petanque die with it.

The status decision is one table-driven function, :func:`decide`, and it takes the
process's exit status and the stream's own verdict as first-class inputs: a CLI that
exits non-zero having written no answer is an ``error`` (infrastructure, never
retried), not a worker's ``stuck`` -- the legacy runner never read the exit code and
burned a retry on every revoked token (ARCHITECTURE.md 8, "misclassified failures").
"""

from __future__ import annotations

import re
import shutil
from collections.abc import Callable, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any

from pcp.config.env import with_runner_defaults
from pcp.mcp.config import MCP_CONFIG_FILE
from pcp.mcp.names import mcp_tool_name
from pcp.orch.protocol import (
    ANSWER_FILE,
    PROOF_FILE,
    NodePayload,
    NodeResult,
    fenced_proof_blocks,
    read_result,
)
from pcp.orch.runners.stream import FORMATS, WorkerTrace, parse_output
from pcp.util.io import read_text
from pcp.util.proc import Streamed, run_async
from pcp.util.text import one_line

if TYPE_CHECKING:
    from pcp.orch.runners.sandbox import Sandbox

DEFAULT_ALLOWED_TOOLS: tuple[str, ...] = ("Read", "Write", "Edit", "Bash", "Glob", "Grep")
#: The decomposer proposes statements; it has no way to write or execute (PLAN.md 8.6).
DECOMPOSER_TOOLS: tuple[str, ...] = ("Read", "Glob", "Grep")
PERMISSION_MODES: tuple[str, ...] = ("default", "acceptEdits", "bypassPermissions", "plan", "dontAsk")

CLAUDE_LOGIN_HINT = "Claude Code's `/login` (or `claude login` from a shell)"
CODEX_LOGIN_HINT = "`codex login` (inside a Claude Code session: `! codex login`)"

#: The line of a CLI's stderr that explains a non-zero exit, if any line does.
_ERRORISH = re.compile(
    r"error|fail|not found|denied|revoked|unauthenticated|unauthorized|forbidden|\b40[13]\b|\b429\b"
    r"|rate limit|usage limit|quota|bwrap:|Input must be provided|no such file|cannot|can't",
    re.I,
)


def _tools(value: str | Sequence[str] | None, default: Sequence[str]) -> list[str]:
    if value is None:
        return list(default)
    if isinstance(value, str):
        return [t.strip() for t in value.split(",") if t.strip()]
    return [str(t) for t in value]


def claude_argv(
    *,
    output_format: str,
    allowed_tools: str | Sequence[str] | None = None,
    permission_mode: str = "acceptEdits",
    mcp_tools: Sequence[str] | None = None,
    mcp_config: str = MCP_CONFIG_FILE,
    model: str | None = None,
    effort: str | None = None,
    extra_args: Sequence[str] = (),
) -> list[str]:
    """The ``claude -p`` command line (contract 3.3).  Every element was paid for:

    * the prompt goes on **stdin** -- ``--allowed-tools`` is variadic, so a trailing
      positional prompt is swallowed and the CLI exits with "Input must be provided";
    * ``--strict-mcp-config`` is **unconditional** and ``--mcp-config`` present only
      with grants: strict means "only the servers named", and with none named that is
      none at all, so the tools-off arm cannot inherit the operator's own servers;
    * ``stream-json`` needs ``--verbose`` in print mode.
    """
    tools = _tools(allowed_tools, DEFAULT_ALLOWED_TOOLS)
    argv = ["claude", "-p", "--output-format", output_format]
    if output_format == "stream-json":
        argv.append("--verbose")
    argv += ["--permission-mode", permission_mode, "--strict-mcp-config"]
    if mcp_tools:
        argv += ["--mcp-config", mcp_config]
        tools += [mcp_tool_name(t) for t in mcp_tools]
    argv += ["--allowed-tools", *tools]
    if model:
        argv += ["--model", model]
    if effort:
        argv += ["--effort", effort]
    argv += [str(a) for a in extra_args]
    return argv


@dataclass
class CLIRunner:
    """Spawn a headless agent CLI in the attempt's workdir and read back its answer."""

    argv: list[str] = field(default_factory=list)
    name: str = "cli"
    binary: str = ""
    #: How to parse the CLI's output: one of :data:`pcp.orch.runners.stream.FORMATS`.
    stream: str = "text"
    #: Command that reports whether this provider's window is authenticated.
    auth_check: tuple[str, ...] | None = None
    #: The model this runner was asked for -- attribution when the stream does not say.
    model: str | None = None
    login: str = ""
    #: The child's environment; ``None`` inherits.  A sandbox sets the allowlist here.
    env: dict[str, str] | None = None

    def __post_init__(self) -> None:
        if self.stream not in FORMATS:
            raise ValueError(f"unknown stream format {self.stream!r}; one of {', '.join(FORMATS)}")

    @property
    def executable(self) -> str:
        return self.binary or (self.argv[0] if self.argv else "")

    def available(self) -> bool:
        return bool(self.executable) and shutil.which(self.executable) is not None

    def login_hint(self) -> str:
        return self.login or f"`{self.executable} login`"

    async def authenticated(self) -> bool | None:
        """``None`` when we cannot tell -- never block dispatch on a guess."""
        if not self.auth_check:
            return None
        probe = await run_async(list(self.auth_check), timeout=20)
        if probe.spawn_error or probe.timed_out:
            return None
        return probe.returncode == 0

    async def run_node(self, node: NodePayload) -> NodeResult:
        return await run_cli(self, node)


async def run_cli(runner: CLIRunner, node: NodePayload) -> NodeResult:
    """One attempt: spawn in the attempt dir, pump until exit or deadline, decide."""
    try:
        prompt = read_text(node.prompt_path)
    except OSError as exc:
        return NodeResult(status="error", evidence=f"the packet has no {node.prompt_file}: {exc}")
    streamed = await run_async(
        runner.argv, cwd=node.workdir, timeout=node.budget_seconds, stdin=prompt, env=with_runner_defaults(runner.env)
    )
    trace = parse_output(streamed.text, runner.stream)
    if runner.model and not trace.model:
        trace.model = runner.model
    return decide(node, streamed, trace, runner)


# ------------------------------------------------------------------ the decision


def has_answer(workdir: Path, prose: str) -> bool:
    """Did the worker *answer* (channels 1-3 of contract 3.2), as opposed to leaving a
    partial in the scratch file or nothing at all?"""
    workdir = Path(workdir)
    if (workdir / ANSWER_FILE).exists() or (workdir / PROOF_FILE).exists():
        return True
    blocks = fenced_proof_blocks(prose)
    return bool(blocks) and bool(blocks[-1].strip())


def decide(node: NodePayload, streamed: Streamed, trace: WorkerTrace, runner: CLIRunner) -> NodeResult:
    """Exit status + deadline + stream verdict + answer -> exactly one ``NodeResult``.

    ============  ==========  =====================================================
    condition     answered?   result
    ============  ==========  =====================================================
    spawn error   --          ``error`` (binary missing / not executable)
    deadline      yes         the answer, its own status; evidence notes the kill
    deadline      no          ``stuck``, partial proof, the contract 3.2 kill message
    stream error  yes         the answer, its own status; evidence names the verdict
    stream error  no          ``error`` naming the verdict (``error_max_turns`` ...)
    exit != 0     yes         the answer; evidence notes the exit status
    exit != 0     no          ``error`` with the first error-looking line or the tail
    exit 0        --          the answer (``stuck`` with no answer, per read_result)
    ============  ==========  =====================================================

    "Answered" means answer.json / proof.v / a fenced proof, so a complete answer
    written just before a kill is honoured with its own status (``qed`` is gated by
    the caller as always); an answer is never downgraded because the CLI ended badly
    afterwards -- that would lose proofs.
    """
    workdir = Path(node.workdir)
    if streamed.spawn_error:
        result = NodeResult(
            status="error",
            evidence=(
                f"{runner.executable} is not on PATH or could not be started ({streamed.spawn_error}); "
                f"install it and log in with {runner.login_hint()}"
            ),
        )
        return _finish(result, streamed, trace, runner)

    prose = streamed.text if runner.stream == "text" else trace.final_text
    answered = has_answer(workdir, prose)
    answer = read_result(workdir, prose, target=node.name, scratch_file=node.scratch_file)
    rc = streamed.returncode

    if streamed.timed_out:
        if answered:
            result = answer
            result.evidence = _join(
                answer.evidence,
                f"the worker was killed at its {node.budget_seconds:.0f}s deadline after writing its answer",
            )
        else:
            result = NodeResult(status="stuck", proof=answer.proof, evidence=deadline_evidence(node, streamed, trace, answer))
    elif trace.result_error:
        verdict = f"the runner ended with {trace.result_error}" + (f": {trace.result_detail}" if trace.result_detail else "")
        if answered:
            result = answer
            result.evidence = _join(answer.evidence, verdict)
        else:
            result = NodeResult(status="error", proof=answer.proof, evidence=_join(verdict, answer.evidence))
    elif rc != 0:
        if answered:
            result = answer
            result.evidence = _join(answer.evidence, f"the runner {_exit_phrase(rc)}")
        else:
            result = NodeResult(
                status="error",
                proof=answer.proof,
                evidence=f"{runner.executable} {_exit_phrase(rc)} and wrote no answer: {error_detail(trace, streamed.text)}",
            )
    else:
        result = answer
    return _finish(result, streamed, trace, runner)


def deadline_evidence(node: NodePayload, streamed: Streamed, trace: WorkerTrace, partial: NodeResult) -> str:
    """The contract 3.2 kill message.  Bytes first and always: turns and tool calls are
    zero for a worker still on its opening message, and a stream that carried work
    must never read like "captured 0 turn(s)"."""
    pieces = [f"worker exceeded its {node.budget_seconds:.0f}s deadline and was killed"]
    if partial.proof.strip():
        pieces.append(f"recovered a {len(partial.proof.strip().splitlines())}-line partial proof")
    captured = len(streamed.buffer)
    if captured:
        pieces.append(
            f"captured {captured} bytes of output before the kill ({trace.turns} turn(s), {trace.n_tool_calls} tool call(s))"
        )
    else:
        pieces.append("the worker produced no output at all before the kill")
    return "; ".join(pieces)


def error_detail(trace: WorkerTrace, text: str) -> str:
    """Why a CLI exited non-zero: its own verdict, else the first error-looking
    stderr line, else the last stderr line, else its final text, else the tail."""
    if trace.result_detail:
        return trace.result_detail
    for line in trace.stderr_lines:
        if _ERRORISH.search(line):
            return one_line(line, 400)
    if trace.stderr_lines:
        return one_line(trace.stderr_lines[-1], 400)
    if trace.final_text.strip():
        return one_line(trace.final_text, 400)
    tail = (text or "").strip()[-400:]
    return one_line(tail, 400) if tail else "no output at all"


def _exit_phrase(rc: int | None) -> str:
    if rc is None:
        return "ended without an exit status"
    if rc < 0:
        return f"was killed by signal {-rc}"
    return f"exited with status {rc}"


def _join(*parts: str) -> str:
    return "; ".join(p.strip() for p in parts if p and p.strip())


def _finish(result: NodeResult, streamed: Streamed, trace: WorkerTrace, runner: CLIRunner) -> NodeResult:
    """The fields every outcome carries.  ``raw`` is the FULL stream (the recorder
    clips, not the runner); ``cost['seconds']`` is the wall clock, always."""
    result.raw = streamed.text
    result.elapsed_s = streamed.elapsed_s
    result.exit_code = streamed.returncode
    result.timed_out = streamed.timed_out
    result.trace = trace.to_json()
    result.cost = {"requests": 1} if runner.stream == "text" else trace.cost()
    result.cost["seconds"] = streamed.elapsed_s
    return result


# ------------------------------------------------------------------ factories


def codex_cli_runner(model: str | None = None, sandbox: str = "workspace-write", *, extra_args: Sequence[str] = ()) -> CLIRunner:
    """``codex exec`` -- runner #1, the only route to the flat-rate workhorse tier.

    ``--skip-git-repo-check``: an attempt dir is never a git checkout, and under bwrap
    the repo's ``.git`` is masked; without the flag codex refuses to start.  ``-``
    reads the prompt from stdin, for the same reason ``claude`` gets it there.
    """
    argv = ["codex", "exec", "--json", "--sandbox", sandbox, "--skip-git-repo-check"]
    if model:
        argv += ["--model", model]
    argv += [str(a) for a in extra_args]
    argv.append("-")
    return CLIRunner(
        argv=argv,
        name=f"codex:{model or 'default'}",
        binary="codex",
        stream="codex",
        auth_check=("codex", "login", "status"),
        model=model,
        login=CODEX_LOGIN_HINT,
    )


def claude_headless_runner(
    model: str | None = None,
    *,
    allowed_tools: str | Sequence[str] | None = None,
    permission_mode: str = "acceptEdits",
    mcp_tools: Sequence[str] | None = None,
    mcp_config: str = MCP_CONFIG_FILE,
    effort: str | None = None,
    extra_args: Sequence[str] = (),
) -> CLIRunner:
    """``claude -p`` -- the same trick on the Claude subscription (argv: contract 3.3)."""
    argv = claude_argv(
        output_format="stream-json",
        allowed_tools=allowed_tools,
        permission_mode=permission_mode,
        mcp_tools=mcp_tools,
        mcp_config=mcp_config,
        model=model,
        effort=effort,
        extra_args=extra_args,
    )
    return CLIRunner(
        argv=argv,
        name=f"claude:{model or 'default'}" + (f"/{effort}" if effort else ""),
        binary="claude",
        stream="claude",
        model=model,
        login=CLAUDE_LOGIN_HINT,
    )


def decomposer_runner(
    model: str | None = None,
    *,
    effort: str | None = None,
    sandbox_factory: Sandbox | Callable[[], Sandbox] | None = None,
) -> Any:
    """The decomposer's runner: ``claude -p`` with ``Read Glob Grep`` only (contract 3.5).

    No Write, no Edit, no Bash: a decomposer proposes statements and never proves
    (PLAN.md 8.6), and the tool allowlist is what makes that structural.  Its
    permission mode stays ``acceptEdits`` even when sandboxed -- there is nothing to
    bypass.  ``sandbox_factory`` may be a :class:`Sandbox` or a zero-argument callable
    producing one; the runner is then wrapped per attempt.
    """
    inner = claude_headless_runner(model, allowed_tools=DECOMPOSER_TOOLS, permission_mode="acceptEdits", effort=effort)
    if sandbox_factory is None:
        return inner
    from pcp.orch.runners.sandbox import Sandbox, SandboxedRunner

    sandbox = sandbox_factory if isinstance(sandbox_factory, Sandbox) else sandbox_factory()
    return SandboxedRunner(inner, sandbox)
