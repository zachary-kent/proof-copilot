"""One-shot CLI runners: `codex exec`, `claude -p` (PLAN.md 11).

These are the workhorses.  The 20x subscription is reachable through the provider's
CLI login, not through a meterable API, so the cheap tier *is* a subprocess -- and
that is a feature: login is delegated, never implemented, and pcp only ever checks
whether a window is authenticated and prints the command to run when it is not.

One-shot runners have no mid-flight channel, so the deadline ladder for them is:
soft deadline -> kill -> requeue with the partial trace as evidence (PLAN.md 6).
"""

from __future__ import annotations

import asyncio
import os
import shutil
import time
from dataclasses import dataclass, field
from pathlib import Path

from pcp.orch.runners.base import NodePayload, NodeResult, read_result, strip_proof_wrapper

#: Written into each worker's directory when an ablation grants MCP tools.
MCP_CONFIG_FILE = ".mcp.json"
MCP_SERVER_NAME = "pcp"


def mcp_tool_name(tool: str) -> str:
    """`proof_ledger` -> `mcp__pcp__proof_ledger`, the name the CLI allowlists."""
    return tool if tool.startswith("mcp__") else f"mcp__{MCP_SERVER_NAME}__{tool}"


def write_mcp_config(workdir: "Path", *, workspace: "Path | None" = None, pcp: str = "pcp") -> "Path":
    """Point the worker's CLI at a `pcp mcp` server rooted in its own workdir."""
    import json as _json
    from pathlib import Path as _Path

    workdir = _Path(workdir)
    target = workdir / MCP_CONFIG_FILE
    target.write_text(
        _json.dumps(
            {
                "mcpServers": {
                    MCP_SERVER_NAME: {
                        "command": pcp,
                        "args": ["mcp", "--workspace", str(workspace or workdir)],
                    }
                }
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    return target


@dataclass
class CLIRunner:
    """Spawn a headless agent CLI in the node's workdir and read back its answer."""

    #: argv template; `{prompt}` is substituted with the task prompt.
    argv: list[str]
    name: str = "cli"
    binary: str = ""
    env: dict[str, str] = field(default_factory=dict)
    #: Command that reports whether this provider's window is authenticated.
    auth_check: list[str] | None = None
    prompt_on_stdin: bool = False
    #: Parse the CLI's streamed event log into a :class:`WorkerTrace`.  Without this
    #: a solved lemma is indistinguishable from a one-shot -- and the interesting
    #: question about a success is how much friction it cost.
    stream_json: bool = False

    def available(self) -> bool:
        return shutil.which(self.binary or self.argv[0]) is not None

    def login_hint(self) -> str:
        return f"`{self.binary or self.argv[0]} login` (run it with `! {self.binary or self.argv[0]} login`)"

    async def authenticated(self) -> bool | None:
        """``None`` when we cannot tell -- never block dispatch on a guess."""
        if not self.auth_check:
            return None
        try:
            proc = await asyncio.create_subprocess_exec(
                *self.auth_check,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.STDOUT,
            )
            await asyncio.wait_for(proc.communicate(), timeout=20)
            return proc.returncode == 0
        except (FileNotFoundError, asyncio.TimeoutError, OSError):
            return None

    async def run_node(self, node: NodePayload) -> NodeResult:
        started = time.perf_counter()
        prompt = (node.workdir / "TASK.md").read_text(encoding="utf-8")
        argv = [prompt if a == "{prompt}" else a for a in self.argv]
        stdin_data = prompt.encode("utf-8") if self.prompt_on_stdin else None
        env = {**os.environ, **self.env}
        try:
            proc = await asyncio.create_subprocess_exec(
                *argv,
                cwd=str(node.workdir),
                stdin=asyncio.subprocess.PIPE if self.prompt_on_stdin else asyncio.subprocess.DEVNULL,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.STDOUT,
                env=env,
            )
        except FileNotFoundError:
            return NodeResult(
                status="error",
                evidence=f"{self.binary or argv[0]} is not on PATH; log in with {self.login_hint()}",
                elapsed_s=time.perf_counter() - started,
            )

        # Accumulate stdout as it arrives rather than via `communicate()`, which
        # returns nothing at all unless the process exits.  Two of three rungs on the
        # 2026-09-01 design ladder died on a decomposer deadline, and because the
        # buffered output was discarded at the kill every record read `trace: {}` with
        # an empty transcript -- so a worker thinking hard for an hour and a worker
        # hung on its first token produced byte-identical evidence.  The recovery path
        # below could not help: it reads files the worker *wrote*, and a decomposer is
        # read-only by construction.  The stream was the only witness there was.
        buffered = bytearray()

        async def _pump() -> None:
            if stdin_data is not None and proc.stdin is not None:
                proc.stdin.write(stdin_data)
                try:
                    await proc.stdin.drain()
                except (BrokenPipeError, ConnectionResetError):
                    pass
                proc.stdin.close()
            assert proc.stdout is not None
            while True:
                chunk = await proc.stdout.read(65536)
                if not chunk:
                    break
                # `+=` would rebind and make `buffered` local to this closure, so the
                # timeout path outside would see an empty buffer -- the exact bug this
                # block exists to fix.  Mutate in place.
                buffered.extend(chunk)

        try:
            await asyncio.wait_for(_pump(), timeout=node.budget_seconds)
            stdout = bytes(buffered)
        except asyncio.TimeoutError:
            # Kill and requeue with whatever the worker left behind as evidence:
            # a partial trace is a better retry input than "timed out".
            proc.kill()
            await proc.wait()
            partial_text = bytes(buffered).decode("utf-8", "replace")
            partial_trace = None
            if self.stream_json and partial_text:
                from pcp.orch.runners.stream import parse_stream

                partial_trace = parse_stream(partial_text)
            partial = read_result(node.workdir, (partial_trace.final_text if partial_trace else "") or "")
            recovered = []
            if partial.proof.strip():
                recovered.append(f"recovered a {len(partial.proof.strip().splitlines())}-line partial proof")
            if partial_text:
                # Bytes first and always: turns and tool calls are zero for a worker
                # that was still on its opening message, and reporting only those
                # would say "captured 0 turn(s)" about a stream that did carry work.
                detail = f"captured {len(partial_text)} bytes of output before the kill"
                if partial_trace is not None:
                    detail += (
                        f" ({partial_trace.turns} turn(s), "
                        f"{len(partial_trace.tool_calls)} tool call(s))"
                    )
                recovered.append(detail)
            else:
                recovered.append("the worker produced no output at all before the kill")
            result = NodeResult(
                status="stuck",
                proof=strip_proof_wrapper(partial.proof) if partial.proof else "",
                evidence=(
                    f"worker exceeded its {node.budget_seconds:.0f}s deadline and was killed; "
                    + "; ".join(recovered)
                ),
                elapsed_s=time.perf_counter() - started,
            )
            if partial_trace is not None:
                result.trace = partial_trace.to_json()
                result.cost = partial_trace.cost()
                result.cost.setdefault("seconds", result.elapsed_s)
            return result

        text = (stdout or b"").decode("utf-8", "replace")
        trace = None
        if self.stream_json:
            from pcp.orch.runners.stream import parse_stream

            trace = parse_stream(text)
            # The fenced-block fallback needs prose, not a wall of JSON events.
            text = trace.final_text or text
        result = read_result(node.workdir, text)
        result.proof = strip_proof_wrapper(result.proof) if result.proof else ""
        result.elapsed_s = time.perf_counter() - started
        if trace is not None:
            result.trace = trace.to_json()
            result.cost = trace.cost()
            result.cost.setdefault("seconds", result.elapsed_s)
        else:
            result.cost = {"requests": 1, "seconds": result.elapsed_s}
        return result


def codex_cli_runner(model: str | None = None, sandbox: str = "workspace-write") -> CLIRunner:
    """`codex exec` -- runner #1, and the only route to the flat-rate workhorse tier.

    The 20x plan is reachable through the CLI login, not through a meterable API
    key, which is exactly why this is the first runner implemented rather than the
    most convenient one.
    """
    argv = ["codex", "exec", "--json", "--sandbox", sandbox]
    if model:
        argv += ["--model", model]
    # `codex exec -` reads the prompt from stdin; same reasoning as the Claude runner
    # -- a positional prompt after variadic flags is a silent-failure hazard.
    argv.append("-")
    return CLIRunner(
        argv=argv,
        name=f"codex:{model or 'default'}",
        binary="codex",
        auth_check=["codex", "auth", "status"],
        prompt_on_stdin=True,
    )


def claude_headless_runner(
    model: str | None = None,
    *,
    allowed_tools: str = "Read,Write,Edit,Bash,Glob,Grep",
    permission_mode: str = "acceptEdits",
    mcp_tools: list[str] | None = None,
    mcp_config: str = MCP_CONFIG_FILE,
    effort: str | None = None,
) -> CLIRunner:
    """`claude -p` -- the same trick on the Claude subscription.

    The prompt goes on **stdin**, not as a positional argument: `--allowed-tools` is
    variadic, so a trailing positional prompt is swallowed by it and the CLI exits
    immediately with "Input must be provided".  That failure is silent from the
    orchestrator's side -- it looks like a worker that produced no answer -- so the
    stdin form is the only one used here.
    """
    tools = allowed_tools.split(",")
    argv = [
        "claude", "-p",
        # `stream-json` is what makes a run analysable: turns, tool calls, tool
        # *results*, and token usage.  `text` reports only the closing message,
        # which hides everything that happened on the way to it.
        "--output-format", "stream-json", "--verbose",
        "--permission-mode", permission_mode,
    ]
    # `--strict-mcp-config` goes on *unconditionally*: it means "only the servers
    # named by --mcp-config", and with none named that is none at all.  Passing it
    # only in the tools-on arm meant the tools-*off* arm inherited whatever MCP
    # config happened to be on the operator's box -- a run recorded
    # `mcp_servers=[{'name': 'claude.ai Google Drive', ...}]` in every worker.  Inert
    # there, but an ablation whose control arm varies by machine measures nothing.
    argv += ["--strict-mcp-config"]
    if mcp_tools:
        argv += ["--mcp-config", mcp_config]
        tools += [mcp_tool_name(t) for t in mcp_tools]
    argv += ["--allowed-tools", *tools]
    if model:
        argv += ["--model", model]
    if effort:
        argv += ["--effort", effort]
    return CLIRunner(
        argv=argv,
        name=f"claude:{model or 'default'}" + (f"/{effort}" if effort else ""),
        binary="claude",
        prompt_on_stdin=True,
        stream_json=True,
    )
