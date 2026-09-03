"""Parse an agent CLI's streamed event log into a usable worker trace.

A runner that reports only its final message makes the *successful* path opaque, and
that is the path most worth reading: a lemma that was proved after six turns of
fighting mask arithmetic tells you to go build mask tooling, and a lemma that was
one-shot tells you nothing needs building.  With only the final answer, both look
identical.

PLAN.md 13 names two metrics this makes obtainable that were not before -- *tokens
per solved lemma* and *tool calls per solved lemma* -- and one it does not name but
should: the **friction sequence**, the errors a worker saw and recovered from.
"""

from __future__ import annotations

import json
import re

from pcp.orch.failures import collapse_environment, looks_like_an_error
from dataclasses import asdict, dataclass, field
from typing import Any, Iterator

#: Tool calls that mean "the worker asked Rocq whether it was right yet".
_CHECK_RE = re.compile(r"\bpcp\s+check\b|\bcoqc\b|\brocq\s+c\b")
#: Rocq's own error shape.  Multi-line on purpose: `Error: In environment Σ : ...`
#: continues onto following lines, and cutting at the first newline threw away the
#: part that says what actually went wrong.
#: A Rocq message ends at a blank line or at the start of the next message -- *not*
#: at the next unindented line.  `Error: In environment` is followed by indented
#: bindings and then by an unindented "The term ... has type ...", which is the half
#: that says what actually went wrong.
#: ... and the worker's own harness chatter is a message end too: `Shell cwd was
#: reset to <path>` gets appended to whatever Rocq last said, so the same error
#: recorded once with the suffix and once without counted as two distinct
#: failures, and the trailing path made both `unclassified`.
_MESSAGE_END = (
    r'(?=\n\s*\n|\nFile "|\nError:|\nWarning:|\nTactic failure:'
    r'|\s*Shell cwd was reset|\Z)'
)
_ERROR_RE = re.compile(r"\bError:\s*(.+?)" + _MESSAGE_END, re.S)
#: Iris reports most failures as a tactic failure rather than a Rocq error.
_TACTIC_FAIL_RE = re.compile(r"\bTactic failure:\s*(.+?)" + _MESSAGE_END, re.S)
_GATE_FAIL = re.compile(r"gate:\s*FAIL")


@dataclass
class ToolCall:
    name: str
    summary: str = ""
    is_check: bool = False
    ok: bool | None = None
    error: str = ""


@dataclass
class WorkerTrace:
    """What a worker actually did, as opposed to what it said at the end."""

    turns: int = 0
    tool_calls: list[ToolCall] = field(default_factory=list)
    input_tokens: int = 0
    output_tokens: int = 0
    cache_read_tokens: int = 0
    cache_creation_tokens: int = 0
    dollars: float = 0.0
    duration_ms: int = 0
    final_text: str = ""
    #: Rocq/gate errors the worker saw and (if it solved) recovered from.
    errors: list[str] = field(default_factory=list)
    #: Events this parser could not read. Recorded rather than raised: a broken
    #: trace is a lost diagnostic, never a lost proof.
    parse_errors: list[str] = field(default_factory=list)
    model: str = ""
    #: MCP servers the CLI reported at startup, with their status.  Recorded because
    #: a server that fails to start is invisible otherwise: the worker simply never
    #: calls the tools, which looks identical to a worker that chose not to.
    mcp_servers: list[dict] = field(default_factory=list)

    @property
    def total_tokens(self) -> int:
        return self.input_tokens + self.output_tokens

    @property
    def n_tool_calls(self) -> int:
        return len(self.tool_calls)

    @property
    def check_iterations(self) -> int:
        """How many times it asked Rocq whether it was right yet."""
        return sum(1 for c in self.tool_calls if c.is_check)

    def tool_histogram(self) -> dict[str, int]:
        out: dict[str, int] = {}
        for call in self.tool_calls:
            out[call.name] = out.get(call.name, 0) + 1
        return out

    def to_json(self) -> dict[str, Any]:
        d = asdict(self)
        d["total_tokens"] = self.total_tokens
        d["n_tool_calls"] = self.n_tool_calls
        d["check_iterations"] = self.check_iterations
        d["tool_histogram"] = self.tool_histogram()
        return d

    def cost(self) -> dict[str, Any]:
        return {
            "requests": 1,
            "turns": self.turns,
            "tokens": self.total_tokens,
            "input_tokens": self.input_tokens,
            "output_tokens": self.output_tokens,
            "cache_read_tokens": self.cache_read_tokens,
            "dollars": self.dollars,
            "tool_calls": self.n_tool_calls,
            "check_iterations": self.check_iterations,
            "seconds": self.duration_ms / 1000.0 if self.duration_ms else 0.0,
        }

    @property
    def failed_mcp_servers(self) -> list[str]:
        return [str(s.get("name")) for s in self.mcp_servers if s.get("status") != "connected"]

    def render(self) -> str:
        bits = [
            f"{self.turns} turns",
            f"{self.n_tool_calls} tool calls ({self.check_iterations} checks)",
            f"{self.total_tokens} tokens",
        ]
        if self.dollars:
            bits.append(f"${self.dollars:.3f}")
        line = " · ".join(bits)
        if self.failed_mcp_servers:
            line += "\n  MCP servers that did NOT connect: " + ", ".join(self.failed_mcp_servers)
        if self.errors:
            line += f"\n  fought through {len(self.errors)} error(s): " + "; ".join(
                " ".join(e.split())[:80] for e in self.errors[:4]
            )
        return line


def parse_stream(text: str) -> WorkerTrace:
    """Parse `claude -p --output-format stream-json --verbose` output.

    Tolerant by construction: a runner whose trace parser throws would turn a
    successful proof into a lost one, so anything unrecognised is skipped -- and so
    is anything that *raises*. That second half used to be only a claim in this
    docstring: unknown events were skipped, but an exception inside a handler
    propagated out of `run_node` and killed the run. It cost two live rungs, because
    the trace is a *diagnostic* -- the proof is in the answer, and losing the record
    of how it was reached must never lose the proof itself.
    """
    trace = WorkerTrace()
    pending: dict[str, ToolCall] = {}
    for event in _events(text):
        kind = event.get("type")
        try:
            if kind == "system" and event.get("subtype") == "init":
                trace.model = str(event.get("model", ""))
                servers = event.get("mcp_servers")
                if isinstance(servers, list):
                    trace.mcp_servers = [s for s in servers if isinstance(s, dict)]
            elif kind == "assistant":
                _read_assistant(event, trace, pending)
            elif kind == "user":
                _read_tool_results(event, pending, trace)
            elif kind == "result":
                _read_result(event, trace)
        except Exception as exc:  # noqa: BLE001 -- see the docstring
            trace.parse_errors.append(f"{type(exc).__name__}: {exc}")
    return trace


def _events(text: str) -> Iterator[dict[str, Any]]:
    for line in (text or "").splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(event, dict):
            yield event


def _read_assistant(event: dict[str, Any], trace: WorkerTrace, pending: dict[str, ToolCall]) -> None:
    message = event.get("message") or {}
    for block in message.get("content") or []:
        if not isinstance(block, dict):
            continue
        if block.get("type") == "tool_use":
            name = str(block.get("name", "?"))
            raw = json.dumps(block.get("input") or {}, default=str)
            call = ToolCall(name=name, summary=raw[:200], is_check=bool(_CHECK_RE.search(raw)))
            trace.tool_calls.append(call)
            ident = block.get("id")
            if ident:
                pending[str(ident)] = call
        elif block.get("type") == "text":
            text = str(block.get("text", "")).strip()
            if text:
                trace.final_text = text


def _read_tool_results(event: dict[str, Any], pending: dict[str, ToolCall], trace: WorkerTrace) -> None:
    message = event.get("message") or {}
    for block in message.get("content") or []:
        if not isinstance(block, dict) or block.get("type") != "tool_result":
            continue
        call = pending.pop(str(block.get("tool_use_id")), None)
        body = block.get("content")
        text = body if isinstance(body, str) else json.dumps(body, default=str)
        failed = (
            bool(block.get("is_error"))
            or bool(_ERROR_RE.search(text))
            or bool(_TACTIC_FAIL_RE.search(text))
            or bool(_GATE_FAIL.search(text))
        )
        detail = _first_error(text)
        if call is not None:
            call.ok = not failed
            if failed:
                call.error = detail
        # A worker that greps the harness's own source gets it back, and
        # `pcp/orch/failures.py` is full of the literal `Error:` its patterns match
        # on -- so reading the classifier taught the classifier that a proof had
        # failed. The guard already existed for scoring; it belongs at capture too,
        # because an error that is never recorded cannot mislead anything later.
        if failed and looks_like_an_error(detail):
            trace.errors.append(detail)


def _first_error(text: str) -> str:
    """The most specific error message in a tool result, kept whole."""
    # Collapse before the cap, not after: the environment dump is what pushes the
    # actual complaint past 600 characters in the first place.
    for pattern in (_TACTIC_FAIL_RE, _ERROR_RE):
        m = pattern.search(text)
        if m:
            return " ".join(collapse_environment(m.group(1)).split())[:600]
    return " ".join(collapse_environment(text).split())[:600]


def _read_result(event: dict[str, Any], trace: WorkerTrace) -> None:
    trace.turns = int(event.get("num_turns") or 0)
    trace.duration_ms = int(event.get("duration_ms") or 0)
    try:
        trace.dollars = float(event.get("total_cost_usd") or 0.0)
    except (TypeError, ValueError):
        trace.dollars = 0.0
    usage = event.get("usage") or {}
    trace.input_tokens = int(usage.get("input_tokens") or 0)
    trace.output_tokens = int(usage.get("output_tokens") or 0)
    trace.cache_read_tokens = int(usage.get("cache_read_input_tokens") or 0)
    trace.cache_creation_tokens = int(usage.get("cache_creation_input_tokens") or 0)
    if isinstance(event.get("result"), str) and event["result"].strip():
        trace.final_text = event["result"]
