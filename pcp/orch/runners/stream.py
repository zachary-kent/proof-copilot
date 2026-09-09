"""Parse an agent CLI's streamed event log into a :class:`WorkerTrace`.

A runner that reports only its final message makes the *successful* path opaque, and
that is the path most worth reading: a lemma proved after six turns of fighting mask
arithmetic says "build mask tooling"; a one-shot says nothing needs building.  PLAN.md
13 names two metrics this makes obtainable -- *tokens per solved lemma* and *tool
calls per solved lemma* -- and one it does not name but should: the **friction
sequence**, the errors a worker saw and recovered from.

Two properties the legacy parser lacked, both paid for by live rungs:

* **Usage is accumulated from every assistant message**, not read once from the final
  ``result`` event, so a worker killed at its deadline still reports what it spent;
  and ``total_tokens`` counts cache reads and cache writes, which for a Claude Code
  worker are the bulk of the bill.
* **The ``result`` event's verdict is kept** (``result_error``: ``error_max_turns``,
  ``error_during_execution``) and **non-JSON lines are kept** (``stderr_lines``), so a
  worker the CLI gave up on is distinguishable from one that chose not to answer.

Tolerant by construction: anything unrecognised is skipped, and anything that
*raises* inside a handler lands in ``parse_errors`` -- a broken trace is a lost
diagnostic, never a lost proof.  Classification of the errors happens later, in
``pcp.orch.failures``; this module only captures.
"""

from __future__ import annotations

import json
import re
from collections.abc import Callable, Mapping
from dataclasses import dataclass, field
from typing import Any

from pcp.util.text import one_line

#: Tool inputs that mean "the worker asked Rocq whether it was right yet".  Matched
#: against the *command* of an executing tool only (a ``Grep`` for ``coqc`` is not a
#: check), plus the gate's own MCP tool by name.
_CHECK_RE = re.compile(r"\bpcp\s+check\b|\bcoqc\b|\brocq\s+c\b")
_CHECK_TOOL_SUFFIX = "__verify_node"

#: A Rocq message ends at a blank line or at the start of the next message -- *not* at
#: the next unindented line: ``Error: In environment`` is followed by indented binders
#: and then by the unindented "The term ... has type ..." that says what went wrong.
#: The worker harness's ``Shell cwd was reset`` chatter is a message end too.
_MESSAGE_END = r'(?=\n\s*\n|\nFile "|\nError:|\nWarning:|\nTactic failure:|\s*Shell cwd was reset|\Z)'
_ERROR_RE = re.compile(r"\bError:\s*(.+?)" + _MESSAGE_END, re.S)
#: Iris reports most failures as a tactic failure rather than a Rocq error.
_TACTIC_FAIL_RE = re.compile(r"\bTactic failure:\s*(.+?)" + _MESSAGE_END, re.S)
_GATE_FAIL_RE = re.compile(r"gate:\s*FAIL")

#: Tools whose *output* is a program's output, where ``Error:`` means a failure.  A
#: ``Read`` of a file that mentions ``Error:`` in a comment is not a failed call.
_EXECUTING_TOOLS = frozenset({"Bash", "command_execution", "local_shell", "shell", "exec_command"})

ERROR_CAP = 600
SUMMARY_CAP = 200

FORMATS: tuple[str, ...] = ("claude", "codex", "json", "text")


def _is_executing(name: str) -> bool:
    return name in _EXECUTING_TOOLS or name.startswith("mcp__")


@dataclass
class ToolCall:
    name: str
    summary: str = ""
    is_check: bool = False
    ok: bool | None = None
    error: str = ""

    def to_json(self) -> dict[str, Any]:
        return {"name": self.name, "summary": self.summary, "is_check": self.is_check, "ok": self.ok, "error": self.error}

    @classmethod
    def from_json(cls, d: Mapping[str, Any]) -> ToolCall:
        return cls(
            name=str(d.get("name", "?")),
            summary=str(d.get("summary", "") or ""),
            is_check=bool(d.get("is_check", False)),
            ok=d.get("ok") if isinstance(d.get("ok"), bool) else None,
            error=str(d.get("error", "") or ""),
        )


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
    #: Rocq/gate errors the worker saw, raw (whitespace-collapsed, capped).  Classified
    #: later by ``pcp.orch.failures``; nothing here decides what they mean.
    errors: list[str] = field(default_factory=list)
    #: Events this parser could not read.  Recorded rather than raised.
    parse_errors: list[str] = field(default_factory=list)
    model: str = ""
    #: MCP servers the CLI reported at startup, with their status.  A server that fails
    #: to start is invisible otherwise: the worker simply never calls the tools.
    mcp_servers: list[dict[str, Any]] = field(default_factory=list)
    #: The CLI's own verdict when it ended abnormally (``error_max_turns``,
    #: ``error_during_execution``, codex ``turn.failed``); empty on a clean finish.
    result_error: str = ""
    #: What the CLI said about that verdict, when it said anything.
    result_detail: str = ""
    #: Every line that was not a JSON event: the CLI's stderr, merged.  Kept because
    #: the one line that explains an exit status is usually here.
    stderr_lines: list[str] = field(default_factory=list)
    #: How many JSON events were read; 0 means the stream carried nothing parseable.
    events: int = 0
    format: str = ""

    @property
    def total_tokens(self) -> int:
        """Every token billed, cache reads and writes included."""
        return self.input_tokens + self.output_tokens + self.cache_read_tokens + self.cache_creation_tokens

    @property
    def n_tool_calls(self) -> int:
        return len(self.tool_calls)

    @property
    def check_iterations(self) -> int:
        """How many times it asked Rocq whether it was right yet."""
        return sum(1 for c in self.tool_calls if c.is_check)

    @property
    def failed_mcp_servers(self) -> list[str]:
        return [str(s.get("name")) for s in self.mcp_servers if s.get("status") != "connected"]

    def tool_histogram(self) -> dict[str, int]:
        out: dict[str, int] = {}
        for call in self.tool_calls:
            out[call.name] = out.get(call.name, 0) + 1
        return out

    def to_json(self) -> dict[str, Any]:
        """The ``trace.json`` shape (contract 5.4) plus the fields this version adds."""
        return {
            "turns": self.turns,
            "tool_calls": [c.to_json() for c in self.tool_calls],
            "input_tokens": self.input_tokens,
            "output_tokens": self.output_tokens,
            "cache_read_tokens": self.cache_read_tokens,
            "cache_creation_tokens": self.cache_creation_tokens,
            "dollars": self.dollars,
            "duration_ms": self.duration_ms,
            "final_text": self.final_text,
            "errors": list(self.errors),
            "parse_errors": list(self.parse_errors),
            "model": self.model,
            "mcp_servers": list(self.mcp_servers),
            "result_error": self.result_error,
            "result_detail": self.result_detail,
            "stderr_lines": list(self.stderr_lines),
            "events": self.events,
            "format": self.format,
            "total_tokens": self.total_tokens,
            "n_tool_calls": self.n_tool_calls,
            "check_iterations": self.check_iterations,
            "tool_histogram": self.tool_histogram(),
        }

    @classmethod
    def from_json(cls, d: Mapping[str, Any]) -> WorkerTrace:
        """Tolerant of records written by earlier versions (missing keys default)."""

        def _int(key: str) -> int:
            try:
                return int(d.get(key) or 0)
            except (TypeError, ValueError):
                return 0

        def _strs(key: str) -> list[str]:
            value = d.get(key)
            return [str(x) for x in value] if isinstance(value, list) else []

        calls = d.get("tool_calls")
        try:
            dollars = float(d.get("dollars") or 0.0)
        except (TypeError, ValueError):
            dollars = 0.0
        return cls(
            turns=_int("turns"),
            tool_calls=[ToolCall.from_json(c) for c in calls if isinstance(c, Mapping)] if isinstance(calls, list) else [],
            input_tokens=_int("input_tokens"),
            output_tokens=_int("output_tokens"),
            cache_read_tokens=_int("cache_read_tokens"),
            cache_creation_tokens=_int("cache_creation_tokens"),
            dollars=dollars,
            duration_ms=_int("duration_ms"),
            final_text=str(d.get("final_text", "") or ""),
            errors=_strs("errors"),
            parse_errors=_strs("parse_errors"),
            model=str(d.get("model", "") or ""),
            mcp_servers=[s for s in d.get("mcp_servers") or [] if isinstance(s, dict)],
            result_error=str(d.get("result_error", "") or ""),
            result_detail=str(d.get("result_detail", "") or ""),
            stderr_lines=_strs("stderr_lines"),
            events=_int("events"),
            format=str(d.get("format", "") or ""),
        )

    def cost(self) -> dict[str, Any]:
        """The cost vector (contract 3.3).  ``seconds`` only when the CLI reported a
        duration -- the runner overwrites it with the wall clock it measured, so a
        killed worker never records 0 s."""
        out: dict[str, Any] = {
            "requests": 1,
            "turns": self.turns,
            "tokens": self.total_tokens,
            "input_tokens": self.input_tokens,
            "output_tokens": self.output_tokens,
            "cache_read_tokens": self.cache_read_tokens,
            "dollars": self.dollars,
            "tool_calls": self.n_tool_calls,
            "check_iterations": self.check_iterations,
        }
        if self.duration_ms:
            out["seconds"] = self.duration_ms / 1000.0
        return out

    def render(self) -> str:
        bits = [
            f"{self.turns} turns",
            f"{self.n_tool_calls} tool calls ({self.check_iterations} checks)",
            f"{self.total_tokens} tokens",
        ]
        if self.dollars:
            bits.append(f"${self.dollars:.3f}")
        line = " · ".join(bits)
        if self.model:
            line += f" · {self.model}"
        if self.result_error:
            line += f"\n  ended with {self.result_error}" + (f": {one_line(self.result_detail, 100)}" if self.result_detail else "")
        if self.failed_mcp_servers:
            line += "\n  MCP servers that did NOT connect: " + ", ".join(self.failed_mcp_servers)
        if self.errors:
            line += f"\n  fought through {len(self.errors)} error(s): " + "; ".join(one_line(e, 80) for e in self.errors[:4])
        return line


# ------------------------------------------------------------------ shared machinery


def _event(line: str) -> dict[str, Any] | None:
    stripped = line.strip()
    if not stripped.startswith("{"):
        return None
    try:
        event = json.loads(stripped)
    except (ValueError, RecursionError):
        # A line nested 100 000 deep is not an event; it must not become the runner's
        # exception either (review finding).
        return None
    return event if isinstance(event, dict) else None


def _walk(text: str, trace: WorkerTrace, handler: Callable[[dict[str, Any]], None]) -> None:
    """Feed every JSON line to ``handler``; keep the rest; never let a handler raise."""
    for line in (text or "").splitlines():
        event = _event(line)
        if event is None:
            if line.strip():
                trace.stderr_lines.append(line.rstrip())
            continue
        trace.events += 1
        try:
            handler(event)
        except Exception as exc:  # noqa: BLE001 -- see the module docstring
            trace.parse_errors.append(f"{type(exc).__name__}: {exc}")


def _hook(name: str) -> Callable[[str], Any] | None:
    """A helper from ``pcp.orch.failures`` if that module (written separately) has it."""
    try:
        from pcp.orch import failures
    except ImportError:
        return None
    fn = getattr(failures, name, None)
    return fn if callable(fn) else None


def _flatten(content: Any) -> str:
    """Tool-result content as text.  List-shaped results (MCP tools) are joined with
    real newlines, not ``json.dumps``'d, so the message-end rules still see lines."""
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        parts: list[str] = []
        for block in content:
            if isinstance(block, dict):
                parts.append(str(block.get("text", "") if block.get("type", "text") == "text" else json.dumps(block, default=str)))
            else:
                parts.append(str(block))
        return "\n".join(parts)
    if content is None:
        return ""
    return json.dumps(content, default=str)


def first_error(text: str) -> str:
    """The most specific error message in a tool result, kept whole.

    Rocq's ``In environment`` binder dump is collapsed (via ``failures`` when present)
    *before* the cap: the dump is what pushed the complaint past 600 characters.
    """
    collapse = _hook("collapse_environment")
    for pattern in (_TACTIC_FAIL_RE, _ERROR_RE):
        m = pattern.search(text)
        if m:
            found = m.group(1)
            return " ".join((collapse(found) if collapse else found).split())[:ERROR_CAP]
    return " ".join((collapse(text) if collapse else text).split())[:ERROR_CAP]


def _looks_failed(text: str) -> bool:
    return bool(_ERROR_RE.search(text) or _TACTIC_FAIL_RE.search(text) or _GATE_FAIL_RE.search(text))


def _record_failure(trace: WorkerTrace, call: ToolCall | None, text: str, *, flagged: bool) -> None:
    """Decide ``ok``/``error`` for one tool result and add the friction entry.

    Pattern-based failure detection applies only to tools that *execute* something;
    for ``Read``/``Grep``/``Edit`` only the CLI's own ``is_error`` counts, so reading a
    file that mentions ``Error:`` does not record a failure (legacy bug 13).
    """
    executing = call is None or _is_executing(call.name)
    failed = flagged or (executing and _looks_failed(text))
    if call is not None:
        call.ok = not failed
    if not failed:
        return
    detail = first_error(text)
    if call is not None:
        call.error = detail
    guard = _hook("looks_like_an_error")
    if detail and (guard is None or guard(detail)):
        trace.errors.append(detail)


def _usage_fields(usage: Mapping[str, Any]) -> tuple[int, int, int, int]:
    def _int(*keys: str) -> int:
        for key in keys:
            value = usage.get(key)
            if value is not None:
                try:
                    return int(value)
                except (TypeError, ValueError):
                    return 0
        return 0

    return (
        _int("input_tokens"),
        _int("output_tokens"),
        _int("cache_read_input_tokens", "cached_input_tokens", "cache_read_tokens"),
        _int("cache_creation_input_tokens", "cache_creation_tokens"),
    )


def _add_usage(trace: WorkerTrace, usage: Any) -> None:
    if not isinstance(usage, Mapping):
        return
    i, o, cr, cc = _usage_fields(usage)
    trace.input_tokens += i
    trace.output_tokens += o
    trace.cache_read_tokens += cr
    trace.cache_creation_tokens += cc


def _take_usage(trace: WorkerTrace, usage: Any) -> None:
    """The ``result`` event's usage is the run total; take the larger of it and what
    was accumulated, so either semantics of the field never under-reports."""
    if not isinstance(usage, Mapping):
        return
    i, o, cr, cc = _usage_fields(usage)
    trace.input_tokens = max(trace.input_tokens, i)
    trace.output_tokens = max(trace.output_tokens, o)
    trace.cache_read_tokens = max(trace.cache_read_tokens, cr)
    trace.cache_creation_tokens = max(trace.cache_creation_tokens, cc)


def _read_result_event(event: Mapping[str, Any], trace: WorkerTrace) -> None:
    """The terminal ``result`` event of ``claude -p`` (stream-json and json alike)."""
    if event.get("num_turns") is not None:
        trace.turns = max(trace.turns, int(event.get("num_turns") or 0))
    trace.duration_ms = int(event.get("duration_ms") or 0)
    try:
        trace.dollars = float(event.get("total_cost_usd") or 0.0)
    except (TypeError, ValueError):
        trace.dollars = 0.0
    _take_usage(trace, event.get("usage"))
    subtype = str(event.get("subtype") or "")
    is_error = bool(event.get("is_error"))
    if is_error or subtype.startswith("error"):
        trace.result_error = subtype or "error"
        errors = event.get("errors")
        details = [str(e) for e in errors if e] if isinstance(errors, list) else []
        if isinstance(event.get("result"), str) and event["result"].strip():
            details.insert(0, event["result"].strip())
        trace.result_detail = one_line("; ".join(details), 400) if details else ""
    text = event.get("result")
    if isinstance(text, str) and text.strip():
        trace.final_text = text
    if not trace.model and isinstance(event.get("model"), str):
        trace.model = event["model"]


# ------------------------------------------------------------------ claude stream-json


def parse_stream(text: str) -> WorkerTrace:
    """Parse ``claude -p --output-format stream-json --verbose`` output."""
    trace = WorkerTrace(format="claude")
    pending: dict[str, ToolCall] = {}
    seen_messages: set[str] = set()
    assistant_messages = 0

    def handle(event: dict[str, Any]) -> None:
        nonlocal assistant_messages
        kind = event.get("type")
        if kind == "system" and event.get("subtype") == "init":
            trace.model = str(event.get("model", "") or "")
            servers = event.get("mcp_servers")
            if isinstance(servers, list):
                trace.mcp_servers = [s for s in servers if isinstance(s, dict)]
        elif kind == "assistant":
            message = event.get("message") or {}
            ident = str(message.get("id") or "")
            # One API turn may be emitted as several ``assistant`` events (one per
            # content block) that share an id and repeat the same usage: count once.
            if not ident or ident not in seen_messages:
                if ident:
                    seen_messages.add(ident)
                assistant_messages += 1
                _add_usage(trace, message.get("usage"))
            if not trace.model and isinstance(message.get("model"), str):
                trace.model = message["model"]
            _read_assistant_content(message, trace, pending)
        elif kind == "user":
            _read_tool_results(event, trace, pending)
        elif kind == "result":
            _read_result_event(event, trace)

    _walk(text, trace, handle)
    trace.turns = max(trace.turns, assistant_messages)
    return trace


def _read_assistant_content(message: Mapping[str, Any], trace: WorkerTrace, pending: dict[str, ToolCall]) -> None:
    for block in message.get("content") or []:
        if not isinstance(block, dict):
            continue
        if block.get("type") == "tool_use":
            name = str(block.get("name", "?"))
            inp = block.get("input")
            raw = json.dumps(inp if inp is not None else {}, default=str)
            command = inp.get("command") if isinstance(inp, Mapping) else None
            is_check = name.endswith(_CHECK_TOOL_SUFFIX) or (
                _is_executing(name) and isinstance(command, str) and bool(_CHECK_RE.search(command))
            )
            call = ToolCall(name=name, summary=raw[:SUMMARY_CAP], is_check=is_check)
            trace.tool_calls.append(call)
            ident = block.get("id")
            if ident:
                pending[str(ident)] = call
        elif block.get("type") == "text":
            txt = str(block.get("text", "")).strip()
            if txt:
                trace.final_text = txt


def _read_tool_results(event: Mapping[str, Any], trace: WorkerTrace, pending: dict[str, ToolCall]) -> None:
    message = event.get("message") or {}
    for block in message.get("content") or []:
        if not isinstance(block, dict) or block.get("type") != "tool_result":
            continue
        call = pending.pop(str(block.get("tool_use_id")), None)
        _record_failure(trace, call, _flatten(block.get("content")), flagged=bool(block.get("is_error")))


# ------------------------------------------------------------------ claude json


def parse_json_result(text: str) -> WorkerTrace:
    """Parse ``claude -p --output-format json``: one object, the ``result`` event's shape.

    Stderr lines may precede it (merged), so the object is located line by line
    rather than assumed to be the whole text.
    """
    trace = WorkerTrace(format="json")
    whole = text.strip()
    if whole.startswith("{"):
        try:
            data = json.loads(whole)
        except json.JSONDecodeError:
            data = None
        if isinstance(data, dict):
            trace.events = 1
            try:
                _read_result_event(data, trace)
            except Exception as exc:  # noqa: BLE001
                trace.parse_errors.append(f"{type(exc).__name__}: {exc}")
            return trace
    _walk(text, trace, lambda event: _read_result_event(event, trace))
    return trace


# ------------------------------------------------------------------ codex exec --json


def parse_codex_stream(text: str) -> WorkerTrace:
    """Parse ``codex exec --json`` JSONL (``thread.started``, ``item.completed``,
    ``turn.completed``) into the same :class:`WorkerTrace`."""
    trace = WorkerTrace(format="codex")

    def handle(event: dict[str, Any]) -> None:
        kind = str(event.get("type") or "")
        if kind == "turn.started":
            trace.turns += 1
        elif kind == "turn.completed":
            _add_usage(trace, event.get("usage"))
        elif kind == "item.completed":
            _read_codex_item(event.get("item") or {}, trace)
        elif kind == "turn.failed":
            err = event.get("error") or {}
            trace.result_error = "turn.failed"
            trace.result_detail = one_line(str(err.get("message") if isinstance(err, Mapping) else err), 400)
        elif kind == "error":
            trace.result_error = trace.result_error or "error"
            trace.result_detail = one_line(str(event.get("message") or ""), 400)
        elif kind == "thread.started" and isinstance(event.get("model"), str):
            trace.model = event["model"]

    _walk(text, trace, handle)
    return trace


def _read_codex_item(item: Mapping[str, Any], trace: WorkerTrace) -> None:
    kind = str(item.get("type") or "")
    if kind == "agent_message":
        txt = str(item.get("text") or "").strip()
        if txt:
            trace.final_text = txt
    elif kind == "command_execution":
        command = str(item.get("command") or "")
        call = ToolCall(name="command_execution", summary=command[:SUMMARY_CAP], is_check=bool(_CHECK_RE.search(command)))
        trace.tool_calls.append(call)
        exit_code = item.get("exit_code")
        failed = item.get("status") == "failed" or (isinstance(exit_code, int) and exit_code != 0)
        _record_failure(trace, call, str(item.get("aggregated_output") or ""), flagged=failed)
    elif kind == "mcp_tool_call":
        name = f"mcp__{item.get('server', '?')}__{item.get('tool', '?')}"
        call = ToolCall(
            name=name,
            summary=json.dumps(item.get("arguments") or {}, default=str)[:SUMMARY_CAP],
            is_check=name.endswith(_CHECK_TOOL_SUFFIX),
        )
        trace.tool_calls.append(call)
        err = item.get("error")
        _record_failure(trace, call, _flatten(item.get("result")) if not err else _flatten(err), flagged=bool(err) or item.get("status") == "failed")
    elif kind in ("file_change", "web_search"):
        trace.tool_calls.append(ToolCall(name=kind, summary=json.dumps({k: v for k, v in item.items() if k != "type"}, default=str)[:SUMMARY_CAP], ok=True))
    elif kind == "error":
        detail = one_line(str(item.get("message") or ""), 400)
        if detail:
            trace.result_error = trace.result_error or "error"
            trace.result_detail = detail


# ------------------------------------------------------------------ plain text


def parse_text(text: str) -> WorkerTrace:
    """A CLI that streams no events: the whole output is the final text."""
    return WorkerTrace(format="text", final_text=text or "")


PARSERS: dict[str, Callable[[str], WorkerTrace]] = {
    "claude": parse_stream,
    "codex": parse_codex_stream,
    "json": parse_json_result,
    "text": parse_text,
}


def parse_output(text: str, fmt: str) -> WorkerTrace:
    """Dispatch on the runner's declared stream format (one of :data:`FORMATS`)."""
    return PARSERS.get(fmt, parse_text)(text)
