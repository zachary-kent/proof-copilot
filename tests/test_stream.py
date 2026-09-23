"""The stream parser: what a worker did, read from the CLI's event log."""

from __future__ import annotations

import json

from pcp.orch.runners.stream import (
    WorkerTrace,
    parse_codex_stream,
    parse_json_result,
    parse_output,
    parse_stream,
)


def ev(**kw) -> str:
    return json.dumps(kw)


def usage(i=10, o=5, cr=100, cc=50) -> dict:
    return {"input_tokens": i, "output_tokens": o, "cache_read_input_tokens": cr, "cache_creation_input_tokens": cc}


def assistant(ident: str, *blocks: dict, use: dict | None = None) -> str:
    return ev(type="assistant", message={"id": ident, "usage": use or usage(), "content": list(blocks)})


def tool_use(ident: str, name: str, inp: dict) -> dict:
    return {"type": "tool_use", "id": ident, "name": name, "input": inp}


def tool_result(ident: str, content, is_error: bool = False) -> str:
    return ev(type="user", message={"content": [{"type": "tool_result", "tool_use_id": ident, "content": content, "is_error": is_error}]})


INIT = ev(type="system", subtype="init", model="claude-sonnet-5", mcp_servers=[{"name": "pcp", "status": "connected"}])


def test_usage_accumulates_from_every_assistant_message_including_cache_tokens() -> None:
    """A killed worker has no result event; its spend must still be reported."""
    text = "\n".join([INIT, assistant("m1", {"type": "text", "text": "thinking"}), assistant("m2", {"type": "text", "text": "more"})])
    trace = parse_stream(text)
    assert (trace.input_tokens, trace.output_tokens, trace.cache_read_tokens, trace.cache_creation_tokens) == (20, 10, 200, 100)
    assert trace.total_tokens == 330
    assert trace.turns == 2
    assert trace.model == "claude-sonnet-5"
    assert trace.final_text == "more"
    assert trace.cost()["tokens"] == 330
    assert "seconds" not in trace.cost(), "no duration reported -> the runner fills seconds from its clock"


def test_assistant_events_sharing_a_message_id_count_usage_once() -> None:
    text = "\n".join([assistant("m1", {"type": "text", "text": "a"}), assistant("m1", tool_use("t1", "Bash", {"command": "ls"}))])
    trace = parse_stream(text)
    assert trace.input_tokens == 10
    assert trace.turns == 1
    assert trace.n_tool_calls == 1


def test_the_result_event_usage_is_the_run_total() -> None:
    text = "\n".join([
        assistant("m1", {"type": "text", "text": "a"}),
        ev(type="result", subtype="success", is_error=False, num_turns=3, duration_ms=1500, total_cost_usd=0.25, usage=usage(40, 20, 400, 200), result="done"),
    ])
    trace = parse_stream(text)
    assert (trace.input_tokens, trace.cache_read_tokens) == (40, 400)
    assert trace.turns == 3
    assert trace.dollars == 0.25
    assert trace.final_text == "done"
    assert trace.result_error == ""
    cost = trace.cost()
    assert cost["seconds"] == 1.5
    assert set(cost) == {"requests", "turns", "tokens", "input_tokens", "output_tokens", "cache_read_tokens", "dollars", "tool_calls", "check_iterations", "seconds"}


def test_error_max_turns_is_surfaced_as_result_error() -> None:
    text = "\n".join([
        assistant("m1", {"type": "text", "text": "still going"}),
        ev(type="result", subtype="error_max_turns", is_error=True, num_turns=50, duration_ms=10, usage=usage()),
    ])
    trace = parse_stream(text)
    assert trace.result_error == "error_max_turns"
    assert trace.final_text == "still going"
    assert "error_max_turns" in trace.render()


def test_error_during_execution_keeps_the_detail() -> None:
    text = ev(type="result", subtype="error_during_execution", is_error=True, errors=["API Error: 401 revoked"], num_turns=1)
    trace = parse_stream(text)
    assert trace.result_error == "error_during_execution"
    assert "401" in trace.result_detail


def test_non_json_lines_are_kept_not_dropped() -> None:
    text = "Failed to authenticate: token revoked\n" + INIT + "\nsome warning\n"
    trace = parse_stream(text)
    assert trace.stderr_lines == ["Failed to authenticate: token revoked", "some warning"]
    assert trace.events == 1
    assert trace.parse_errors == []


def test_friction_is_recorded_only_for_executing_tools() -> None:
    """Reading a file that says ``Error:`` is not a failed call."""
    text = "\n".join([
        assistant("m1", tool_use("t1", "Bash", {"command": "pcp check"}), tool_use("t2", "Read", {"file_path": "failures.py"})),
        tool_result("t1", "File \"./node.v\", line 3\nError: The reference foo was not found.\n\nnext"),
        tool_result("t2", "# patterns\n_RE = 'Error: something'\n"),
    ])
    trace = parse_stream(text)
    bash, read = trace.tool_calls
    assert bash.ok is False and bash.is_check
    assert bash.error == "The reference foo was not found."
    assert read.ok is True and read.error == ""
    assert trace.errors == ["The reference foo was not found."]
    assert trace.check_iterations == 1


def test_is_error_from_the_cli_marks_any_tool_failed() -> None:
    text = "\n".join([assistant("m1", tool_use("t1", "Edit", {"file_path": "x"})), tool_result("t1", "File has not been read yet", is_error=True)])
    trace = parse_stream(text)
    assert trace.tool_calls[0].ok is False
    assert trace.errors == ["File has not been read yet"]


def test_is_check_matches_bash_commands_and_verify_node_only() -> None:
    text = assistant(
        "m1",
        tool_use("t1", "Grep", {"pattern": "coqc"}),
        tool_use("t2", "Bash", {"command": "coqc -Q . bench node.v"}),
        tool_use("t3", "mcp__pcp__verify_node", {"body": "done."}),
        tool_use("t4", "mcp__pcp__proof_step", {"tactic": "iIntros."}),
    )
    trace = parse_stream(text)
    assert [c.is_check for c in trace.tool_calls] == [False, True, True, False]
    assert trace.tool_histogram() == {"Grep": 1, "Bash": 1, "mcp__pcp__verify_node": 1, "mcp__pcp__proof_step": 1}


def test_list_shaped_tool_results_keep_real_newlines() -> None:
    text = "\n".join([
        assistant("m1", tool_use("t1", "mcp__pcp__proof_step", {"tactic": "iApply foo."})),
        tool_result("t1", [{"type": "text", "text": "Tactic failure: iApply: cannot apply foo.\n\nGoal: ..."}]),
    ])
    trace = parse_stream(text)
    assert trace.tool_calls[0].error == "iApply: cannot apply foo."
    assert trace.errors == ["iApply: cannot apply foo."]


def test_a_throwing_handler_lands_in_parse_errors_not_in_the_caller() -> None:
    text = "\n".join([ev(type="result", num_turns="not a number"), assistant("m1", {"type": "text", "text": "ok"})])
    trace = parse_stream(text)
    assert trace.parse_errors and "ValueError" in trace.parse_errors[0]
    assert trace.final_text == "ok"


def test_mcp_servers_that_did_not_connect_are_visible() -> None:
    text = ev(type="system", subtype="init", model="m", mcp_servers=[{"name": "pcp", "status": "failed"}])
    trace = parse_stream(text)
    assert trace.failed_mcp_servers == ["pcp"]
    assert "did NOT connect" in trace.render()


def test_codex_jsonl_is_parsed_into_the_same_trace() -> None:
    text = "\n".join([
        ev(type="thread.started", thread_id="t"),
        ev(type="turn.started"),
        ev(type="item.completed", item={"id": "i0", "type": "command_execution", "command": "pcp check", "aggregated_output": "gate: FAIL\nError: nope.\n", "exit_code": 1, "status": "failed"}),
        ev(type="item.completed", item={"id": "i1", "type": "reasoning", "text": "hmm"}),
        ev(type="item.completed", item={"id": "i2", "type": "agent_message", "text": "Here:\n```coq\nexact I.\n```"}),
        ev(type="turn.completed", usage={"input_tokens": 100, "cached_input_tokens": 40, "output_tokens": 7}),
    ])
    trace = parse_codex_stream(text)
    assert trace.format == "codex"
    assert trace.turns == 1
    assert "```coq\nexact I.\n```" in trace.final_text
    assert (trace.input_tokens, trace.cache_read_tokens, trace.output_tokens) == (100, 40, 7)
    assert trace.total_tokens == 147
    call = trace.tool_calls[0]
    assert call.name == "command_execution" and call.is_check and call.ok is False
    assert trace.errors == ["nope."]
    assert trace.result_error == ""


def test_codex_turn_failed_sets_result_error() -> None:
    text = "\n".join([ev(type="turn.started"), ev(type="turn.failed", error={"message": "usage limit reached"})])
    trace = parse_codex_stream(text)
    assert trace.result_error == "turn.failed"
    assert "usage limit" in trace.result_detail


def test_json_output_format_is_one_result_object_possibly_after_stderr() -> None:
    text = "warning: something\n" + ev(type="result", subtype="success", is_error=False, num_turns=2, duration_ms=20, total_cost_usd=0.5, usage=usage(1, 2, 3, 4), result="```coq\nexact I.\n```")
    trace = parse_json_result(text)
    assert trace.turns == 2 and trace.dollars == 0.5 and trace.total_tokens == 10
    assert trace.final_text.startswith("```coq")
    assert trace.stderr_lines == ["warning: something"]
    assert parse_output(text, "json").final_text == trace.final_text


def test_trace_json_round_trips() -> None:
    text = "\n".join([INIT, assistant("m1", tool_use("t1", "Bash", {"command": "ls"})), tool_result("t1", "a b"), ev(type="result", subtype="success", num_turns=1, duration_ms=5, usage=usage())])
    trace = parse_stream(text)
    d = trace.to_json()
    for key in ("turns", "tool_calls", "input_tokens", "output_tokens", "cache_read_tokens", "cache_creation_tokens", "dollars", "duration_ms", "final_text", "errors", "parse_errors", "model", "mcp_servers", "total_tokens", "n_tool_calls", "check_iterations", "tool_histogram"):
        assert key in d, key
    again = WorkerTrace.from_json(json.loads(json.dumps(d)))
    assert again.to_json() == d
    assert WorkerTrace.from_json({}).turns == 0, "older records lack keys and still load"


def test_plain_text_output_is_the_final_text() -> None:
    trace = parse_output("```coq\nexact I.\n```", "text")
    assert trace.final_text.startswith("```coq") and trace.format == "text"
