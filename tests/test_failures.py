"""Failure classification (PLAN.md 1) -- a benchmark's work queue."""

from __future__ import annotations

from pathlib import Path

from pcp.orch.failures import TAXONOMY, classify, looks_like_an_error, summarize


def test_the_taxonomy_covers_plan_section_1() -> None:
    for klass in (
        "premature-consumption", "leftover-spatial", "mask-arithmetic",
        "later-modality", "persistent-vs-spatial", "retrieval", "context-pollution",
    ):
        assert klass in TAXONOMY


def test_real_error_strings_land_in_the_right_class() -> None:
    cases = {
        "Error: The reference wp_cmpxchg_suc was not found in the current environment": "retrieval",
        "iOrDestruct: cannot destruct (P ∗ Q)%I": "pattern-mismatch",
        "gate: FAIL\n  [FAIL] no new Admitted / admit / Axiom: admit": "gate-violation",
        "the worker produced no answer.json, no proof.v and no fenced proof block": "protocol-violation",
        'Error: Unable to unify "wp e {{ v, Q v }}" with "WP e @ E {{ Φ }}"': "unification-failure",
        "worker exceeded its 900s deadline and was killed": "deadline",
        "the spatial context is not empty: \"Hl\", \"HQ\"": "leftover-spatial",
        "Error: fupd_mask_subseteq: ↑N ⊆ E is not provable": "mask-arithmetic",
    }
    for text, expected in cases.items():
        assert classify(text).primary == expected, f"{text[:50]!r} -> {classify(text).render()}"


def test_a_syntax_error_is_the_worker_s_formatting_not_a_reasoning_failure() -> None:
    c = classify("Error: Syntax error: [ltac_use_default] expected after [tactic]")
    assert c.primary == "protocol-violation"


def test_contested_is_not_a_failure_mode_to_debug() -> None:
    assert classify("the statement cannot hold because ...", status="contested").primary == "contested"


def test_unmatched_text_is_unclassified_rather_than_forced() -> None:
    """A taxonomy that always has an answer teaches you nothing."""
    c = classify("something entirely novel happened here")
    assert c.primary == "unclassified"
    assert c.findings[0].evidence


def test_no_evidence_is_reported_as_such() -> None:
    assert classify("", None).primary == "unclassified"


def test_summarize_builds_a_work_queue() -> None:
    report = summarize([
        {"lemma": "a", "solved": True},
        {"lemma": "b", "solved": False, "evidence": "iOrDestruct: cannot destruct"},
        {"lemma": "c", "solved": False, "evidence": "iAndDestruct failed"},
        {"lemma": "d", "solved": False, "evidence": "The reference foo was not found in the current environment"},
    ])
    assert report.total == 4 and report.solved == 1
    assert report.primary["pattern-mismatch"] == 2
    text = report.render()
    assert "1/4 solved" in text and "pattern-mismatch" in text


def test_records_round_trip(tmp_path: Path) -> None:
    from pcp.orch.record import AttemptRecord, Recorder, load_records

    rec = Recorder(tmp_path, run_id="r1")
    workdir = tmp_path / "w"
    workdir.mkdir()
    (workdir / "TASK.md").write_text("the packet", encoding="utf-8")
    out = rec.write(
        AttemptRecord(
            run_id="r1", node="n", lemma="foo_spec", attempt=1, runner="mock",
            status="stuck", solved=False,
            evidence="iOrDestruct: cannot destruct (P ∗ Q)%I",
        ),
        workdir=workdir,
        transcript="worker said things",
    )
    assert (out / "TASK.md").read_text(encoding="utf-8") == "the packet"
    assert (out / "transcript.txt").exists()
    records = list(load_records(rec.root))
    assert len(records) == 1
    assert records[0]["primary_failure"] == "pattern-mismatch"
    assert records[0]["lemma"] == "foo_spec"


def test_infrastructure_failures_are_not_blamed_on_the_worker() -> None:
    """A sandbox that cannot start looks exactly like a worker that said nothing.

    This rule exists because the first benchmark run misfiled a bubblewrap bug as a
    protocol violation, which points the reader at the prompt instead of the harness.
    """
    c = classify(
        "the worker produced no answer.json, no proof.v and no fenced proof block",
        None,
        None,
        "bwrap: Can't find source path /tmp/pcp-hosts-xyz: No such file or directory",
    )
    assert c.primary == "runner-error"
    assert "protocol-violation" in c.classes  # still recorded, just not primary


def test_a_genuine_protocol_violation_still_reads_as_one() -> None:
    c = classify(
        "the worker produced no answer.json, no proof.v and no fenced proof block",
        None, None, "I think the proof is left as an exercise.",
    )
    assert c.primary == "protocol-violation"


def test_transcript_tail_is_recorded_and_classified(tmp_path: Path) -> None:
    from pcp.orch.record import AttemptRecord, Recorder, load_records

    rec = Recorder(tmp_path, run_id="r")
    rec.write(
        AttemptRecord(run_id="r", node="n", lemma="l", attempt=1, runner="cli",
                      status="stuck", solved=False,
                      evidence="the worker produced no answer.json"),
        transcript="bwrap: execvp claude: No such file or directory",
    )
    record = list(load_records(rec.root))[0]
    assert record["primary_failure"] == "runner-error"
    assert "bwrap" in record["transcript_tail"]


def test_friction_is_counted_on_solved_lemmas_too() -> None:
    """The errors a worker recovered from are the cheapest wins available: the
    capability is there, the tooling is just charging turns for it."""
    report = summarize([
        {"lemma": "a", "solved": True, "trace": {
            "turns": 9, "check_iterations": 4,
            "errors": ["Error: fupd_mask_subseteq: ↑N ⊆ E is not provable",
                       "iOrDestruct: cannot destruct (P ∗ Q)%I"],
        }},
        {"lemma": "b", "solved": True, "trace": {"turns": 2, "check_iterations": 1, "errors": []}},
    ])
    assert report.solved == 2 and report.total == 2
    assert report.friction["mask-arithmetic"] == 1
    assert report.friction["pattern-mismatch"] == 1
    text = report.render()
    assert "2/2 solved" in text
    assert "friction" in text and "mask-arithmetic" in text
    assert "5.5 turns" in text  # (9 + 2) / 2


def test_stream_parsing_extracts_turns_tools_tokens_and_errors() -> None:
    import json as _json

    from pcp.orch.runners.stream import parse_stream

    events = [
        {"type": "system", "subtype": "init", "model": "m"},
        {"type": "assistant", "message": {"content": [
            {"type": "tool_use", "id": "a", "name": "Bash", "input": {"command": "pcp check"}}]}},
        {"type": "user", "message": {"content": [
            {"type": "tool_result", "tool_use_id": "a",
             "content": "gate: FAIL\nError: Unable to unify X with Y"}]}},
        {"type": "assistant", "message": {"content": [
            {"type": "tool_use", "id": "b", "name": "Edit", "input": {"file_path": "x.v"}}]}},
        {"type": "user", "message": {"content": [
            {"type": "tool_result", "tool_use_id": "b", "content": "edited"}]}},
        {"type": "result", "num_turns": 5, "duration_ms": 9000, "total_cost_usd": 0.12,
         "usage": {"input_tokens": 10, "output_tokens": 500, "cache_read_input_tokens": 40000}},
    ]
    trace = parse_stream("\n".join(_json.dumps(e) for e in events))
    assert trace.turns == 5
    assert trace.n_tool_calls == 2 and trace.check_iterations == 1
    assert trace.total_tokens == 510 and trace.dollars == 0.12
    assert trace.tool_histogram() == {"Bash": 1, "Edit": 1}
    assert len(trace.errors) == 1 and "Unable to unify" in trace.errors[0]
    # The failed check is marked; the successful edit is not.
    assert trace.tool_calls[0].ok is False and trace.tool_calls[1].ok is True


def test_stream_parsing_never_raises_on_junk() -> None:
    from pcp.orch.runners.stream import parse_stream

    for text in ("", "not json", '{"type":"assistant"}', '{"broken":', "{}\n[]\n"):
        parse_stream(text)


def test_classes_added_from_real_trace_evidence() -> None:
    """Each of these was a misclassification found by reading an actual run.

    `wp_bind: cannot find …` was filed under `retrieval`, which inflated that bucket
    and hid the mode the state layer's WP-expression field addresses directly; the
    others were `unclassified`.
    """
    cases = {
        "Tactic failure: wp_pure: cannot find ?y in": "evaluation-position",
        "Tactic failure: wp_bind: cannot find (! ?e)%E in": "evaluation-position",
        "Tactic failure: iModIntro: the goal is not a modality.": "later-modality",
        "(in proof f): Attempt to save an incomplete proof": "incomplete-proof",
        "This Bash command contains multiple operations. The following part requires approval: rm -f x":
            "permission-denied",
    }
    for text, expected in cases.items():
        assert classify(text).primary == expected, f"{text[:40]!r} -> {classify(text).render()}"


def test_a_real_lemma_name_failure_is_still_retrieval() -> None:
    """The new evaluation-position rule must not swallow genuine retrieval."""
    assert classify(
        "The variable map_seq_nil was not found in the current environment."
    ).primary == "retrieval"


def test_file_contents_a_worker_read_are_not_classified_as_failures() -> None:
    """One run classified a chunk of `gate.py` as a proof failure, because the
    worker had grepped it and the docstring contained the word Error."""
    from pcp.orch.failures import looks_like_an_error

    assert not looks_like_an_error('"""The integrity gate: deterministic (PLAN.md 8.7). No model."""')
    assert not looks_like_an_error("   42:  Lemma foo : True.")
    assert looks_like_an_error("Error: The reference foo was not found")
    assert classify('"""The integrity gate (PLAN.md 8.7)."""').primary == "unclassified"


def test_multiline_rocq_errors_are_kept_whole() -> None:
    """`Error: In environment Σ : gFunctors` continues onto following lines; cutting
    at the first newline threw away the part that says what went wrong."""
    import json as _json

    from pcp.orch.runners.stream import parse_stream

    body = "Error: In environment\n  Σ : gFunctors\n  P : iProp Σ\nUnable to unify \"P\" with \"Q\"."
    events = [
        {"type": "assistant", "message": {"content": [
            {"type": "tool_use", "id": "a", "name": "Bash", "input": {"command": "pcp check"}}]}},
        {"type": "user", "message": {"content": [
            {"type": "tool_result", "tool_use_id": "a", "content": body}]}},
    ]
    trace = parse_stream("\n".join(_json.dumps(e) for e in events))
    assert len(trace.errors) == 1
    # Kept whole *across lines* -- that is what this test is for. The environment
    # dump itself is deliberately collapsed (`collapse_environment`): on a real Iris
    # goal it runs past the capture limit and pushes the complaint out of the record,
    # which is how 53 errors in one run became `In environment Σ : gFunctors`.
    assert "Unable to unify" in trace.errors[0]
    assert "In environment [...]" in trace.errors[0]
    assert "gFunctors" not in trace.errors[0]


def test_tactic_failures_are_captured_even_without_the_word_error() -> None:
    import json as _json

    from pcp.orch.runners.stream import parse_stream

    events = [
        {"type": "assistant", "message": {"content": [
            {"type": "tool_use", "id": "a", "name": "Bash", "input": {"command": "coqc x.v"}}]}},
        {"type": "user", "message": {"content": [
            {"type": "tool_result", "tool_use_id": "a",
             "content": "Tactic failure: wp_bind: cannot find (! ?e)%E in."}]}},
    ]
    trace = parse_stream("\n".join(_json.dumps(e) for e in events))
    assert trace.errors and "wp_bind" in trace.errors[0]
    assert trace.tool_calls[0].ok is False


def test_a_transcript_cannot_re_diagnose_a_definite_verdict() -> None:
    """The decomposer's parser rejects on shape, and that verdict is final.

    A real round died on `each definition must be an object` -- the design was
    returned as a list of strings instead of objects. It was filed as
    `mask-arithmetic`, because the *transcript* held a lemma the decomposer had
    proposed, and Iris statements are full of `↑N` and `∖ ↑`. So the work queue said
    "build mask tooling" about a run that failed on a pair of braces, and quoted the
    decomposer's own writing back as evidence of a proof failure.
    """
    c = classify(
        "each definition must be an object",
        None, None,
        status="error",
        context=(
            '"statement": "Lemma write_au_commit (γ : gname) (m n : Z) (Q : iProp Σ) :\\n'
            '  own γ (●E m) -∗ write_au γ n Q ={⊤ ∖ ↑rwcasN}=∗ own γ (●E n) ∗ Q."'
        ),
    )
    assert c.primary == "protocol-violation", c.render()
    assert "mask-arithmetic" not in c.classes
    assert "each definition must be an object" in c.findings[0].evidence


def test_the_harness_failing_under_a_worker_still_shows_through_the_transcript() -> None:
    """The counterweight: a transcript may not re-diagnose the proof, but it must
    still be able to say the sandbox never started. That is the one thing evidence
    cannot know, and blaming the worker sends you to debug the prompt."""
    c = classify(
        "the worker produced no answer.json",
        None, None,
        context="bwrap: execvp claude: No such file or directory",
    )
    assert c.primary == "runner-error", c.render()
    assert "protocol-violation" in c.classes


def test_with_no_evidence_the_transcript_is_all_there_is() -> None:
    c = classify("", None, None, context="Error: Unable to unify the two terms")
    assert c.primary == "unification-failure", c.render()


def test_a_decomposer_killed_at_its_deadline_reads_as_a_deadline() -> None:
    """Not as a protocol violation.

    The runner reports the kill correctly; the decomposer used to discard that and
    parse the empty output instead, so a round that ran out of clock was recorded as
    "the decomposer produced no JSON object to read". That reads as a model ignoring
    the protocol and sends you to rewrite the prompt, when the fix is a bigger
    budget -- observed rounds ran 892.8s, 895.5s and 900.1s against a 900s ceiling.
    """
    c = classify("worker exceeded its 900s deadline and was killed", status="error")
    assert c.primary == "deadline", c.render()


def test_harness_chatter_does_not_split_one_error_into_two() -> None:
    """`Shell cwd was reset to <path>` is the worker's own harness, not Rocq.

    Appended to whatever Rocq last said, it made the same failure record twice --
    once clean, once with a path glued on -- so a friction count of 20 was really 13,
    and the trailing absolute path pushed the polluted copy into `unclassified`.
    """
    from pcp.orch.runners.stream import _first_error

    detail = _first_error(
        "Error: The variable n1 was not found in the current environment.\n"
        "Shell cwd was reset to /home/zkent/proof-copilot/.pcp/work/run/write_spec"
    )
    assert detail == "The variable n1 was not found in the current environment."
    assert "Shell cwd" not in detail


def test_reading_the_classifier_is_not_a_proof_failure() -> None:
    """`pcp/orch/failures.py` is full of the literal `Error:` its own patterns match.

    A worker grepped it and the hit was recorded as a proof failure -- the guard's
    docstring already tells this story about `gate.py`, and the anchor it used
    (`^\\s*\\d+[:\\t]`) missed a grep hit reported as `in line: 545 ...` mid-string.
    """
    assert not looks_like_an_error(
        '" in line: 545 return " ".join(l.strip() for l in lines[max(0, i - 1) : i + 3])[:400] '
        "546 return _tail(output, 3)[:400]"
    )


def test_a_directory_listing_is_not_a_proof_failure() -> None:
    """One rwcas run filed 36 of these; they crowd out the report they appear in."""
    from pcp.orch.failures import looks_like_an_error

    assert not looks_like_an_error("Exit code 1 _CoqProject M8f1e46.v pcp-node.json TASK.md")
    assert not looks_like_an_error("Exit code 1\n")
    # ... and a real failure still reads as one.
    assert looks_like_an_error("iMod: cannot eliminate modality (▷ x13_inv γ n requests)%I")
    assert looks_like_an_error(
        'File "./M8f1e46.v", line 12, characters 2-29:\nError: Tactic failure: iAndDestruct.')


def test_the_report_filters_noise_from_records_written_before_the_guard() -> None:
    """A capture-time guard cannot clean up records that already exist."""
    from pcp.orch.failures import summarize

    report = summarize([
        {"lemma": "a", "solved": True, "trace": {"errors": [
            "Exit code 1 _CoqProject M8f1e46.v pcp-node.json TASK.md",
            "iMod: cannot eliminate modality (▷ inv)%I",
        ]}},
    ])
    assert sum(report.friction.values()) == 1
    assert "unclassified" not in report.friction or report.friction["unclassified"] == 0


def test_the_state_tools_own_output_is_decoded_before_classifying() -> None:
    """`\\u25b7` matched no rule, so the tools' output was invisible to the report."""
    from pcp.orch.failures import summarize, unescape

    raw = r"iMod: cannot eliminate modality (\u25b7 x13_inv \u03b3 n)%I in (WP ! #l @ \u22a4 \u2216 \u2191bb6"
    assert "▷" in unescape(raw)

    report = summarize([{"lemma": "a", "solved": True, "trace": {"errors": [raw]}}])
    assert report.friction["unclassified"] == 0, dict(report.friction)


def test_unescaping_leaves_an_unescaped_string_untouched() -> None:
    from pcp.orch.failures import unescape

    for text in ("iFrame: cannot frame (Φ #()).", "", "a ∗ b -∗ c", "C:\\path"):
        assert unescape(text) == text or "\\" in text


def test_the_environment_dump_does_not_eat_the_complaint() -> None:
    """Rocq prints every binder in scope before saying what is wrong.

    53 errors in one run were recorded as the fragment `In environment Σ : gFunctors`
    because the dump ran past the capture limit and the verb was cut off.
    """
    from pcp.orch.failures import classify, collapse_environment

    binders = "\n".join(f"H{i} : long_hypothesis_type_{i} γ ver" for i in range(40))
    raw = (f'In environment\nΣ : gFunctors\nver : nat\n{binders}\n'
           'The term "Z.of_nat ver" has type "Z" while it is expected to have type "nat".')
    assert len(raw) > 600

    collapsed = collapse_environment(raw)
    assert "Z.of_nat ver" in collapsed[:200], "the complaint must survive the cap"
    assert classify(collapsed).primary == "scope-or-type-error"


def test_an_error_without_a_complaint_marker_is_left_whole() -> None:
    """Collapsing on a guess would destroy information; only splice what is matched."""
    from pcp.orch.failures import collapse_environment

    for text in ("In environment\nΣ : gFunctors\n", "iFrame: cannot frame (Φ #()).", ""):
        assert collapse_environment(text) == text


def test_the_capture_path_collapses_before_truncating() -> None:
    """Collapsing after the cap would be too late -- the dump is what causes the cap."""
    from pcp.orch.runners.stream import _first_error

    binders = "\n".join(f"H{i} : long_hypothesis_type_{i} γ ver" for i in range(60))
    text = (f'Error: In environment\nΣ : gFunctors\n{binders}\n'
            'The term "Z.of_nat ver" has type "Z" while it is expected to have type "nat".\n\n')
    assert "Z.of_nat ver" in _first_error(text)


def test_iSpecialize_failures_are_their_own_class() -> None:
    from pcp.orch.failures import classify

    assert classify("iSpecialize: hypotheses [\"Hlb0\"] not found.").primary == "specialization"
    assert classify(
        "iSpecialize: cannot instantiate (ghost_var γ (1/2+1/2) false -∗ P)%I"
    ).primary == "specialization"


def test_a_failing_state_tool_is_not_a_failing_proof() -> None:
    """13 `proof_open` failures in one run were the poisoned file, not the lemmas.

    Worth its own class precisely because the state layer is the thing being ablated:
    counting its outages as proof failures makes it look worse than it is.
    """
    from pcp.orch.failures import classify

    assert classify("Error executing tool proof_open").primary == "state-tool-error"
    assert classify("Error executing tool mcp__pcp__proof_step").primary == "state-tool-error"


def test_focus_and_bullet_errors_are_classified() -> None:
    from pcp.orch.failures import classify

    assert classify(
        "This proof is focused, but cannot be unfocused this way"
    ).primary == "focus-or-bullet"


def test_the_permission_rule_matches_the_wording_the_cli_actually_uses() -> None:
    """The rule was written against wording the CLI does not use, so it never fired."""
    from pcp.orch.failures import classify

    assert classify(
        "ls in '/home/zkent/proof-copilot' was blocked. For security, ..."
    ).primary == "permission-denied"
    assert classify(
        "This Bash command contains multiple operations. The following part requires approval: ls -la"
    ).primary == "permission-denied"


def test_the_taxonomy_does_not_classify_our_own_diagnosis() -> None:
    """`pcp check` appends a diagnosis that names modalities, masks and tactics.

    Classifying it labels the failure with our diagnostic vocabulary instead of the
    compiler's: an `iIntro` failure was measured becoming `mask-arithmetic` purely
    because the attached diagnosis mentioned a mask. Same principle as the guard that
    stops a worker grepping `failures.py` from teaching the classifier.
    """
    from pcp.orch.failures import classify, strip_our_own_diagnosis

    err = 'iIntro: could not introduce "Hmn", goal is not a wand or implication.'
    polluted = err + ('", "diagnosis": "Coq: Tactic failure: iIntro. '
                      'current modality: ⊤ ∖ ↑N. tactics that apply: iSplitL"')
    assert classify(strip_our_own_diagnosis(polluted)).primary != "mask-arithmetic"
    assert "iIntro" in strip_our_own_diagnosis(polluted)


def test_a_real_mask_failure_still_classifies_after_stripping() -> None:
    from pcp.orch.failures import classify, strip_our_own_diagnosis

    real = "iMod: cannot eliminate modality. mask ↑N ⊆ ⊤ ∖ ↑N does not hold"
    assert classify(strip_our_own_diagnosis(real)).primary == "mask-arithmetic"


def test_a_throwing_trace_parser_does_not_lose_the_proof() -> None:
    """The docstring claimed this; it was not true, and it cost two live rungs.

    Unknown *events* were skipped, but an exception inside a handler propagated out
    of `run_node` and killed the run. The trace is a diagnostic; the proof is in the
    answer. Losing the record of how a proof was reached must not lose the proof.
    """
    import json as _json

    from pcp.orch.runners import stream

    events = [
        {"type": "assistant", "message": {"content": [
            {"type": "tool_use", "id": "a", "name": "Bash", "input": {"command": "pcp check"}}]}},
        {"type": "user", "message": {"content": [
            {"type": "tool_result", "tool_use_id": "a", "content": "Error: boom\n\n"}]}},
        {"type": "result", "num_turns": 7, "result": "done"},
    ]
    raw = "\n".join(_json.dumps(e) for e in events)

    original = stream._read_tool_results
    try:
        stream._read_tool_results = lambda *a, **k: (_ for _ in ()).throw(ImportError("gone"))
        trace = stream.parse_stream(raw)
    finally:
        stream._read_tool_results = original

    assert trace.turns == 7, "the rest of the trace must still be read"
    assert trace.final_text == "done"
    assert any("ImportError" in e for e in trace.parse_errors)
