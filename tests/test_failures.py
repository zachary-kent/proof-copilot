"""pcp.orch.failures: the taxonomy and the one classifier."""

from __future__ import annotations

import pytest

from pcp.orch.failures import (
    TAXONOMY,
    Classification,
    FailureReport,
    classify,
    classify_record,
    collapse_environment,
    looks_like_an_error,
    summarize,
    unescape,
)

POSITIVE = {
    "premature-consumption": 'Error: iDestruct: "HP" not found in the context',
    "leftover-spatial": "Error: iFrame: cannot frame; spatial context is not empty",
    "mask-arithmetic": "Error: fupd_mask_subseteq: ↑N ⊆ E does not hold",
    "later-modality": "Error: iNext: no later modality to strip",
    "persistent-vs-spatial": 'Error: "HP" is not persistent',
    "retrieval": "Error: The reference ghost_varG was not found in the current environment.",
    "context-pollution": "prompt is too long: context window exceeded",
    "pattern-mismatch": 'Error: iDestruct: cannot destruct "HP": not a disjunction',
    "evaluation-position": "Error: wp_bind: cannot find (! #l) in (let: ...)",
    "incomplete-proof": "Error: Attempt to save an incomplete proof",
    "permission-denied": "This command requires approval before it can run",
    "unification-failure": 'Error: Unable to unify "nat" with "Z".',
    "prophecy-atomicity": "Error: atomic_update: cannot commit without AU",
    "no-progress": "the worker showed no progress for 3 checks; loop detected",
    "deadline": "worker exceeded its 900s deadline and was killed",
    "gate-violation": "gate: FAIL (0.1s)\n  [FAIL] no new Admitted / admit / Axiom / Parameter: c: forbidden tactic `admit`",
    "protocol-violation": "the worker produced no answer.json, no proof.v and no fenced proof block",
    "scope-or-type-error": 'Error: The term "1" has type "nat" while it is expected to have type "Z".',
    "state-tool-error": "Error executing tool mcp__pcp__proof_open: the file does not compile",
    "focus-or-bullet": "Error: Wrong bullet -: Current bullet + is not finished.",
    "specialization": 'Error: iSpecialize: cannot instantiate (H with "HP")',
    "runner-error": "claude: command not found",
}


@pytest.mark.parametrize("klass", sorted(POSITIVE))
def test_every_regex_class_has_a_positive_example(klass):
    assert classify(POSITIVE[klass]).primary == klass


def test_taxonomy_is_exactly_the_contracts_24_classes():
    assert set(POSITIVE) | {"contested", "unclassified"} == set(TAXONOMY)
    assert list(TAXONOMY)[:7] == ["premature-consumption", "leftover-spatial", "mask-arithmetic", "later-modality",
                                  "persistent-vs-spatial", "retrieval", "context-pollution"]


def test_contested_and_unclassified_by_construction():
    assert classify("anything", status="contested").classes == ["contested"]
    assert classify("").primary == "unclassified"
    assert classify("some prose nobody can place here").primary == "unclassified"


def test_line_401_is_not_a_runner_error():
    c = classify('File "./M.v", line 401, characters 4-10:\nError: Unable to unify "nat" with "Z".')
    assert c.primary == "unification-failure" and "runner-error" not in c.classes
    assert classify("Error: characters 401-410: The reference x was not found in the current environment").primary == "retrieval"
    assert classify("HTTP 401 Unauthorized from the provider").primary == "runner-error"


def test_unresolved_implicit_is_not_prophecy_atomicity():
    c = classify("The following term contains unresolved implicit arguments")
    assert "prophecy-atomicity" not in c.classes
    assert "prophecy-atomicity" not in classify("Error: iApply failed au niveau").classes


def test_passing_gate_report_is_not_a_gate_violation():
    report = (
        "gate: FAIL (1.2s)\n  [ok ] no new Admitted / admit / Axiom / Parameter\n  [ok ] no escape hatches\n"
        "  [ok ] ambient-state hygiene (no global Instance/Hint/Notation/Ltac)\n  [ok ] statement pinning by construction\n"
        "  [FAIL] compiles (coqc): Error: The reference ghost_varG was not found in the current environment."
    )
    c = classify(report)
    assert c.primary == "retrieval" and "gate-violation" not in c.classes
    failing = report + "\n  [FAIL] axiom hygiene (Print Assumptions ⊆ whitelist + open stubs): x: classic"
    assert "gate-violation" in classify(failing).classes


def test_permission_denied_on_rm_is_not_infrastructure():
    c = classify("gate: FAIL\n  [FAIL] compiles (coqc): Error: Unable to unify a with b", context="rm: cannot remove: Permission denied")
    assert c.primary == "unification-failure"


def test_exit_code_and_error_status_are_first_class():
    assert classify("", exit_code=1).primary == "runner-error"
    assert classify("the worker produced no answer.json, no proof.v and no fenced proof block", exit_code=2).primary == "runner-error"
    assert classify("Error: Unable to unify a with b", exit_code=1).primary == "unification-failure"
    assert classify("something odd", is_error=True).primary == "runner-error"
    assert classify("something odd", status="error").primary == "runner-error"


def test_gate_infrastructure_is_runner_error_never_deadline():
    text = "gate: FAIL (600.0s)\n  [FAIL] compiles (coqc): gate could not run: coqc timed out after 600s"
    c = classify(text, infrastructure=True)
    assert c.primary == "runner-error" and "deadline" not in c.classes
    assert classify(text).primary == "runner-error"
    assert classify("Error: Timeout!").primary != "deadline"


def test_transcript_may_only_establish_harness_failures():
    evidence = "Error: iNext: no later modality to strip"
    c = classify(evidence, context="I tried the mask arithmetic for the invariant masks")
    assert c.primary == "later-modality"
    c = classify(evidence, context="bwrap: execvp claude: No such file or directory")
    assert c.primary == "runner-error"
    c = classify("", context="Error: iFrame: cannot frame; spatial context is not empty")
    assert c.primary == "leftover-spatial"


def test_unescape_decodes_json_but_leaves_rocq_disjunction():
    assert unescape("A \\/ B") == "A \\/ B"
    assert unescape('iMod: \\u25b7 inv \\"x\\"') == 'iMod: ▷ inv "x"'
    assert unescape("\\\\u2217 twice") == "∗ twice"
    assert classify("iMod: cannot eliminate modality \\u25b7 inv").primary == "later-modality"


def test_collapse_environment_keeps_the_complaint():
    text = 'In environment\nΣ : gFunctors\nx : nat\nThe term "1" has type "nat" while it is expected to have type "Z".'
    assert collapse_environment(text).startswith("In environment [...] The term")
    assert classify(text).primary == "scope-or-type-error"


def test_looks_like_an_error_guards():
    assert looks_like_an_error("# Where I got stuck\niFrame: cannot frame it")
    assert classify("# Where I got stuck\nError: iFrame: cannot frame; spatial context is not empty").primary == "leftover-spatial"
    assert not looks_like_an_error("Exit code 1\n_CoqProject TASK.md answer.json Dev.v")
    assert not looks_like_an_error('def foo(x):\n    """doc"""\n    Error handling here')
    assert not looks_like_an_error("ab")


def test_syntax_error_falls_back_to_protocol_violation():
    assert classify("Syntax error: '.' expected after [command]").primary == "protocol-violation"
    assert classify("recovered a partial proof from the worker's edited file; it wrote no answer.json").primary == "protocol-violation"


def test_classification_helpers():
    c = classify("Error: Unable to unify a with b")
    assert c.render() == "unification-failure" and c.to_json()["primary"] == "unification-failure"
    assert Classification().primary == "unclassified" and Classification().render() == "unclassified"


def _record(**kw):
    base = {"lemma": "x", "attempt": 1, "status": "stuck", "solved": False, "evidence": "", "gate_report": "",
            "compile_output": "", "transcript_tail": "", "trace": {}, "gate_checks": [], "exit_code": None}
    base.update(kw)
    return base


def test_summarize_agrees_with_classify_record():
    records = [
        _record(evidence="Error: iNext: no later modality", transcript_tail="mask mask mask"),
        _record(lemma="y", evidence="", gate_report="gate: FAIL\n  [FAIL] compiles (coqc): Error: Unable to unify a with b",
                transcript_tail="Error: iOrDestruct: cannot destruct"),
        _record(lemma="z", status="error", evidence="claude exited 1", exit_code=1),
        _record(lemma="w", solved=True, status="qed", trace={"turns": 4, "check_iterations": 2, "errors": ["Error: iFrame: cannot frame; spatial context is not empty"]}),
        _record(lemma="t", gate_checks=[{"name": "compiles (coqc)", "ok": False, "detail": "gate could not run: no coqc on PATH"}],
                evidence="gate: FAIL\n  [FAIL] compiles (coqc): gate could not run: no coqc on PATH"),
    ]
    report = summarize(records)
    assert report.total == 5 and report.solved == 1
    for rec in records:
        if rec["solved"]:
            continue
        assert report.primary[classify_record(rec).primary] >= 1
    assert report.primary["later-modality"] == 1 and report.primary["unification-failure"] == 1
    assert report.primary["runner-error"] == 2 and report.friction["leftover-spatial"] == 1
    assert report.turns == [4] and report.checks == [2]
    text = report.render()
    assert text.startswith("1/5 solved · 4 failed") and "failures, by primary class:" in text and "friction --" in text
    assert report.to_json() == {"total": 5, "solved": 1, "primary": dict(report.primary), "all_classes": dict(report.all_classes)}


def test_empty_report_renders_nothing_to_report():
    assert "nothing to report" in FailureReport().render()


def test_a_protocol_violation_recorded_with_status_error_stays_a_protocol_violation():
    c = classify("the decomposer produced no JSON object to read", status="error")
    assert c.classes[:2] == ["protocol-violation", "runner-error"]
    c = classify("each definition must be an object", status="error")
    assert c.primary == "protocol-violation"
    c = classify("claude exited with status 1 and wrote no answer: 401 OAuth access token has been revoked", status="error", exit_code=1)
    assert c.primary == "runner-error"
    assert classify("worker exceeded its 1800s deadline and was killed", status="error").primary == "runner-error"
