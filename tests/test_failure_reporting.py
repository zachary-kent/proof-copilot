"""Failure reporting without Rocq: error shaping, the prefix check's parsing, trace
failure locations, hidden-printer marks (issues 4, 10, 11, 14, 15).

Every test pins one way the old reports misled: a head-only cut that dropped the
cause, a start failure that named the lemma instead of the broken ``Require``, a
trace failure without its sentence, a ``nat``-looking equality that was a ``Z`` one.
"""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace

import pytest

from pcp.rocq import errors as rerrors
from pcp.rocq.errors import (
    ELISION,
    PrefixCheck,
    _first_error,
    _running_sentence,
    check_text,
    collapse_environment,
    shape_error,
)
from pcp.state.ipm.model import Hyp, IrisGoal, Step
from pcp.state.petanque import PetProcess, StartFailed
from pcp.state.printing import GoalHidden, Hidden, compare, compare_goals
from pcp.state.render import render_goal
from pcp.state.trace import Trace, explain_start_failure, proof_script

# ----------------------------------------------------------- issue 14: shaping

#: The shape from the issue: a statement whose `[#h1; …]` lexed as `[#`, a 30-line
#: binder dump, and the cause last.
ENV_LINES = [f"x{i} : loc" for i in range(26)] + ["c : loc", "h1, h2 : val", "et : val", "Φ : val → iProp Σ"]
ISSUE_14 = (
    "Theorem_not_found: [find_thm] Theorem found but failed with Coq error:\n In environment\n"
    + "\n".join(f" {line}" for line in ENV_LINES)
    + '\n The term "[# h1; # h2; et]" has type "vec val 2" while it is expected to have type "vec loc ?n".!'
)


def test_shape_error_keeps_the_cause_of_the_issue_14_error() -> None:
    assert len(ENV_LINES) == 30
    shaped = shape_error(ISSUE_14, 500)
    assert len(shaped) <= 500
    assert "has type \"vec val 2\" while it is expected to have type \"vec loc ?n\"" in shaped
    assert shaped.startswith("Theorem_not_found") and "In environment [...]" in shaped
    assert "x13 : loc" not in shaped
    # The old cut: the cause is exactly what a head-only truncation drops.
    assert "vec loc ?n" not in ISSUE_14[:500]


def test_shape_error_elides_the_middle_when_there_is_no_dump() -> None:
    text = "Error: " + " ".join(f"w{i}" for i in range(400)) + " THE CAUSE."
    shaped = shape_error(text, 200)
    assert len(shaped) <= 200 and ELISION in shaped
    assert shaped.startswith("Error: w0") and shaped.endswith("THE CAUSE.")
    assert shape_error("short", 200) == "short"
    assert shape_error(None) == ""


def test_short_errors_keep_their_environment() -> None:
    text = 'In environment\nx : nat\nThe term "x" has type "nat" while it is expected to have type "Z".'
    assert shape_error(text) == text
    assert collapse_environment(text).startswith("In environment [...] The term")


def test_petanque_translation_keeps_the_tail(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """`petanque `start` failed: … In environment <30 lines> Φ :` -- and stopped there."""
    proc = PetProcess(tmp_path)
    monkeypatch.setattr(proc, "alive", lambda: True)
    for message in (ISSUE_14, ISSUE_14.replace(" In environment\n", " In environment\n" + " y : nat\n" * 400)):
        err = str(proc._translate(SimpleNamespace(code=-32004, message=message), "start"))  # type: ignore[arg-type]
        assert err.endswith('expected to have type "vec loc ?n".!') and len(err) < 1600


def test_orch_uses_the_same_binder_dump_rule() -> None:
    from pcp.orch import failures

    assert failures.collapse_environment is collapse_environment


# ------------------------------------------------ issue 4 / 10: prefix check

SOURCE = """From Stdlib Require Import ZArith.

Lemma first : True.
Proof.
  exact I.
  (* a long
     proof *)
Qed.

Section S.
  Context (n : nat).
  From co Require Import Missing.

  Lemma target : n = n.
  Proof. reflexivity. Qed.
End S.
"""


def test_check_text_preserves_lines_admits_proofs_and_closes_scopes() -> None:
    built = check_text(SOURCE, "target")
    assert built is not None
    text, at = built
    src_lines, out_lines = SOURCE.splitlines(), text.splitlines()
    for n in (1, 3, 4, 10, 12, 14):  # every non-proof line keeps its number
        assert out_lines[n - 1] == src_lines[n - 1], n
    assert "exact I" not in text and out_lines[7].strip() == "Admitted."
    assert "reflexivity" not in text and text.rstrip().endswith("Admitted.\nEnd S.")
    assert SOURCE[at:].startswith("Lemma target")
    assert check_text(SOURCE, "nope") is None


def test_first_error_skips_warnings_and_timing_lines() -> None:
    output = (
        "Chars 0 - 34 [From~Stdlib~Require~Import~ZArith.] 0.1 secs (0.u,0.s)\n"
        'File "./x_pcpcheck.v", line 3, characters 0-5:\nWarning: something harmless [w,default]\n'
        'File "./x_pcpcheck.v", line 12, characters 25-32:\n'
        "Error:\nCompiled library smr.lang (in file /p/lang.vo) makes inconsistent assumptions\n"
        "over library Corelib.Init.Prelude\n"
    )
    line, char, message = _first_error(output) or (0, 0, "")
    assert (line, char) == (12, 25)
    assert message == (
        "Compiled library smr.lang (in file /p/lang.vo) makes inconsistent assumptions over library Corelib.Init.Prelude"
    )


def test_running_sentence_is_the_one_after_the_last_timed() -> None:
    text = "Definition a := 1.\nLemma b : True.\nProof. exact I. Defined.\nDefinition slow := 0.\n"
    timings = "Chars 0 - 18 [Definition~a~:=~1.] 0. secs\nChars 19 - 34 [Lemma~b~:~True.] 0. secs\n"
    line, col, sent = _running_sentence(text, timings) or (0, 0, "")
    assert (line, col, sent) == (3, 1, "Proof.")
    assert _running_sentence(text, "")[:2] == (1, 1)  # nothing finished: the first sentence


def test_prefix_check_renders_each_cause() -> None:
    base = {"thm": "t", "file": "theories/x.v"}
    req = PrefixCheck(ok=False, line=12, sentence="From smr Require Import lang.", message="makes inconsistent assumptions", **base)
    assert req.render() == (
        "the document does not check before t: theories/x.v:12 `From smr Require Import lang.`: makes inconsistent assumptions"
    )
    stmt = PrefixCheck(ok=False, line=14, in_statement=True, message="The term …", **base)
    assert stmt.render().startswith("the statement of t does not elaborate: theories/x.v:14")
    slow = PrefixCheck(ok=False, timed_out=True, budget_s=20, elapsed_s=21, line=4, sentence="iFrame.", **base)
    assert slow.render() == "the statements up to t do not check within 20 s; coqc was still checking theories/x.v:4 `iFrame.` after 21 s"
    assert PrefixCheck(ok=True, **base).render() == ""


def _failed(**kw) -> StartFailed:
    defaults = {"thm": "t", "file": "/p/x.v", "detail": "Theorem_not_found: [find_thm] Theorem not found!"}
    defaults.update(kw)
    return StartFailed("petanque could not open t in /p/x.v: " + defaults["detail"], **defaults)


def test_explain_start_failure_puts_the_cause_first_and_keeps_petanques_words(monkeypatch) -> None:
    check = PrefixCheck(thm="t", file="x.v", ok=False, line=2, sentence="From co Require Import M.", message="Unable to locate library M")
    monkeypatch.setattr("pcp.state.trace.check_prefix", lambda *a, **k: check)
    out = explain_start_failure(_failed(), "/p/x.v")
    assert isinstance(out, StartFailed)
    first, second = str(out).split("\n")
    assert first == "the document does not check before t: x.v:2 `From co Require Import M.`: Unable to locate library M"
    assert "petanque said: Theorem_not_found" in second

    monkeypatch.setattr("pcp.state.trace.check_prefix", lambda *a, **k: None)
    assert str(explain_start_failure(_failed(), "/p/x.v")).startswith("x.v declares no `t`")


def test_a_start_timeout_says_the_document_does_not_check_up_to_the_lemma(monkeypatch) -> None:
    seen = {}

    def fake(*a, **k):
        seen.update(k)
        return PrefixCheck(thm="t", file="x.v", ok=False, timed_out=True, budget_s=k["timeout"], elapsed_s=21, line=4, sentence="iFrame.")

    monkeypatch.setattr("pcp.state.trace.check_prefix", fake)
    exc = StartFailed("the document does not check up to t within 300 s (/p/x.v; petanque was killed and restarts on the next call)",
                      thm="t", file="/p/x.v", detail="wall clock", timed_out=True, budget_s=300)
    out = explain_start_failure(exc, "/p/x.v", timeout=20)
    assert str(out).startswith("the document does not check up to t within 300 s")
    assert "coqc was still checking x.v:4 `iFrame.`" in str(out) and out.timed_out
    assert seen["timeout"] == 20  # the diagnosis is bounded well below start's own budget


# ------------------------------------------------------- issue 11: trace failure


PROOF = """Lemma l : True /\\ True.
Proof.
  split.
  - exact I.
  - (* the culprit *) exact Q.
Qed.
"""


def test_proof_script_places_every_sentence_in_the_file() -> None:
    tactics, places = proof_script(PROOF, "l") or ([], [])
    assert tactics == ["split.", "-", "exact I.", "-", "exact Q."]
    assert [(p.line, p.column) for p in places] == [(3, 3), (4, 3), (4, 5), (5, 3), (5, 23)]
    assert proof_script(PROOF, "missing") is None


def test_trace_failure_names_step_sentence_and_place_and_survives_jsonl() -> None:
    trace = Trace(file="/p/x.v", thm="l")
    trace.steps = [
        Step(step=0, state_id=1, tactic="<start>", goals=[]),
        Step(step=1, state_id=2, tactic="split.", goals=[]),
        Step(step=2, state_id=-1, tactic="exact Q.", goals=[], ok=False, error="The reference Q was not found"),
    ]
    trace.error, trace.failed_at, trace.failed_line, trace.failed_column = "The reference Q was not found", 2, 5, 23
    assert trace.failure() == {"step": 2, "sentence": "exact Q.", "error": "The reference Q was not found", "line": 5, "column": 23}
    assert trace.failure_note() == "stopped at step 2 (x.v:5:23) `exact Q.`: The reference Q was not found"
    again = Trace.loads(trace.dumps())
    assert (again.failed_at, again.failed_line, again.failed_column) == (2, 5, 23)
    assert Trace(file="/p/x.v", thm="l").failure() is None


# ----------------------------------------------------- issue 15: hidden printing


def test_compare_finds_the_hidden_z_of_nat_of_the_issue() -> None:
    hidden = compare("sq2 = e_seq e", "Z.of_nat sq2 =@{ Z} Z.of_nat (e_seq e)",
                     "@Z.of_nat sq2 =@{ Z} Z.of_nat (@e_seq nat e)")
    assert hidden.coercions == ("Z.of_nat",) and hidden.carriers == ("Z",)
    assert hidden.explicit == "Z.of_nat sq2 =@{Z} Z.of_nat (e_seq e)"
    assert hidden.implicit is not None and "@e_seq nat e" in hidden.implicit


def test_structure_carriers_and_heap_lang_injections_are_not_marked() -> None:
    assert not compare("PROP", "bi_car PROP", "bi_car PROP")
    assert not compare("WP #l {{ v, True }}", "WP Val (LitV (LitLoc l)) {{ v, True }}").coercions
    plain_eq = compare("length l = 2", "length l =@{ nat} 2", "@length nat l =@{ nat} 2")
    assert plain_eq.carriers == ("nat",) and not plain_eq.coercions and plain_eq.implicit


def _goal(heq: str) -> IrisGoal:
    return IrisGoal(
        goal="True",
        pure=[Hyp("sq2", "nat", klass="pure"), Hyp("Heq", heq, klass="pure")],
        spatial=[Hyp("HP", "P")],
    )


def test_compare_goals_aligns_by_class_and_id() -> None:
    plain = [_goal("sq2 = e_seq e")]
    coerced = [_goal("Z.of_nat sq2 =@{ Z} Z.of_nat (e_seq e)")]
    (hidden,) = compare_goals(plain, coerced, None)
    assert set(hidden.hyps) == {"pure:Heq"} and hidden.goal is None


def test_render_marks_the_hidden_coercion_and_keeps_diff_and_select_working() -> None:
    goal = _goal("sq2 = e_seq e")
    detail = Hidden(coercions=("Z.of_nat",), explicit="Z.of_nat sq2 =@{Z} Z.of_nat (e_seq e)", carriers=("Z",),
                    implicit="Z.of_nat sq2 =@{Z} Z.of_nat (@e_seq nat e)")
    hidden = GoalHidden(hyps={"pure:Heq": detail})
    text = render_goal(goal, hidden=hidden).text
    assert '"Heq" : sq2 = e_seq e   [= at Z]' in text
    assert "↳ with coercions (Z.of_nat): Z.of_nat sq2 =@{Z} Z.of_nat (e_seq e)" in text
    assert "implicit arguments" not in text  # noise unless asked for
    selected = render_goal(goal, hidden=hidden, select="Heq").text
    assert "↳ with implicit arguments: Z.of_nat sq2 =@{Z} Z.of_nat (@e_seq nat e)" in selected
    assert "HP" not in selected.split("…")[0]
    diffed = render_goal(goal, hidden=hidden, diff_only=True, prev=goal)
    assert "Heq=unchanged" in diffed.text and "↳" not in diffed.text
    assert "↳" not in render_goal(goal, hidden=hidden, mode="summary").text
    assert rerrors.DEFAULT_ERROR_CHARS > 500
