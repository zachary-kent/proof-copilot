"""The approver (pcp.orch.decomposer adjudication), the definition-taint helpers
(pcp.orch.amend) and the approver's runner wiring (pcp.cli.runners / main)."""

from __future__ import annotations

import argparse
import asyncio
import json

import pytest

from pcp.cli.main import build_parser
from pcp.cli.runners import select_approver
from pcp.config.schema import Config
from pcp.errors import ProtocolError
from pcp.orch.amend import AMENDED_MARKER, mentions_definition, reopen_for_amendment, statement_invalidated
from pcp.orch.contract import DesignContract
from pcp.orch.decomposer import (
    Decomposer,
    ProofEngineeringAttempt,
    Verdict,
    assert_statement_only,
    parse_verdict,
    render_amendment_adjudication,
    render_contest_adjudication,
)
from pcp.orch.model import node_id
from pcp.orch.protocol import AmendmentRequest, NodeResult
from pcp.rocq.assemble import Development
from tests._orch_fixtures import build_plain_graph

IRIS_SOURCE = """From iris.base_logic Require Import lib.own.
Definition I (γ : gname) : iProp Σ := (∃ n, own γ n)%I.
Definition J (γ : gname) : iProp Σ := I γ ∗ True.
Definition K (γ : gname) : iProp Σ := J γ.
Lemma root_goal γ : K γ -∗ True.
Proof. Admitted.
"""
CONTRACT = DesignContract.from_names(["I"])
DESIGN = ["Definition I (γ : gname) : iProp Σ := (∃ n, own γ n)%I."]
EVIDENCE = "closing the invariant after the CmpXchg: the goal needs ▷ Q and the registry entry stores Q"
REQUEST = AmendmentRequest(definition="I", add="▷ Q", at="closing the invariant after the CmpXchg", why="the close site needs the later", requester="i33")


class ScriptedRunner:
    """A runner whose reply is canned JSON in ``trace.final_text`` -- the shape the
    stream-json parser leaves for the triage."""

    def __init__(self, text: str = "", *, name: str = "scripted", status: str = "qed", timed_out: bool = False, evidence: str = ""):
        self.text, self.name, self.status, self.timed_out, self.evidence = text, name, status, timed_out, evidence
        self.seen: list = []

    def available(self):
        return True

    async def run_node(self, node):
        self.seen.append(node)
        return NodeResult(
            status=self.status, evidence=self.evidence, raw=self.text, timed_out=self.timed_out,
            trace={"final_text": self.text, "model": self.name}, cost={"requests": 1, "seconds": 2.0},
        )


def canned(**payload) -> str:
    return "Decided.\n```json\n" + json.dumps(payload, ensure_ascii=False) + "\n```\n"


def iris_dev(tmp_path) -> Development:
    return Development(tmp_path / "Iris.v", source=IRIS_SOURCE)


def decomposer(tmp_path, runner, *, approver=None):
    graph, root, _dev = build_plain_graph(tmp_path, names=("c1",))
    return Decomposer(runner, graph, iris_dev(tmp_path), tmp_path / "w", approver=approver), graph, root


def amend(d, root, text_runner_result=None, **kw):
    return asyncio.run(d.adjudicate_amendment(
        root, REQUEST, evidence=EVIDENCE, budget_seconds=5, contract=CONTRACT, design=DESIGN, **kw
    ))


def events(graph, kind):
    return [e for e in graph.events_since(0, limit=5000) if e["kind"] == kind]


# --- amendment verdicts -----------------------------------------------------------


def test_accept_is_read_and_recorded_without_a_body(tmp_path):
    d, graph, root = decomposer(tmp_path, ScriptedRunner(canned(verdict="accept", why="true at every close site")))
    out = amend(d, root)
    assert out.ok and out.verdict == "accept" and out.kind == "amendment" and out.hint == "true at every close site"
    row = graph.attempts_for(root.id)[-1]
    assert row["role"] == "approver" and row["body"] is None and row["status"] == "qed"
    assert graph.by_name("root").attempts == 0, "an adjudication is not a proof attempt"
    task = (tmp_path / "w" / f"{root.id}.adjudicate1" / f"a{out.attempt_id}" / "TASK.md").read_text(encoding="utf-8")
    assert EVIDENCE in task and CONTRACT.describe() in task
    assert events(graph, "approver.verdict")[-1]["payload"]["verdict"] == "accept"
    graph.close()


def test_adjust_keeps_a_statement_only_replacement(tmp_path):
    fix = "Definition I (γ : gname) : iProp Σ := (∃ n, own γ n ∗ ▷ True)%I"
    d, graph, root = decomposer(tmp_path, ScriptedRunner(canned(verdict="adjust", definition="I", text=fix, why="needs the later")))
    out = amend(d, root)
    assert out.ok and out.verdict == "adjust" and out.definition == "I"
    assert out.text == fix + ".", "the terminating period is supplied"
    assert_statement_only(out.text)
    graph.close()


def test_adjust_carrying_proof_text_is_a_role_violation(tmp_path):
    fix = "Definition I (γ : gname) : iProp Σ := True%I.\nProof.\n  done.\nQed."
    d, graph, root = decomposer(tmp_path, ScriptedRunner(canned(verdict="adjust", definition="I", text=fix)))
    out = amend(d, root)
    assert not out.ok and out.verdict == "" and "proof text" in out.violation
    assert events(graph, "decomposer.violation"), "a verdict carrying a proof is filed as a role violation"
    assert graph.attempts_for(root.id)[-1]["status"] == "stuck"
    graph.close()


def test_adjust_that_states_an_obligation_is_refused(tmp_path):
    d, graph, root = decomposer(tmp_path, ScriptedRunner(canned(verdict="adjust", definition="I", text="Lemma I : True.")))
    out = amend(d, root)
    assert not out.ok and "Lemma" in out.violation
    graph.close()


def test_adjust_without_a_sentence_is_no_verdict(tmp_path):
    d, graph, root = decomposer(tmp_path, ScriptedRunner(canned(verdict="adjust", definition="I", why="add the later")))
    out = amend(d, root)
    assert not out.ok and "adjust" in out.violation
    graph.close()


def test_adjust_of_a_different_definition_than_asked_is_refused(tmp_path):
    d, graph, root = decomposer(tmp_path, ScriptedRunner(canned(verdict="adjust", text="Definition J (γ : gname) : iProp Σ := I γ.")))
    out = amend(d, root)
    assert not out.ok and "'J'" in out.violation and "'I'" in out.violation
    graph.close()


def test_reject_carries_its_reason_as_the_hint(tmp_path):
    why = "the CmpXchg failure branch cannot restore n = 0 before closing"
    d, graph, root = decomposer(tmp_path, ScriptedRunner(canned(verdict="reject", why=why)))
    out = amend(d, root)
    assert out.ok and out.verdict == "reject" and out.hint == why
    assert out.summary().startswith("reject: the CmpXchg")
    graph.close()


def test_a_reply_without_json_is_no_verdict(tmp_path):
    d, graph, root = decomposer(tmp_path, ScriptedRunner("Looks fine to me, go ahead."))
    out = amend(d, root)
    assert not out.ok and out.verdict == "" and "no JSON verdict" in out.violation and not out.infrastructure
    graph.close()


def test_a_runner_error_is_infrastructure_not_a_verdict(tmp_path):
    d, graph, root = decomposer(tmp_path, ScriptedRunner("", status="error", evidence="claude: not logged in"))
    out = amend(d, root)
    assert not out.ok and out.infrastructure and "not logged in" in out.violation
    assert graph.attempts_for(root.id)[-1]["status"] == "error"
    graph.close()


def test_a_deadline_is_a_deadline(tmp_path):
    d, graph, root = decomposer(tmp_path, ScriptedRunner("", status="stuck", timed_out=True))
    out = amend(d, root)
    assert not out.ok and out.deadline and not out.infrastructure
    graph.close()


def test_the_approver_runner_is_used_when_configured(tmp_path):
    designer = ScriptedRunner(canned(verdict="reject"), name="designer/xhigh")
    approver = ScriptedRunner(canned(verdict="accept"), name="approver/medium")
    d, graph, root = decomposer(tmp_path, designer, approver=approver)
    out = amend(d, root)
    assert out.verdict == "accept" and approver.seen and not designer.seen
    assert graph.attempts_for(root.id)[-1]["runner"] == "approver/medium"
    graph.close()


def test_the_design_runner_stands_in_without_an_approver(tmp_path):
    designer = ScriptedRunner(canned(verdict="accept"), name="designer/xhigh")
    d, graph, root = decomposer(tmp_path, designer)
    assert amend(d, root).verdict == "accept" and designer.seen
    graph.close()


def test_each_adjudication_gets_its_own_directory(tmp_path):
    d, graph, root = decomposer(tmp_path, ScriptedRunner(canned(verdict="accept")))
    amend(d, root)
    amend(d, root)
    assert (tmp_path / "w" / f"{root.id}.adjudicate1").is_dir() and (tmp_path / "w" / f"{root.id}.adjudicate2").is_dir()
    assert graph.attempts_for(root.id)[-1]["round"] == 2
    graph.close()


# --- contest verdicts -------------------------------------------------------------


def contest(d, graph, root):
    c1 = graph.by_name("c1")
    graph.set_proof_status(c1.id, "claimed")
    graph.set_proof_status(c1.id, "contested", evidence="cannot commit the atomic update: the AU is not in context")
    c1 = graph.by_name("c1")
    return c1, asyncio.run(d.adjudicate_contest(
        root, c1, evidence=c1.evidence, budget_seconds=5, contract=CONTRACT, design=DESIGN,
    ))


def test_contest_strategy_verdict_is_recorded_on_the_contested_node(tmp_path):
    hint = "Register the atomic update before opening the invariant. Commit it at the CmpXchg success branch."
    d, graph, root = decomposer(tmp_path, ScriptedRunner(canned(verdict="strategy", hint=hint)))
    c1, out = contest(d, graph, root)
    assert out.ok and out.kind == "contest" and out.verdict == "strategy" and out.hint == hint
    assert graph.attempts_for(c1.id)[-1]["role"] == "approver" and graph.attempts_for(c1.id)[-1]["body"] is None
    assert (tmp_path / "w" / f"{c1.id}.adjudicate1").is_dir()
    assert graph.by_name("c1").proof_status == "contested", "the verdict is not the move; the human's delegate makes it"
    graph.close()


def test_contest_statement_with_a_one_definition_fix(tmp_path):
    fix = "Definition I (γ : gname) : iProp Σ := (∃ n, own γ n ∗ ⌜n = 0⌝)%I."
    d, graph, root = decomposer(tmp_path, ScriptedRunner(canned(verdict="statement", text=fix)))
    _c1, out = contest(d, graph, root)
    assert out.ok and out.verdict == "statement" and out.definition == "I" and out.text == fix
    assert_statement_only(out.text)
    graph.close()


def test_contest_statement_fix_whose_text_declares_another_name_is_refused(tmp_path):
    d, graph, root = decomposer(tmp_path, ScriptedRunner(canned(verdict="statement", definition="I", text="Definition J (γ : gname) : iProp Σ := I γ.")))
    _c1, out = contest(d, graph, root)
    assert not out.ok and "declares 'J'" in out.violation
    graph.close()


def test_contest_statement_fix_with_tactics_is_a_violation(tmp_path):
    d, graph, root = decomposer(tmp_path, ScriptedRunner(canned(verdict="statement", definition="I", text="iIntros \"H\". iFrame.")))
    _c1, out = contest(d, graph, root)
    assert not out.ok and "tactic" in out.violation and events(graph, "decomposer.violation")
    graph.close()


# --- the parser and the type ----------------------------------------------------------


def test_verdict_words_are_normalised_and_unknown_ones_refused():
    assert parse_verdict({"verdict": "Approve"}, kind="amendment").verdict == "accept"
    assert parse_verdict({"verdict": "Rejected.", "why": "false"}, kind="amendment").hint == "false"
    assert parse_verdict({"verdict": "design"}, kind="contest").verdict == "statement"
    with pytest.raises(ProtocolError):
        parse_verdict({"verdict": "maybe"}, kind="amendment")
    with pytest.raises(ProtocolError):
        parse_verdict({"verdict": "accept"}, kind="contest"), "an amendment word is not a contest verdict"
    with pytest.raises(ProofEngineeringAttempt):
        parse_verdict({"verdict": "accept", "text": "Definition I : nat. Proof. exact 0. Defined."}, kind="amendment")


def test_verdict_json_round_trip_and_ok():
    v = Verdict(verdict="adjust", definition="I", text="Definition I : Prop := True.", hint="h", kind="amendment", model="m", attempt_id=3)
    assert v.ok and Verdict.from_json(v.to_json()) == Verdict(**{**v.__dict__})
    assert not Verdict(verdict="").ok and not Verdict(verdict="accept", violation="x").ok
    assert "adjust `I`" in v.summary() and "amendment:" in v.render()
    assert "could not run" in Verdict(verdict="", infrastructure=True, violation="down").render()


# --- the prompts ------------------------------------------------------------------


def test_amendment_prompt_carries_the_request_the_evidence_and_the_ban(tmp_path):
    graph, root, _ = build_plain_graph(tmp_path, names=())
    text = render_amendment_adjudication(root, iris_dev(tmp_path), REQUEST, evidence=EVIDENCE, contract=CONTRACT, design=DESIGN)
    for needle in (
        "▷ Q", "`i33`", "closing the invariant after the CmpXchg", EVIDENCE, CONTRACT.describe(), DESIGN[0],
        "300 tokens", "**reject** only when the fact is false or unmaintainable", "no `Proof.`, no tactics",
        '"verdict": "accept | adjust | reject"', root.statement.strip(),
    ):
        assert needle in text, needle
    assert "`I` today:" in text, "the definition as it stands is shown"
    # A stronger hypothesis is a weaker theorem, so the approver is told
    # what an unsatisfiable conjunct does and to reject it.
    assert "**unsatisfiable**" in text and "`False`" in text and "proves every specification that assumes it" in text
    replaced = AmendmentRequest(definition="I", replace="Definition I (γ : gname) : iProp Σ := True%I.")
    assert "**become**" in render_amendment_adjudication(root, iris_dev(tmp_path), replaced, evidence="", design=())
    graph.close()


def test_contest_prompt_carries_the_statement_and_the_two_directions(tmp_path):
    graph, root, _ = build_plain_graph(tmp_path, names=("c1",))
    c1 = graph.by_name("c1")
    text = render_contest_adjudication(root, iris_dev(tmp_path), c1, evidence="dies at the iInv close", contract=CONTRACT, design=DESIGN)
    for needle in (
        c1.statement, root.statement.strip(), "dies at the iInv close", CONTRACT.describe(), DESIGN[0],
        "too **strong**", "too **weak**", "at most three sentences", '"verdict": "statement | strategy"',
        "no `Proof.`, no tactics", "300 tokens",
    ):
        assert needle in text, needle
    graph.close()


# --- taint helpers ----------------------------------------------------------------


def test_mentions_definition_direct_and_one_level_through_a_definition(tmp_path):
    dev = iris_dev(tmp_path)
    assert mentions_definition(dev, "Lemma x γ : I γ -∗ True.", "I")
    assert mentions_definition(dev, "Lemma x γ : J γ -∗ True.", "I"), "J's body mentions I"
    assert not mentions_definition(dev, "Lemma x γ : K γ -∗ True.", "I"), "two levels is the full revision's job"
    assert mentions_definition(dev, "Lemma x γ : K γ -∗ True.", "J")
    assert not mentions_definition(dev, "Lemma x : Inv_I -∗ True.", "I"), "identifiers, not substrings"
    assert not mentions_definition(dev, "Lemma x : True.", "I")


def test_statement_invalidated_picks_non_root_non_attic_mentions(tmp_path):
    graph, root, _plain = build_plain_graph(tmp_path, names=("uses_I", "uses_J", "uses_K", "plain", "retired"))
    dev = iris_dev(tmp_path)
    graph.update(root.id, statement="Lemma root γ : I γ -∗ True.", role="human")
    graph.update(node_id("uses_I"), statement="Lemma uses_I γ : I γ -∗ True.", role="human")
    graph.update(node_id("uses_J"), statement="Lemma uses_J γ : J γ -∗ True.", role="human")
    graph.update(node_id("uses_K"), statement="Lemma uses_K γ : K γ -∗ True.", role="human")
    graph.update(node_id("retired"), statement="Lemma retired γ : I γ -∗ True.", role="human")
    graph.set_proof_status(node_id("retired"), "attic")
    assert [n.name for n in statement_invalidated(graph, dev, "I")] == ["uses_I", "uses_J"]
    assert [n.name for n in statement_invalidated(graph, dev, "K")] == ["uses_K"]
    graph.close()


def test_reopen_for_amendment_moves_failed_nodes_to_open_at_the_next_epoch(tmp_path):
    graph, root, _ = build_plain_graph(tmp_path, names=("gated", "stuck", "contested", "claimed", "untouched", "attic"))
    graph.set_proof_status(node_id("gated"), "claimed")
    graph.record_proof(node_id("gated"), "intros H. exact H.")
    graph.set_proof_status(node_id("stuck"), "claimed")
    graph.set_proof_status(node_id("stuck"), "stuck", evidence="old evidence")
    graph.set_proof_status(node_id("contested"), "claimed")
    graph.set_proof_status(node_id("contested"), "contested", evidence="the statement is wrong")
    graph.set_proof_status(node_id("claimed"), "claimed")
    graph.set_proof_status(node_id("attic"), "attic")
    listed = [graph.by_name(n) for n in ("gated", "stuck", "contested", "claimed", "attic")]
    detail = "`I` now also carries `⌜n = 0⌝` (requested by c1 at closing the invariant: the close site needs it)"
    names = reopen_for_amendment(graph, listed, definition="I", detail=detail)
    assert names == ["gated", "stuck", "contested", "claimed"], "the attic is left alone"
    for name in names:
        node = graph.by_name(name)
        assert node.proof_status == "open" and node.epoch == 1 and node.body is None, name
        assert node.evidence.startswith(AMENDED_MARKER) and detail in node.evidence, name
    assert graph.by_name("attic").proof_status == "attic" and graph.by_name("attic").epoch == 0
    untouched = graph.by_name("untouched")
    assert untouched.proof_status == "open" and untouched.epoch == 0 and untouched.evidence == ""
    reopened = events(graph, "node.reopened_by_amendment")
    assert sorted(e["node"] for e in reopened) == sorted(node_id(n) for n in names)
    contested_event = next(e for e in reopened if e["node"] == node_id("contested"))
    assert contested_event["payload"]["from_status"] == "contested" and contested_event["payload"]["role"] == "human"
    assert contested_event["payload"]["definition"] == "I" and contested_event["payload"]["to_epoch"] == 1
    graph.close()


def test_reopen_for_amendment_includes_the_root_when_listed_and_keeps_one_marker(tmp_path):
    graph, root, _ = build_plain_graph(tmp_path, names=("c1",))
    graph.set_proof_status(root.id, "claimed")
    graph.record_proof(root.id, "intros H _. exact H.")
    names = reopen_for_amendment(graph, [graph.by_name("root")], definition="I", detail=f"{AMENDED_MARKER} `I` changed")
    assert names == ["root"]
    reopened = graph.by_name("root")
    assert reopened.proof_status == "open" and reopened.epoch == 1 and reopened.body is None
    assert reopened.evidence == f"{AMENDED_MARKER} `I` changed", "an already-marked detail is not marked twice"
    assert graph.stale_edges(root.id) == [], "the root's own reopening does not stale its edges"
    graph.close()


def test_reopen_for_amendment_is_one_transaction(tmp_path):
    graph, root, _ = build_plain_graph(tmp_path, names=("c1", "c2"))
    ghost = graph.by_name("c2")
    graph.set_proof_status(node_id("c1"), "claimed")
    graph.set_proof_status(node_id("c1"), "stuck")
    graph.set_proof_status(ghost.id, "claimed")
    graph.record_proof(ghost.id, "exact I.")
    ghost.id = "no-such-node"  # a node that is not in the graph fails the whole move
    with pytest.raises(Exception):  # noqa: B017 -- the store's own error type is not the point
        reopen_for_amendment(graph, [graph.by_name("c1"), ghost], definition="I", detail="d")
    assert graph.by_name("c1").proof_status == "stuck" and graph.by_name("c1").epoch == 0, "rolled back"
    graph.close()


# --- runner wiring ----------------------------------------------------------------


def test_select_approver_is_the_decomposer_runner_at_medium_and_the_flag_overrides(tmp_path):
    cfg = Config()
    args = argparse.Namespace(decomposer=None, approver_effort=None, sandbox=False)
    runner = select_approver(args, cfg, corpus_dir=tmp_path)
    argv = runner.argv
    assert argv[argv.index("--effort") + 1] == "medium" and runner.name.endswith("/medium")
    tools = argv[argv.index("--allowed-tools") + 1 : argv.index("--allowed-tools") + 4]
    assert tools == ["Read", "Glob", "Grep"], "the approver cannot prove either"
    for forbidden in ("Write", "Edit", "Bash"):
        assert forbidden not in argv
    high = select_approver(argparse.Namespace(decomposer=None, approver_effort="high", sandbox=False), cfg, corpus_dir=tmp_path)
    assert high.argv[high.argv.index("--effort") + 1] == "high"
    pinned = select_approver(argparse.Namespace(decomposer="anthropic/claude-opus-4-1", approver_effort=None, sandbox=False), cfg, corpus_dir=tmp_path)
    assert pinned.argv[pinned.argv.index("--model") + 1] == "claude-opus-4-1", "the model follows --decomposer"


def test_the_approver_effort_flag_parses_and_defaults_to_unset():
    parser = build_parser()
    assert parser.parse_args(["prove", "x.v", "L"]).approver_effort is None
    assert parser.parse_args(["prove", "x.v", "L", "--approver-effort", "low"]).approver_effort == "low"
    with pytest.raises(SystemExit):
        parser.parse_args(["prove", "x.v", "L", "--approver-effort", "extreme"])


# --- restatements ---------------------------------------------------------------------


def test_contest_restatement_under_the_same_name_is_read(tmp_path):
    fixed = "Lemma c1 (P : iProp Σ) : {{{ P }}} #() {{{ RET #(); P }}}."
    d, graph, root = decomposer(tmp_path, ScriptedRunner(canned(verdict="statement", restatement=fixed, hint="the resource belongs in the precondition")))
    c1, out = contest(d, graph, root)
    assert out.ok and out.verdict == "statement" and out.restatement == fixed and out.text == "" and out.definition == ""
    assert "restated" in out.summary()
    assert graph.by_name("c1").proof_status == "contested", "the verdict is not the move"
    graph.close()


def test_contest_restatement_declaring_another_name_is_refused(tmp_path):
    d, graph, root = decomposer(tmp_path, ScriptedRunner(canned(verdict="statement", restatement="Lemma c9 (P : iProp Σ) : P -∗ P.")))
    _c1, out = contest(d, graph, root)
    assert not out.ok and "declares 'c9'" in out.violation
    graph.close()


def test_a_corrected_lemma_arriving_under_text_is_the_restatement(tmp_path):
    fixed = "Lemma c1 (P : iProp Σ) : P -∗ P."
    d, graph, root = decomposer(tmp_path, ScriptedRunner(canned(verdict="statement", text=fixed)))
    _c1, out = contest(d, graph, root)
    assert out.ok and out.restatement == fixed and out.text == ""
    graph.close()


def test_a_restatement_with_proof_text_or_two_sentences_is_refused():
    with pytest.raises(ProofEngineeringAttempt):
        parse_verdict({"verdict": "statement", "restatement": "Lemma c1 : True. Proof. done. Qed."}, kind="contest", node_name="c1")
    with pytest.raises(ProtocolError):
        parse_verdict({"verdict": "statement", "restatement": "Lemma c1 : True. Lemma c2 : True."}, kind="contest", node_name="c1")
    stray = parse_verdict({"verdict": "strategy", "hint": "h", "lemma": "c1"}, kind="contest", node_name="c1")
    assert stray.verdict == "strategy" and stray.restatement == "", "an echo of the name under `lemma` is not a restatement"
    with_comment = parse_verdict({"verdict": "statement", "restatement": "Lemma c1 : True. (* was False *)"}, kind="contest", node_name="c1")
    assert with_comment.restatement.startswith("Lemma c1 : True.") and not with_comment.restatement.endswith(").")
    v = parse_verdict({"verdict": "statement", "restated": "Lemma c1 : True"}, kind="contest", node_name="c1")
    assert v.restatement == "Lemma c1 : True." and Verdict.from_json(v.to_json()).restatement == v.restatement


def test_the_review_variant_of_the_contest_prompt(tmp_path):
    graph, root, _dev = build_plain_graph(tmp_path, names=("c1",))
    c1 = graph.by_name("c1")
    review = render_contest_adjudication(root, iris_dev(tmp_path), c1, evidence="gate: FAIL", failed_attempts=2)
    assert "# Review `c1` after 2 failed attempt(s)" in review and "## The last attempt's evidence" in review
    assert "No prover contested this obligation" in review and "restatement" in review
    contest = render_contest_adjudication(root, iris_dev(tmp_path), c1, evidence="I contest")
    assert "# Adjudicate the contest on `c1`" in contest and "## The prover's case" in contest
    graph.close()


def test_the_review_after_flag_parses_and_defaults_to_two():
    parser = build_parser()
    assert parser.parse_args(["prove", "x.v", "L"]).review_after == 2
    assert parser.parse_args(["prove", "x.v", "L", "--review-after", "0"]).review_after == 0
