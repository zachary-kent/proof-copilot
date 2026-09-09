"""pcp.orch.decomposer: the three structural barriers, the tolerant parser, the triage."""

from __future__ import annotations

import asyncio
import dataclasses
import json

import pytest

from pcp.errors import RoleViolation
from pcp.orch.decomposer import (
    ChildStatement,
    Decomposer,
    DesignDefinition,
    PlanProposal,
    ProofEngineeringAttempt,
    already_declared,
    assert_statement_only,
    blank_predicates,
    extract_json,
    parse_proposal,
    render_amendment_task,
    render_decomposition_task,
    validate_proposal,
)
from pcp.orch.model import Node, node_id
from pcp.orch.protocol import NodeResult
from pcp.orch.runners.base import decomposer_runner
from pcp.rocq.assemble import Development
from tests._orch_fixtures import build_plain_graph

# --- barrier 1: capability ------------------------------------------------------


def test_the_decomposer_runner_has_no_way_to_write_or_execute():
    argv = decomposer_runner("m").argv
    tools = argv[argv.index("--allowed-tools") + 1 : argv.index("--model")]
    assert tools == ["Read", "Glob", "Grep"]
    for forbidden in ("Write", "Edit", "Bash", "NotebookEdit", "MultiEdit"):
        assert forbidden not in argv


# --- barrier 2: type --------------------------------------------------------------


def test_the_proposal_type_has_no_field_a_proof_could_travel_in():
    for cls in (PlanProposal, ChildStatement, DesignDefinition):
        names = {f.name for f in dataclasses.fields(cls)}
        assert not names & {"body", "proof", "script", "tactics"}, cls


@pytest.mark.parametrize(
    "text",
    [
        "Lemma foo : True.\nProof.\n  exact I.\nQed.",
        "Lemma foo : True. Proof. done. Qed.",
        "iIntros \"H\". iFrame.",
        "intros H. exact H.",
        "wp_load. wp_pures.",
        "Lemma foo : True. admit.",
        "Next Obligation. done. Qed.",
        "- exact I.",
        "Check foo.",
        "Definition foo : nat. Proof. exact 0. Defined.",
    ],
)
def test_proof_text_is_rejected_at_construction(text):
    with pytest.raises(ProofEngineeringAttempt):
        assert_statement_only(text)
    with pytest.raises(ProofEngineeringAttempt):
        ChildStatement("foo", text)
    with pytest.raises(ProofEngineeringAttempt):
        DesignDefinition("foo", text)


@pytest.mark.parametrize(
    "text",
    [
        "Lemma foo (P : Prop) : P -> P.",
        "From iris.base_logic.lib Require Import ghost_var.",
        "Definition value (γ : gname) (n : Z) : iProp Σ := ghost_var γ (1/2)%Qp n.",
        "Class rwcasG Σ := {\n  rwcas_heapGS :: heapGS Σ;\n  rwcas_ghost_varG :: ghost_varG Σ Z;\n}.",
        "Instance foo_persistent : Persistent foo := _.",
        "Notation \"x ↦ y\" := (mapsto x y).",
        "Open Scope Z_scope.",
        "(* a comment *) Definition x := 1.",
    ],
)
def test_statements_and_design_are_accepted(text):
    assert_statement_only(text)


# --- barrier 3: store -------------------------------------------------------------


def test_the_graph_refuses_a_body_from_the_decomposer_role(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    graph.set_proof_status(node_id("c1"), "claimed")
    with pytest.raises(RoleViolation):
        graph.set_proof_status(node_id("c1"), "gated", body="exact I.", role="decomposer")
    with pytest.raises(RoleViolation):
        graph.update(node_id("c1"), body="exact I.")
    graph.close()


class ScriptedDecomposer:
    name = "scripted"

    def __init__(self, text: str = "", *, status: str = "qed", timed_out: bool = False, evidence: str = "", raise_exc: bool = False):
        self.text, self.status, self.timed_out, self.evidence, self.raise_exc = text, status, timed_out, evidence, raise_exc
        self.seen = []

    def available(self):
        return True

    async def run_node(self, node):
        self.seen.append(node)
        if self.raise_exc:
            raise RuntimeError("boom")
        return NodeResult(
            status=self.status, evidence=self.evidence, raw=self.text, timed_out=self.timed_out,
            trace={"final_text": self.text, "model": "scripted"}, cost={"requests": 1, "seconds": 3.0},
        )


PLAN = json.dumps({
    "rationale": "split",
    "children": [
        {"name": "c1", "statement": "Lemma c1 (P : Prop) : P -> P.", "rationale": "a"},
        {"name": "c3", "statement": "∀ (Q : Prop), Q -> Q", "rationale": "b"},
    ],
    "glue_rationale": "compose",
})


def test_a_decomposition_attempt_never_writes_a_body(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=())
    d = Decomposer(ScriptedDecomposer(PLAN), graph, dev, tmp_path / "w")
    out = asyncio.run(d.propose(root, None, budget_seconds=5))
    assert out.ok, out.render()
    rows = graph.attempts_for(root.id)
    assert rows[-1]["role"] == "decomposer" and rows[-1]["body"] is None and rows[-1]["status"] == "qed"
    assert rows[-1]["tier"] == "human", "owner is who stated the node, not who ran the attempt"
    assert graph.by_name("root").attempts == 0, "a decomposer round is not a proof attempt"
    assert (tmp_path / "w" / f"{root.id}.decompose" / f"a{out.attempt_id}" / "TASK.md").exists()
    assert out.proposal.children[1].statement == "Lemma c3 :\n  ∀ (Q : Prop), Q -> Q."
    graph.close()


# --- the parser ---------------------------------------------------------------


def test_json_is_found_after_prose_with_braces_and_inside_a_fence():
    prose = 'The goal is {{{ True }}} incr #l {{{ RET #(); True }}} and |={E}=> stuff.\n\n```json\n{"children": [{"name": "a", "statement": "Lemma a : True."}]}\n```\nDone.'
    assert extract_json(prose)["children"][0]["name"] == "a"
    bare = 'Here {[k:=v]} first. {"rationale": "x", "children": []} trailing prose'
    assert extract_json(bare) == {"rationale": "x", "children": []}
    strings = '{"rationale": "a } inside a string { and", "children": []}'
    assert extract_json(strings)["rationale"].startswith("a }")
    event = '{"type":"assistant","message":{"content":[{"type":"text","text":"{\\"children\\": []}"}]}}'
    assert extract_json(event) is None, "a stream event is not a proposal"
    assert extract_json("no json here") is None


def test_a_child_with_a_lemma_header_but_no_period_gets_one():
    p = parse_proposal('{"children": [{"name": "collect_later", "statement": "Lemma collect_later (P : Prop) : P -> P"}]}')
    assert p.children[0].statement == "Lemma collect_later (P : Prop) : P -> P."
    assert validate_proposal(p) == []


def test_a_bare_proposition_gets_its_header_and_a_declared_child_is_never_renamed():
    p = parse_proposal('{"children": [{"name": "x", "statement": "∀ (P : Prop), P -> P."}]}')
    assert p.children[0].statement == "Lemma x :\n  ∀ (P : Prop), P -> P."
    other = parse_proposal('{"children": [{"name": "wanted", "statement": "Lemma something_else (n : nat) : n = n."}]}')
    assert any("wanted" in prob for prob in validate_proposal(other))


def test_definitions_may_be_bare_strings_and_imports_get_their_period():
    p = parse_proposal(json.dumps({
        "definitions": ["Definition value (n : nat) : Prop := n = n.", {"text": "Open Scope Z_scope."}],
        "imports": "From iris.base_logic.lib Require Import ghost_var",
        "children": [{"name": "c", "statement": "Lemma c : True."}],
    }))
    assert p.definitions[0].name == "value" and p.definitions[1].name == ""
    assert p.imports == ("From iris.base_logic.lib Require Import ghost_var.",)
    with pytest.raises(ProofEngineeringAttempt, match="not a Require line"):
        parse_proposal('{"imports": ["Import foo."], "children": []}')
    with pytest.raises(ProofEngineeringAttempt, match="no JSON"):
        parse_proposal("nothing")


def test_a_definitions_only_proposal_is_a_problem_when_orchestration_is_required():
    p = parse_proposal('{"definitions": ["Definition v : nat := 0."], "children": []}')
    assert any("no children" in prob for prob in validate_proposal(p))
    assert validate_proposal(p, require_children=False) == []
    empty = parse_proposal('{"children": [], "definitions": []}')
    assert any("has no children" in prob for prob in validate_proposal(empty))


def test_validation_refuses_obligations_smuggled_as_design_and_duplicates():
    p = parse_proposal(json.dumps({
        "definitions": [{"name": "h", "text": "Lemma h : True."}, {"name": "v", "text": "Definition w : nat := 0."}],
        "children": [{"name": "c", "statement": "Lemma c : True."}, {"name": "c", "statement": "Lemma c : False."},
                     {"name": "d", "statement": "Definition d : nat := 0."}],
    }))
    problems = validate_proposal(p)
    assert any("declares a Lemma" in x for x in problems)
    assert any("does not declare v" in x for x in problems)
    assert any("duplicate child name 'c'" in x for x in problems)
    assert any("children must be lemmas" in x for x in problems)


def test_a_child_already_declared_in_the_development_is_refused(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=())
    p = parse_proposal('{"children": [{"name": "helper", "statement": "Lemma helper (P : Prop) : P -> P."}, {"name": "fresh", "statement": "Lemma fresh : True."}]}')
    problems = already_declared(dev, p)
    assert len(problems) == 1 and "helper" in problems[0] and "use it" in problems[0]
    graph.close()


def test_merging_a_revision_over_its_base_keeps_omitted_definitions():
    base = parse_proposal(json.dumps({"definitions": [{"name": "a", "text": "Definition a : nat := 0."}, {"name": "b", "text": "Definition b : nat := 0."}],
                                      "imports": ["Require Import X."], "children": [{"name": "c", "statement": "Lemma c : True."}]}))
    revised = parse_proposal(json.dumps({"definitions": [{"name": "b", "text": "Definition b : nat := 1."}], "children": []}))
    merged = revised.merged_over(base)
    assert {d.name: d.text for d in merged.definitions} == {"a": "Definition a : nat := 0.", "b": "Definition b : nat := 1."}
    assert merged.imports == ("Require Import X.",) and merged.names() == ["c"]
    assert PlanProposal.from_json(merged.to_json()).to_json() == merged.to_json()


# --- triage ---------------------------------------------------------------------


def test_a_killed_decomposer_with_text_but_no_json_is_a_deadline_not_a_violation(tmp_path):
    from pcp.orch.failures import classify

    graph, root, dev = build_plain_graph(tmp_path, names=())
    runner = ScriptedDecomposer("Let me read the development first.", status="stuck", timed_out=True,
                                evidence="worker exceeded its 1800s deadline and was killed; captured 120 bytes of output before the kill (1 turn(s), 0 tool call(s))")
    out = asyncio.run(Decomposer(runner, graph, dev, tmp_path / "w").propose(root, None, budget_seconds=1800))
    assert not out.ok and out.deadline and not out.infrastructure
    assert classify(out.violation).primary == "deadline"
    assert "no JSON" not in out.violation
    assert graph.attempts_for(root.id)[-1]["status"] == "stuck", "a deadline is the round's failure, not infrastructure"
    graph.close()


def test_a_killed_decomposer_that_finished_its_json_is_parsed(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=())
    runner = ScriptedDecomposer(PLAN, status="stuck", timed_out=True, evidence="killed at the deadline after writing")
    out = asyncio.run(Decomposer(runner, graph, dev, tmp_path / "w").propose(root, None, budget_seconds=5))
    assert out.ok
    graph.close()


def test_an_error_result_is_infrastructure_and_a_revoked_token_in_prose_too(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=())
    out = asyncio.run(Decomposer(ScriptedDecomposer("", status="error", evidence="`claude` is not on PATH"), graph, dev, tmp_path / "w").propose(root, None, budget_seconds=5))
    assert out.infrastructure and "could not run at all" in out.render()
    out2 = asyncio.run(Decomposer(ScriptedDecomposer("401 OAuth access token has been revoked. Please run /login"), graph, dev, tmp_path / "w").propose(root, None, budget_seconds=5))
    assert out2.infrastructure
    out3 = asyncio.run(Decomposer(ScriptedDecomposer(raise_exc=True), graph, dev, tmp_path / "w").propose(root, None, budget_seconds=5))
    assert out3.infrastructure and "boom" in out3.violation
    graph.close()


def test_a_protocol_violation_is_distinct_from_a_structural_problem(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=())
    d = Decomposer(ScriptedDecomposer('{"children": [{"name": "c", "statement": "Lemma c : True. Proof. exact I. Qed."}]}'), graph, dev, tmp_path / "w")
    out = asyncio.run(d.propose(root, None, budget_seconds=5))
    assert out.violation and "proof" in out.violation and out.proposal is None
    kinds = [e["kind"] for e in graph.events_since()]
    assert "decomposer.violation" in kinds
    d2 = Decomposer(ScriptedDecomposer('{"children": [{"name": "helper", "statement": "Lemma helper : True."}]}'), graph, dev, tmp_path / "w")
    out2 = asyncio.run(d2.propose(root, None, budget_seconds=5))
    assert not out2.ok and out2.problems and not out2.violation
    assert graph.attempts_for(root.id)[-1]["status"] == "stuck"
    graph.close()


def test_sentinels_run_on_every_proposal(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    graph.set_proof_status(node_id("c1"), "claimed")
    graph.set_proof_status(node_id("c1"), "stuck", evidence="hard")
    restated_root = json.dumps({"children": [{"name": "again", "statement": "Lemma again (P Q : Prop) : P -> Q -> P."}]})
    out = asyncio.run(Decomposer(ScriptedDecomposer(restated_root), graph, dev, tmp_path / "w").propose(root, None, budget_seconds=5))
    assert not out.ok and any("restates the root" in n for n in out.notes), "a redundant child is dropped, and nothing remained"
    converging = json.dumps({"children": [{"name": "other_name", "statement": "Lemma other_name (P : Prop) : P -> P."}]})
    out2 = asyncio.run(Decomposer(ScriptedDecomposer(converging), graph, dev, tmp_path / "w").propose(root, None, budget_seconds=5))
    assert not out2.ok and any("converging failure" in p for p in out2.problems)
    same_name = json.dumps({"children": [{"name": "c1", "statement": "Lemma c1 (P : Prop) : P -> P."}]})
    out3 = asyncio.run(Decomposer(ScriptedDecomposer(same_name), graph, dev, tmp_path / "w").propose(root, None, budget_seconds=5))
    assert out3.ok, "re-proposing a child under its own name is a revision, not a duplicate"
    graph.close()


def test_records_are_keyed_by_attempt_id_so_reasks_never_overwrite(tmp_path):
    from pcp.orch.record import Recorder

    graph, root, dev = build_plain_graph(tmp_path, names=())
    rec = Recorder(tmp_path / "rec", run_id="run")
    d = Decomposer(ScriptedDecomposer(PLAN), graph, dev, tmp_path / "w", rec)
    a = asyncio.run(d.propose(root, None, budget_seconds=5))
    b = asyncio.run(d.amend(root, evidence="e", round_no=2, budget_seconds=5))
    dirs = sorted(p.name for p in (tmp_path / "rec" / "run").iterdir())
    assert dirs == sorted([f"root.{a.attempt_id}.decompose", f"root.{b.attempt_id}.amend2"])
    graph.close()


# --- prompts ---------------------------------------------------------------------


def _node():
    return Node(id="a", name="a", statement="Lemma a : True.", statement_status="frozen")


def test_the_decomposition_prompt_pins_its_strings(tmp_path):
    src = tmp_path / "Dev.v"
    src.write_text("Definition value (x : nat) : Prop := True.\nLemma a : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    dev = Development(src)
    assert blank_predicates(dev) == ["value"]
    text = render_decomposition_task(_node(), dev, design_brief="THE SECRET BRIEF", brief_mode="spec-only")
    for s in ("decomposer", "you are not proving", '"children"', "designing it is your job", "`value`",
              "tightly scoped proof engineering", "Prefer more, smaller obligations", "fifty tactics",
              "Each `statement` is exactly one `Lemma … .` sentence", "No `Proof.`, no tactics, no `Qed.`"):
        assert s in text, s
    for s in ("pcp check", "ghost_var", "iris.base_logic.lib", "(1/2)", "THE SECRET BRIEF", "The design is already there"):
        assert s not in text, s
    given = tmp_path / "Given.v"
    given.write_text("Definition inv (x : nat) : Prop := x = x.\nLemma a : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    text2 = render_decomposition_task(_node(), Development(given), design_brief="BRIEF", brief_mode="full", library=[tmp_path])
    assert "The design is already there" in text2 and "frozen" in text2 and "designing it is your job" not in text2
    assert "BRIEF" in text2 and "What you may consult" in text2 and "worked example" in text2


def test_the_amendment_prompt_pins_its_strings(tmp_path):
    src = tmp_path / "Dev.v"
    src.write_text("Definition value (x : nat) : Prop := True.\nLemma a : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    text = render_amendment_task(_node(), Development(src), design=["Definition value (x : nat) : Prop := True."], evidence="it failed", round_no=2)
    for s in ("Your current design", "What happened", "it failed", "not tightly scoped",
              "split it into smaller obligations before you touch the design", "too **strong**", "too **weak**",
              "the revised design, complete", "A definition you omit keeps its current form"):
        assert s in text, s
    given = tmp_path / "Given.v"
    given.write_text("Definition inv (x : nat) : Prop := x = x.\nLemma a : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    text2 = render_amendment_task(_node(), Development(given), design=[], evidence="x", round_no=2)
    assert "given and frozen" in text2 and "the revised design, complete" not in text2
    text3 = render_amendment_task(_node(), Development(given), design=[], evidence="does not compile", round_no=2, kind="design")
    assert "could not be applied" in text3 and "checker's" in text3 and "obligations were not proved" not in text3
