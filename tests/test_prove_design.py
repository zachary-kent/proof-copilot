"""pcp.orch.prove.design: application, placement, the contract, staging, the ladder."""

from __future__ import annotations

import asyncio
import dataclasses
import json
import shutil
from pathlib import Path

import pytest

from pcp.orch.contract import DesignContract
from pcp.orch.decomposer import DecompositionResult, parse_payload, parse_proposal
from pcp.orch.graph import Graph
from pcp.orch.model import Node, node_id
from pcp.orch.packet import build_packet
from pcp.orch.prove import DesignFailed, OrchestrationRequired, ProveConfig, ProveResult, freeze_target, prove
from pcp.orch.prove.design import (
    DECOMPOSE_DEADLINE_RETRIES,
    DesignDriver,
    DesignViolatesContract,
    add_imports,
    adopt_proposal,
    apply_design,
    blame_child,
    decompose_with_retry,
    design_dir,
    design_evidence,
    design_failed,
    design_rounds_used,
    place_additions,
    refresh_after_revision,
    scan_fragment,
    stage_spec_only,
    standing_failures,
    why_it_failed,
)
from pcp.orch.runners.mock import MockRunner
from pcp.orch.schedule import NodeOutcome, RunReport, siblings_of
from pcp.orch.sentinels import SentinelReport
from pcp.rocq.assemble import Development, NodeSpec
from tests._orch_fixtures import ScriptedDecomposerRunner, build_plain_graph, plain_cfg
from tests.conftest import needs_rocq

ROOT = Path(__file__).resolve().parents[1]

# --- placement -------------------------------------------------------------------

_FILE = """From iris.heap_lang Require Import lang proofmode notation.

Class rwcasG Σ := {
  rwcas_heapGS :: heapGS Σ;
  rwcas_reg :: inG Σ regUR;
}.

Section rwcas.
  Context `{!rwcasG Σ}.

  Definition value (γ : gname) (n : Z) : iProp Σ := marker γ n.

  Lemma spec : True.
  Proof.
  Admitted.
End rwcas.
"""


def test_an_addition_lands_before_its_first_use_even_in_an_unnamed_sentence():
    out = place_additions(
        _FILE,
        ["Definition regUR : ucmra := authUR (gmapUR nat unitR).",
         "Definition marker (γ : gname) (n : Z) : iProp Σ := own γ (to_agree n)."],
        anchor="spec",
    )
    assert out.index("Definition regUR") < out.index("Class rwcasG")
    assert out.index("Section rwcas.") < out.index("Definition marker") < out.index("Definition value")
    # A consumer that is a `Context` line (unnamed) is scanned too.
    text = _FILE.replace("Context `{!rwcasG Σ}.", "Context `{!rwcasG Σ, !fooG Σ}.")
    out2 = place_additions(text, ["Class fooG Σ := { foo_inG :: inG Σ unitR }."], anchor="spec")
    assert out2.index("Class fooG") < out2.index("Context `{!rwcasG Σ, !fooG Σ}.")


def test_an_orphan_lands_in_the_anchors_section_and_the_fixpoint_orders_a_chain():
    out = place_additions(_FILE, ["Definition orphan : nat := 0."], anchor="spec")
    assert out.index("Section rwcas.") < out.index("Definition orphan") < out.index("Lemma spec")
    chain = place_additions(
        _FILE,
        ["Definition c (γ : gname) : iProp Σ := b γ.", "Definition b (γ : gname) : iProp Σ := a γ.",
         "Definition a (γ : gname) : iProp Σ := marker γ 0.",
         "Definition marker (γ : gname) (n : Z) : iProp Σ := own γ (to_agree n)."],
        anchor="spec",
    )
    for earlier, later in (("marker", "a"), ("a", "b"), ("b", "c")):
        assert chain.index(f"Definition {earlier}") < chain.index(f"Definition {later}")
    cycle = place_additions(_FILE, ["Definition p : nat := q.", "Definition q : nat := p."], anchor="spec")
    assert "Definition p" in cycle and "Definition q" in cycle
    assert place_additions(_FILE, [], anchor="spec") == _FILE


def test_imports_go_after_the_last_require_and_deduplicate():
    src = "Require Import Stdlib.Lists.List.\nRequire Import Stdlib.Arith.Arith.\n\nDefinition x := 1.\n"
    out = add_imports(src, ["From iris.base_logic.lib Require Import ghost_var.", "Require Import Stdlib.Arith.Arith."])
    lines = out.splitlines()
    assert lines[1] == "Require Import Stdlib.Arith.Arith."
    assert lines[2] == "From iris.base_logic.lib Require Import ghost_var." and lines.count("Require Import Stdlib.Arith.Arith.") == 1
    no_require = "Definition x := 1.\n"
    assert add_imports(no_require, ["Require Import A."]).startswith("Require Import A.\n")


def test_every_fragment_is_scanned_for_escape_hatches_and_axioms(tmp_path):
    with pytest.raises(DesignViolatesContract, match="Guard Checking"):
        scan_fragment("Unset Guard Checking.", "x")
    with pytest.raises(DesignViolatesContract, match="axiom"):
        scan_fragment("Axiom magic : False.", "x")
    scan_fragment("Set Implicit Arguments.", "x")
    scan_fragment("Definition v : nat := 0.", "x")
    graph, root, dev = build_plain_graph(tmp_path, names=())
    cfg = plain_cfg(tmp_path)
    proposal = parse_proposal(json.dumps({"definitions": ["Unset Guard Checking."], "children": [{"name": "c", "statement": "Lemma c : True."}]}))
    contract = DesignContract(allow_additions=True)
    with pytest.raises(DesignViolatesContract, match="Guard Checking"):
        apply_design(cfg, graph, dev, root, proposal, contract=contract, round_no=1, workroot=tmp_path / "w")
    assert not list((tmp_path / "w").glob("*.designed*")) if (tmp_path / "w").exists() else True
    graph.close()


def test_the_contract_refuses_before_any_compile(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=())
    cfg = plain_cfg(tmp_path)
    proposal = parse_proposal(json.dumps({"definitions": [{"name": "helper_two", "text": "Definition helper_two : nat := 0."}], "children": [{"name": "c", "statement": "Lemma c : True."}]}))
    with pytest.raises(DesignViolatesContract, match="permits no additions"):
        apply_design(cfg, graph, dev, root, proposal, contract=DesignContract.everything_frozen(), round_no=1, workroot=tmp_path / "w")
    graph.close()


def test_design_dirs_are_never_overwritten(tmp_path):
    assert design_dir(tmp_path, "r", 1) == tmp_path / "r.designed"
    (tmp_path / "r.designed").mkdir()
    assert design_dir(tmp_path, "r", 1) == tmp_path / "r.designed2"
    assert design_dir(tmp_path, "r", 3) == tmp_path / "r.designed3"


def test_blame_child_names_exactly_one():
    specs = [NodeSpec("fc50_acquire", ""), NodeSpec("fc50_release", "")]
    assert blame_child('File "./M.v", line 376: Error: in fc50_acquire the term has type Z', specs) == " (`fc50_acquire`)"
    assert blame_child("Error: something", specs) == "" and blame_child("fc50_acquire and fc50_release", specs) == ""


# --- adoption -------------------------------------------------------------------


def _plan(*names, **statements):
    from pcp.orch.decomposer import ChildStatement, PlanProposal

    return PlanProposal(children=tuple(ChildStatement(n, statements.get(n, f"Lemma {n} : True.")) for n in names))


def _live(graph):
    return sorted(n.name for n in graph.nodes() if n.rank != "root" and n.proof_status != "attic" and not n.body)


def test_a_revision_retires_revives_and_restates(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=())
    cfg = plain_cfg(tmp_path)
    adopt_proposal(cfg, graph, dev, root, _plan("helper_a", "keep_me"))
    assert _live(graph) == ["helper_a", "keep_me"]
    assert graph.by_name("helper_a").owner == "decomposer" and graph.by_name("helper_a").depth == 1
    adopt_proposal(cfg, graph, dev, root, _plan("helper_b", "keep_me"))
    assert _live(graph) == ["helper_b", "keep_me"] and graph.by_name("helper_a").proof_status == "attic"
    adopt_proposal(cfg, graph, dev, root, _plan("helper_a"))
    assert graph.by_name("helper_a").proof_status == "open" and graph.by_name("helper_b").proof_status == "attic"
    # A restated child gets the new statement at the next epoch, body cleared.
    graph.set_proof_status(node_id("helper_a"), "claimed")
    graph.record_proof(node_id("helper_a"), "exact I.")
    adopt_proposal(cfg, graph, dev, root, _plan("helper_a", helper_a="Lemma helper_a (P : Prop) : P -> P."))
    a = graph.by_name("helper_a")
    assert a.epoch == 1 and a.body is None and a.proof_status == "open" and "P -> P" in a.statement
    kinds = [e["kind"] for e in graph.events_since()]
    assert {"plan.retired", "plan.revived", "plan.restated", "plan.adopted"} <= set(kinds)
    # A proved orphan is kept.
    graph.set_proof_status(node_id("helper_a"), "claimed")
    graph.record_proof(node_id("helper_a"), "intros H. exact H.")
    adopt_proposal(cfg, graph, dev, root, _plan("other"))
    assert graph.by_name("helper_a").proof_status == "gated"
    graph.close()


def test_refresh_after_revision_gives_unproved_nodes_a_fresh_epoch(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("stuck", "proved"))
    graph.set_proof_status(node_id("stuck"), "claimed")
    graph.set_proof_status(node_id("stuck"), "stuck", evidence="x")
    graph.set_proof_status(node_id("proved"), "claimed")
    graph.record_proof(node_id("proved"), "exact I.")
    refreshed = refresh_after_revision(graph, root)
    assert set(refreshed) == {"stuck", "root"}
    assert graph.by_name("stuck").epoch == 1 and graph.by_name("proved").epoch == 0
    graph.close()


# --- staging -----------------------------------------------------------------


def test_spec_only_staging_hides_the_brief_and_carries_only_the_contract(tmp_path):
    cfg = plain_cfg(tmp_path, brief="spec-only")
    corpus = cfg.file.parent
    (corpus / "DESIGN.md").write_text("# the answer is 42", encoding="utf-8")
    (corpus / "bench.json").write_text(json.dumps({"holdout": [{"name": "root"}], "mutable": ["helper"], "notes": ["secret"]}), encoding="utf-8")
    (corpus / "design.json").write_text(json.dumps({"mutable": ["helper"], "allow_additions": True}), encoding="utf-8")
    (corpus / "Makefile").write_text("all:\n", encoding="utf-8")
    contract = DesignContract.from_corpus(corpus)
    staged = stage_spec_only(cfg, "root", contract=contract)
    listing = sorted(p.name for p in staged.path.parent.iterdir())
    assert listing == ["Makefile", "Plain.v", "_CoqProject", "design.json", "plan.v"]
    assert json.loads((staged.path.parent / "design.json").read_text()) == contract.to_json()
    assert "secret" not in (staged.path.parent / "design.json").read_text()
    assert DesignContract.from_corpus(staged.path.parent).results == frozenset({"root"})
    assert staged.source == cfg.file.read_text()


# --- evidence ------------------------------------------------------------------


def test_design_evidence_quotes_requests_and_gives_the_granularity_verdict():
    report = RunReport(outcomes=[
        NodeOutcome("1", "c129_register", "stuck", attempts=2, elapsed_s=1200, evidence="worker exceeded its 1200s deadline and was killed",
                    requests=[{"statement": "Lemma f111_spec_same_backup : True.", "rationale": "pins backup"}]),
        NodeOutcome("2", "fine", "qed"),
    ])
    text = design_evidence(report)
    for s in ("1 of 2 obligations were not proved", "tightly scoped proof engineering", "split the failing obligations further",
              "this obligation is too large", "f111_spec_same_backup", "pins backup", "asked to exist", "requests, not decisions"):
        assert s in text, s
    assert "asked to exist" not in design_evidence(RunReport(outcomes=[NodeOutcome("1", "a", "stuck", evidence="boom")]))
    assert "statement itself is wrong" in why_it_failed(NodeOutcome("1", "c", "contested", evidence="wrong"))
    assert "evidence about the obligation, not the prover" in why_it_failed(NodeOutcome("1", "x", "stuck", attempts=3, evidence="iApply failed"))
    assert why_it_failed(NodeOutcome("1", "x", "stuck", attempts=1, evidence="")) == "did not finish"


def test_design_failed_ignores_blameless_failures():
    assert not design_failed(RunReport(outcomes=[NodeOutcome("1", "a", "error", evidence="claude is not on PATH")]))
    assert not design_failed(RunReport(outcomes=[NodeOutcome("1", "a", "stuck", evidence="the worker produced no answer.json")]))
    assert design_failed(RunReport(outcomes=[NodeOutcome("1", "a", "contested", evidence="wrong")]))
    assert design_failed(RunReport(outcomes=[NodeOutcome("1", "a", "stuck", evidence="Error: iFrame failed: spatial context is not empty")]))
    assert not design_failed(RunReport(outcomes=[NodeOutcome("1", "a", "qed")]))


# --- the deadline ladder ---------------------------------------------------------


class _Decomposer:
    def __init__(self, violation: str, *, infrastructure: bool = False, deadline: bool = False):
        self.budgets: list[float] = []
        self.violation, self.infrastructure, self.deadline = violation, infrastructure, deadline

    async def propose(self, root, contract, *, budget_seconds, **kw):
        self.budgets.append(budget_seconds)
        return DecompositionResult(violation=self.violation, infrastructure=self.infrastructure, deadline=self.deadline)


class _Graph:
    def __init__(self):
        self.events = []

    def emit(self, kind, node=None, /, **payload):
        self.events.append((kind, payload))


_ROOT = Node(id="n", name="n", statement="Lemma n : True.")


def _ladder(seconds: float, cap: float, **kw) -> tuple[list[float], list[str]]:
    d = _Decomposer(kw.pop("violation", "worker exceeded its deadline and was killed"), **kw)
    g = _Graph()
    asyncio.run(decompose_with_retry(d, _ROOT, contract=None, seconds=seconds, cap_seconds=cap, graph=g))
    return d.budgets, [k for k, _ in g.events]


def test_a_deadline_is_retried_with_a_doubled_clock_inside_the_budget():
    assert DECOMPOSE_DEADLINE_RETRIES == 2
    budgets, events = _ladder(100.0, 10800.0, deadline=True)
    assert budgets == [100.0, 200.0, 400.0] and events == ["decomposer.retried"] * 2
    budgets, events = _ladder(4500.0, 10800.0, deadline=True)
    assert sum(budgets) <= 10800.0 and budgets[0] == 4500.0 and "decomposer.gave_up" in events
    budgets, _ = _ladder(100.0, 0.0, deadline=True)
    assert budgets == [100.0, 200.0, 400.0], "an unset budget does not cap the ladder"
    assert _ladder(100.0, 10800.0, violation="the decomposer produced no JSON object to read")[0] == [100.0]
    assert _ladder(100.0, 10800.0, violation="401 access token has been revoked", infrastructure=True)[0] == [100.0]


# --- the driver: contract carried across rounds -----------------------------------


def test_the_contract_is_loaded_once_and_carried_through_every_round(tmp_path, monkeypatch):
    import pcp.orch.prove.design as design_mod

    seen: list[object] = []

    def fake_apply(cfg, graph, dev, root, proposal, *, contract, round_no, workroot, preamble=""):
        seen.append(contract)
        if round_no == 1:
            raise design_mod.DesignDoesNotCompile("unresolved implicit")
        return dev

    monkeypatch.setattr(design_mod, "apply_design", fake_apply)
    graph, root, dev = build_plain_graph(tmp_path, names=())
    contract = DesignContract(mutable=frozenset({"helper"}), allow_additions=True)
    plan = json.dumps({"children": [{"name": "c1", "statement": "Lemma c1 : True."}], "definitions": [{"name": "v", "text": "Definition v : nat := 0."}]})
    cfg = plain_cfg(tmp_path, decomposer_runner=ScriptedDecomposerRunner([plan]), max_design_rounds=3, decomposer_seconds=5)
    driver = DesignDriver(cfg, graph, root, contract=contract)
    out_dev = asyncio.run(driver.initial(dev))
    assert out_dev is dev and driver.rounds_used == 2
    assert seen == [contract, contract], "the same contract object in round 1 and in the repair round"
    assert [k for k, in [(e["kind"],) for e in graph.events_since()] if k.startswith("design.")] == ["design.rejected"]
    assert graph.by_name("c1") is not None
    graph.close()


def test_a_rejected_initial_proposal_is_reasked_and_the_rounds_are_counted_once(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=())
    bad = '{"children": [{"name": "helper", "statement": "Lemma helper : True."}]}'
    good = '{"children": [{"name": "c1", "statement": "Lemma c1 : True."}]}'
    cfg = plain_cfg(tmp_path, decomposer_runner=ScriptedDecomposerRunner([bad, bad, good]), max_design_rounds=3, decomposer_seconds=5)
    driver = DesignDriver(cfg, graph, root, contract=DesignContract.everything_frozen())
    asyncio.run(driver.initial(dev))
    assert driver.rounds_used == 3 and cfg.decomposer_runner.calls == 3
    assert graph.by_name("c1") is not None and graph.by_name("helper") is None
    graph.close()
    graph2, root2, dev2 = build_plain_graph(tmp_path / "b", names=())
    cfg2 = plain_cfg(tmp_path / "b", decomposer_runner=ScriptedDecomposerRunner([bad]), max_design_rounds=2, decomposer_seconds=5)
    with pytest.raises(OrchestrationRequired, match="Tried 2 of 2"):
        asyncio.run(DesignDriver(cfg2, graph2, root2, contract=DesignContract.everything_frozen()).initial(dev2))
    assert cfg2.decomposer_runner.calls == 2
    graph2.close()


def test_no_decomposer_and_no_plan_is_orchestration_required(tmp_path):
    cfg = plain_cfg(tmp_path, plan_source=None)
    cfg.plan = None
    with pytest.raises(OrchestrationRequired, match="no decomposer runner"):
        asyncio.run(prove(cfg, MockRunner({})))


# --- end to end with real Rocq ------------------------------------------------------

CANARY_ANSWERS = {
    "canary_swap": 'iIntros "[HA HB]". iFrame.',
    "canary_assoc": 'iIntros (A B C) "[HA [HB HC]]". iFrame.',
    "canary_main": 'iIntros "H". iDestruct (canary_swap with "H") as "[HQR HP]". iDestruct "HQR" as "[HQ HR]". iFrame.',
    "canary_dup_intro": 'iIntros "[H1 H2]". rewrite /canary_dup. iFrame.',
}


@needs_rocq
def test_a_children_only_decomposition_is_adopted_dispatched_and_integrated(tmp_path, canary_dir):
    plan = json.dumps({"children": [
        {"name": "canary_swap", "statement": "Lemma canary_swap (A B : PROP) : A ∗ B -∗ B ∗ A."},
        {"name": "canary_assoc", "statement": "∀ (A B C : PROP), A ∗ (B ∗ C) -∗ (A ∗ B) ∗ C"},
    ]})
    cfg = ProveConfig(
        file=canary_dir / "Canary.v", target="canary_main", graph_path=tmp_path / "g.db", workroot=tmp_path / "w",
        node_seconds=60, decomposer_runner=ScriptedDecomposerRunner([plan]), decomposer_seconds=5, run_lock=False,
    )
    result = asyncio.run(prove(cfg, MockRunner(dict(CANARY_ANSWERS))))
    assert result.integrated, result.render()
    assert "decomposer: scripted" in result.render() and "plan: 2 obligation(s)" in result.render()
    assert result.graph.get_meta("designed_file") is None, "children only: no designed copy"
    result.close()


@needs_rocq
def test_a_design_with_a_definition_is_applied_typechecked_and_proved(tmp_path, canary_dir):
    plan = json.dumps({
        "definitions": [{"name": "canary_dup", "text": "Definition canary_dup (P : PROP) : PROP := (P ∗ P)%I."}],
        "children": [
            {"name": "canary_dup_intro", "statement": "Lemma canary_dup_intro (P : PROP) : P ∗ P -∗ canary_dup P."},
            {"name": "canary_swap", "statement": "Lemma canary_swap (A B : PROP) : A ∗ B -∗ B ∗ A."},
        ],
    })
    seen = []
    cfg = ProveConfig(
        file=canary_dir / "Canary.v", target="canary_main", graph_path=tmp_path / "g.db", workroot=tmp_path / "w",
        node_seconds=60, decomposer_runner=ScriptedDecomposerRunner([plan]), decomposer_seconds=5, run_lock=False,
        contract=DesignContract(allow_additions=True), record_root=tmp_path / "rec",
    )
    result = asyncio.run(prove(cfg, MockRunner(dict(CANARY_ANSWERS), on_dispatch=seen.append)))
    assert result.integrated, result.render()
    designed = tmp_path / "w" / "canary_main.designed" / "Canary.v"
    assert designed.exists() and "Definition canary_dup" in designed.read_text()
    text = designed.read_text()
    assert text.index("Section canary.") < text.index("Definition canary_dup") < text.index("Lemma canary_main")
    assert result.graph.get_meta("designed_file") == str(designed)
    for p in seen:
        assert p.file == str(designed)
        assert json.loads((p.workdir / "pcp-node.json").read_text())["file"] == str(designed.resolve())
    assert result.solution is not None and "COMPLETE" in result.solution.read_text()[:400]
    assert "INCOMPLETE" not in result.solution.read_text()[:400]
    result.close()


@needs_rocq
def test_a_child_statement_that_does_not_typecheck_is_caught_before_dispatch(tmp_path, canary_dir):
    bad = json.dumps({"children": [{"name": "canary_bad", "statement": "Lemma canary_bad (A : PROP) : A ∗ nonsense_ident -∗ A."}]})
    cfg = ProveConfig(
        file=canary_dir / "Canary.v", target="canary_main", graph_path=tmp_path / "g.db", workroot=tmp_path / "w",
        node_seconds=60, decomposer_runner=ScriptedDecomposerRunner([bad]), decomposer_seconds=5, run_lock=False, max_design_rounds=2,
    )
    dispatched = []
    with pytest.raises(OrchestrationRequired) as exc:
        asyncio.run(prove(cfg, MockRunner({}, on_dispatch=dispatched.append)))
    assert "does not typecheck (`canary_bad`)" in str(exc.value)
    assert "nonsense_ident" in str(exc.value) and dispatched == []


@needs_rocq
def test_a_contest_is_settled_by_the_approver_restating_the_obligation_without_a_design_round(tmp_path, canary_dir):
    """Round 8 of the spec-only seqlock_wf run: two children stated a resource outside a
    □-boxed triple, the prover contested validly, and the contests reached the report
    unadjudicated because the design rounds were spent.  The approver now restates the
    obligation itself; the run integrates without another decomposer round."""
    from pcp.orch.protocol import ADJUDICATED_MARKER

    plan = json.dumps({"children": [
        {"name": "canary_swap", "statement": "Lemma canary_swap (A B : PROP) : A ∗ B -∗ B ∗ A."},
        {"name": "canary_wrong", "statement": "Lemma canary_wrong (A B : PROP) : A -∗ B."},
    ]})
    fixed = "Lemma canary_wrong (A B : PROP) : B -∗ B."
    decomposer = ScriptedDecomposerRunner([plan])
    approver = ScriptedDecomposerRunner([json.dumps({"verdict": "statement", "restatement": fixed, "hint": "B was never a premise"})])

    class ContestingRunner(MockRunner):
        def __init__(self, answers):
            super().__init__(answers)
            self.dispatches: list[tuple[str, str]] = []

        def scripted_answer(self, node):
            self.dispatches.append((node.name, node.evidence))
            if node.name == "canary_wrong" and not node.evidence.startswith(ADJUDICATED_MARKER):
                return {"status": "contested", "evidence": "A -∗ B is not provable: B is nowhere in the premises"}
            return super().scripted_answer(node)

    answers = dict(CANARY_ANSWERS)
    answers["canary_wrong"] = 'iIntros "HB". iFrame.'
    runner = ContestingRunner(answers)
    cfg = ProveConfig(
        file=canary_dir / "Canary.v", target="canary_main", graph_path=tmp_path / "g.db", workroot=tmp_path / "w",
        node_seconds=60, decomposer_runner=decomposer, approver_runner=approver, decomposer_seconds=5, approver_seconds=5,
        run_lock=False, max_design_rounds=1, contract=DesignContract(allow_additions=True),
    )
    result = asyncio.run(prove(cfg, runner))
    trail = [(e["kind"], e.get("payload")) for e in result.graph.events_since(0, limit=5000)
             if e["kind"] in ("contest.adjudicated", "approver.verdict", "restatement.rejected", "decomposer.violation", "decomposer.failed", "node.restated_by_adjudication")]
    assert result.integrated, (result.render(), trail)
    assert decomposer.calls == 1, "a statement being wrong costs no design round"
    assert approver.calls == 1
    node = result.graph.by_name("canary_wrong")
    assert node.epoch == 1 and node.statement == fixed and node.proof_status in ("gated", "integrated")
    kinds = [e["kind"] for e in result.graph.events_since(0, limit=5000)]
    assert "node.restated_by_adjudication" in kinds and "plan.restated" in kinds and "restatement.rejected" not in kinds
    names = [d[0] for d in runner.dispatches]
    assert names.count("canary_wrong") == 2 and names.count("canary_swap") == 1
    reopened = [ev for n, ev in runner.dispatches if n == "canary_wrong" and ev.startswith(ADJUDICATED_MARKER)]
    assert len(reopened) == 1 and "The old statement was" in reopened[0] and "A -∗ B." in reopened[0]
    result.close()


@needs_rocq
def test_a_twice_failed_node_is_reviewed_by_the_approver_before_its_budget_is_spent(tmp_path, canary_dir):
    """PLAN.md 8.9: a node escalated twice is a statement problem -- or a strategy one.
    Either way a verdict costs seconds where each further attempt costs the node's
    clock (i31 on the spec-only seqlock_wf run: four 45-minute deadline kills)."""
    from pcp.orch.protocol import ADJUDICATED_MARKER

    plan = json.dumps({"children": [{"name": "canary_swap", "statement": "Lemma canary_swap (A B : PROP) : A ∗ B -∗ B ∗ A."}]})
    decomposer = ScriptedDecomposerRunner([plan])
    approver = ScriptedDecomposerRunner([json.dumps({"verdict": "strategy", "hint": "destruct the star and frame both halves"})])

    class FailingTwiceRunner(MockRunner):
        def __init__(self, answers):
            super().__init__(answers)
            self.dispatches: list[tuple[str, str]] = []

        def scripted_answer(self, node):
            self.dispatches.append((node.name, node.evidence))
            if node.name == "canary_swap" and not node.evidence.startswith(ADJUDICATED_MARKER):
                return {"status": "stuck", "evidence": "iFrame left a goal open"}
            return super().scripted_answer(node)

    runner = FailingTwiceRunner(dict(CANARY_ANSWERS))
    cfg = ProveConfig(
        file=canary_dir / "Canary.v", target="canary_main", graph_path=tmp_path / "g.db", workroot=tmp_path / "w",
        node_seconds=60, decomposer_runner=decomposer, approver_runner=approver, decomposer_seconds=5, approver_seconds=5,
        run_lock=False, max_design_rounds=1, max_attempts=4, review_after=2,
    )
    result = asyncio.run(prove(cfg, runner))
    assert result.integrated, result.render()
    assert approver.calls == 1 and decomposer.calls == 1
    swap = result.graph.by_name("canary_swap")
    rows = [(a["epoch"], a["status"]) for a in result.graph.attempts_for(swap.id) if a["role"] == "prover"]
    assert rows == [(0, "stuck"), (0, "stuck"), (1, "qed")], rows
    kinds = [e["kind"] for e in result.graph.events_since(0, limit=5000)]
    assert "node.for_review" in kinds and "node.reopened_by_adjudication" in kinds
    names = [d[0] for d in runner.dispatches]
    assert names.count("canary_swap") == 3 and swap.epoch == 1
    result.close()


# --- the design budget, the frozen target and the report -----------------------------


def test_design_rounds_are_bounded_across_resumes(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=())
    for rnd in (1, 2):
        a = graph.start_attempt(root.id, runner="d", role="decomposer", round=rnd)
        graph.finish_attempt(a, status="stuck", evidence="rejected")
    assert design_rounds_used(graph, root) == 2
    plan = '{"children": [{"name": "c1", "statement": "Lemma c1 : True."}]}'
    runner = ScriptedDecomposerRunner([plan])
    cfg = plain_cfg(tmp_path, decomposer_runner=runner, max_design_rounds=2, decomposer_seconds=5)
    with pytest.raises(OrchestrationRequired, match="design budget is spent"):
        asyncio.run(DesignDriver(cfg, graph, root, contract=DesignContract.everything_frozen()).initial(dev))
    assert runner.calls == 0, "the budget is checked before the decomposer is spent"
    cfg.max_design_rounds = 3
    asyncio.run(DesignDriver(cfg, graph, root, contract=DesignContract.everything_frozen()).initial(dev))
    rows = [r for r in graph.attempts_for(root.id) if r["role"] == "decomposer"]
    assert runner.calls == 1 and rows[-1]["round"] == 3 and graph.by_name("c1") is not None
    graph.close()


def test_the_run_target_is_frozen_whatever_the_contract_says(tmp_path):
    loose = DesignContract(results=frozenset({"helper"}), mutable_lemmas=True, allow_additions=True)
    frozen = freeze_target(loose, "root")
    assert frozen.results == {"helper", "root"} and freeze_target(frozen, "root") is frozen
    assert freeze_target(object(), "root") is not None  # a contract without results is left alone
    graph, root, dev = build_plain_graph(tmp_path, names=())
    rewrite = json.dumps({
        "definitions": [{"name": "root", "text": "Definition root : Prop."}],
        "children": [{"name": "c", "statement": "Lemma c : True."}],
    })
    cfg = plain_cfg(
        tmp_path, plan_source=None, decomposer_runner=ScriptedDecomposerRunner([rewrite]),
        max_design_rounds=1, decomposer_seconds=5, contract=loose,
    )
    graph.close()
    with pytest.raises(OrchestrationRequired) as exc:
        asyncio.run(prove(cfg, MockRunner({})))
    assert "root: changed" in str(exc.value) and "result to be proved" in str(exc.value)
    graph = Graph(cfg.graph_path)
    assert graph.get_meta("designed_file") is None
    graph.close()


def test_the_report_stays_one_screen_with_a_dozen_children_and_revisions(tmp_path):
    names = [f"child_{i}" for i in range(12)]
    plan = parse_proposal(json.dumps({"children": [{"name": n, "statement": f"Lemma {n} : True."} for n in names]}))
    rejected = DecompositionResult(problems=[f"problem {i}" for i in range(8)], round=3)
    report = RunReport(outcomes=[NodeOutcome(n, n, "stuck", evidence="x" * 300) for n in names] + [NodeOutcome("root", "root", "stuck", evidence="y")])
    graph, root, dev = build_plain_graph(tmp_path, names=())
    result = ProveResult(
        report=report, sentinels=SentinelReport(), graph=graph, root=root,
        decomposition=DecompositionResult(proposal=plan, model="m"),
        design_rounds=[DecompositionResult(proposal=plan, model="m", round=2), rejected],
        integration_detail="13 open", record_dir=tmp_path,
    )
    lines = result.render().splitlines()
    assert len(lines) <= 24, "\n".join(lines)
    assert lines[0] == "decomposer: m -- plan: 12 obligation(s)"
    assert lines[1] == "design revision 2: plan: 12 obligation(s)"
    assert lines[2].startswith("design revision 3: decomposition rejected:") and "(+5 more)" in lines[2]
    assert max(len(x) for x in lines if not x.startswith(("records:", "solution:"))) <= 140
    graph.close()


def test_design_failure_after_running_is_a_result_not_a_usage_error() -> None:
    assert issubclass(DesignFailed, OrchestrationRequired)
    assert DesignFailed("x").exit_code == 1
    assert OrchestrationRequired("x").exit_code == 2


def test_standing_contested_and_exhausted_nodes_count_as_design_failures(tmp_path: Path) -> None:
    """A resumed run whose single dispatched node proved still has the design's business
    to finish when a contested child and an attempt-exhausted child sit in the graph."""
    g = Graph(tmp_path / "g.db")
    for name, status in (("root", "gated"), ("c_contested", "contested"), ("c_spent", "stuck"), ("c_live", "stuck")):
        g.add_node(Node(id=node_id(name), name=name, statement=f"Lemma {name} : True.", statement_status="frozen",
                        rank="root" if name == "root" else "local"))
        if status != "open":
            g.set_proof_status(node_id(name), "claimed")
            if status == "gated":
                g.record_proof(node_id(name), "exact I.")
            else:
                g.set_proof_status(node_id(name), status, evidence=f"{name} evidence")
    for _ in range(2):
        aid = g.start_attempt(node_id("c_spent"), runner="mock", owner="human")
        g.finish_attempt(aid, status="stuck")
    aid = g.start_attempt(node_id("c_live"), runner="mock", owner="human")
    g.finish_attempt(aid, status="stuck")
    report = RunReport(outcomes=[NodeOutcome(node_id=node_id("root"), name="root", status="qed")])
    assert not design_failed(report)
    standing = standing_failures(g, report, max_attempts=2)
    assert sorted(o.name for o in standing.outcomes) == ["c_contested", "c_spent"]  # c_live still has an attempt
    assert design_failed(RunReport.combined([report, standing]))
    g.close()


def test_the_glue_rationale_reaches_the_root_prover(tmp_path: Path) -> None:
    """The decomposer's account of how the parent follows from the children becomes the
    root's intent and reaches the root prover's packet."""
    src = tmp_path / "D.v"
    src.write_text("Lemma root : True.\nProof.\nAdmitted.\n", encoding="utf-8")
    dev = Development(src)
    graph = Graph(tmp_path / "g.db")
    root = graph.add_node(Node(id=node_id("root"), name="root", statement="Lemma root : True.", statement_status="frozen", rank="root"))
    proposal = parse_payload({
        "children": [{"name": "c1", "statement": "Lemma c1 : 1 = 1."}],
        "glue_rationale": "Deposit the atomic update at the load of the version; collect Q in the failure branch.",
    })
    cfg = ProveConfig(file=src, target="root", workroot=tmp_path / "work", contract=DesignContract.everything_frozen())
    adopt_proposal(cfg, graph, dev, root, proposal)
    root = graph.require(root.id)
    assert root.intent.startswith("Deposit the atomic update")
    paths = build_packet(graph, root, dev, siblings_of(graph, dev), anchor="root", root=tmp_path / "work", attempt_id=1)
    task = paths.task.read_text(encoding="utf-8")
    assert "## Why this lemma exists" in task and "Deposit the atomic update" in task
    graph.close()


# --- rwcas_design: contract, staging, sandbox ------------------------------------------


@needs_rocq
def test_rwcas_design_contract_import_and_frozen_result(tmp_path, bench_dir):
    corpus = tmp_path / "rwcas_design"
    shutil.copytree(bench_dir / "rwcas_design", corpus)
    contract = freeze_target(DesignContract.from_corpus(corpus), "write_spec")
    assert {"is_rwcas", "rwcasG", "value"} == set(contract.mutable) and "write_spec" in contract.results
    dev = Development(corpus / "Rwcas.v")
    graph = Graph(tmp_path / "g.db")
    root = graph.add_node(Node(id=node_id("write_spec"), name="write_spec", statement=dev.require_block("write_spec").statement, rank="root", statement_status="frozen"))
    cfg = ProveConfig(file=corpus / "Rwcas.v", target="write_spec", graph_path=tmp_path / "g.db", workroot=tmp_path / "w", run_lock=False)
    design = parse_proposal(json.dumps({
        "imports": ["From iris.base_logic.lib Require Import ghost_var."],
        "definitions": [
            {"name": "rwcasG", "text": "Class rwcasG Σ := {\n  rwcas_heapGS :: heapGS Σ;\n  rwcas_ghost_varG :: ghost_varG Σ Z;\n}."},
            {"name": "value", "text": "Definition value (γ : gname) (n : Z) : iProp Σ := ghost_var γ (1/2) n."},
            {"name": "rwcas_inv", "text": "Definition rwcas_inv (γ : gname) (l : loc) : iProp Σ := (∃ n : Z, l ↦ #n ∗ ghost_var γ (1/2) n)%I."},
            {"name": "is_rwcas", "text": "Definition is_rwcas (γ : gname) (v : val) : iProp Σ := (∃ l : loc, ⌜v = #l⌝ ∗ inv rwcasN (rwcas_inv γ l))%I."},
        ],
        "children": [{"name": "rwcas_value_agree", "statement": "Lemma rwcas_value_agree (γ : gname) (n m : Z) : value γ n -∗ value γ m -∗ ⌜n = m⌝."}],
    }))
    designed = apply_design(cfg, graph, dev, root, design, contract=contract, round_no=1, workroot=tmp_path / "w")
    text = designed.source
    assert "ghost_var." in "\n".join(text.splitlines()[:5]) and text.index("Definition rwcas_inv") < text.index("Definition is_rwcas")
    assert graph.get_meta("designed_file") == str(designed.path)
    for name, bad_text in (("rwcasN", 'Definition rwcasN : namespace := N .@ "other".'), ("write_spec", "Definition write_spec : Prop.")):
        bad = parse_proposal(json.dumps({"definitions": [{"name": name, "text": bad_text}], "children": [{"name": "c", "statement": "Lemma c : True."}]}))
        with pytest.raises(DesignViolatesContract, match=f"{name}: changed"):
            apply_design(cfg, graph, dev, root, bad, contract=contract, round_no=2, workroot=tmp_path / "w")
    graph.close()


def test_spec_only_staging_binds_only_the_staged_directory_into_the_sandbox(tmp_path, bench_dir):
    corpus = tmp_path / "rwcas_design"
    shutil.copytree(bench_dir / "rwcas_design", corpus)
    cfg = ProveConfig(file=corpus / "Rwcas.v", target="write_spec", graph_path=tmp_path / "g.db", workroot=tmp_path / "w", brief="spec-only", run_lock=False)
    staged = stage_spec_only(cfg, node_id("write_spec"), contract=DesignContract.from_corpus(corpus))
    assert sorted(p.name for p in staged.path.parent.iterdir()) == ["Rwcas.v", "_CoqProject", "design.json"]
    assert set(json.loads((staged.path.parent / "design.json").read_text())) == {"mutable", "results", "mutable_lemmas", "allow_additions", "allow_imports", "frozen_names"}
    from pcp.orch.runners import sandbox as sb

    if not sb.available():
        pytest.skip("no bubblewrap")
    box = sb.Sandbox.for_benchmark(ROOT, reference=tmp_path / "ref", corpus_dir=staged.path.parent, provider="anthropic", root=tmp_path / "stage")
    box = dataclasses.replace(box, refresh_credentials=False, clearenv=True)
    argv = box.wrap(["claude", "-p"], workdir=tmp_path / "w" / "n" / "a1", node_file_dir=staged.path.parent)
    joined = " ".join(argv)
    assert str(corpus) not in joined and str(bench_dir) not in joined and str(staged.path.parent) in joined
    binds = [argv[i + 1] for i, a in enumerate(argv) if a in ("--ro-bind", "--bind")]
    assert not [b for b in binds if (Path(b) / "DESIGN.md").exists() or Path(b).name == "DESIGN.md"]
    masked = [argv[i + 1] for i, a in enumerate(argv) if a == "--tmpfs"]
    assert str(ROOT / "eval") in masked and str(ROOT / ".pcp") in masked
