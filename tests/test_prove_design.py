"""pcp.orch.prove.design: application, placement, the contract, staging, the ladder."""

from __future__ import annotations

import asyncio
import json

import pytest

from pcp.orch.contract import DesignContract
from pcp.orch.decomposer import DecompositionResult, parse_proposal
from pcp.orch.model import Node, node_id
from pcp.orch.protocol import NodeResult
from pcp.orch.prove import OrchestrationRequired, ProveConfig, prove
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
    place_additions,
    refresh_after_revision,
    scan_fragment,
    stage_spec_only,
    why_it_failed,
)
from pcp.orch.runners.mock import MockRunner
from pcp.orch.schedule import NodeOutcome, RunReport
from pcp.rocq.assemble import NodeSpec
from tests._orch_fixtures import build_plain_graph, plain_cfg
from tests.conftest import needs_rocq

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


class ScriptedDecomposerRunner:
    name = "scripted-decomposer"

    def __init__(self, answers: list[str]):
        self.answers = list(answers)
        self.calls = 0

    def available(self):
        return True

    async def run_node(self, node):
        text = self.answers[min(self.calls, len(self.answers) - 1)]
        self.calls += 1
        return NodeResult(status="qed", raw=text, trace={"final_text": text, "model": "scripted"})


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
