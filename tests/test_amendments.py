"""pcp.orch.prove.amendments: the one-conjunct route back to the design (PLAN.md 8.5).

Parsing, the strengthening surgery, the scheduler surfacing requests, applying one
against a synthetic development (a scripted ``apply_design`` and ``FakeGate`` stand in
for ``coqc``), the loop through ``prove()``, contest adjudication, the report and the
packet -- and one real-Rocq run on a tiny Iris file.
"""

from __future__ import annotations

import asyncio
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import pytest

import pcp.orch.prove as prove_mod
import pcp.orch.prove.amendments as amend_mod
import pcp.orch.prove.design as design_mod
from pcp.orch.contract import DesignContract
from pcp.orch.graph import Graph
from pcp.orch.model import Budget, Node, node_id
from pcp.orch.packet import render_task
from pcp.orch.protocol import (
    ADJUDICATED_MARKER,
    AMENDED_MARKER,
    ANSWER_FILE,
    AmendmentRequest,
    LemmaRequest,
    NodePayload,
    NodeResult,
    parse_requests,
    read_answer_file,
)
from pcp.orch.prove import ProveConfig, ProveResult, prove
from pcp.orch.prove.amendments import (
    AmendmentOutcome,
    AmendmentRefused,
    AmendmentRun,
    amendment_detail,
    apply_amendment,
    strengthened_definition,
)
from pcp.orch.prove.design import ADOPTED_PROPOSAL_META, DesignViolatesContract, design_dir, design_evidence
from pcp.orch.prove.resume import DESIGNED_FILE_META
from pcp.orch.runners.mock import MockRunner
from pcp.orch.schedule import NodeOutcome, RunReport, Scheduler, attempts_spent, requested_amendments
from pcp.orch.sentinels import SentinelReport
from pcp.rocq.assemble import Development
from pcp.util.io import atomic_write_text, ensure_dir, json_dump
from tests._orch_fixtures import FakeGate, write_plain
from tests.conftest import needs_rocq

# --- fixtures -------------------------------------------------------------------

SOURCE = """(* a plain development, no Iris *)
Set Default Proof Using "Type".

Definition my_inv (n : nat) : Prop := n = 0.

Definition wraps (n : nat) : Prop := my_inv n.

Lemma root (P Q : Prop) : P -> Q -> P.
Proof.
Admitted.
"""

CONTRACT = DesignContract(mutable=frozenset({"my_inv"}), allow_additions=True)
ADD = AmendmentRequest(definition="my_inv", add="n < 5", at="closing my_inv after the step", why="the bound is needed", requester="i33")


def _events(graph: Graph) -> list[str]:
    return [e["kind"] for e in graph.events_since(limit=5000)]


def _payloads(graph: Graph, kind: str) -> list[dict[str, Any]]:
    return [e["payload"] for e in graph.events_since(limit=5000) if e["kind"] == kind]


def _spend(graph: Graph, node: Node, n: int, *, status: str = "stuck", body: str | None = None) -> None:
    for _ in range(n):
        a = graph.start_attempt(node.id, runner="mock", role="prover")
        graph.finish_attempt(a, status=status, evidence="tried", body=body)


def synthetic_graph(tmp_path: Path) -> tuple[Graph, Node, Development]:
    """Root plus six children in every state the amendment path distinguishes."""
    dev_path, _ = write_plain(tmp_path, source=SOURCE, plan=None)
    dev = Development(dev_path)
    graph = Graph(tmp_path / "graph.db")
    root = graph.add_node(Node(
        id=node_id("root"), name="root", statement=dev.require_block("root").statement, rank="root",
        statement_status="frozen", owner="human", is_glue=True, ordering=1_000_000, file=str(dev_path),
    ))
    statements = {
        "i33": "Lemma i33 (n : nat) : my_inv n -> n = 0.",            # the requester, stuck, one attempt spent
        "fc50_spec": "Lemma fc50_spec (n : nat) : n = 0 -> my_inv n.",  # proved; its proof closes my_inv
        "other": "Lemma other (P : Prop) : P -> P.",                    # proved, unaffected
        "via_wraps": "Lemma via_wraps (n : nat) : wraps n -> True.",    # contested; mentions my_inv through wraps
        "stuck_free": "Lemma stuck_free (Q : Prop) : Q -> Q.",          # stuck, attempts left, unrelated
        "spent": "Lemma spent (R : Prop) : R -> R.",                    # stuck, budget gone, unrelated
    }
    for i, (name, statement) in enumerate(statements.items()):
        child = graph.add_node(Node(
            id=node_id(name), name=name, statement=statement, rank="local", parent=root.id, depth=1,
            statement_status="frozen", owner="human", ordering=i, file=str(dev_path),
        ))
        graph.add_edge(root.id, child.id)
    for name, body in (("fc50_spec", "unfold my_inv. closes_inv."), ("other", "intros H. exact H.")):
        graph.set_proof_status(node_id(name), "claimed")
        graph.record_proof(node_id(name), body)
    for name, spent in (("i33", 1), ("stuck_free", 1), ("spent", 2)):
        _spend(graph, graph.by_name(name), spent)
        graph.set_proof_status(node_id(name), "claimed")
        graph.set_proof_status(node_id(name), "stuck", evidence=f"{name}: stuck at the close site")
    graph.set_proof_status(node_id("via_wraps"), "claimed")
    graph.set_proof_status(node_id("via_wraps"), "contested", evidence="via_wraps: the statement is wrong")
    return graph, root, dev


def fake_apply_design(cfg, graph, dev, root, proposal, *, contract, round_no, workroot, preamble=""):
    """``apply_design`` without ``coqc``: splice the definitions, check the contract,
    write the designed copy, set the meta -- what the real one does around the compile."""
    text = dev.source
    for definition in proposal.definitions:
        block = dev.block(definition.name)
        if block is not None:
            text = text[: block.statement_start] + definition.text + text[block.statement_end :]
    check = contract.check(dev.source, text)
    if not check.ok:
        raise DesignViolatesContract(check.detail)
    if not proposal.definitions:
        return dev
    target_dir = ensure_dir(design_dir(workroot, root.id, round_no))
    target = target_dir / dev.path.name
    atomic_write_text(target, text)
    graph.emit("design.applied", root.id, round=round_no, definitions=proposal.definition_names(), file=str(target))
    graph.set_meta(DESIGNED_FILE_META, str(target))
    return Development(target)


@dataclass
class FakeVerdict:
    """Agent B's ``Verdict`` surface, as the amendment path reads it."""

    verdict: str
    definition: str = ""
    text: str = ""
    hint: str = ""
    violation: str = ""

    @property
    def ok(self) -> bool:
        return bool(self.verdict) and not self.violation

    def summary(self) -> str:
        return self.violation or f"{self.verdict} {self.hint}".strip()


class FakeApprover:
    def __init__(self, amendment: FakeVerdict | None = None, contest: dict[str, FakeVerdict] | None = None):
        self.amendment, self.contest = amendment, contest or {}
        self.asked: list[tuple[str, str]] = []

    async def adjudicate_amendment(self, root, amendment, *, evidence, budget_seconds, contract, design):
        self.asked.append(("amendment", amendment.definition))
        assert evidence, "the approver sees the requester's evidence"
        return self.amendment or FakeVerdict("")

    async def adjudicate_contest(self, root, node, *, evidence, budget_seconds, contract, design):
        self.asked.append(("contest", node.name))
        return self.contest.get(node.name, FakeVerdict(""))


class FakeDriver:
    """What ``apply_amendment`` and ``AmendmentRun`` read off a ``DesignDriver``."""

    def __init__(self, cfg, graph, root, *, contract=CONTRACT, approver: FakeApprover | None = None, gate: FakeGate | None = None):
        self.cfg, self.graph, self.root, self.contract = cfg, graph, root, contract
        self.preamble = ""
        self.rounds_used = 1
        self.approver = approver
        self.gate = gate or FakeGate(reject=("closes_inv",))
        self.gate_factory = lambda dev: self.gate

    def decomposer(self, dev):
        assert self.approver is not None, "no approver configured"
        return self.approver


def cfg_for(tmp_path: Path, **kw) -> ProveConfig:
    defaults: dict[str, Any] = dict(
        file=tmp_path / "corpus" / "Plain.v", target="root", graph_path=tmp_path / "graph.db",
        workroot=tmp_path / "work", node_seconds=30, max_attempts=2, run_lock=False,
    )
    defaults.update(kw)
    return ProveConfig(**defaults)


def _apply(tmp_path, graph, root, dev, req, *, driver=None, approved=False, cfg=None):
    cfg = cfg or cfg_for(tmp_path)
    return asyncio.run(apply_amendment(
        cfg, graph, dev, root, req, contract=driver.contract if driver else CONTRACT, round_no=2, driver=driver, approved=approved,
    ))


# --- parsing ---------------------------------------------------------------------


def test_a_stuck_answer_with_an_add_amendment_is_parsed(tmp_path):
    path = tmp_path / ANSWER_FILE
    json_dump(path, {"status": "stuck", "evidence": "closing the invariant",
                     "amendments": [{"definition": "my_inv", "add": "▷ Q", "at": "after the CmpXchg", "why": "needed later"}]})
    result = read_answer_file(path)
    assert result.status == "stuck" and len(result.amendments) == 1
    a = result.amendments[0]
    assert (a.definition, a.kind, a.add, a.at, a.why, a.requester) == ("my_inv", "add", "▷ Q", "after the CmpXchg", "needed later", "")
    assert a.describe() == "my_inv: + ▷ Q"
    assert result.to_json()["amendments"][0]["kind"] == "amend"


def test_a_contested_answer_with_a_replace_amendment_is_parsed(tmp_path):
    path = tmp_path / ANSWER_FILE
    json_dump(path, {"status": "contested", "evidence": "wrong modality",
                     "amendments": [{"definition": "my_inv", "replace": "Definition my_inv (n : nat) : Prop := n < 5.", "rationale": "why"}]})
    result = read_answer_file(path)
    a = result.amendments[0]
    assert result.status == "contested" and a.kind == "replace" and a.text.startswith("Definition my_inv")
    assert a.why == "why", "`rationale` is accepted as a synonym for `why`"
    assert a.describe() == "my_inv: replaced"


def test_malformed_amendments_are_skipped_with_the_reason_kept_in_evidence(tmp_path):
    path = tmp_path / ANSWER_FILE
    json_dump(path, {"status": "stuck", "evidence": "e", "amendments": [
        {"add": "x"}, {"definition": "d"}, "not an object", {"definition": "ok", "add": "y"},
    ]})
    result = read_answer_file(path)
    assert [a.definition for a in result.amendments] == ["ok"]
    assert "without a `definition`" in result.evidence and "neither `add` nor `replace`" in result.evidence
    assert "must be an object" in result.evidence and result.evidence.startswith("e")
    json_dump(path, {"status": "stuck", "amendments": {"definition": "d", "add": "x"}})
    assert read_answer_file(path).amendments == [] and "must be a list" in read_answer_file(path).evidence
    json_dump(path, {"status": "qed", "proof": "done."})
    assert read_answer_file(path).amendments == []


def test_both_request_kinds_are_tagged_and_split_back():
    lemma, amend = LemmaRequest("Lemma h : True.", "r"), AmendmentRequest("d", add="x", requester="n")
    assert lemma.to_json()["kind"] == "lemma" and amend.to_json()["kind"] == "amend"
    lemmas, amendments = parse_requests([lemma.to_json(), amend.to_json(), {"junk": 1}])
    assert [r.statement for r in lemmas] == ["Lemma h : True."] and [a.key() for a in amendments] == [amend.key()]
    assert AmendmentRequest.from_json(amend.to_json()) == amend
    assert AmendmentRequest.from_json({"definition": "d"}) is None


def test_the_dedupe_key_ignores_whitespace_but_not_the_kind():
    a, b = AmendmentRequest("d", add="▷  Q"), AmendmentRequest("d", add="▷ Q", requester="other", at="elsewhere")
    assert a.key() == b.key()
    assert AmendmentRequest("d", replace="▷ Q").key() != a.key()
    assert AmendmentRequest("e", add="▷ Q").key() != a.key()


# --- strengthening ----------------------------------------------------------------


def test_strengthening_keeps_the_iris_scope_outside_the_parentheses():
    out = strengthened_definition("Definition I (γ : gname) : iProp Σ := (∃ n, own γ n)%I.", "⌜n = 0⌝")
    assert out == "Definition I (γ : gname) : iProp Σ := ((∃ n, own γ n) ∗ (⌜n = 0⌝))%I."
    assert strengthened_definition("Definition I : iProp Σ := True%I.", "⌜n = 0⌝") == "Definition I : iProp Σ := (True ∗ (⌜n = 0⌝))%I."


def test_strengthening_a_body_outside_the_iris_scope_parenthesises_it():
    out = strengthened_definition("Definition P (n : nat) : Prop :=\n  n = 0.", " n < 5 ")
    assert out == "Definition P (n : nat) : Prop := (n = 0) ∗ (n < 5)."
    assert strengthened_definition("Definition S : Prop := True.", "P") == "Definition S : Prop := True ∗ (P)."
    # Already one group: not wrapped twice.  A `:=` inside a comment is not the body's.
    out = strengthened_definition("Definition Q (* x := 1 *) : Prop := (1 = 1).", "True")
    assert out == "Definition Q : Prop := (1 = 1) ∗ (True)."
    out = strengthened_definition("Local Definition R : Prop := (a = 1) /\\ (b = 2).", "True")
    assert out == "Local Definition R : Prop := ((a = 1) /\\ (b = 2)) ∗ (True)."


@pytest.mark.parametrize(
    ("sentence", "why"),
    [
        ("Definition foo : nat.", "no `:=` body"),
        ("Lemma foo : True.", "not a Definition"),
        ("Fixpoint f (n : nat) : nat := n.", "not a Definition"),
        ("Definition foo : nat := 0", "no final"),
        ("Definition foo : nat := .", "empty body"),
    ],
)
def test_strengthening_refuses_what_is_not_a_definition_with_a_body(sentence, why):
    with pytest.raises(AmendmentRefused, match=why):
        strengthened_definition(sentence, "True")
    with pytest.raises(AmendmentRefused, match="nothing to add"):
        strengthened_definition("Definition foo : nat := 0.", "   ")


# --- the scheduler ------------------------------------------------------------------


class AskingRunner(MockRunner):
    """A mock prover that asks for an amendment until the packet says the design changed."""

    def __init__(self, answers, *, asks: dict[str, list[dict[str, str]]], always: bool = False, **kw):
        super().__init__(answers, **kw)
        self.asks, self.always = asks, always
        self.dispatches: list[tuple[str, str]] = []

    def scripted_answer(self, node: NodePayload) -> dict[str, Any]:
        self.dispatches.append((node.name, node.evidence))
        if node.name in self.asks and (self.always or not node.evidence.startswith(AMENDED_MARKER)):
            return {"status": "stuck", "evidence": f"stuck closing the invariant in {node.name}", "amendments": self.asks[node.name],
                    "requests": [{"statement": "Lemma helper : True.", "rationale": "r"}]}
        return super().scripted_answer(node)


def test_the_scheduler_surfaces_amendments_and_stores_both_kinds_without_spending_the_retry(tmp_path):
    graph, root, dev = synthetic_graph(tmp_path)
    graph.set_proof_status(node_id("stuck_free"), "open")
    graph.set_proof_status(node_id("i33"), "open")
    runner = AskingRunner({}, asks={"i33": [{"definition": "my_inv", "add": "n < 5", "at": "close", "why": "w"}],
                                   "stuck_free": [{"definition": "my_inv", "add": "n  <  5"}]})
    report = asyncio.run(Scheduler(graph, dev, runner, anchor="root", gate=FakeGate(), workroot=tmp_path / "w", node_seconds=5).run())
    i33 = next(o for o in report.outcomes if o.name == "i33")
    assert i33.status == "stuck" and i33.attempts == 1, "a design verdict does not spend the retry"
    assert [a.requester for a in i33.amendments] == ["i33"] and i33.requests == [{"kind": "lemma", "statement": "Lemma helper : True.", "rationale": "r"}]
    assert graph.by_name("i33").proof_status == "stuck"
    row = [r for r in graph.attempts_for(node_id("i33")) if r.get("finished")][-1]
    kinds = [r["kind"] for r in json.loads(row["requests"])]
    assert kinds == ["lemma", "amend"] and json.loads(row["requests"])[1]["requester"] == "i33"
    # Deduped across nodes by key: two provers hitting the same missing fact is one amendment.
    asked = report.amendments()
    assert [(a.definition, a.requester) for a in asked] == [("my_inv", "i33")]
    assert "node.asked_amendment" in _events(graph)
    assert "[asks: my_inv: + n < 5]" in i33.one_line()
    graph.close()


def test_with_amendments_off_the_scheduler_retries_as_before(tmp_path):
    graph, root, dev = synthetic_graph(tmp_path)
    graph.set_proof_status(node_id("i33"), "open")
    runner = AskingRunner({}, asks={"i33": [{"definition": "my_inv", "add": "n < 5"}]}, always=True)
    sched = Scheduler(graph, dev, runner, anchor="root", gate=FakeGate(), workroot=tmp_path / "w", node_seconds=5, amendments=False)
    report = asyncio.run(sched.run())
    i33 = next(o for o in report.outcomes if o.name == "i33")
    assert i33.attempts == 1 and len([d for d in runner.dispatches if d[0] == "i33"]) == 1, "one attempt was left at this epoch"
    assert i33.amendments and "node.asked_amendment" not in _events(graph)
    graph.close()


def test_a_qed_asks_for_nothing():
    node = Node(id="n", name="n", statement="Lemma n : True.")
    result = NodeResult(status="qed", proof="done.", amendments=[AmendmentRequest("d", add="x")])
    assert requested_amendments(node, result) == []
    stuck = NodeResult(status="stuck", amendments=[AmendmentRequest("d", add="x")])
    assert [a.requester for a in requested_amendments(node, stuck)] == ["n"]


# --- applying one, synthetically ------------------------------------------------------


def test_an_add_is_applied_replayed_and_reopens_exactly_the_right_nodes(tmp_path, monkeypatch):
    monkeypatch.setattr(amend_mod, "apply_design", fake_apply_design)
    graph, root, dev = synthetic_graph(tmp_path)
    cfg = cfg_for(tmp_path)
    driver = FakeDriver(cfg, graph, root)
    new_dev, outcome = _apply(tmp_path, graph, root, dev, ADD, driver=driver, cfg=cfg)
    assert outcome.applied and outcome.verdict == "auto-accepted", outcome.render()
    assert new_dev.path == tmp_path / "work" / "root.designed2" / "Plain.v"
    assert "Definition my_inv (n : nat) : Prop := (n = 0) ∗ (n < 5)." in new_dev.source
    assert graph.get_meta(DESIGNED_FILE_META) == str(new_dev.path)
    # Replay-first: the proof that closes my_inv fails and reopens at epoch+1; the other holds.
    fc50, other = graph.by_name("fc50_spec"), graph.by_name("other")
    assert fc50.proof_status == "open" and fc50.epoch == 1 and fc50.body is None and fc50.evidence.startswith(AMENDED_MARKER)
    assert other.proof_status == "gated" and other.epoch == 0 and outcome.kept == ["other"]
    # The requester keeps its epoch (an attempt is left, so its partial reaches the packet).
    i33 = graph.by_name("i33")
    assert i33.proof_status == "open" and i33.epoch == 0 and i33.evidence.startswith(AMENDED_MARKER)
    assert "now also carries `n < 5`" in i33.evidence and "requested by `i33`" in i33.evidence
    # Statement-invalidation through one level of unfolding: the contest reopens fresh.
    via = graph.by_name("via_wraps")
    assert via.proof_status == "open" and via.epoch == 1 and via.evidence.startswith(AMENDED_MARKER)
    # Unrelated: with attempts left it goes again and is told what changed; with none it stays.
    free, spent = graph.by_name("stuck_free"), graph.by_name("spent")
    assert free.proof_status == "open" and free.epoch == 0 and free.evidence.startswith(AMENDED_MARKER) and "stuck at the close site" in free.evidence
    assert spent.proof_status == "stuck" and spent.epoch == 0
    assert set(outcome.reopened) == {"fc50_spec", "i33", "via_wraps", "stuck_free"}
    applied = _payloads(graph, "amendment.applied")
    assert len(applied) == 1 and applied[0]["definition"] == "my_inv" and applied[0]["kind"] == "add" and applied[0]["requester"] == "i33"
    assert set(applied[0]["reopened"]) == set(outcome.reopened) and applied[0]["kept"] == ["other"]
    assert "node.reopened_by_amendment" in _events(graph)
    # Later revisions complete from the amended definition.
    adopted = json.loads(graph.get_meta(ADOPTED_PROPOSAL_META))
    assert [d["name"] for d in adopted["definitions"]] == ["my_inv"] and "(n < 5)" in adopted["definitions"][0]["text"]
    assert outcome.render() == (
        "amended my_inv: + n < 5  (requested by i33; reopened fc50_spec, i33, via_wraps, stuck_free; kept 1; "
        "unreviewed: no approver is configured)"
    )
    graph.close()


def test_a_frozen_or_unknown_definition_is_refused_and_the_requester_is_told(tmp_path, monkeypatch):
    monkeypatch.setattr(amend_mod, "apply_design", fake_apply_design)
    graph, root, dev = synthetic_graph(tmp_path)
    frozen = FakeDriver(cfg_for(tmp_path), graph, root, contract=DesignContract(mutable=frozenset({"wraps"})))
    same, outcome = _apply(tmp_path, graph, root, dev, ADD, driver=frozen)
    assert same is dev and not outcome.applied and outcome.verdict == "refused"
    assert "not contract-mutable" in outcome.problems[0] and "may change: `wraps`" in outcome.problems[0]
    assert graph.by_name("i33").evidence.startswith("your amendment request (my_inv: + n < 5) was not applied")
    assert "stuck at the close site" in graph.by_name("i33").evidence, "the old evidence is kept below the note"
    assert graph.by_name("i33").proof_status == "stuck"
    _, unknown = _apply(tmp_path, graph, root, dev, AmendmentRequest("nope", add="x", requester="i33"))
    assert "no definition named `nope`" in unknown.problems[0]
    _, lemma = _apply(tmp_path, graph, root, dev, AmendmentRequest("root", add="x"), driver=FakeDriver(cfg_for(tmp_path), graph, root, contract=DesignContract(mutable=frozenset({"root"}))))
    assert "not a Definition" in lemma.problems[0]
    rejected = _payloads(graph, "amendment.rejected")
    assert len(rejected) == 3 and rejected[0]["definition"] == "my_inv"
    assert graph.get_meta(DESIGNED_FILE_META) is None and not (tmp_path / "work").exists()
    graph.close()


def test_a_replace_needs_an_approver_and_leaves_no_designed_file_behind_the_graph(tmp_path, monkeypatch):
    monkeypatch.setattr(amend_mod, "apply_design", fake_apply_design)
    graph, root, dev = synthetic_graph(tmp_path)
    graph.set_meta(DESIGNED_FILE_META, str(dev.path))
    req = AmendmentRequest("my_inv", replace="Definition my_inv (n : nat) : Prop := n < 5.", requester="i33")
    cfg = cfg_for(tmp_path)  # no decomposer, no approver
    same, outcome = _apply(tmp_path, graph, root, dev, req, cfg=cfg)
    assert same is dev and outcome.verdict == "no approver" and "needs an approver" in outcome.problems[0]
    assert graph.get_meta(DESIGNED_FILE_META) == str(dev.path), "the compiled-but-unapproved copy is not the run's development"
    assert (tmp_path / "work" / "root.designed2").exists(), "the copy was checked before the approver was asked"
    # Pre-approved (a contest verdict's fix): no approver needed, applied as a replace.
    new_dev, ok = _apply(tmp_path, graph, root, dev, req, cfg=cfg, approved=True)
    assert ok.applied and ok.verdict == "accept" and "n < 5." in new_dev.source
    assert ok.render().startswith("amended my_inv: replaced (accept)  (requested by i33;")
    graph.close()


def test_a_replace_is_adjudicated_accept_adjust_reject(tmp_path, monkeypatch):
    monkeypatch.setattr(amend_mod, "apply_design", fake_apply_design)
    req = AmendmentRequest("my_inv", replace="Definition my_inv (n : nat) : Prop := n < 5.", requester="i33", why="w")
    graph, root, dev = synthetic_graph(tmp_path)
    cfg = cfg_for(tmp_path, decomposer_runner=MockRunner({}))
    approver = FakeApprover(FakeVerdict("accept"))
    new_dev, outcome = _apply(tmp_path, graph, root, dev, req, driver=FakeDriver(cfg, graph, root, approver=approver), cfg=cfg)
    assert outcome.applied and outcome.verdict == "accept" and approver.asked == [("amendment", "my_inv")]
    assert "n < 5." in new_dev.source and _payloads(graph, "amendment.adjudicated")[0]["verdict"] == "accept"
    graph.close()

    graph, root, dev = synthetic_graph(tmp_path / "b")
    cfg = cfg_for(tmp_path / "b", decomposer_runner=MockRunner({}))
    adjust = FakeVerdict("adjust", definition="my_inv", text="Definition my_inv (n : nat) : Prop := n < 7.", hint="7 is the bound")
    new_dev, outcome = _apply(tmp_path / "b", graph, root, dev, req, driver=FakeDriver(cfg, graph, root, approver=FakeApprover(adjust)), cfg=cfg)
    assert outcome.applied and outcome.verdict == "adjust" and "n < 7." in new_dev.source and outcome.text.endswith("n < 7.")
    assert graph.get_meta(DESIGNED_FILE_META) == str(new_dev.path)
    graph.close()

    graph, root, dev = synthetic_graph(tmp_path / "c")
    cfg = cfg_for(tmp_path / "c", decomposer_runner=MockRunner({}))
    reject = FakeVerdict("reject", hint="false: the release site cannot restore it")
    same, outcome = _apply(tmp_path / "c", graph, root, dev, req, driver=FakeDriver(cfg, graph, root, approver=FakeApprover(reject)), cfg=cfg)
    assert same is dev and not outcome.applied and outcome.verdict == "reject" and outcome.problems == [reject.hint]
    assert graph.get_meta(DESIGNED_FILE_META) == str(dev.path) and "release site" in graph.by_name("i33").evidence
    graph.close()

    graph, root, dev = synthetic_graph(tmp_path / "d")
    cfg = cfg_for(tmp_path / "d", decomposer_runner=MockRunner({}))
    none = FakeVerdict("", violation="the approver produced no JSON")
    same, outcome = _apply(tmp_path / "d", graph, root, dev, req, driver=FakeDriver(cfg, graph, root, approver=FakeApprover(none)), cfg=cfg)
    assert not outcome.applied and outcome.verdict == "no verdict" and "no usable verdict" in outcome.problems[0]
    graph.close()


def test_a_replace_that_misnames_or_carries_proof_text_is_refused_before_any_compile(tmp_path, monkeypatch):
    def never(*a, **kw):
        raise AssertionError("apply_design must not run")

    monkeypatch.setattr(amend_mod, "apply_design", never)
    graph, root, dev = synthetic_graph(tmp_path)
    _, misnamed = _apply(tmp_path, graph, root, dev, AmendmentRequest("my_inv", replace="Definition other_inv : Prop := True."))
    assert "declares `other_inv`, not `my_inv`" in misnamed.problems[0]
    _, proofy = _apply(tmp_path, graph, root, dev, AmendmentRequest("my_inv", replace="Definition my_inv : Prop := True. Proof. exact I. Qed."))
    assert "proof text" in proofy.problems[0]
    _, hatch = _apply(tmp_path, graph, root, dev, AmendmentRequest("my_inv", add="True. Unset Guard Checking"))
    assert not hatch.applied and ("Unset Guard Checking" in hatch.problems[0] or "not a single sentence" in hatch.problems[0])
    _, two = _apply(tmp_path, graph, root, dev, AmendmentRequest("my_inv", add="True. Definition evil : Prop := True"))
    assert not two.applied and "not a single sentence" in two.problems[0]
    _, axiom = _apply(tmp_path, graph, root, dev, AmendmentRequest("my_inv", replace="Axiom my_inv : Prop."))
    assert not axiom.applied and "axiom" in axiom.problems[0]
    graph.close()


# --- the loop, through prove() -----------------------------------------------------


class ScriptedDecomposerRunner:
    """The decomposer's runner: design answers in order, and -- since the same runner
    stands in as the approver -- a canned verdict for every adjudication packet."""

    name = "scripted-decomposer"

    def __init__(self, answers: list[str], *, verdict: dict[str, str] | None = None):
        self.answers, self.calls, self.design_calls, self.verdicts = list(answers), 0, 0, 0
        self.verdict = verdict or {"verdict": "accept", "why": "scripted"}

    def available(self) -> bool:
        return True

    async def run_node(self, node):
        self.calls += 1
        task = (Path(node.workdir) / "TASK.md").read_text(encoding="utf-8")
        if task.startswith("# Approve, adjust or reject") or task.startswith("# Adjudicate the contest"):
            self.verdicts += 1
            text = "```json\n" + json.dumps(self.verdict, ensure_ascii=False) + "\n```\n"
        else:
            text = self.answers[min(self.design_calls, len(self.answers) - 1)]
            self.design_calls += 1
        return NodeResult(status="qed", raw=text, trace={"final_text": text, "model": "scripted"})


PLAN = json.dumps({"children": [
    {"name": "c1", "statement": "Lemma c1 (n : nat) : my_inv n -> n = 0."},
    {"name": "c2", "statement": "Lemma c2 (P : Prop) : P -> P."},
]})
ANSWERS = {"c1": "intros H. exact H.", "c2": "intros H. exact H.", "root": "intros H _. exact H."}
ASK_C1 = {"c1": [{"definition": "my_inv", "add": "n < 5", "at": "closing my_inv", "why": "the bound"}]}


def _no_coqc(monkeypatch) -> None:
    monkeypatch.setattr(amend_mod, "apply_design", fake_apply_design)
    monkeypatch.setattr(design_mod, "apply_design", fake_apply_design)
    monkeypatch.setattr(prove_mod, "Gate", lambda dev, **kw: FakeGate())


def _loop_cfg(tmp_path: Path, **kw) -> ProveConfig:
    write_plain(tmp_path, source=SOURCE, plan=None)
    defaults: dict[str, Any] = dict(
        decomposer_runner=ScriptedDecomposerRunner([PLAN]), decomposer_seconds=5, max_design_rounds=3,
        contract=CONTRACT, budget=Budget(requests=50, seconds=1800),
    )
    defaults.update(kw)
    return cfg_for(tmp_path, plan=None, **defaults)


def test_the_loop_applies_the_amendment_and_redispatches_with_no_design_revision(tmp_path, monkeypatch):
    _no_coqc(monkeypatch)
    cfg = _loop_cfg(tmp_path)
    runner = AskingRunner(dict(ANSWERS), asks=ASK_C1)
    result = asyncio.run(prove(cfg, runner))
    assert result.integrated, result.render()
    assert result.design_rounds == [] and cfg.decomposer_runner.design_calls == 1, "no design revision round ran"
    assert cfg.decomposer_runner.verdicts == 1, "the approver (the decomposer's runner) read the strengthening"
    assert [(o.applied, o.verdict) for o in result.amendments] == [(True, "accept")]
    c1 = [d for d in runner.dispatches if d[0] == "c1"]
    assert len(c1) == 2 and c1[0][1] == "" and c1[1][1].startswith(AMENDED_MARKER), c1
    assert [d[0] for d in runner.dispatches].count("c2") == 1, "an unaffected proved sibling is not re-dispatched"
    assert result.report.dispatched == 4 and result.graph.by_name("c1").epoch == 0
    assert result.graph.get_meta(DESIGNED_FILE_META) == str(tmp_path / "work" / "root.designed2" / "Plain.v")
    text = result.render()
    assert "amended my_inv: + n < 5  (requested by c1; reopened c1; kept" in text and "design revision" not in text
    assert result.to_json()["amendments"][0]["request"]["kind"] == "amend"
    events = _events(result.graph)
    assert events.count("amendment.applied") == 1 and "node.asked_amendment" in events
    result.close()


def test_the_cap_is_honoured_and_a_capped_request_is_reported(tmp_path, monkeypatch):
    _no_coqc(monkeypatch)
    cfg = _loop_cfg(tmp_path, max_amendments=1)
    asks = dict(ASK_C1, c2=[{"definition": "my_inv", "add": "n < 7", "at": "c2", "why": "w"}])
    runner = AskingRunner(dict(ANSWERS), asks=asks)
    result = asyncio.run(prove(cfg, runner))
    verdicts = sorted(o.verdict for o in result.amendments)
    assert verdicts == ["accept", "capped"], verdicts
    assert sum(o.applied for o in result.amendments) == 1
    capped = next(o for o in result.amendments if o.verdict == "capped")
    assert "--amendments 1" in capped.problems[0] and "amendment refused" in capped.render()
    assert result.integrated, "the capped requester was still re-dispatched (attempts left) and proved"
    assert cfg.decomposer_runner.design_calls == 1 and cfg.decomposer_runner.verdicts == 1
    capped_dispatch = next(d for d in runner.dispatches if d[0] == "c2" and d[1])
    assert "was not applied: --amendments 1" in capped_dispatch[1], "the capped requester is told why"
    assert any(p["verdict"] == "capped" for p in _payloads(result.graph, "amendment.rejected"))
    result.close()


def test_the_loop_stops_when_a_dispatch_asks_for_nothing_new(tmp_path, monkeypatch):
    _no_coqc(monkeypatch)
    cfg = _loop_cfg(tmp_path, max_design_rounds=1)
    runner = AskingRunner(dict(ANSWERS), asks=ASK_C1, always=True)  # asks for the same conjunct forever
    result = asyncio.run(prove(cfg, runner))
    assert [d[0] for d in runner.dispatches].count("c1") == 2, "applied once, re-dispatched once, then the same key is ignored"
    assert len(result.amendments) == 1 and result.amendments[0].applied
    assert not result.integrated and result.graph.by_name("c1").proof_status == "stuck"
    assert _events(result.graph).count("amendment.applied") == 1
    result.close()


def test_amendments_zero_disables_the_path(tmp_path, monkeypatch):
    _no_coqc(monkeypatch)
    cfg = _loop_cfg(tmp_path, max_amendments=0, max_design_rounds=1)
    runner = AskingRunner(dict(ANSWERS), asks=ASK_C1, always=True)
    result = asyncio.run(prove(cfg, runner))
    assert result.amendments == [] and not result.integrated
    assert not any(k.startswith("amendment.") for k in _events(result.graph))
    assert [d[0] for d in runner.dispatches].count("c1") == 2, "the ordinary retry ran instead"
    assert result.graph.get_meta(DESIGNED_FILE_META) is None
    result.close()


# --- contest adjudication -------------------------------------------------------------


def test_contest_adjudication_reopens_on_strategy_and_returns_a_fix_on_statement(tmp_path):
    graph, root, dev = synthetic_graph(tmp_path)
    graph.set_proof_status(node_id("stuck_free"), "open")
    graph.set_proof_status(node_id("stuck_free"), "claimed")
    graph.set_proof_status(node_id("stuck_free"), "contested", evidence="stuck_free: I say it is wrong")
    cfg = cfg_for(tmp_path, decomposer_runner=MockRunner({}))
    approver = FakeApprover(contest={
        "via_wraps": FakeVerdict("strategy", hint="register the update before the CmpXchg"),
        "stuck_free": FakeVerdict("statement", definition="my_inv", text="Definition my_inv (n : nat) : Prop := n < 5.", hint="too weak"),
    })
    run = AmendmentRun(FakeDriver(cfg, graph, root, approver=approver))
    _dev, reopened, fixes = asyncio.run(run.adjudicate(dev, [graph.by_name("via_wraps"), graph.by_name("stuck_free"), graph.by_name("spent")]))
    assert reopened[0] == "via_wraps" and sorted(approver.asked) == [("contest", "stuck_free"), ("contest", "via_wraps")]
    via = graph.by_name("via_wraps")
    assert via.proof_status == "open" and via.epoch == 1 and via.evidence.startswith(ADJUDICATED_MARKER)
    assert "register the update" in via.evidence and "I say" not in via.evidence and "the statement is wrong" in via.evidence
    assert fixes == [] and "amendment.applied" in _events(graph), "the one-definition fix is applied by the adjudication itself"
    assert graph.by_name("stuck_free").proof_status == "open" and "stuck_free" in reopened, "the fix reopened the node it was about"
    assert sorted(p["verdict"] for p in _payloads(graph, "contest.adjudicated")) == ["statement", "strategy"]
    assert "node.reopened_by_adjudication" in _events(graph)
    # Once per node per epoch, and once per run: asking again costs nothing.
    again = asyncio.run(run.adjudicate(dev, [graph.by_name("stuck_free")]))[1:]
    assert again == ([], []) and len(approver.asked) == 2
    fresh = AmendmentRun(FakeDriver(cfg, graph, root, approver=approver))
    assert asyncio.run(fresh.adjudicate(dev, [graph.by_name("stuck_free")]))[1:] == ([], []) and len(approver.asked) == 2
    # An unusable verdict is not remembered, so a later run may ask again.
    graph.set_proof_status(node_id("spent"), "open")
    graph.set_proof_status(node_id("spent"), "claimed")
    graph.set_proof_status(node_id("spent"), "contested", evidence="spent: wrong")
    outage = AmendmentRun(FakeDriver(cfg, graph, root, approver=FakeApprover(contest={"spent": FakeVerdict("", violation="401")})))
    assert asyncio.run(outage.adjudicate(dev, [graph.by_name("spent")]))[1:] == ([], [])
    assert graph.get_meta("contest_adjudicated:spent") is None and graph.by_name("spent").proof_status == "contested"
    bare = AmendmentRun(FakeDriver(cfg_for(tmp_path), graph, root))  # neither decomposer nor approver
    assert asyncio.run(bare.adjudicate(dev, [graph.by_name("spent")]))[1:] == ([], []), "no approver: nothing happens"
    graph.close()


def test_a_contest_left_by_an_earlier_run_is_adjudicated_before_the_first_dispatch(tmp_path, monkeypatch):
    _no_coqc(monkeypatch)
    cfg = _loop_cfg(tmp_path)
    runner = AskingRunner(dict(ANSWERS), asks={})
    runner.statuses = {"c1": "contested"}
    first = asyncio.run(prove(cfg, runner))
    assert first.graph.by_name("c1").proof_status == "contested"
    assert cfg.decomposer_runner.calls >= 1
    first.close()
    # Resume with an approver that says "strategy": c1 is reopened and this time proves.
    calls: list[str] = []

    class Approver:
        async def adjudicate_contest(self, root, node, *, evidence, budget_seconds, contract, design):
            calls.append(node.name)
            assert "scripted contested" in evidence
            return FakeVerdict("strategy", hint="use the stub as given")

        async def adjudicate_amendment(self, *a, **kw):
            raise AssertionError("no amendment was asked")

    monkeypatch.setattr(design_mod.DesignDriver, "decomposer", lambda self, dev: Approver())
    cfg2 = _loop_cfg(tmp_path, decomposer_runner=ScriptedDecomposerRunner([PLAN]))
    runner2 = AskingRunner(dict(ANSWERS), asks={})
    second = asyncio.run(prove(cfg2, runner2))
    assert calls == ["c1"] and second.integrated, second.render()
    c1 = [d for d in runner2.dispatches if d[0] == "c1"]
    assert len(c1) == 1 and c1[0][1].startswith(ADJUDICATED_MARKER) and "use the stub" in c1[0][1]
    assert second.graph.by_name("c1").epoch >= 1 and second.graph.get_meta("contest_adjudicated:c1") is not None
    second.close()


# --- report and packet ------------------------------------------------------------------


def test_outcome_render_and_json_and_the_result_line():
    req = AmendmentRequest("d15", add="▷ Q", at="closing", why="w", requester="i33")
    ok = AmendmentOutcome(req, applied=True, verdict="auto-accepted", reopened=["i33", "fc50_spec"], kept=["a", "b", "c"], round_no=2)
    assert ok.render() == "amended d15: + ▷ Q  (requested by i33; reopened i33, fc50_spec; kept 3; unreviewed: no approver is configured)"
    reviewed = AmendmentOutcome(req, applied=True, verdict="accept", reopened=["i33"], kept=[])
    assert reviewed.render() == "amended d15: + ▷ Q  (requested by i33; reopened i33; kept 0)"
    adjusted = AmendmentOutcome(req, applied=True, verdict="adjust", reopened=["i33"], kept=[])
    assert adjusted.render().startswith("amended d15: + ▷ Q (adjusted by the approver)  (requested by i33;")
    no = AmendmentOutcome(req).refuse("refused", "`d15` is not contract-mutable (nothing may change)")
    assert no.render() == "amendment refused d15: + ▷ Q  (requested by i33): `d15` is not contract-mutable (nothing may change)"
    data = ok.to_json()
    assert data["request"] == req.to_json() and data["applied"] is True and data["round"] == 2 and data["reopened"] == ["i33", "fc50_spec"]
    assert amendment_detail(req).startswith(f"{AMENDED_MARKER} `d15` now also carries `▷ Q` (requested by `i33` at closing: w)")
    rep = AmendmentRequest("d15", replace="Definition d15 : Prop := True.", requester="x")
    assert amendment_detail(rep, "Definition d15 : Prop := True.").endswith("Definition d15 : Prop := True.")

    class G:
        def close(self):
            pass

    result = ProveResult(report=RunReport(), sentinels=SentinelReport(), graph=G(), root=Node(id="r", name="r", statement="Lemma r : True."),
                         amendments=[ok, no], integration_detail="x")
    lines = result.render().splitlines()
    assert lines[0] == ok.render() and lines[1] == no.render() and lines[2] == ""
    assert len(result.to_json()["amendments"]) == 2


def test_the_packet_asks_for_amendments_and_titles_a_reopened_nodes_evidence(tmp_path):
    _, dev = None, Development(write_plain(tmp_path, source=SOURCE, plan=None)[0])
    node = Node(id="i33", name="i33", statement="Lemma i33 (n : nat) : my_inv n -> n = 0.")
    plain = render_task(node, dev, [], scratch_name="Plain.v", evidence="Error: iFrame failed", attempt=2, docs=[])
    assert '"amendments"' in plain and '"add": "▷ Q"' in plain and "closing the invariant after the CmpXchg" in plain
    assert "you do not need to contest the statement for this" in plain and "applied mechanically" in plain
    assert "## What went wrong last time (attempt 1)" in plain and "Do not repeat the same approach" in plain
    amended = render_task(node, dev, [], scratch_name="Plain.v", evidence=amendment_detail(ADD), attempt=2, docs=[])
    assert "## The design changed since your last attempt" in amended and "What went wrong" not in amended
    assert "`my_inv` now also carries `n < 5`" in amended and "AMENDED:" not in amended
    assert "Do not repeat the same approach" not in amended and "partial proof, if any, is in the scratch file" in amended
    adjudicated = render_task(node, dev, [], scratch_name="Plain.v", evidence=f"{ADJUDICATED_MARKER} register earlier\n\nYour contest was: no", docs=[])
    assert "## Your contest was reviewed: the statement stands" in adjudicated and "register earlier" in adjudicated
    assert "Do not contest it again" in adjudicated


def test_design_evidence_quotes_amendment_requests_for_the_decomposer():
    report = RunReport(outcomes=[
        NodeOutcome("1", "i33", "stuck", attempts=1, evidence="Error: iFrame failed", amendments=[ADD]),
        NodeOutcome("2", "x", "contested", evidence="wrong", amendments=[AmendmentRequest("d", replace="Definition d : Prop := True.", requester="x")]),
    ])
    text = design_evidence(report)
    assert "i33 asked for the design to change: `my_inv` to also carry `n < 5`" in text and "at: closing my_inv after the step" in text
    assert "x asked for the design to change: `d` to be restated" in text and "requests, not decisions" in text


# --- review findings (wave 4 adversarial pass) ---------------------------------------------


@pytest.mark.parametrize(
    "conjunct",
    [
        "True) ∨ (False",          # (body) ∗ (True) ∨ (False): ∨ binds looser than ∗ -- not a strengthening
        "True) -∗ (⌜n = 7⌝",       # (body) ∗ (True) -∗ (⌜n = 7⌝): weaker than the body (checked with coqc)
        "True)",                   # unbalanced
        "True (* ",                # an unclosed comment swallows the rest of the file
        "True *) Definition evil : Prop := True. (* ",
        "(True) ∗ (True",          # balanced in count, but the group is closed and reopened
    ],
)
def test_a_conjunct_whose_parentheses_escape_the_group_is_refused_before_any_compile(tmp_path, monkeypatch, conjunct):
    with pytest.raises(AmendmentRefused, match="not one term"):
        strengthened_definition("Definition my_inv (n : nat) : Prop := n = 0.", conjunct)
    with pytest.raises(AmendmentRefused, match="not one term"):
        strengthened_definition("Definition I (γ : gname) : iProp Σ := (∃ n, own γ n)%I.", conjunct)

    def never(*a, **kw):
        raise AssertionError("apply_design must not run")

    monkeypatch.setattr(amend_mod, "apply_design", never)
    graph, root, dev = synthetic_graph(tmp_path)
    _, outcome = _apply(tmp_path, graph, root, dev, AmendmentRequest("my_inv", add=conjunct, requester="i33"))
    assert not outcome.applied and outcome.verdict == "refused" and "not one term" in outcome.problems[0]
    assert "not one term" in graph.by_name("i33").evidence
    graph.close()


def test_a_conjunct_that_is_one_term_may_nest_parentheses_strings_and_comments():
    out = strengthened_definition("Definition I (γ : gname) : iProp Σ := (∃ n, own γ n)%I.", "∃ m, own γ (Excl m) ∗ ⌜m = (0)⌝")
    assert out == "Definition I (γ : gname) : iProp Σ := ((∃ n, own γ n) ∗ (∃ m, own γ (Excl m) ∗ ⌜m = (0)⌝))%I."
    assert strengthened_definition("Definition S : Prop := True.", 'P ")" (* ) *)') == 'Definition S : Prop := True ∗ (P ")" (* ) *)).'
    assert strengthened_definition("Definition S : Prop := True.", "[∗ list] x ∈ l, P x") == "Definition S : Prop := True ∗ ([∗ list] x ∈ l, P x)."


def test_body_shapes_the_strengthening_handles():
    # a trailing comment before the period; a cast body; a multi-line body with comments inside
    assert strengthened_definition("Definition I : iProp Σ := True%I (* trailing *).", "P") == "Definition I : iProp Σ := (True ∗ (P))%I."
    assert strengthened_definition("Definition I := 0 : nat.", "P") == "Definition I := (0 : nat) ∗ (P)."
    assert strengthened_definition("Definition I : Prop :=\n  (* c *) a = 1 /\\\n  b = 2 (* d *).", "P") == "Definition I : Prop := (a = 1 /\\\n  b = 2) ∗ (P)."
    # the `%I` of a sub-term at the end of the body is lifted over the whole conjunction
    assert strengthened_definition("Definition I : iProp Σ := ∀ x, P x ∗ Q%I.", "R") == "Definition I : iProp Σ := ((∀ x, P x ∗ Q) ∗ (R))%I."
    # a `:=` inside the type is not the body's; a `let` in the body is left alone
    assert strengthened_definition("Definition I : (let t := nat in t) := let x := 1 in x.", "P") == "Definition I : (let t := nat in t) := (let x := 1 in x) ∗ (P)."


def test_an_adjustment_is_asked_once_and_a_failed_one_restores_the_designed_file(tmp_path, monkeypatch):
    monkeypatch.setattr(amend_mod, "apply_design", fake_apply_design)
    graph, root, dev = synthetic_graph(tmp_path)
    graph.set_meta(DESIGNED_FILE_META, str(dev.path))
    cfg = cfg_for(tmp_path, decomposer_runner=MockRunner({}))
    two_sentences = "Definition my_inv (n : nat) : Prop := n < 7. Definition evil : Prop := True."
    approver = FakeApprover(FakeVerdict("adjust", definition="my_inv", text=two_sentences, hint="h"))
    req = AmendmentRequest("my_inv", replace="Definition my_inv (n : nat) : Prop := n < 5.", requester="i33")
    same, outcome = _apply(tmp_path, graph, root, dev, req, driver=FakeDriver(cfg, graph, root, approver=approver), cfg=cfg)
    assert same is dev and not outcome.applied and outcome.verdict == "adjust"
    assert "could not be applied" in outcome.problems[0] and "not a single sentence" in outcome.problems[0]
    assert approver.asked == [("amendment", "my_inv")], "the approver is not asked to adjust its adjustment"
    assert graph.get_meta(DESIGNED_FILE_META) == str(dev.path)
    assert "could not be applied" in graph.by_name("i33").evidence
    graph.close()


def test_an_attributed_or_modified_definition_is_strengthened_and_an_attributed_lemma_refused():
    assert strengthened_definition("#[local] Definition my_inv (n : nat) : Prop := n = 0.", "True") == "#[local] Definition my_inv (n : nat) : Prop := (n = 0) ∗ (True)."
    assert strengthened_definition("#[global] Local Definition my_inv : Prop := True.", "P") == "#[global] Local Definition my_inv : Prop := True ∗ (P)."
    with pytest.raises(AmendmentRefused, match="`foo` is a Lemma"):
        strengthened_definition("#[local] Lemma foo : True.", "P")
    with pytest.raises(AmendmentRefused, match="is a Instance"):
        strengthened_definition("Global Instance foo : Persistent P := _.", "Q")


def test_an_add_is_reviewed_by_the_approver_when_one_is_configured(tmp_path, monkeypatch):
    """A strengthened hypothesis is a weakened theorem, so an `add` is a judgement, not a
    compile check: it goes to the approver whenever one exists (auto-accept only when
    nobody can be asked, and then the report says so)."""
    monkeypatch.setattr(amend_mod, "apply_design", fake_apply_design)
    graph, root, dev = synthetic_graph(tmp_path)
    cfg = cfg_for(tmp_path, decomposer_runner=MockRunner({}))
    approver = FakeApprover(FakeVerdict("accept", hint="true at every close site"))
    new_dev, outcome = _apply(tmp_path, graph, root, dev, ADD, driver=FakeDriver(cfg, graph, root, approver=approver), cfg=cfg)
    assert outcome.applied and outcome.verdict == "accept" and approver.asked == [("amendment", "my_inv")]
    assert "(n < 5)" in new_dev.source and "unreviewed" not in outcome.render()
    assert _payloads(graph, "amendment.adjudicated")[0]["verdict"] == "accept"
    graph.close()

    graph, root, dev = synthetic_graph(tmp_path / "reject")
    cfg = cfg_for(tmp_path / "reject", decomposer_runner=MockRunner({}))
    graph.set_meta(DESIGNED_FILE_META, str(dev.path))
    vacuous = AmendmentRequest("my_inv", add="False", at="the goal", why="makes it go through", requester="i33")
    reject = FakeVerdict("reject", hint="nothing can establish my_inv once it carries False")
    same, outcome = _apply(tmp_path / "reject", graph, root, dev, vacuous, driver=FakeDriver(cfg, graph, root, approver=FakeApprover(reject)), cfg=cfg)
    assert same is dev and not outcome.applied and outcome.verdict == "reject" and outcome.problems == [reject.hint]
    assert graph.get_meta(DESIGNED_FILE_META) == str(dev.path), "the compiled-but-rejected copy is not the run's development"
    assert (tmp_path / "reject" / "work" / "root.designed2").exists(), "it was compiled before the approver was asked"
    assert graph.by_name("i33").evidence.startswith("your amendment request (my_inv: + False) was not applied: nothing can establish")
    assert graph.by_name("i33").proof_status == "stuck" and graph.by_name("fc50_spec").proof_status == "gated", "nothing was replayed or reopened"
    assert not _payloads(graph, "amendment.applied")
    graph.close()

    graph, root, dev = synthetic_graph(tmp_path / "nobody")
    cfg = cfg_for(tmp_path / "nobody")  # no decomposer, no approver
    _, outcome = _apply(tmp_path / "nobody", graph, root, dev, ADD, driver=FakeDriver(cfg, graph, root), cfg=cfg)
    assert outcome.applied and outcome.verdict == "auto-accepted" and "unreviewed: no approver is configured" in outcome.render()
    graph.close()


class RefusedThenProves(AskingRunner):
    """Asks once for a conjunct on a frozen definition; proves once told it was refused."""

    def scripted_answer(self, node: NodePayload) -> dict[str, Any]:
        self.dispatches.append((node.name, node.evidence))
        if node.name in self.asks and not node.evidence:
            return {"status": "stuck", "evidence": f"stuck in {node.name}: wraps says too little", "amendments": self.asks[node.name]}
        return {"status": "qed", "proof": ANSWERS[node.name]}


def test_a_refused_request_still_buys_the_requester_its_retry_without_a_design_round(tmp_path, monkeypatch):
    """The scheduler withholds the retry from a `stuck` that asks for an amendment.  When
    the request is refused, that retry used to happen only through a full design
    revision (with a decomposer) or not at all (a plan run)."""
    _no_coqc(monkeypatch)
    asks = {"c1": [{"definition": "wraps", "add": "n < 5", "at": "c1", "why": "w"}]}  # `wraps` is frozen
    cfg = _loop_cfg(tmp_path)
    runner = RefusedThenProves(dict(ANSWERS), asks=asks)
    result = asyncio.run(prove(cfg, runner))
    assert result.integrated, result.render()
    assert result.design_rounds == [] and cfg.decomposer_runner.design_calls == 1, "no design revision paid for the retry"
    assert [(o.applied, o.verdict) for o in result.amendments] == [(False, "refused")]
    c1 = [d for d in runner.dispatches if d[0] == "c1"]
    assert len(c1) == 2 and c1[1][1].startswith("your amendment request (wraps: + n < 5) was not applied: `wraps` is not contract-mutable")
    assert "node.retried_after_refusal" in _events(result.graph) and result.graph.by_name("c1").epoch == 0
    assert result.report.dispatched == 4
    result.close()

    # A plan run: no decomposer at all, and the retry still happens.
    dev_path, plan_path = write_plain(tmp_path / "plan", source=SOURCE, plan=(
        "Lemma c1 (n : nat) : my_inv n -> n = 0.\nProof. Admitted.\n\nLemma c2 (P : Prop) : P -> P.\nProof. Admitted.\n"
    ))
    cfg2 = cfg_for(tmp_path / "plan", plan=plan_path, contract=CONTRACT, budget=Budget(requests=50, seconds=1800))
    runner2 = RefusedThenProves(dict(ANSWERS), asks=asks)
    result2 = asyncio.run(prove(cfg2, runner2))
    assert result2.integrated, result2.render()
    assert [d[0] for d in runner2.dispatches].count("c1") == 2
    result2.close()


def test_a_refusal_never_retries_a_node_out_of_attempts_or_a_second_time(tmp_path, monkeypatch):
    _no_coqc(monkeypatch)
    cfg = _loop_cfg(tmp_path, max_design_rounds=1)
    runner = AskingRunner(dict(ANSWERS), asks={"c1": [{"definition": "wraps", "add": "n < 5"}]}, always=True)  # asks forever
    result = asyncio.run(prove(cfg, runner))
    c1 = [d[0] for d in runner.dispatches].count("c1")
    assert c1 == 2, "one retry after the refusal; the second identical request is already seen"
    assert not result.integrated and result.graph.by_name("c1").proof_status == "stuck"
    assert _events(result.graph).count("node.retried_after_refusal") == 1
    result.close()


def test_a_replace_and_an_add_on_one_definition_in_one_pass_keep_both(tmp_path, monkeypatch):
    monkeypatch.setattr(amend_mod, "apply_design", fake_apply_design)
    graph, root, dev = synthetic_graph(tmp_path)
    cfg = cfg_for(tmp_path, decomposer_runner=MockRunner({}))
    run = AmendmentRun(FakeDriver(cfg, graph, root, approver=FakeApprover(FakeVerdict("accept"))))
    requests = [
        AmendmentRequest("my_inv", add="n < 5", requester="i33"),
        AmendmentRequest("my_inv", replace="Definition my_inv (n : nat) : Prop := n < 7.", requester="stuck_free"),
    ]
    new_dev, changed = asyncio.run(run.apply(dev, requests))
    assert changed and "Definition my_inv (n : nat) : Prop := (n < 7) ∗ (n < 5)." in new_dev.source
    assert [o.request.kind for o in run.outcomes] == ["replace", "add"], "the restatement first, the conjunct on top of it"
    assert all(o.applied for o in run.outcomes)
    assert "now also carries `n < 5`" in graph.by_name("i33").evidence, "what the requester is told is true of the file"
    graph.close()


def test_a_contested_root_whose_statement_mentions_the_definition_is_reopened(tmp_path, monkeypatch):
    monkeypatch.setattr(amend_mod, "apply_design", fake_apply_design)
    graph, root, dev = synthetic_graph(tmp_path)
    graph.update(root.id, statement="Lemma root (n : nat) : my_inv n -> n = 0.", role="human")
    graph.set_proof_status(root.id, "claimed")
    graph.set_proof_status(root.id, "contested", evidence="root: n = 0 does not follow")
    cfg = cfg_for(tmp_path)
    _, outcome = _apply(tmp_path, graph, root, dev, ADD, driver=FakeDriver(cfg, graph, root), cfg=cfg)
    reopened = graph.by_name("root")
    assert "root" in outcome.reopened and reopened.proof_status == "open" and reopened.epoch == 1
    assert reopened.evidence.startswith(AMENDED_MARKER) and graph.stale_edges(root.id) == []
    graph.close()
    # A contested root whose statement does not mention it is left to the adjudicator.
    graph, root, dev = synthetic_graph(tmp_path / "b")
    graph.set_proof_status(root.id, "claimed")
    graph.set_proof_status(root.id, "contested", evidence="root: wrong")
    _, outcome = _apply(tmp_path / "b", graph, root, dev, ADD, driver=FakeDriver(cfg_for(tmp_path / "b"), graph, root), cfg=cfg_for(tmp_path / "b"))
    assert "root" not in outcome.reopened and graph.by_name("root").proof_status == "contested"
    graph.close()


class WholeFileGate(FakeGate):
    """Decides like ``coqc`` does: the assembled file fails if *any* injected body --
    a sibling's included -- carries a rejected token, not only the target's."""

    def run(self, anchor, nodes, *, target=None, target_body=None, **kw):
        result = super().run(anchor, nodes, target=target, target_body=target_body, **kw)
        poisoned = [s.name for s in nodes if s.body and any(r in s.body for r in self.reject)]
        if result.ok and poisoned:
            from pcp.orch.gate import CHECK_COMPILES, Check, GateResult

            return GateResult(ok=False, checks=[Check(CHECK_COMPILES, False, f"Error: in {poisoned[0]}")], compile_output="")
        return result

def test_revalidate_blames_a_sound_proof_for_a_later_siblings_broken_body(tmp_path, monkeypatch):
    """Reproduced with coqc: `unaffected : P -∗ P` was reopened because `proof_uses`, later
    in plan order and broken by the amendment, was injected with its body into
    `unaffected`'s replay file (`stub_prefix` stubs only the file's own proofs)."""
    monkeypatch.setattr(amend_mod, "apply_design", fake_apply_design)
    graph, root, dev = synthetic_graph(tmp_path)
    # `other` (sound) is ordered before `fc50_spec` (broken by the amendment) in the fixture.
    graph.update(node_id("other"), ordering=0, role="human")
    graph.update(node_id("fc50_spec"), ordering=5, role="human")
    cfg = cfg_for(tmp_path)
    driver = FakeDriver(cfg, graph, root, gate=WholeFileGate(reject=("closes_inv",)))
    _, outcome = _apply(tmp_path, graph, root, dev, ADD, driver=driver, cfg=cfg)
    assert outcome.applied
    assert graph.by_name("other").proof_status == "gated" and "other" in outcome.kept, outcome.render()
    assert graph.by_name("fc50_spec").proof_status == "open"
    graph.close()


def test_the_worker_may_not_name_the_requester(tmp_path):
    path = tmp_path / ANSWER_FILE
    json_dump(path, {"status": "stuck", "amendments": [{"definition": "my_inv", "add": "x", "requester": "root"}]})
    result = read_answer_file(path)
    assert result.amendments[0].requester == ""
    node = Node(id="c1", name="c1", statement="Lemma c1 : True.")
    assert [a.requester for a in requested_amendments(node, result)] == ["c1"]
    # The attempt-row round trip keeps the scheduler's own value.
    assert AmendmentRequest.from_json(AmendmentRequest("d", add="x", requester="c1").to_json()).requester == "c1"


# --- real Rocq ---------------------------------------------------------------------------

IRIS_SOURCE = """From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import base_logic.

Set Default Proof Using "Type".

Section amend.
  Context {PROP : bi}.

  Definition amend_inv (n : nat) : PROP := True%I.

  Lemma amend_main (n : nat) : ⌜n = 0⌝ -∗ amend_inv n ∗ True.
  Proof.
  Admitted.
End amend.
"""

# `proof_uses` is placed before `unaffected` on purpose: `revalidate` replays proved
# nodes in plan order with the *not yet replayed* siblings' bodies injected, so a
# broken body late in the order fails the compile of every replay before it (handoff
# finding, `test_revalidate_blames_a_sound_proof_for_a_later_siblings_broken_body`).
IRIS_PLAN = """Lemma close_inv (n : nat) : ⌜n = 0⌝ -∗ amend_inv n.
Proof. Admitted.

Lemma proof_uses (m : nat) : ⌜m = 0⌝ -∗ (True : PROP).
Proof. Admitted.

Lemma unaffected (P : PROP) : P -∗ P.
Proof. Admitted.

Lemma needs_fact (n : nat) : amend_inv n -∗ ⌜n = 0⌝.
Proof. Admitted.
"""


@needs_rocq
def test_a_real_strengthening_replays_reopens_the_closing_proof_and_keeps_the_rest(tmp_path):
    """Four children: one closes the invariant (its proof breaks), one is untouched, one
    is the requester, and one -- ``proof_uses`` -- never *mentions* ``amend_inv`` in its
    statement but unfolds it in its proof, so only the replay can find out that it
    broke.  Then the root integrates over the reopened-and-reproved children."""
    corpus = ensure_dir(tmp_path / "corpus")
    atomic_write_text(corpus / "Amend.v", IRIS_SOURCE)
    atomic_write_text(corpus / "plan.v", IRIS_PLAN)
    atomic_write_text(corpus / "_CoqProject", "-Q . amend\n")
    atomic_write_text(corpus / "design.json", json.dumps({"mutable": ["amend_inv"], "allow_additions": True}))
    answers = {
        "close_inv": 'iIntros "_". rewrite /amend_inv. done.',                              # holds only while amend_inv is True
        "unaffected": 'iIntros "H". done.',
        "needs_fact": 'iIntros "[_ %H]". iPureIntro. exact H.',                             # provable only after the amendment
        "proof_uses": 'iIntros "%H". iAssert (amend_inv 7) as "_"; [by rewrite /amend_inv | done].',  # unfolds amend_inv 7
        "amend_main": 'iIntros "H". iSplitL "H"; [by iApply close_inv | done].',
    }
    after = {
        "close_inv": 'iIntros "%H". rewrite /amend_inv. iSplit; [done | by iPureIntro].',
        "proof_uses": 'iIntros "%H". done.',
    }

    class IrisRunner(AskingRunner):
        def scripted_answer(self, node: NodePayload) -> dict[str, Any]:
            if node.name in after and node.evidence.startswith(AMENDED_MARKER):
                self.dispatches.append((node.name, node.evidence))
                return {"status": "qed", "proof": after[node.name]}
            return super().scripted_answer(node)

    runner = IrisRunner(answers, asks={"needs_fact": [{"definition": "amend_inv", "add": "⌜n = 0⌝", "at": "the goal after opening amend_inv", "why": "amend_inv n says nothing about n"}]})
    cfg = ProveConfig(
        file=corpus / "Amend.v", target="amend_main", plan=corpus / "plan.v", graph_path=tmp_path / "g.db",
        workroot=tmp_path / "w", node_seconds=120, budget=Budget(requests=50, seconds=1800), run_lock=False,
    )
    result = asyncio.run(prove(cfg, runner))
    assert result.integrated, result.render()
    assert len(result.amendments) == 1 and result.amendments[0].applied and result.amendments[0].verdict == "auto-accepted"
    outcome = result.amendments[0]
    assert set(outcome.reopened) == {"needs_fact", "close_inv", "proof_uses"} and set(outcome.kept) == {"unaffected", "amend_main"}, outcome.render()
    designed = tmp_path / "w" / "amend_main.designed2" / "Amend.v"
    assert designed.exists() and "Definition amend_inv (n : nat) : PROP := (True ∗ (⌜n = 0⌝))%I." in designed.read_text()
    names = [d[0] for d in runner.dispatches]
    assert names.count("unaffected") == 1 and names.count("amend_main") == 1 and names.count("close_inv") == 2 and names.count("needs_fact") == 2
    assert names.count("proof_uses") == 2, "a proof that unfolds the definition is replayed, found broken, and re-dispatched"
    assert result.graph.by_name("needs_fact").epoch == 0, "the requester kept its epoch (an attempt was left)"
    assert result.graph.by_name("close_inv").epoch == 1, "the reopened proof is of the new epoch"
    assert result.graph.by_name("proof_uses").epoch == 1 and result.graph.by_name("proof_uses").body == after["proof_uses"]
    assert result.graph.stale_edges(result.root.id) == [], "the root's demand edges followed the reopened children's epochs"
    assert result.solution is None and result.graph.summary() == {"integrated": 5}
    assert result.design_rounds == [] and "amended amend_inv: + ⌜n = 0⌝  (requested by needs_fact;" in result.render()
    assert "unreviewed: no approver is configured" in result.render()
    result.close()


VACUOUS_SOURCE = """From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import base_logic.

Set Default Proof Using "Type".

Section amend.
  Context {PROP : bi}.

  Definition amend_inv (n : nat) : PROP := True%I.

  Lemma amend_main (n : nat) : amend_inv n -∗ ⌜n = 42⌝.
  Proof.
  Admitted.
End amend.
"""
VACUOUS_PLAN = """Lemma unaffected (P : PROP) : P -∗ P.
Proof. Admitted.
"""


class VacuousProver(AskingRunner):
    """Asks for `False` to be added to the predicate its own goal assumes, then proves
    the (false) goal from it: `amend_inv n ⊢ ⌜n = 42⌝` once `amend_inv n = True ∗ False`."""

    def scripted_answer(self, node: NodePayload) -> dict[str, Any]:
        self.dispatches.append((node.name, node.evidence))
        if node.name != "amend_main":
            return {"status": "qed", "proof": 'iIntros "H". done.'}
        if node.evidence.startswith(AMENDED_MARKER):
            return {"status": "qed", "proof": 'iIntros "[_ []]".'}
        return {"status": "stuck", "evidence": "n = 42 does not follow from True", "amendments": [
            {"definition": "amend_inv", "add": "False", "at": "the only goal", "why": "makes it go through"},
        ]}


@needs_rocq
def test_a_real_vacuous_add_is_stopped_by_the_approver_and_only_the_report_without_one(tmp_path):
    """Review finding: `add` was auto-accepted as a machine-checked strengthening, but a
    stronger *hypothesis* is a weaker theorem -- `amend_main` is false as designed and
    integrated with a clean `Print Assumptions`.  With an approver configured the add is
    reviewed and the rejection buys the prover its ordinary retry; without one it is
    applied and the report line says so, because the human reading it is the auditor."""
    from tests.test_adjudication import ScriptedRunner, canned

    def corpus_at(base: Path) -> Path:
        corpus = ensure_dir(base / "corpus")
        atomic_write_text(corpus / "Amend.v", VACUOUS_SOURCE)
        atomic_write_text(corpus / "plan.v", VACUOUS_PLAN)
        atomic_write_text(corpus / "_CoqProject", "-Q . amend\n")
        atomic_write_text(corpus / "design.json", json.dumps({"mutable": ["amend_inv"], "allow_additions": True}))
        return corpus

    def cfg_at(base: Path, **kw: Any) -> ProveConfig:
        corpus = corpus_at(base)
        return ProveConfig(
            file=corpus / "Amend.v", target="amend_main", plan=corpus / "plan.v", graph_path=base / "g.db",
            workroot=base / "w", node_seconds=120, budget=Budget(requests=50, seconds=1800), run_lock=False, **kw,
        )

    approver = ScriptedRunner(canned(verdict="reject", why="nothing establishes amend_inv once it carries False"))
    runner = VacuousProver({}, asks={})
    result = asyncio.run(prove(cfg_at(tmp_path / "reviewed", approver_runner=approver), runner))
    assert not result.integrated and "`amend_main` is not proved" in result.integration_detail, result.render()
    assert len(approver.seen) == 1 and "# Approve, adjust or reject a change to `amend_inv`" in (Path(approver.seen[0].workdir) / "TASK.md").read_text(encoding="utf-8")
    assert [(o.applied, o.verdict) for o in result.amendments] == [(False, "reject")]
    assert "amendment refused amend_inv: + False  (requested by amend_main)" in result.render() and "nothing establishes" in result.render()
    main = [d for d in runner.dispatches if d[0] == "amend_main"]
    assert len(main) == 2 and main[1][1].startswith("your amendment request (amend_inv: + False) was not applied"), "the refusal bought the retry"
    assert result.graph.by_name("amend_main").proof_status == "stuck" and result.graph.by_name("amend_main").epoch == 0
    assert not (tmp_path / "reviewed" / "w" / "amend_main.designed2" / "Amend.v").samefile(result.graph.get_meta(DESIGNED_FILE_META))
    assert _payloads(result.graph, "amendment.adjudicated")[0]["verdict"] == "reject"
    assert "node.retried_after_refusal" in _events(result.graph)
    result.close()

    # No approver anywhere: the human is the auditor, and the report says so.
    unreviewed = asyncio.run(prove(cfg_at(tmp_path / "unreviewed"), VacuousProver({}, asks={})))
    assert unreviewed.integrated, "documented residual: a plan run has no approver, so the add is applied"
    assert "amended amend_inv: + False  (requested by amend_main;" in unreviewed.render()
    assert "unreviewed: no approver is configured" in unreviewed.render()
    unreviewed.close()


class ReviewingApprover(FakeApprover):
    """A fake that also sees how many attempts failed (the review variant of the prompt)."""

    def __init__(self, **kw):
        super().__init__(**kw)
        self.failed: list[tuple[str, int]] = []

    async def adjudicate_contest(self, root, node, *, evidence, budget_seconds, contract, design, failed_attempts=0):
        self.failed.append((node.name, failed_attempts))
        return await super().adjudicate_contest(root, node, evidence=evidence, budget_seconds=budget_seconds, contract=contract, design=design)


def test_a_reviewed_stuck_node_reopens_on_strategy_and_becomes_contested_on_statement(tmp_path):
    graph, root, dev = synthetic_graph(tmp_path)
    for name in ("stuck_free", "spent"):
        graph.set_proof_status(node_id(name), "open")
        graph.set_proof_status(node_id(name), "claimed")
        graph.set_proof_status(node_id(name), "stuck", evidence=f"{name}: gate: FAIL -- could not close the invariant")
    cfg = cfg_for(tmp_path, decomposer_runner=MockRunner({}))
    approver = ReviewingApprover(contest={
        "stuck_free": FakeVerdict("strategy", hint="open the invariant after the CmpXchg, not before"),
        "spent": FakeVerdict("statement", hint="the postcondition asks for a resource the invariant never gives back"),
    })
    run = AmendmentRun(FakeDriver(cfg, graph, root, approver=approver))
    ids = {node_id("stuck_free"), node_id("spent")}
    expected = sorted((n, attempts_spent(graph, graph.by_name(n))) for n in ("spent", "stuck_free"))
    _dev, reopened, fixes = asyncio.run(run.adjudicate(dev, [graph.by_name("stuck_free"), graph.by_name("spent")], review=ids))
    assert reopened == ["stuck_free"] and fixes == []
    assert sorted(approver.failed) == expected, "the review variant is asked, with the attempt count"
    free = graph.by_name("stuck_free")
    assert free.proof_status == "open" and free.epoch == 1 and free.evidence.startswith(ADJUDICATED_MARKER)
    assert "Your last attempt's evidence was" in free.evidence and "open the invariant after" in free.evidence
    spent = graph.by_name("spent")
    assert spent.proof_status == "contested" and spent.evidence.startswith(ADJUDICATED_MARKER)
    assert "finds this statement wrong" in spent.evidence and "never gives back" in spent.evidence
    assert "node.contested_by_adjudication" in _events(graph)
    assert graph.get_meta("contest_adjudicated:spent") == "0" and graph.get_meta("contest_adjudicated:stuck_free") == "0"
    graph.close()


def test_only_a_human_may_contest_a_stuck_node(tmp_path):
    from pcp.orch.model import InvalidTransition

    graph, root, dev = synthetic_graph(tmp_path)
    graph.set_proof_status(node_id("spent"), "open")
    graph.set_proof_status(node_id("spent"), "claimed")
    graph.set_proof_status(node_id("spent"), "stuck", evidence="x")
    with pytest.raises(InvalidTransition):
        graph.set_proof_status(node_id("spent"), "contested", evidence="a model says so")
    graph.set_proof_status(node_id("spent"), "contested", evidence="the approver says so", role="human")
    assert graph.by_name("spent").proof_status == "contested"
    graph.close()


def test_a_node_reviewed_at_one_epoch_is_reviewed_again_at_the_next_within_the_same_run(tmp_path):
    """Review finding: the per-run memo was keyed by node id, so a node reopened at
    epoch+1 by a strategy verdict could never be reviewed again and wedged stuck."""
    graph, root, dev = synthetic_graph(tmp_path)
    graph.set_proof_status(node_id("stuck_free"), "open")
    graph.set_proof_status(node_id("stuck_free"), "claimed")
    graph.set_proof_status(node_id("stuck_free"), "stuck", evidence="gate: FAIL")
    cfg = cfg_for(tmp_path, decomposer_runner=MockRunner({}))
    approver = ReviewingApprover(contest={"stuck_free": FakeVerdict("strategy", hint="try the other branch first")})
    run = AmendmentRun(FakeDriver(cfg, graph, root, approver=approver))
    _dev, reopened, _ = asyncio.run(run.adjudicate(dev, [graph.by_name("stuck_free")], review={node_id("stuck_free")}))
    assert reopened == ["stuck_free"] and graph.by_name("stuck_free").epoch == 1 and graph.get_meta("contest_adjudicated:stuck_free") == "0"
    # fails again at epoch 1 and is parked for review: the same run asks again
    graph.set_proof_status(node_id("stuck_free"), "claimed")
    graph.set_proof_status(node_id("stuck_free"), "stuck", evidence="gate: FAIL again")
    _dev, reopened, _ = asyncio.run(run.adjudicate(dev, [graph.by_name("stuck_free")], review={node_id("stuck_free")}))
    assert reopened == ["stuck_free"] and len(approver.asked) == 2
    assert graph.by_name("stuck_free").epoch == 2 and graph.get_meta("contest_adjudicated:stuck_free") == "1"
    # ...but never twice at the same epoch
    graph.set_proof_status(node_id("stuck_free"), "claimed")
    graph.set_proof_status(node_id("stuck_free"), "stuck", evidence="x")
    graph.update(node_id("stuck_free"), epoch=1, role="human")
    assert asyncio.run(run.adjudicate(dev, [graph.by_name("stuck_free")], review={node_id("stuck_free")}))[1] == [] and len(approver.asked) == 2
    graph.close()


def test_an_unusable_verdict_does_not_drop_the_node_from_review_for_the_run(tmp_path):
    graph, root, dev = synthetic_graph(tmp_path)
    graph.set_proof_status(node_id("stuck_free"), "open")
    graph.set_proof_status(node_id("stuck_free"), "claimed")
    graph.set_proof_status(node_id("stuck_free"), "stuck", evidence="gate: FAIL")
    cfg = cfg_for(tmp_path, decomposer_runner=MockRunner({}))
    approver = ReviewingApprover(contest={"stuck_free": FakeVerdict("", violation="401 revoked")})
    run = AmendmentRun(FakeDriver(cfg, graph, root, approver=approver))
    assert asyncio.run(run.adjudicate(dev, [graph.by_name("stuck_free")], review={node_id("stuck_free")}))[1] == []
    approver.contest["stuck_free"] = FakeVerdict("strategy", hint="now it works")
    assert asyncio.run(run.adjudicate(dev, [graph.by_name("stuck_free")], review={node_id("stuck_free")}))[1] == ["stuck_free"]
    assert len(approver.asked) == 2 and graph.by_name("stuck_free").epoch == 1
    graph.close()


def test_siblings_blocked_on_a_reviewed_non_mockable_node_reopen_with_it(tmp_path):
    from pcp.orch.schedule import BLOCKED_PREFIX

    graph, root, dev = synthetic_graph(tmp_path)
    graph.set_proof_status(node_id("stuck_free"), "open")
    graph.set_proof_status(node_id("stuck_free"), "claimed")
    graph.set_proof_status(node_id("stuck_free"), "stuck", evidence="gate: FAIL")
    graph.set_proof_status(node_id("spent"), "open")
    graph.set_proof_status(node_id("spent"), "claimed")
    graph.set_proof_status(node_id("spent"), "stuck", evidence=f"{BLOCKED_PREFIX} stuck_free are unproved and cannot be stubbed into this node's file")
    cfg = cfg_for(tmp_path, decomposer_runner=MockRunner({}), max_attempts=3)
    approver = ReviewingApprover(contest={"stuck_free": FakeVerdict("strategy", hint="h")})
    run = AmendmentRun(FakeDriver(cfg, graph, root, approver=approver))
    _dev, reopened, _ = asyncio.run(run.adjudicate(dev, [graph.by_name("stuck_free")], review={node_id("stuck_free")}))
    assert reopened == ["stuck_free", "spent"] and graph.by_name("spent").proof_status == "open"
    assert graph.by_name("spent").evidence == "", "the scheduling note is not evidence for the prover"
    assert "node.unblocked" in _events(graph) and len(approver.asked) == 1
    # a sibling blocked on some OTHER node, or with no budget left, stays where it is
    graph.set_proof_status(node_id("spent"), "claimed")
    graph.set_proof_status(node_id("spent"), "stuck", evidence=f"{BLOCKED_PREFIX} i33 are unproved and cannot be stubbed into this node's file")
    graph.set_proof_status(node_id("stuck_free"), "claimed")
    graph.set_proof_status(node_id("stuck_free"), "stuck", evidence="gate: FAIL")
    _dev, reopened, _ = asyncio.run(run.adjudicate(dev, [graph.by_name("stuck_free")], review={node_id("stuck_free")}))
    assert reopened == ["stuck_free"] and graph.by_name("spent").proof_status == "stuck"
    graph.close()


def test_a_rejected_restatement_on_a_reviewed_node_contests_it(tmp_path):
    graph, root, dev = synthetic_graph(tmp_path)
    graph.set_proof_status(node_id("stuck_free"), "open")
    graph.set_proof_status(node_id("stuck_free"), "claimed")
    graph.set_proof_status(node_id("stuck_free"), "stuck", evidence="gate: FAIL")
    cfg = cfg_for(tmp_path, decomposer_runner=MockRunner({}))
    v = FakeVerdict("statement", hint="the premise is missing")
    v.restatement = "Lemma stuck_free : True."  # no adopted design in this graph: rejected
    approver = ReviewingApprover(contest={"stuck_free": v})
    run = AmendmentRun(FakeDriver(cfg, graph, root, approver=approver))
    _dev, reopened, fixes = asyncio.run(run.adjudicate(dev, [graph.by_name("stuck_free")], review={node_id("stuck_free")}))
    assert reopened == [] and fixes == []
    node = graph.by_name("stuck_free")
    assert node.proof_status == "contested" and "restatement.rejected" in _events(graph) and "node.contested_by_adjudication" in _events(graph)
    assert graph.get_meta("contest_adjudicated:stuck_free") == "0"
    graph.close()


def test_verdict_driven_reopenings_are_bounded(tmp_path):
    """Review finding: a strategy-always approver and a stuck-always prover cycled
    forever (2 attempts + 1 verdict per epoch).  After MAX_VERDICT_REOPENS the epoch
    counts as reviewed and the budget is spent normally."""
    from pcp.orch.prove.amendments import MAX_VERDICT_REOPENS

    graph, root, dev = synthetic_graph(tmp_path)
    cfg = cfg_for(tmp_path, decomposer_runner=MockRunner({}))
    approver = ReviewingApprover(contest={"stuck_free": FakeVerdict("strategy", hint="again")})
    run = AmendmentRun(FakeDriver(cfg, graph, root, approver=approver))
    for k in range(MAX_VERDICT_REOPENS + 2):
        node = graph.by_name("stuck_free")
        if node.proof_status == "open":
            graph.set_proof_status(node.id, "claimed")
        if graph.by_name("stuck_free").proof_status == "claimed":
            graph.set_proof_status(node.id, "stuck", evidence=f"gate: FAIL {k}")
        _dev, reopened, _ = asyncio.run(run.adjudicate(dev, [graph.by_name("stuck_free")], review={node.id}))
        if k < MAX_VERDICT_REOPENS:
            assert reopened == ["stuck_free"] and graph.by_name("stuck_free").epoch == k + 1
        else:
            assert reopened == [] and graph.by_name("stuck_free").proof_status == "stuck"
            assert graph.get_meta(f"contest_adjudicated:{node.id}") == str(node.epoch), "the epoch counts as reviewed"
    assert "contest.reopens_exhausted" in _events(graph)
    assert graph.get_meta(f"contest_adjudicated:reopens:{node_id('stuck_free')}") == str(MAX_VERDICT_REOPENS)
    graph.close()


def test_a_fix_applied_with_a_rejected_restatement_reopens_instead_of_crashing(tmp_path, monkeypatch):
    """Review finding: the fix reopened the node, then the rejected restatement fell
    through to `stuck -> contested` on an open node -- an InvalidTransition that killed the run."""
    import pcp.orch.prove.amendments as mod

    graph, root, dev = synthetic_graph(tmp_path)
    graph.set_proof_status(node_id("stuck_free"), "open")
    graph.set_proof_status(node_id("stuck_free"), "claimed")
    graph.set_proof_status(node_id("stuck_free"), "stuck", evidence="gate: FAIL")

    async def fake_apply(cfg, graph_, dev_, root_, req, **kw):
        graph_.set_proof_status(node_id(req.requester), "open", evidence=f"{AMENDED_MARKER} {req.definition} changed")
        return dev_, mod.AmendmentOutcome(request=req, applied=True, verdict="auto-accepted", reopened=[req.requester])

    monkeypatch.setattr(mod, "apply_amendment", fake_apply)
    cfg = cfg_for(tmp_path, decomposer_runner=MockRunner({}))
    v = FakeVerdict("statement", definition="my_inv", text="Definition my_inv (n : nat) : Prop := n < 7.", hint="both")
    v.restatement = "Lemma stuck_free : True. Proof. auto. Qed."  # proof text: rejected
    approver = ReviewingApprover(contest={"stuck_free": v})
    run = AmendmentRun(FakeDriver(cfg, graph, root, approver=approver))
    _dev, reopened, fixes = asyncio.run(run.adjudicate(dev, [graph.by_name("stuck_free")], review={node_id("stuck_free")}))
    assert reopened == ["stuck_free"] and fixes == []
    assert graph.by_name("stuck_free").proof_status == "open" and graph.get_meta("contest_adjudicated:stuck_free") == "0"
    graph.close()


def test_parked_for_review_finds_the_nodes_a_resumed_run_must_adjudicate_first(tmp_path):
    from pcp.orch.prove.amendments import parked_for_review, review_after

    graph, root, dev = synthetic_graph(tmp_path)
    cfg = cfg_for(tmp_path, decomposer_runner=MockRunner({}), review_after=2, max_attempts=2)
    assert review_after(cfg) == 2 and review_after(cfg_for(tmp_path, review_after=2)) == 0, "no approver: nothing to review"
    assert review_after(cfg_for(tmp_path, decomposer_runner=MockRunner({}), review_after=2, max_amendments=0)) == 0
    names = {n.name for n in parked_for_review(graph, cfg)}
    assert "spent" in names, "2 of 2 attempts, no verdict yet"
    assert "stuck_free" not in names, "1 attempt only"
    graph.set_meta("contest_adjudicated:spent", "0")
    assert "spent" not in {n.name for n in parked_for_review(graph, cfg)}
    graph.close()
