"""pcp.orch.amend: the two built rungs (refute, replay-first) and the designed routing."""

from __future__ import annotations

import pytest

from pcp.config.schema import Config
from pcp.errors import UsageError
from pcp.orch.amend import (
    Amendment,
    apply_amendment,
    audit_rung,
    classify,
    impact_of,
    mentions,
    precleared,
    propose,
    refutation_statement,
    refute,
    replay_first,
    taint,
)
from pcp.orch.gate import Gate
from pcp.orch.model import Node, node_id
from pcp.rocq.assemble import Development
from tests._orch_fixtures import FakeGate, build_plain_graph
from tests.conftest import needs_rocq


def flagged() -> Config:
    cfg = Config()
    cfg.flags["amendment_lattice"] = True
    return cfg


def test_the_refutation_keeps_the_binders():
    assert refutation_statement("Lemma foo (x : nat) : x <> 0.") == "Lemma foo__refutation (x : nat) : (x <> 0) -> False."
    assert refutation_statement("Lemma bar : True.") == "Lemma bar__refutation : (True) -> False."
    assert refutation_statement("Lemma baz (P : Prop) (n : nat) : P -> n = n.") == "Lemma baz__refutation (P : Prop) (n : nat) : (P -> n = n) -> False."


def test_classification_and_rungs():
    assert classify("Lemma a (x : nat) : x = x.", "Lemma a (x : nat) : x = x.") == "iso"
    assert classify("Lemma a (x : nat) : x = x.", "Lemma a (x : nat) (H : x > 0) : x = x.") == "weaken"
    assert classify("Lemma a (x : nat) (H : x > 0) : x = x.", "Lemma a (x : nat) : x = x.") == "strengthen"
    assert precleared(["inG Σ fooR", "Countable K"]) and not precleared(["H : x > 0"]) and not precleared([])
    root = Node(id="r", name="r", statement="Lemma r : True.", rank="root")
    local = Node(id="l", name="l", statement="Lemma l : True.")
    interface = Node(id="i", name="i", statement="Lemma i : True.", rank="interface")
    weaken = Amendment(node="x", klass="weaken", statement="s")
    from pcp.orch.amend import ImpactReport

    small, big = ImpactReport("x"), ImpactReport("x", reopened=list("abcdefg"))
    assert audit_rung(root, weaken, small) == "human"
    assert audit_rung(interface, weaken, big) == "quorum" and audit_rung(interface, weaken, small) == "one-auditor"
    assert audit_rung(local, weaken, small) == "deterministic" and audit_rung(local, weaken, big) == "one-auditor"
    assert audit_rung(root, Amendment(node="x", klass="refute", statement="s"), big) == "deterministic"


def test_impact_uses_identifiers_not_substrings(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("inv", "invariant_holds", "uses_inv"))
    graph.update(node_id("invariant_holds"), statement="Lemma invariant_holds : invariant_holds_now.", role="human")
    graph.update(node_id("uses_inv"), statement="Lemma uses_inv : inv -> True.", role="human")
    for dep in ("invariant_holds", "uses_inv"):
        graph.add_edge(node_id(dep), node_id("inv"))
    assert mentions("Lemma x : inv -> True.", "inv") and not mentions("Lemma x : invariant_holds.", "inv")
    impact = impact_of(graph, graph.by_name("inv"))
    assert impact.statement_invalidated == ["uses_inv"]
    assert set(impact.reopened) == {"invariant_holds", "root"}
    assert impact.size() == 3 and "impact of amending `inv`" in impact.render()
    graph.close()


def test_everything_but_replay_is_behind_the_flag(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    c1 = graph.by_name("c1")
    with pytest.raises(UsageError, match="amendment_lattice"):
        refute(graph, dev, FakeGate(), c1, counterexample="intros H. exact H.")
    with pytest.raises(UsageError):
        taint(graph, c1)
    with pytest.raises(UsageError):
        propose(graph, c1, Amendment(node="c1", klass="weaken", statement="s"))
    with pytest.raises(UsageError):
        apply_amendment(graph, c1, Amendment(node="c1", klass="weaken", statement="s", status="accepted"))
    graph.close()


def test_refute_with_a_scripted_gate_taints_dependents_along_two_channels(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("bad", "uses_bad", "proof_uses_bad"))
    graph.update(node_id("uses_bad"), statement="Lemma uses_bad : bad -> True.", role="human")
    for dep in ("uses_bad", "proof_uses_bad"):
        graph.add_edge(node_id(dep), node_id("bad"))
    graph.set_proof_status(node_id("proof_uses_bad"), "claimed")
    graph.record_proof(node_id("proof_uses_bad"), "exact I.")
    gate = FakeGate()
    amendment = refute(graph, dev, gate, graph.by_name("bad"), counterexample="intros H. exact H.", config=flagged())
    assert amendment.status == "accepted" and amendment.klass == "refute"
    call = gate.calls[-1]
    assert call["anchor"] == "root" and call["target"] == "bad__refutation" and call["stub_prefix"]
    assert graph.by_name("bad").statement_status == "refuted"
    assert graph.by_name("uses_bad").statement_status == "proposed"
    assert graph.by_name("proof_uses_bad").proof_status == "open" and graph.by_name("proof_uses_bad").body is None
    rejected = refute(graph, dev, FakeGate(reject=("nope",)), graph.by_name("root"), counterexample="nope.", config=flagged())
    assert rejected.status == "rejected" and "does not check" in rejected.rationale
    graph.close()


def test_propose_and_apply_bump_the_epoch(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    c1 = graph.by_name("c1")
    graph.set_proof_status(c1.id, "claimed")
    graph.record_proof(c1.id, "exact I.")
    amendment = propose(graph, c1, Amendment(node="c1", klass="weaken", statement="Lemma c1 (P : Prop) (H : P) : P -> P."), config=flagged())
    assert amendment.rung == "one-auditor" and amendment.impact.reopened == ["root"]
    assert apply_amendment(graph, c1, amendment, config=flagged()) is None, "not accepted yet"
    amendment.status = "accepted"
    updated = apply_amendment(graph, c1, amendment, config=flagged())
    assert updated.epoch == 1 and updated.body is None and updated.proof_status == "open" and "(H : P)" in updated.statement
    assert graph.stale_edges(root.id) == [(c1.id, 0, 1)]
    graph.close()


def test_replay_first_salvages_the_newest_gating_body(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    c1 = graph.by_name("c1")
    graph.set_proof_status(c1.id, "claimed")
    a = graph.start_attempt(c1.id, runner="mock")
    graph.finish_attempt(a, status="stuck", body="exact wrong_proof_from_mock.")
    b = graph.start_attempt(c1.id, runner="mock")
    graph.finish_attempt(b, status="stuck", body="intros H. exact H.")
    graph.set_proof_status(c1.id, "open")
    gate = FakeGate()
    assert replay_first(graph, dev, gate, root, graph.by_name("c1"))
    assert graph.by_name("c1").proof_status == "gated" and graph.by_name("c1").body == "intros H. exact H."
    assert gate.calls[0]["body"] == "intros H. exact H.", "newest first"
    assert not replay_first(graph, dev, gate, root, graph.by_name("root")), "no bodies, nothing to replay"
    graph.close()


@needs_rocq
def test_refute_is_machine_checked_on_a_real_false_statement(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("bad",))
    graph.update(node_id("bad"), statement="Lemma bad (n : nat) : n = n + 1.", role="human")
    counterexample = "intros H. induction n as [|n IH]. - discriminate H. - apply IH. simpl in H. injection H as H. exact H."
    amendment = refute(graph, dev, Gate(dev), graph.by_name("bad"), counterexample=counterexample, config=flagged())
    assert amendment.status == "accepted", amendment.rationale
    assert graph.by_name("bad").statement_status == "refuted"
    wrong = refute(graph, dev, Gate(dev), graph.by_name("root"), counterexample="intros H. exact I.", config=flagged())
    assert wrong.status == "rejected"
    graph.close()


@needs_rocq
def test_replay_first_against_the_real_gate(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    c1 = graph.by_name("c1")
    graph.set_proof_status(c1.id, "claimed")
    a = graph.start_attempt(c1.id, runner="mock")
    graph.finish_attempt(a, status="stuck", body="intros H. exact H.")
    graph.set_proof_status(c1.id, "open")
    assert replay_first(graph, dev, Gate(dev), root, graph.by_name("c1"))
    assert graph.by_name("c1").proved
    assert Development(dev.path).block("root") is not None
    graph.close()
