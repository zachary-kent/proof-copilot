"""pcp.orch.prove.plan: freezing the user's plan, reconciled by hash, gated bodies."""

from __future__ import annotations

from pathlib import Path

import pytest

from pcp.errors import UsageError
from pcp.orch.model import node_id
from pcp.orch.prove.plan import build_graph, has_children, plan_nodes, plan_sentinels
from tests._orch_fixtures import PLAN_SOURCE, plain_cfg
from tests.conftest import needs_rocq


def _build(tmp_path, **kw):
    cfg = plain_cfg(tmp_path, **kw)
    plan = plan_nodes(cfg)
    return cfg, plan, build_graph(cfg, plan)


def test_plan_nodes_reads_specs_and_preamble(tmp_path):
    cfg = plain_cfg(tmp_path, plan_source="Require Import Stdlib.Lists.List.\n" + PLAN_SOURCE)
    plan = plan_nodes(cfg)
    assert [s.name for s in plan.specs] == ["c1", "c2"]
    assert plan.preamble == "Require Import Stdlib.Lists.List."
    cfg.target = "nope"
    with pytest.raises(UsageError, match="no declaration named 'nope'"):
        plan_nodes(cfg)


def test_the_root_is_inserted_first_and_children_get_demand_edges(tmp_path):
    cfg, plan, (graph, root, sentinels) = _build(tmp_path)
    assert sentinels.ok
    added = [e["payload"]["name"] for e in graph.events_since() if e["kind"] == "node.added"]
    assert added[0] == "root" and set(added[1:]) == {"c1", "c2"}
    assert root.rank == "root" and root.is_glue and root.ordering == 1_000_000 and root.owner == "human"
    for name in ("c1", "c2"):
        n = graph.by_name(name)
        assert n.parent == root.id and n.depth == 1 and n.dispatchable and n.owner == "human"
        assert (n.id, 0, "uses") in [(d, e, k) for d, e, k in graph.deps(root.id)]
    assert has_children(graph, root)
    graph.close()


def test_a_plan_that_restates_the_root_is_blocked_not_inserted(tmp_path):
    plan = PLAN_SOURCE + "\nLemma root (P Q : Prop) : P -> Q -> P.\nProof. Admitted.\n"
    cfg, plan_ctx, (graph, root, sentinels) = _build(tmp_path, plan_source=plan)
    assert not sentinels.ok
    assert any(h.node == "root" and h.blocking for h in sentinels.hits)
    assert {n.name for n in graph.nodes()} == {"root", "c1", "c2"}
    assert graph.by_name("root").rank == "root"
    # A second build on the same graph is just as calm.
    graph.close()
    _, _, (graph2, _, sentinels2) = _build(tmp_path, plan_source=plan)
    assert not sentinels2.ok and len(graph2.nodes()) == 3
    graph2.close()


def test_a_plan_child_shadowing_a_file_lemma_is_blocked(tmp_path):
    plan = PLAN_SOURCE + "\nLemma helper (P : Prop) : P -> P.\nProof. Admitted.\n"
    cfg, _, (graph, root, sentinels) = _build(tmp_path, plan_source=plan)
    hits = [h for h in sentinels.hits if h.node == "helper"]
    assert hits and all(h.blocking for h in hits) and any("already declared" in h.detail for h in hits)
    assert graph.by_name("helper") is None
    graph.close()


def test_two_children_with_the_same_statement_are_a_blocking_duplicate(tmp_path):
    plan = "Lemma c1 (P : Prop) : P -> P.\nProof. Admitted.\nLemma c1_again (P : Prop) : P -> P.\nProof. Admitted.\n"
    cfg = plain_cfg(tmp_path, plan_source=plan)
    report = plan_sentinels(plan_nodes(cfg), "root")
    assert [h.node for h in report.blocking] == ["c1_again"]


def test_a_changed_statement_is_refrozen_at_the_next_epoch_with_its_body_cleared(tmp_path):
    cfg, plan, (graph, root, _) = _build(tmp_path)
    graph.set_proof_status(node_id("c1"), "claimed")
    graph.record_proof(node_id("c1"), "intros H. exact H.")
    graph.close()
    edited = PLAN_SOURCE.replace("Lemma c1 (P : Prop) : P -> P.", "Lemma c1 (P : Prop) : P -> P -> P.")
    cfg2, _, (graph2, _, sentinels) = _build(tmp_path, plan_source=edited)
    c1 = graph2.by_name("c1")
    assert sentinels.ok
    assert c1.epoch == 1 and c1.body is None and c1.proof_status == "open"
    assert "P -> P -> P" in c1.statement
    assert any(e["kind"] == "plan.restated" and e["node"] == c1.id for e in graph2.events_since())
    assert graph2.by_name("c2").epoch == 0, "an unchanged child is untouched"
    graph2.close()


def test_a_removed_child_is_retired_and_a_proved_one_is_kept(tmp_path):
    cfg, plan, (graph, root, _) = _build(tmp_path)
    graph.set_proof_status(node_id("c2"), "claimed")
    graph.record_proof(node_id("c2"), "intros H. exact H.")
    graph.close()
    only_c1 = "Lemma c1 (P : Prop) : P -> P.\nProof. Admitted.\n"
    _, _, (graph2, _, _) = _build(tmp_path, plan_source=only_c1)
    assert graph2.by_name("c2").proof_status == "gated", "a proved orphan may be cited by the root"
    graph2.close()
    # Now with c2 unproved: it goes to the attic.
    _, _, (graph3, _, _) = _build(tmp_path / "b", plan_source=PLAN_SOURCE)
    graph3.close()
    _, _, (graph3, _, _) = _build(tmp_path / "b", plan_source=only_c1)
    assert graph3.by_name("c2").proof_status == "attic"
    assert any(e["kind"] == "plan.retired" and e["payload"]["retired"] == ["c2"] for e in graph3.events_since())
    assert not graph3.by_name("c2").dispatchable
    graph3.close()


def test_a_retired_child_is_revived_when_the_plan_asks_for_it_again(tmp_path):
    _build(tmp_path)[2][0].close()
    _build(tmp_path, plan_source="Lemma c1 (P : Prop) : P -> P.\nProof. Admitted.\n")[2][0].close()
    _, _, (graph, _, _) = _build(tmp_path)
    assert graph.by_name("c2").proof_status == "open"
    assert any(e["kind"] == "plan.revived" for e in graph.events_since())
    graph.close()


def test_an_edited_root_statement_is_refrozen(tmp_path):
    cfg, plan, (graph, root, _) = _build(tmp_path)
    graph.close()
    src = Path(cfg.file).read_text().replace("Lemma root (P Q : Prop) : P -> Q -> P.", "Lemma root (P Q : Prop) : Q -> P -> P.")
    Path(cfg.file).write_text(src)
    graph2, root2, _ = build_graph(cfg, plan_nodes(cfg))
    assert root2.epoch == 1 and "Q -> P -> P" in root2.statement
    graph2.close()


@needs_rocq
def test_a_plan_supplied_qed_body_is_gated_before_it_is_accepted(tmp_path, canary_dir):
    from pcp.orch.prove import ProveConfig

    good = (canary_dir / "plan.v").read_text().replace(
        "Lemma canary_swap (A B : PROP) : A ∗ B -∗ B ∗ A.\nProof. Admitted.",
        'Lemma canary_swap (A B : PROP) : A ∗ B -∗ B ∗ A.\nProof. iIntros "[HA HB]". iFrame. Qed.',
    )
    plan = tmp_path / "plan.v"
    plan.write_text(good, encoding="utf-8")
    cfg = ProveConfig(file=canary_dir / "Canary.v", target="canary_main", plan=plan, graph_path=tmp_path / "g.db", workroot=tmp_path / "w")
    graph, root, sentinels = build_graph(cfg, plan_nodes(cfg))
    swap = graph.by_name("canary_swap")
    assert swap.proof_status == "gated" and swap.body == 'iIntros "[HA HB]". iFrame.'
    assert graph.by_name("canary_assoc").proof_status == "open"
    graph.close()

    bad = good.replace('iIntros "[HA HB]". iFrame. Qed.', "admit. Qed.")
    plan.write_text(bad, encoding="utf-8")
    cfg2 = ProveConfig(file=canary_dir / "Canary.v", target="canary_main", plan=plan, graph_path=tmp_path / "g2.db", workroot=tmp_path / "w2")
    with pytest.raises(UsageError, match="canary_swap"):
        build_graph(cfg2, plan_nodes(cfg2))


@needs_rocq
def test_the_plan_preamble_reaches_the_gate_and_the_worker(tmp_path, canary_dir):
    """A child that needs an import only the plan supplies must still prove."""
    from pcp.orch.prove import ProveConfig, run
    from pcp.orch.runners.mock import MockRunner

    plan = tmp_path / "plan.v"
    plan.write_text(
        "From iris.bi Require Import bi.\n"
        "Lemma canary_swap (A B : PROP) : A ∗ B -∗ B ∗ A.\nProof. Admitted.\n",
        encoding="utf-8",
    )
    seen = []
    cfg = ProveConfig(
        file=canary_dir / "Canary.v", target="canary_main", plan=plan, graph_path=tmp_path / "g.db",
        workroot=tmp_path / "w", node_seconds=60, run_lock=False,
    )
    runner = MockRunner(
        {"canary_swap": 'iIntros "[HA HB]". iFrame.', "canary_main": 'iIntros "H". iDestruct (canary_swap with "H") as "[HQR HP]". iDestruct "HQR" as "[HQ HR]". iFrame.'},
        on_dispatch=seen.append,
    )
    result = run(cfg, runner)
    assert result.integrated, result.render()
    scratch = next(p.workdir for p in seen if p.name == "canary_swap") / "Canary.v"
    assert "From iris.bi Require Import bi." in scratch.read_text()
    assert result.solution is None
    result.close()
