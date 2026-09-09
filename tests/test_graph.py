"""pcp.orch.graph: the SQLite store, its invariants and the v1 migration."""

from __future__ import annotations

import hashlib
import json
import shutil
import threading
from pathlib import Path

import pytest

from pcp.errors import RoleViolation, UsageError
from pcp.orch.graph import SCHEMA_VERSION, Graph
from pcp.orch.model import Budget, InvalidTransition, Node, node_id

LEGACY_DB = Path(__file__).resolve().parents[1] / ".pcp" / "graph_ladder_20260831_rwcas.db"


def _node(name: str, **kw) -> Node:
    kw.setdefault("statement_status", "frozen")
    return Node(id=node_id(name), name=name, statement=kw.pop("statement", f"Lemma {name} : True."), **kw)


@pytest.fixture
def graph(tmp_path):
    g = Graph(tmp_path / "g.db")
    g.add_node(_node("root", rank="root", is_glue=True, ordering=1_000_000))
    g.add_node(_node("c1", parent="root", depth=1, ordering=0))
    g.add_node(_node("c2", parent="root", depth=1, ordering=1))
    g.add_edge("root", "c1")
    g.add_edge("root", "c2")
    yield g
    g.close()


def test_fresh_graph_has_schema_version_2(tmp_path):
    with Graph(tmp_path / "g.db") as g:
        assert g.get_meta("schema_version") == str(SCHEMA_VERSION) == "2"
        cols = {r[1] for r in g.db.execute("PRAGMA table_info(nodes)")}
        assert "transparent" in cols and "tier" in {r[1] for r in g.db.execute("PRAGMA table_info(attempts)")}


def test_duplicate_id_and_name_are_usage_errors(graph):
    with pytest.raises(UsageError, match="already exists"):
        graph.add_node(Node(id="c1", name="other", statement="Lemma other : True."))
    with pytest.raises(UsageError, match="named 'c1'"):
        graph.add_node(Node(id="zz", name="c1", statement="Lemma c1 : True."))
    # Distinct names whose legacy slugs collided are distinct nodes now.
    graph.add_node(_node("foo.bar"))
    graph.add_node(_node("foo_bar"))
    assert graph.by_name("foo.bar").id != graph.by_name("foo_bar").id


def test_invalid_enums_are_rejected_on_insert_and_update(graph):
    with pytest.raises(UsageError):
        graph.add_node(_node("x", rank="boss"))
    with pytest.raises(UsageError):
        graph.add_node(_node("y", statement_status="bogus"))
    with pytest.raises(UsageError):
        graph.update("c1", statement_status="bogus")
    with pytest.raises(UsageError):
        graph.update("c1", proof_statu="open")


def test_body_only_enters_through_record_proof(graph):
    with pytest.raises(RoleViolation):
        graph.update("c1", body="exact I.")
    graph.set_proof_status("c1", "claimed")
    with pytest.raises(RoleViolation):
        graph.set_proof_status("c1", "gated", body="exact I.", role="decomposer")
    graph.record_proof("c1", "Proof.\n  exact I.\nQed.")
    n = graph.get("c1")
    assert n.proof_status == "gated" and n.body == "exact I." and n.proved


def test_transitions_are_enforced_by_the_store(graph):
    with pytest.raises(InvalidTransition):
        graph.set_proof_status("c1", "gated")
    graph.set_proof_status("c1", "claimed")
    graph.set_proof_status("c1", "contested", evidence="wrong")
    with pytest.raises(InvalidTransition):
        graph.set_proof_status("c1", "open")
    graph.set_proof_status("c1", "open", role="human")
    graph.set_proof_status("c2", "attic")
    with pytest.raises(InvalidTransition):
        graph.update("c2", proof_status="integrated")


def test_reopening_a_proved_node_bumps_epoch_and_clears_body(graph):
    graph.set_proof_status("c1", "claimed")
    graph.record_proof("c1", "exact I.")
    graph.set_proof_status("c1", "open", evidence="revalidation")
    n = graph.get("c1")
    assert n.epoch == 1 and n.body is None and n.proof_status == "open"
    assert graph.stale_edges("root") == [("c1", 0, 1)]


def test_proved_nodes_cannot_go_to_the_attic(graph):
    graph.set_proof_status("c1", "claimed")
    graph.record_proof("c1", "exact I.")
    with pytest.raises(InvalidTransition):
        graph.set_proof_status("c1", "attic")


def test_clear_body_and_freeze(tmp_path):
    with Graph(tmp_path / "g.db") as g:
        g.add_node(_node("p", statement_status="proposed"))
        assert not g.get("p").dispatchable
        g.freeze("p")
        assert g.get("p").dispatchable
        with pytest.raises(UsageError):
            g.freeze("missing")
        g.set_proof_status("p", "claimed")
        g.record_proof("p", "exact I.")
        g.clear_body("p")
        assert g.get("p").body is None


def test_frontier_order_non_mockable_first_root_last(tmp_path):
    with Graph(tmp_path / "g.db") as g:
        g.add_node(_node("root", rank="root", ordering=1_000_000))
        g.add_node(_node("deep", depth=2, ordering=0))
        g.add_node(_node("b", depth=1, ordering=1))
        g.add_node(_node("a", depth=1, ordering=0))
        g.add_node(_node("hard", depth=1, ordering=5, mockable=False))
        g.add_node(_node("done", depth=1, ordering=0, proof_status="gated", body="exact I."))
        assert [n.name for n in g.frontier()] == ["hard", "root", "a", "b", "deep"]
        assert g.open_count() == 5 and g.summary() == {"open": 5, "gated": 1}


def test_edges_and_dependents(graph):
    assert sorted(d for d, _e, _k in graph.deps("root")) == ["c1", "c2"]
    assert graph.dependents("c1") == ["root"]
    assert graph.transitive_dependents("c1") == ["root"]
    with pytest.raises(UsageError):
        graph.add_edge("root", "nope")


def test_attempts_count_only_provers(graph):
    a1 = graph.start_attempt("root", runner="claude", owner="human", role="decomposer")
    a2 = graph.start_attempt("root", runner="mock", owner="human", role="prover", round=2)
    assert graph.get("root").attempts == 1
    graph.finish_attempt(a1, status="qed")
    graph.finish_attempt(a2, status="stuck", evidence="no", requests=[{"statement": "Lemma h : True.", "rationale": "r"}])
    rows = graph.attempts_for("root")
    assert [r["id"] for r in rows] == [a1, a2] and rows[1]["round"] == 2 and rows[0]["tier"] == "human"
    assert json.loads(rows[1]["requests"])[0]["statement"] == "Lemma h : True."
    with pytest.raises(UsageError):
        graph.finish_attempt(999, status="qed")
    with pytest.raises(UsageError):
        graph.finish_attempt(a2, status="claimed")


def test_salvageable_body_is_the_latest_gated_qed(graph):
    a1 = graph.start_attempt("c1", runner="mock", owner="human")
    graph.finish_attempt(a1, status="qed", body="admit.", gate={"ok": False})
    assert graph.salvageable_body("c1") is None
    a2 = graph.start_attempt("c1", runner="mock", owner="human")
    graph.finish_attempt(a2, status="qed", body="exact I.", gate={"ok": True})
    a3 = graph.start_attempt("c1", runner="mock", owner="human")
    graph.finish_attempt(a3, status="stuck", body="idtac.", gate={})
    assert graph.salvageable_body("c1") == "exact I."


def test_every_mutation_emits_an_event(graph):
    kinds = [e["kind"] for e in graph.events_since()]
    assert kinds.count("node.added") == 3 and kinds.count("edge.added") == 2
    before = len(kinds)
    graph.set_meta("designed_file", "/x")
    graph.put_blob("hello")
    graph.set_proof_status("c1", "claimed")
    a = graph.start_attempt("c1", runner="mock", owner="human")
    graph.finish_attempt(a, status="stuck")
    new = [e["kind"] for e in graph.events_since()][before:]
    assert new == ["meta.set", "blob.put", "node.updated", "node.proof_status", "attempt.started", "attempt.finished"]
    ev = [e for e in graph.events_since() if e["kind"] == "attempt.started"][-1]
    assert {"runner", "owner", "role", "attempt"} <= set(ev["payload"]) and "tier" not in ev["payload"]
    assert graph.get_blob(graph.put_blob("hello")) == "hello"


def test_events_since_cursor(graph):
    first = graph.events_since(limit=2)
    assert len(first) == 2
    rest = graph.events_since(first[-1]["id"])
    assert rest[0]["id"] == first[-1]["id"] + 1


def test_update_converts_budget_and_bools(graph):
    n = graph.update("c1", budget=Budget(requests=7), mockable=False, cost={"dollars": 1})
    assert n.budget.requests == 7 and n.mockable is False and n.cost == {"dollars": 1}
    assert graph.nodes(mockable=False)[0].name == "c1"
    with pytest.raises(UsageError):
        graph.nodes(bogus=1)


def test_concurrent_writers_share_one_locked_connection(graph):
    errors: list[BaseException] = []

    def work(i: int) -> None:
        try:
            for _ in range(20):
                graph.emit("tick", "c1", i=i)
                graph.update("c1", intent=f"thread {i}")
                graph.get("c1")
        except BaseException as exc:  # noqa: BLE001
            errors.append(exc)

    threads = [threading.Thread(target=work, args=(i,)) for i in range(6)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    assert not errors
    assert len([e for e in graph.events_since(limit=10_000) if e["kind"] == "tick"]) == 120


@pytest.mark.skipif(not LEGACY_DB.exists(), reason="no legacy graph on this machine")
def test_migration_of_a_legacy_v1_database(tmp_path):
    src = LEGACY_DB
    dst = tmp_path / "legacy.db"
    shutil.copy(src, dst)
    before = hashlib.sha256(src.read_bytes()).hexdigest()
    with Graph(dst) as g:
        assert g.get_meta("schema_version") == "2"
        assert "transparent" in {r[1] for r in g.db.execute("PRAGMA table_info(nodes)")}
        assert "round" in {r[1] for r in g.db.execute("PRAGMA table_info(attempts)")}
        nodes = g.nodes()
        assert len(nodes) == 11 and any(n.rank == "root" for n in nodes)
        root = next(n for n in nodes if n.rank == "root")
        assert root.body and root.budget.requests == 200 and root.transparent is False
        rows = g.attempts_for(root.id)
        assert rows and all(r["round"] == 1 for r in rows) and rows[0]["tier"] in ("human", "decomposer")
        assert g.salvageable_body(root.id)
        assert g.events_since()[-1]["kind"] == "schema.migrated"
        assert len(g.frontier()) == 0
    with Graph(dst) as g:  # idempotent
        assert g.get_meta("schema_version") == "2"
        assert [e["kind"] for e in g.events_since(limit=10_000)].count("schema.migrated") == 1
    assert hashlib.sha256(src.read_bytes()).hexdigest() == before, "the original must never be modified"


@pytest.mark.skipif(not LEGACY_DB.exists(), reason="no legacy graph on this machine")
def test_readonly_open_of_a_v1_database_reads_without_migrating(tmp_path):
    dst = tmp_path / "legacy.db"
    shutil.copy(LEGACY_DB, dst)
    digest = hashlib.sha256(dst.read_bytes()).hexdigest()
    with Graph.open_readonly(dst) as g:
        assert g.get_meta("schema_version") == "1"
        assert len(g.nodes()) == 11 and g.nodes()[0].transparent is False
        assert g.attempts_for(g.nodes()[0].id) is not None
        with pytest.raises(UsageError):
            g.set_meta("x", "y")
        with pytest.raises(UsageError):
            g.emit("x")
    assert hashlib.sha256(dst.read_bytes()).hexdigest() == digest


def test_readonly_open_never_creates_a_database(tmp_path):
    with pytest.raises(UsageError, match="no graph"):
        Graph.open_readonly(tmp_path / "typo.db")
    assert not (tmp_path / "typo.db").exists()


def test_newer_schema_is_refused(tmp_path):
    with Graph(tmp_path / "g.db") as g:
        g.set_meta("schema_version", "99")
    with pytest.raises(UsageError, match="newer"):
        Graph(tmp_path / "g.db")


def test_record_proof_strips_wrapper_and_add_node_too(tmp_path):
    with Graph(tmp_path / "g.db") as g:
        g.add_node(_node("p", proof_status="gated", body="Proof. exact I. Qed."))
        assert g.get("p").body == "exact I."
