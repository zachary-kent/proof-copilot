"""Wave-3 review: the store's role split over the statement ledger, and every legacy
graph on this machine migrating on a copy."""

from __future__ import annotations

import hashlib
import shutil
from pathlib import Path

import pytest

from pcp.errors import RoleViolation
from pcp.orch.graph import SCHEMA_VERSION, Graph
from pcp.orch.model import PROOF_STATUSES, STATEMENT_STATUSES, Node, node_id

REPO = Path(__file__).resolve().parents[1]
def _schema_version(path: Path) -> str:
    """Read-only peek; graphs the rewrite itself wrote (schema 2, possibly live) are not legacy."""
    import sqlite3

    try:
        db = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
        try:
            row = db.execute("SELECT value FROM meta WHERE key='schema_version'").fetchone()
        finally:
            db.close()
    except sqlite3.Error:
        return ""
    return str(row[0]) if row else "1"


LEGACY = sorted(
    p for p in list((REPO / ".pcp").glob("*.db")) + list((REPO / ".pcp" / "graphs").glob("*.db"))
    if _schema_version(p) == "1"
)


def _node(name: str, **kw) -> Node:
    kw.setdefault("statement_status", "frozen")
    return Node(id=node_id(name), name=name, statement=kw.pop("statement", f"Lemma {name} : True."), **kw)


def test_only_a_human_write_may_restate_or_move_the_epoch(tmp_path):
    with Graph(tmp_path / "g.db") as g:
        g.add_node(_node("c"))
        for fields in ({"statement": "Lemma c : False."}, {"statement_hash": "s:0"}, {"epoch": 3}, {"statement_status": "refuted"}):
            with pytest.raises(RoleViolation):
                g.update("c", **fields)
            with pytest.raises(RoleViolation):
                g.update("c", role="decomposer", **fields)
        n = g.update("c", statement="Lemma c : False.", epoch=1, role="human")
        assert n.statement == "Lemma c : False." and n.epoch == 1
        g.set_proof_status("c", "claimed")
        g.record_proof("c", "exact I.")
        # The store's own invalidation still bumps the epoch for a prover-role move.
        assert g.set_proof_status("c", "open", evidence="revalidate").epoch == 2


def test_a_stuck_node_carrying_a_partial_body_can_still_be_retired(tmp_path):
    with Graph(tmp_path / "g.db") as g:
        g.add_node(_node("c"))
        g.set_proof_status("c", "claimed")
        g.set_proof_status("c", "stuck", evidence="partial", body="iIntros.")
        assert g.get("c").body == "iIntros." and not g.get("c").proved
        assert g.set_proof_status("c", "attic", role="human").proof_status == "attic"


@pytest.mark.skipif(not LEGACY, reason="no legacy graphs on this machine")
@pytest.mark.parametrize("src", LEGACY, ids=[p.name for p in LEGACY])
def test_every_legacy_graph_migrates_on_a_copy_and_the_original_is_untouched(tmp_path, src):
    before = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in src.parent.glob(src.name + "*")}
    dst = tmp_path / src.name
    for suffix in ("", "-wal", "-shm"):
        if Path(str(src) + suffix).exists():
            shutil.copy(str(src) + suffix, str(dst) + suffix)
    with Graph.open_readonly(dst) as ro:
        nodes = ro.nodes()
        assert all(n.proof_status in PROOF_STATUSES and n.statement_status in STATEMENT_STATUSES for n in nodes)
        ro.events_since(limit=100_000)
    with Graph(dst) as g:
        assert g.get_meta("schema_version") == str(SCHEMA_VERSION)
        assert len(g.nodes()) == len(nodes)
        for n in g.nodes():
            g.attempts_for(n.id)
            g.salvageable_body(n.id)
        assert [e["kind"] for e in g.events_since(limit=100_000)].count("schema.migrated") == 1
    with Graph(dst) as g:
        assert [e["kind"] for e in g.events_since(limit=100_000)].count("schema.migrated") == 1
    assert {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in src.parent.glob(src.name + "*")} == before


def test_transaction_groups_mutations_atomically(tmp_path):
    with Graph(tmp_path / "g.db") as g:
        g.add_node(_node("a"))
        g.add_node(_node("b"))
        with pytest.raises(RuntimeError), g.transaction():
            g.set_proof_status("a", "claimed")
            g.set_proof_status("b", "claimed")
            raise RuntimeError("crash between the two status writes")
        assert {n.name: n.proof_status for n in g.nodes()} == {"a": "open", "b": "open"}
        assert not [e for e in g.events_since() if e["kind"] == "node.proof_status"]
        with g.transaction():
            g.set_proof_status("a", "claimed")
            g.set_proof_status("b", "claimed")
        assert {n.proof_status for n in g.nodes()} == {"claimed"}


def test_salvageable_body_is_epoch_aware(tmp_path):
    """A body gated at epoch 0 is not a proof of the epoch-1 statement (review handoff)."""
    from pcp.orch.graph import Graph
    from pcp.orch.model import Node, node_id

    g = Graph(tmp_path / "g.db")
    g.add_node(Node(id=node_id("c"), name="c", statement="Lemma c : True.", statement_status="frozen", rank="local"))
    aid = g.start_attempt(node_id("c"), runner="mock", owner="human")
    g.finish_attempt(aid, status="qed", body="exact I.", gate={"ok": True})
    assert g.salvageable_body(node_id("c")) == "exact I."
    g.update(node_id("c"), epoch=1, statement="Lemma c : 1 = 1.", role="human")
    assert g.salvageable_body(node_id("c")) is None
    assert g.salvageable_body(node_id("c"), epoch=0) == "exact I."
    g.close()
