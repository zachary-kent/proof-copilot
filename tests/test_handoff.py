"""pcp.orch.handoff: the handoff .v (contract §1.4)."""

from __future__ import annotations

import pytest

from pcp.orch.graph import Graph
from pcp.orch.handoff import best_partial, comment_safe, render_handoff
from pcp.orch.model import Node, node_id


@pytest.fixture
def graph(tmp_path):
    g = Graph(tmp_path / "g.db")
    g.add_node(Node(id=node_id("root"), name="root", statement="Lemma root : True.", rank="root",
                    statement_status="frozen", ordering=1_000_000, file="/dev/Dev.v"))
    g.add_node(Node(id=node_id("child"), name="child", statement="Lemma child (P : Prop) : P -> P.",
                    statement_status="frozen", intent="because the root needs it", file="/dev/Dev.v"))
    g.add_edge("root", "child")
    yield g
    g.close()


def test_layout_matches_the_contract(graph):
    graph.set_proof_status("child", "claimed")
    a = graph.start_attempt("child", runner="mock", owner="human")
    graph.finish_attempt(a, status="stuck", evidence="iFrame failed", body="intros P HP.",
                         requests=[{"statement": "Lemma helper : True.", "rationale": "would unblock"}])
    graph.set_proof_status("child", "stuck", evidence="iFrame failed *) Qed.")
    text = render_handoff(graph, graph.get("child"))
    lines = text.splitlines()
    assert lines[0] == "(* child -- handed off from pcp *)"
    assert lines[1] == "(*" and lines[2] == f"   node          {node_id('child')}"
    assert lines[3] == "   status        stuck (statement frozen@0)"
    assert lines[4] == "   attempts      1" and lines[5] == "   source        /dev/Dev.v"
    assert lines[6] == "   intent" and lines[7] == "     because the root needs it" and lines[8] == "*)"
    assert "(* Why it stopped:\n   iFrame failed * ) Qed.\n*)" in text
    assert "(* Lemmas the workers asked for" in text and "(*   Lemma helper : True. *)" in text
    assert "(*     because: would unblock *)" in text
    assert text.endswith("Lemma child (P : Prop) : P -> P.\nProof.\n  (* best partial script from the attempts above *)\n  intros P HP.\nAdmitted.\n")
    assert "*)" not in "\n".join(ln for ln in lines if ln.startswith("   ") or ln.startswith("(*   "))[:0]


def test_dependencies_with_pinned_epochs(graph):
    text = render_handoff(graph, graph.get("root"))
    assert "(* Depends on (pinned epochs): *)\n(*   child @0 [uses] *)" in text
    assert "(* no partial script survived; start from the statement *)" in text


def test_hostile_body_never_becomes_the_partial(graph):
    node = graph.get("child")
    attempts = [
        {"body": "intros P HP. Qed. Lemma sneaky : False. Proof. admit. Admitted. Lemma z : True. Proof. exact I."},
        {"body": "intros P."},
        {"body": "admit."},
    ]
    assert best_partial(node, attempts) == "intros P."
    assert best_partial(node, [{"body": None}]) is None


def test_comment_safe_neutralises_delimiters():
    assert comment_safe("a *) b (* c") == "a * ) b ( * c"
    assert "(*" not in comment_safe("(*(*")


def test_requests_tolerate_bad_rows(graph):
    from pcp.orch.handoff import collect_requests

    rows = [{"requests": "not json"}, {"requests": '["Lemma x"]'}, {"requests": [{"statement": " S ", "rationale": None}]}]
    assert collect_requests(rows) == [{"statement": " S ", "rationale": ""}]
