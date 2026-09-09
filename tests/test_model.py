"""pcp.orch.model: the status lattice, budgets, node ids."""

from __future__ import annotations

import pytest

from pcp.errors import UsageError
from pcp.orch.model import (
    PROOF_STATUSES,
    STATEMENT_STATUSES,
    Budget,
    InvalidTransition,
    Node,
    node_id,
    transition,
)


def test_vocabularies_are_the_contracts():
    assert STATEMENT_STATUSES == ("proposed", "audited", "frozen", "refuted")
    assert PROOF_STATUSES == ("open", "claimed", "qed", "gated", "integrated", "contested", "stuck", "attic")


@pytest.mark.parametrize(
    "chain",
    [
        ("open", "claimed", "qed", "gated", "integrated"),
        ("open", "claimed", "gated", "open"),
        ("open", "claimed", "stuck", "open"),
        ("open", "claimed", "contested"),
        ("open", "claimed", "open"),
        ("stuck", "attic", "open"),
        ("integrated", "open", "claimed"),
    ],
)
def test_lattice_moves_are_allowed(chain):
    for a, b in zip(chain, chain[1:], strict=False):
        transition(a, b)


@pytest.mark.parametrize(
    "current,new",
    [("attic", "integrated"), ("open", "gated"), ("open", "integrated"), ("stuck", "gated"),
     ("gated", "claimed"), ("integrated", "claimed"), ("contested", "claimed"), ("open", "stuck")],
)
def test_forbidden_moves_raise(current, new):
    with pytest.raises(InvalidTransition):
        transition(current, new)


def test_attic_to_integrated_is_impossible():
    with pytest.raises(InvalidTransition):
        transition("attic", "integrated")


def test_contested_reopens_only_for_a_human():
    with pytest.raises(InvalidTransition):
        transition("contested", "open")
    transition("contested", "open", human=True)


def test_only_unproved_nodes_go_to_the_attic():
    transition("open", "attic")
    transition("claimed", "attic")
    transition("stuck", "attic")
    with pytest.raises(InvalidTransition):
        transition("gated", "attic", proved=True)
    with pytest.raises(InvalidTransition):
        transition("integrated", "attic", proved=True)


def test_unknown_status_is_rejected():
    with pytest.raises(InvalidTransition):
        transition("open", "bogus")
    with pytest.raises(InvalidTransition):
        transition("bogus", "open")


def test_no_op_is_not_a_move():
    for s in PROOF_STATUSES:
        transition(s, s)


def test_budget_split_divides_metered_dimensions_but_not_the_clock():
    b = Budget(requests=200, tokens=1000, dollars=10.0, seconds=7200).split(4)
    assert (b.requests, b.tokens, b.dollars, b.seconds) == (50, 250, 2.5, 7200)
    half = Budget(seconds=100).split(2, share=0.5)
    assert half.seconds == 50


def test_clock_only_budget_is_live_not_exhausted():
    b = Budget(requests=200, seconds=7200).split(300)
    assert b.requests == 0 and b.seconds == 7200
    assert not b.exhausted()


def test_unset_budget_is_not_exhausted_and_negative_is():
    assert Budget().unset and not Budget().exhausted()
    assert Budget(requests=-1).exhausted()
    assert not Budget(requests=1).exhausted()


def test_budget_from_json_ignores_unknown_keys_instead_of_resetting():
    assert Budget.from_json('{"requests": 5, "extra": 1}') == Budget(requests=5)
    assert Budget.from_json({"seconds": 3}) == Budget(seconds=3.0)
    assert Budget.from_json(None) == Budget()


def test_budget_from_json_rejects_garbage():
    with pytest.raises(UsageError):
        Budget.from_json("{not json")
    with pytest.raises(UsageError):
        Budget.from_json("[1,2]")


def test_budget_json_roundtrip():
    b = Budget(requests=3, tokens=4, dollars=0.5, seconds=9)
    assert Budget.from_json(b.dumps()) == b
    assert Budget.from_json(b.to_json()) == b


def test_node_json_roundtrip_and_flags():
    n = Node(id=node_id("x"), name="x", statement="Lemma x : True.", statement_status="frozen",
             transparent=True, budget=Budget(requests=2))
    assert n.dispatchable and not n.done and not n.proved
    back = Node.from_json(n.to_json())
    assert back == n
    assert Node.from_json({**n.to_json(), "unknown": 1}).name == "x"


def test_node_ids_are_collision_free():
    assert node_id("foo_bar") == "foo_bar"
    assert node_id("foo.bar") != node_id("foo_bar")
    long_a, long_b = "a" * 70 + "x", "a" * 70 + "y"
    assert node_id(long_a) != node_id(long_b)
    assert len(node_id(long_a)) <= 64
