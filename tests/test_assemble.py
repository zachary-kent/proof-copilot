"""Two-zone assembly (PLAN.md 8.3): the freeze is enforced by construction."""

from __future__ import annotations

from pathlib import Path

import pytest


@pytest.fixture(scope="module")
def dev(scratch_dir: Path):
    from pcp.orch.assemble import Development

    return Development(scratch_dir / "Basic.v")


def test_children_land_inside_the_root_s_section(dev) -> None:
    """`Section`/`Context` variables are invisible on the lemma line but are real
    hypotheses; children must inherit exactly the ones the root has."""
    from pcp.orch.assemble import NodeSpec

    a = dev.assemble("load_twice", [NodeSpec("helper", "Lemma helper (P : iProp Σ) : P -∗ P.")])
    assert a.open_sections == ["basics"]
    assert a.text.index("Section basics.") < a.text.index("Lemma helper")
    assert a.text.index("Lemma helper") < a.text.index("Lemma load_twice")
    assert a.text.rstrip().endswith("End basics.")


def test_a_worker_body_cannot_reach_outside_its_span(dev) -> None:
    """Whatever a worker writes lands between `Proof.` and the terminator, full stop."""
    from pcp.orch.assemble import NodeSpec

    hostile = "iIntros. iFrame.\nQed.\nLemma sneaky : False.\nProof. admit.\nAdmitted.\nLemma x : True.\nProof."
    a = dev.assemble("sep_comm", [NodeSpec("c", "Lemma c : True.", body=hostile)])
    # The text is present -- assembly does not sanitise -- but it is inside the body
    # span, so the static checks see it and the gate rejects the patch.
    start, end = a.spans["c"]
    assert hostile in a.text[start:end]
    from pcp.orch.gate import Gate

    checks = {c.name: c for c in Gate(dev).static_checks({"c": hostile})}
    assert not checks["no new Admitted / admit / Axiom / Parameter"].ok


def test_untruncated_assembly_keeps_the_rest_of_the_file(dev) -> None:
    a = dev.assemble("sep_comm", [], anchor_body='iIntros "[HP HQ]". iFrame.', truncate=False)
    assert "Lemma load_twice" in a.text
    assert "End basics." in a.text


def test_admitted_stub_rendering() -> None:
    from pcp.orch.assemble import NodeSpec

    assert NodeSpec("a", "Lemma a : True.").render() == "Lemma a : True.\nProof.\nAdmitted.\n"
    assert NodeSpec("a", "Lemma a : True.", body="exact I.").render() == (
        "Lemma a : True.\nProof.\nexact I.\nQed.\n"
    )


def test_non_mockable_nodes_refuse_to_be_stubbed() -> None:
    """Obligations that must be transparent cannot be stubbed by an admit; they
    genuinely block their dependents (PLAN.md 0)."""
    from pcp.orch.assemble import NodeSpec

    with pytest.raises(ValueError, match="non-mockable"):
        NodeSpec("d", "Definition d : nat.", body=None, mockable=False).render()


def test_plan_parsing_distinguishes_proved_from_admitted() -> None:
    from pcp.orch.assemble import parse_plan

    specs = parse_plan(
        "Lemma a : True.\nProof. Admitted.\n\nLemma b : True.\nProof. exact I. Qed.\n"
    )
    assert [(s.name, s.body) for s in specs] == [("a", None), ("b", "exact I.")]


def test_binder_surgery() -> None:
    from pcp.orch.assemble import remove_binder, statement_binders

    st = "Lemma f (n : nat) (Hn : n > 0) (P Q : iProp Σ) : P -∗ P."
    assert statement_binders(st) == ["n", "Hn", "P", "Q"]
    assert remove_binder(st, "Hn") == "Lemma f (n : nat) (P Q : iProp Σ) : P -∗ P."
    assert remove_binder(st, "P") == "Lemma f (n : nat) (Hn : n > 0) (Q : iProp Σ) : P -∗ P."
    assert remove_binder(st, "nope") is None
