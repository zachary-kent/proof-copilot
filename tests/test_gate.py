"""The integrity gate (PLAN.md 8.7), against real Rocq.

An agent-built development can be fully `Qed`-clean and still worthless, because the
kernel checks proofs, not statements.  Each test here corresponds to a specific way
that goes wrong.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from tests.conftest import needs_rocq


@pytest.fixture(scope="module")
def dev(scratch_dir: Path):
    from pcp.orch.assemble import Development

    return Development(scratch_dir / "Basic.v")


@pytest.fixture(scope="module")
def gate(dev):
    from pcp.orch.gate import Gate

    return Gate(dev)


# ----------------------------------------------------------------- static checks

def test_static_checks_reject_admits_hatches_and_globals(gate) -> None:
    checks = {c.name: c for c in gate.static_checks({
        "a": "iIntros. admit.",
        "b": "Unset Universe Checking. iIntros.",
        "c": "Global Instance foo : True := I.",
    })}
    assert not checks["no new Admitted / admit / Axiom / Parameter"].ok
    assert not checks["no escape hatches"].ok
    assert not checks["ambient-state hygiene (no global Instance/Hint/Notation/Ltac)"].ok


def test_static_checks_ignore_the_words_inside_comments(gate) -> None:
    checks = {c.name: c for c in gate.static_checks({"a": "(* we could admit here *) iIntros. iFrame."})}
    assert checks["no new Admitted / admit / Axiom / Parameter"].ok


def test_local_registrations_are_allowed(gate) -> None:
    """Node-local helpers are unrestricted; only *global* registration is a spec change."""
    checks = {c.name: c for c in gate.static_checks({"a": "Local Ltac t := iFrame.\nt."})}
    assert checks["ambient-state hygiene (no global Instance/Hint/Notation/Ltac)"].ok


def test_a_disqualified_patch_never_pays_for_a_compile(gate) -> None:
    result = gate.run("sep_comm", [], target_body="admit.")
    assert not result.ok
    compile_check = next(c for c in result.checks if c.name == "compiles (coqc)")
    assert "skipped" in compile_check.detail
    assert result.elapsed_s < 1.0


# ------------------------------------------------------------------- with Rocq

@needs_rocq
def test_a_correct_proof_passes_and_prints_clean_assumptions(gate) -> None:
    result = gate.run("sep_comm", [], target_body='iIntros "[HP HQ]". iFrame.')
    assert result.ok, result.render()
    assert result.assumptions == {"sep_comm": []}


@needs_rocq
def test_a_wrong_proof_fails_with_the_first_error(gate) -> None:
    result = gate.run("sep_comm", [], target_body='iIntros "[HP HQ]". done.')
    assert not result.ok
    compile_check = next(c for c in result.checks if c.name == "compiles (coqc)")
    assert not compile_check.ok
    assert "Error" in result.compile_output


@needs_rocq
def test_proving_against_an_admitted_stub_is_allowed_and_reported(gate) -> None:
    """Claim 1: a proof against a type-checked stub is the work that survives."""
    from pcp.orch.assemble import NodeSpec

    child = NodeSpec(
        name="comm_helper",
        statement="Lemma comm_helper (P Q : iProp Σ) : P ∗ Q -∗ Q ∗ P.",
        body=None,
    )
    result = gate.run("sep_comm", [child], target_body="iApply comm_helper.")
    assert result.ok, result.render()
    assert result.assumptions["sep_comm"] == ["comm_helper"]
    leaning = next(c for c in result.checks if c.name == "rests on open stubs")
    assert leaning.advisory and "comm_helper" in leaning.detail


@needs_rocq
def test_statement_pinning_holds_for_an_injected_child(gate) -> None:
    from pcp.orch.assemble import NodeSpec

    child = NodeSpec(
        name="pinned_child",
        statement="Lemma pinned_child (P : iProp Σ) : P -∗ P.",
        body='iIntros "H". iFrame.',
    )
    result = gate.run("sep_comm", [child], target_body=None, target="pinned_child")
    pin = next(c for c in result.checks if c.name == "statement pinning by construction")
    assert pin.ok
    assert child.statement in result.assembled


@needs_rocq
def test_the_unused_premise_probe_finds_a_real_one_and_no_others(gate) -> None:
    """The removal probe is ground truth: restate without the premise and re-run."""
    over = gate.run("over_strong", [], target_body='iIntros "HP". iFrame.', unused_premise_report=True)
    assert over.unused_premises == ["Hn"], over.render()
    tight = gate.run("sep_comm", [], target_body='iIntros "[HP HQ]". iFrame.', unused_premise_report=True)
    assert tight.unused_premises == []
    # It is advisory: an over-strong statement still gates.
    assert over.ok


@needs_rocq
def test_proof_using_is_injected(gate) -> None:
    from pcp.orch.assemble import PROOF_USING_DIRECTIVE

    result = gate.run("sep_comm", [], target_body='iIntros "[HP HQ]". iFrame.')
    assert PROOF_USING_DIRECTIVE in result.assembled


def test_assumption_parsing_refuses_to_misattribute() -> None:
    """Wrong attribution is worse than none: mismatched counts return nothing."""
    from pcp.orch.gate import parse_assumptions

    out = "Closed under the global context\nAxioms:\nfoo : nat\n"
    assert parse_assumptions(out, ["a", "b"]) == {"a": [], "b": ["foo"]}
    assert parse_assumptions(out, ["a"]) == {}
    assert parse_assumptions("", ["a"]) == {}


def test_warnings_are_not_mistaken_for_axioms() -> None:
    from pcp.orch.gate import parse_assumptions

    out = "Axioms:\nfoo : nat\n\nWarning: Deprecated environment variable COQPATH\n"
    assert parse_assumptions(out, ["a"]) == {"a": ["foo"]}


# --------------------------------------------------------------- prefix stubbing

def test_stubbing_the_prefix_keeps_statements_and_drops_bodies() -> None:
    from pcp.orch.assemble import stub_proof_bodies

    src = (
        "Lemma a : True.\nProof. exact I. Qed.\n\n"
        "Definition d : nat.\nProof. exact 0. Defined.\n\n"
        "Lemma b : True.\nProof. Admitted.\n"
    )
    out, stubbed = stub_proof_bodies(src)
    assert stubbed == ["a"]
    assert "Lemma a : True." in out and "exact I." not in out
    # Transparent proofs are left alone: a dependent may need to compute with them.
    assert "exact 0." in out and "Defined." in out
    # Already-admitted blocks are untouched.
    assert out.count("Admitted.") == 2


def test_stubbing_can_keep_named_blocks() -> None:
    from pcp.orch.assemble import stub_proof_bodies

    src = "Lemma a : True.\nProof. exact I. Qed.\nLemma b : True.\nProof. exact I. Qed.\n"
    out, stubbed = stub_proof_bodies(src, keep={"b"})
    assert stubbed == ["a"]
    assert out.count("exact I.") == 1


@needs_rocq
def test_the_fast_and_full_paths_agree_on_accept_and_reject(dev, gate) -> None:
    """Stubbing must change the cost of the check, not its verdict."""
    good = 'iIntros "[HP HQ]". iFrame.'
    bad = 'iIntros "[HP HQ]". done.'
    for body, expected in ((good, True), (bad, False)):
        fast = gate.run("sep_comm", [], target_body=body, stub_prefix=True)
        full = gate.run("sep_comm", [], target_body=body, stub_prefix=False)
        assert fast.ok is expected, fast.render()
        assert full.ok is expected, full.render()


@needs_rocq
def test_stubbed_siblings_are_allowed_assumptions(dev, gate) -> None:
    """The target legitimately rests on the stubs, and the gate says so rather than
    failing on axiom hygiene."""
    result = gate.run("load_twice", [], target_body='iIntros "Hl". wp_load. wp_seq. wp_load. iFrame. done.',
                      stub_prefix=True)
    assert result.ok, result.render()


# ------------------------------------------------------------------ design mode

DESIGN_SRC = """\
Definition prog : val := #0.
Definition inv_pred (n : nat) : Prop := True.
Lemma spec (n : nat) : inv_pred n.
Proof.
Admitted.
"""


def test_run_design_gates_a_whole_file_against_the_contract(dev, gate) -> None:
    """A design task cannot be gated by proof-body spans -- filling in an invariant
    means editing definitions -- so the contract does it instead."""
    from pcp.orch.contract import DesignContract

    contract = DesignContract.from_names(["over_strong"])
    unchanged = dev.source
    result = gate.run_design(unchanged, contract, check_assumptions=False)
    contract_check = next(
        c for c in result.checks if c.name.startswith("design contract")
    )
    assert contract_check.ok

    edited = unchanged.replace(
        'Definition new_rwcas', 'Definition tampered'
    ) if "new_rwcas" in unchanged else unchanged.replace(
        "Lemma sep_comm", "Lemma sep_comm_renamed"
    )
    bad = gate.run_design(edited, contract, check_assumptions=False)
    assert not bad.ok


def test_run_design_defaults_proved_to_whatever_the_file_closes(dev, gate) -> None:
    from pcp.orch.contract import DesignContract

    result = gate.run_design(
        "Lemma a : True.\nProof. exact I. Qed.\n",
        DesignContract.from_names([]),
        check_assumptions=False,
    )
    # It reports a contract violation (everything was deleted), not a crash.
    assert not result.ok
