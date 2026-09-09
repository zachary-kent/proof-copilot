"""Wave-3 review: gate soundness and durability findings, each reproduced first."""

from __future__ import annotations

from pathlib import Path

import pytest

from pcp.orch import gate as gate_mod
from pcp.orch.contract import DesignContract
from pcp.orch.gate import (
    CHECK_AXIOMS,
    CHECK_AXIOMS_DESIGN,
    CHECK_ESCAPE,
    CHECK_NO_ADMIT,
    Gate,
    escape_hatch,
    static_checks,
)
from pcp.rocq.assemble import Development, NodeSpec
from pcp.rocq.assumptions import classify_assumptions, parse_assumptions, trailer
from pcp.rocq.body import validate_body
from pcp.rocq.decls import find_block
from pcp.rocq.project import CompileResult
from tests.conftest import needs_rocq

PU = 'Set Default Proof Using "Type".\n'

SECTION = PU + """Section s.
  Variable n : nat.
  Hypothesis Hn : 0 < n.
  Lemma helper : 0 < n.
  Proof using Hn. exact Hn. Qed.
  Lemma target : 0 < n.
  Proof using Hn.
    exact Hn.
  Qed.
End s.
"""

EVIL = PU + "Module Evil. Axiom classic : False. End Evil.\nLemma target : False.\nProof. Admitted.\n"
ABBREV = PU + "Lemma target : True.\nProof. exact I. Qed.\nNotation TT := target.\n"
DESIGN = PU + "Definition value := 1.\nLemma h : True.\nProof. Admitted.\nLemma spec : True.\nProof. exact I. Qed.\n"

#: What Rocq 9.1.1 prints for a constant compiled under ``Unset Universe Checking``.
UNSAFE_HIERARCHY = "Constant dev.Dev.spec\nAxioms:\nu relies on an unsafe hierarchy.\n"


def _dev(tmp_path: Path, source: str) -> Development:
    (tmp_path / "_CoqProject").write_text("-Q . dev\n")
    (tmp_path / "Dev.v").write_text(source)
    return Development(tmp_path / "Dev.v")


def _by_name(result):
    return {c.name: c for c in result.checks}


def _fake_compile(monkeypatch, **fields):
    monkeypatch.setattr(gate_mod, "compile_text", lambda text, **kw: CompileResult(**{"ok": True, **fields}))


# ------------------------------------------------------------------ Proof using

def test_the_frozen_proof_using_clause_survives_assembly(tmp_path):
    dev = _dev(tmp_path, SECTION)
    text = dev.assemble("target", [NodeSpec("c", "Lemma c : True.", body="exact I.")], anchor_body="exact Hn.").text
    anchor = find_block(text, "target")
    assert anchor is not None and anchor.proof_opener == "Proof using Hn." and anchor.body(text).strip() == "exact Hn."
    assert find_block(text, "c").proof_opener == "Proof."
    stubbed = dev.assemble("target", [], anchor_body="exact Hn.", stub_prefix=True).text
    assert "Proof using Hn.\nAdmitted." in stubbed
    spec = NodeSpec("x", "Lemma x : True.", opener="Proof using All.")
    assert spec.with_body("exact I.").render() == "Lemma x : True.\nProof using All.\nexact I.\nQed.\n"


@needs_rocq
def test_a_correct_proof_that_needs_its_proof_using_clause_passes(tmp_path):
    dev = _dev(tmp_path, SECTION)
    assert Gate(dev).run("target", [], target_body="exact Hn.").ok
    assert Gate(dev).run("target", [], target_body="exact Hn.", stub_prefix=True).ok
    assert Gate(dev).run("target", [], target_body="exact helper.", truncate=False).ok


# ------------------------------------------------------------------ assumptions

def test_whitelist_matching_is_component_wise():
    from pcp.rocq.assumptions import Assumption

    wl = {"Classical_Prop.classic", "JMeq_eq"}
    ok, _, bad = classify_assumptions(
        [Assumption("classic"), Assumption("Stdlib.Logic.Classical_Prop.classic"), Assumption("Evil.classic"), Assumption("M.JMeq_eq")],
        whitelist=wl, stubs=set(),
    )
    assert [a.name for a in ok] == ["classic", "Stdlib.Logic.Classical_Prop.classic", "M.JMeq_eq"]
    assert [a.name for a in bad] == ["Evil.classic"]
    _, leaning, bad = classify_assumptions([Assumption("Outer.Inner.stub"), Assumption("Other.stub")], whitelist=set(), stubs={"Inner.stub"})
    assert [a.name for a in leaning] == ["Outer.Inner.stub"] and [a.name for a in bad] == ["Other.stub"]


@needs_rocq
def test_a_module_axiom_sharing_a_whitelisted_bare_name_is_rejected(tmp_path):
    r = Gate(_dev(tmp_path, EVIL)).run("target", [], target_body="exact Evil.classic.")
    assert not r.ok and _by_name(r)[CHECK_AXIOMS].detail == "target: Evil.classic"


def test_the_marker_is_a_located_constant_and_unknown_entries_fail_closed():
    assert trailer(["M.t"]) == "Locate M.t.\nPrint Assumptions M.t."
    report = parse_assumptions(UNSAFE_HIERARCHY, ["spec"])
    assert report.ok and [a.render() for a in report.by_name["spec"]] == ["u (assumed unsafe an unsafe hierarchy)"]
    _, _, bad = classify_assumptions(report.by_name["spec"], whitelist={"u"}, stubs={"u"})
    assert [a.name for a in bad] == ["u"]
    odd = parse_assumptions("Constant dev.Dev.t\nAxioms:\nsomething this parser has never seen\nx : nat\n", ["t"])
    assert [a.kind for a in odd.by_name["t"]] == ["unrecognised", "axiom"]
    located = parse_assumptions("Constant dev.Dev.M.t\n  (shorter name is t)\nClosed under the global context\n", ["M.t"])
    assert located.ok and located.by_name == {"M.t": []}


@needs_rocq
def test_an_abbreviation_for_the_target_does_not_make_the_proof_unverified(tmp_path):
    r = Gate(_dev(tmp_path, ABBREV)).run("target", [], target_body="exact I.", truncate=False)
    assert r.ok, r.render()
    assert r.assumptions == {"target": []}


# ------------------------------------------------------------------ static checks

def test_admit_inside_a_string_is_not_an_admit():
    assert validate_body('idtac "admit". iFrame.') == []
    assert validate_body('idtac "(* admit *)". exact (ltac:(admit)).')[0].reason == "forbidden tactic `admit`"
    assert all(c.ok for c in static_checks({"t": 'idtac "give_up". exact I.'}))


def test_a_modified_set_or_unset_is_still_an_escape_hatch():
    assert escape_hatch("Local Unset Guard Checking.") == "Unset Guard Checking"
    assert escape_hatch("#[global] Global Unset Universe Checking.") == "Unset Universe Checking"
    assert escape_hatch("Export Set Nested Proofs Allowed.") == "Set Nested Proofs"
    assert escape_hatch("Local Set Printing All.") is None
    c = {x.name: x for x in static_checks({"t": "Local Unset Guard Checking.\nexact I."})}
    assert not c[CHECK_ESCAPE].ok and "Guard Checking" in c[CHECK_ESCAPE].detail


def test_design_fragments_and_admitted_bodies_are_scanned_for_hatches(tmp_path, monkeypatch):
    _fake_compile(monkeypatch, stdout="Constant dev.Dev.spec\nClosed under the global context\n")
    dev = _dev(tmp_path, DESIGN)
    contract = DesignContract(mutable=frozenset({"value"}), results=frozenset({"spec"}))
    assert Gate(dev).run_design(dev.source, contract).ok
    r = Gate(dev).run_design(dev.source + "Local Unset Universe Checking.\n", contract)
    assert not _by_name(r)[CHECK_ESCAPE].ok and "Universe Checking" in _by_name(r)[CHECK_ESCAPE].detail
    inside = dev.source.replace("Lemma h : True.\nProof. Admitted.", "Lemma h : True.\nProof. Unset Universe Checking. Admitted.")
    r = Gate(dev).run_design(inside, contract)
    assert not _by_name(r)[CHECK_ESCAPE].ok and "h" in _by_name(r)[CHECK_ESCAPE].detail
    partial = dev.source.replace("Lemma h : True.\nProof. Admitted.", "Lemma h : True.\nProof. idtac. admit. Admitted.")
    r = Gate(dev).run_design(partial, contract)
    assert _by_name(r)[CHECK_NO_ADMIT].ok and _by_name(r)[CHECK_ESCAPE].ok


def test_an_unsafe_hierarchy_entry_fails_the_design_gate(tmp_path, monkeypatch):
    _fake_compile(monkeypatch, stdout=UNSAFE_HIERARCHY)
    dev = _dev(tmp_path, DESIGN)
    r = Gate(dev).run_design(dev.source, DesignContract(mutable=frozenset({"value"}), results=frozenset({"spec"})))
    assert not r.ok and "unsafe" in _by_name(r)[CHECK_AXIOMS_DESIGN].detail


@pytest.mark.parametrize("body", ["exact I. Fail Qed. Lemma d : True. Proof. exact I.", "all: Qed. Lemma d : True. Proof. exact I.",
                                  "exact I. Timeout 5 Qed. Lemma d : True. Proof. exact I.", "Local Unset Guard Checking. exact I."])
def test_wrapped_and_selected_enders_are_rejected_statically(body):
    assert any(not c.ok for c in static_checks({"t": body}))


# ------------------------------------------------------------------ text plumbing

def test_strip_proof_wrapper_tolerates_comments_around_the_wrapper():
    from pcp.rocq.body import strip_proof_wrapper

    assert strip_proof_wrapper("(* strategy *)\nProof.\n iFrame.\nQed. (* done *)") == "iFrame."
    assert strip_proof_wrapper("Proof with auto.\n iFrame.\nQed.") == "iFrame."
    assert strip_proof_wrapper("Proof (I).") == "Proof (I)."
    assert strip_proof_wrapper("exact I. Qed. Lemma d : True. Proof. exact I.") == "exact I. Qed. Lemma d : True. Proof. exact I."
    assert strip_proof_wrapper("Qed.") == "" and strip_proof_wrapper("") == ""


def test_coqproject_quoting_and_comments(tmp_path):
    from pcp.rocq.project import coq_project_flags

    (tmp_path / "_CoqProject").write_text('-Q . dev  # the library\n# -Q secret hidden\n-arg "-w -deprecated"\n-arg -w -arg -notation-overridden\nDev.v\n')
    assert coq_project_flags(tmp_path) == ["-Q", ".", "dev", "-w", "-deprecated", "-w", "-notation-overridden"]


@needs_rocq
def test_a_rocq_binary_is_invoked_as_rocq_compile(tmp_path, monkeypatch):
    import shutil

    from pcp.rocq.project import compile_text

    rocq = shutil.which("rocq")
    if rocq is None:
        pytest.skip("no rocq front end")
    monkeypatch.setenv("PCP_COQC", rocq)
    res = compile_text("Lemma t : True. Proof. exact I. Qed.\n", filename="T.v", root=tmp_path)
    assert res.ok, res.output
    assert res.argv[:2] == [rocq, "compile"]


def test_plan_preamble_refuses_scopes_and_parse_plan_refuses_definitions():
    from pcp.errors import UsageError
    from pcp.rocq.assemble import parse_plan, plan_preamble

    assert plan_preamble("From iris Require Import base.\n(* c *)\nLocal Open Scope Z_scope.\nLemma c : True.\nProof. Admitted.\n") == "From iris Require Import base.\nLocal Open Scope Z_scope."
    with pytest.raises(UsageError, match="opens a scope"):
        plan_preamble("From iris Require Import base.\nSection p.\nContext (x : nat).\nLemma c : True.\nProof. Admitted.\n")
    with pytest.raises(UsageError, match="not an obligation"):
        parse_plan("Definition helper := 0.\nLemma c : helper = 0.\nProof. Admitted.\n")
    assert [s.name for s in parse_plan("Lemma a : True.\nProof. Admitted.\nTheorem b : True.\nProof. exact I. Qed.\n")] == ["a", "b"]


def test_definition_and_proofless_anchors_assemble_verbatim_for_integration(tmp_path):
    dev = _dev(tmp_path, PU + "Definition d := 0.\nLemma a : True.\nexact I.\nQed.\n")
    text = dev.assemble("d", [], truncate=False).text
    assert "Definition d := 0.\n" in text and "Admitted." not in text and text.count("Qed.") == 1
    text = dev.assemble("a", [], anchor_body="exact I.", truncate=False).text
    assert text.count("exact I.") == 1 and text.count("Qed.") == 1
