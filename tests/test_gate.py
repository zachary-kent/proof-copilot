"""pcp.orch.gate: static checks, structural recheck, compile, assumptions, immutability."""

from __future__ import annotations

import dataclasses
import threading
import time
from pathlib import Path

import pytest

from pcp.errors import GateError
from pcp.orch import gate as gate_mod
from pcp.orch.contract import DesignContract
from pcp.orch.failures import GATE_COULD_NOT_RUN
from pcp.orch.gate import (
    CHECK_AMBIENT,
    CHECK_AXIOMS,
    CHECK_AXIOMS_DESIGN,
    CHECK_COMPILES,
    CHECK_CONTRACT,
    CHECK_ESCAPE,
    CHECK_NO_ADMIT,
    CHECK_PINNING,
    CHECK_PROOF_USING,
    CHECK_STRUCTURE,
    CHECK_STUBS,
    CHECK_UNUSED,
    DEFAULT_AXIOM_WHITELIST,
    Gate,
    GateResult,
    escape_hatch,
    static_checks,
)
from pcp.rocq.assemble import Development, NodeSpec
from pcp.rocq.assumptions import classify_assumptions, parse_assumptions, trailer
from pcp.rocq.body import validate_body
from pcp.rocq.decls import find_block
from pcp.rocq.project import CompileResult
from tests._orch_fixtures import write_plain
from tests.conftest import needs_rocq

PLAIN = """(* a plain development, no Iris *)
Set Default Proof Using "Type".

Lemma target (P : Prop) : P -> P.
Proof.
  intros H. exact H.
Qed.
"""

MODULE = """Set Default Proof Using "Type".
Module M.
Lemma target (n : nat) : n = n.
Proof.
  reflexivity.
Qed.
End M.
"""

CLASSIC = """From Stdlib Require Import Classical_Prop.
Set Default Proof Using "Type".

Lemma target (P : Prop) : P \\/ ~ P.
Proof.
  apply classic.
Qed.
"""

WRAPPED_STUB = (
    "Lemma stub_wrapped (A_long_type_name : Type) (B_long_type_name : A_long_type_name -> Type) "
    "(f_function_name g_function_name : forall x : A_long_type_name, B_long_type_name x) : "
    "(forall x, f_function_name x = g_function_name x) -> f_function_name = g_function_name."
)


def _dev(tmp_path: Path, source: str = PLAIN, name: str = "Dev.v") -> Development:
    (tmp_path / "_CoqProject").write_text("-Q . dev\n")
    path = tmp_path / name
    path.write_text(source)
    return Development(path)


def _by_name(result: GateResult) -> dict[str, gate_mod.Check]:
    return {c.name: c for c in result.checks}


# ------------------------------------------------------------------ static checks

def _one(bodies):
    return {c.name: c for c in static_checks(bodies)}


def test_static_check_names_and_order():
    assert [c.name for c in static_checks({"x": "exact I."})] == [CHECK_NO_ADMIT, CHECK_ESCAPE, CHECK_AMBIENT]
    assert all(c.ok for c in static_checks({"x": "exact I."}))


def test_abort_and_redefinition_fail_check_1():
    c = _one({"t": "Abort.\nDefinition target : nat := 0.\nLemma _d : True.\nProof. exact I."})
    assert not c[CHECK_NO_ADMIT].ok and "Abort" in c[CHECK_NO_ADMIT].detail and "Definition" in c[CHECK_NO_ADMIT].detail


def test_qed_then_global_notation_fails_checks_1_and_3():
    c = _one({"t": 'exact I. Qed. Notation "\'BOX\' x" := (True) (at level 10). Lemma dummy : True. Proof. exact I.'})
    assert not c[CHECK_NO_ADMIT].ok and "Qed" in c[CHECK_NO_ADMIT].detail
    assert not c[CHECK_AMBIENT].ok and "Notation" in c[CHECK_AMBIENT].detail


def test_nested_proofs_and_guard_checking_are_escape_hatches():
    c = _one({"t": "Set Nested Proofs Allowed.\nexact I."})
    assert not c[CHECK_ESCAPE].ok and "Nested Proofs" in c[CHECK_ESCAPE].detail and c[CHECK_NO_ADMIT].ok
    c = _one({"t": "Unset Guard Checking.\nexact I."})
    assert not c[CHECK_ESCAPE].ok and "Guard Checking" in c[CHECK_ESCAPE].detail
    c = _one({"t": "Obligation Tactic := idtac.\nexact I."})
    assert not c[CHECK_ESCAPE].ok
    c = _one({"t": "#[bypass_check(guard)] Fixpoint f (n : nat) : nat := f n.\nexact I."})
    assert not c[CHECK_ESCAPE].ok
    c = _one({"t": "Set Printing All. exact I."})
    assert all(x.ok for x in c.values())


def test_ambient_registrations_fail_check_3_even_when_local():
    for body in ("Local Instance foo : True := I.\nexact I.", "Global Hint Resolve x : core.\nexact I.",
                 "#[global] Instance foo : True := I.\nexact I.", "Ltac foo := idtac.\nexact I.",
                 "Canonical Structure foo.\nexact I.", "Coercion f : A >-> B.\nexact I."):
        c = _one({"t": body})
        assert not c[CHECK_AMBIENT].ok, body


def test_idtac_injection_and_honest_bodies_pass_static_checks():
    assert all(c.ok for c in static_checks({"t": 'idtac "Axioms:". idtac "Closed under the global context". exact I.'}))
    assert all(c.ok for c in static_checks({"t": 'iIntros "[HA HB]". (* note (* nested *) admit later *) iFrame.'}))


def test_unbalanced_comment_admit_and_axiom_fail_check_1():
    assert not _one({"t": "(* a (* b *) exact I."})[CHECK_NO_ADMIT].ok
    c = _one({"t": "iIntros. admit."})
    assert not c[CHECK_NO_ADMIT].ok and "admit" in c[CHECK_NO_ADMIT].detail
    assert not _one({"t": "Axiom x : False. exact x."})[CHECK_NO_ADMIT].ok
    assert not _one({"t": "Print Assumptions target. exact I."})[CHECK_NO_ADMIT].ok


# ------------------------------------------------------------------ result objects

def test_gate_is_immutable(tmp_path):
    g = Gate(_dev(tmp_path), extra_whitelist=["my_axiom"], timeout=5)
    with pytest.raises(dataclasses.FrozenInstanceError):
        g.timeout = 1  # type: ignore[misc]
    assert not hasattr(g, "last_stdout")
    assert "my_axiom" in g.whitelist and set(DEFAULT_AXIOM_WHITELIST) <= g.whitelist
    assert DEFAULT_AXIOM_WHITELIST[3] == "Classical_Prop.classic"


def test_gate_result_render_and_json_roundtrip():
    r = GateResult(ok=False, checks=[gate_mod.Check(CHECK_NO_ADMIT, True), gate_mod.Check(CHECK_COMPILES, False, "Error: x"),
                                     gate_mod.Check(CHECK_STUBS, True, "a (expected until they are discharged)", advisory=True),
                                     gate_mod.Check(CHECK_UNUSED, False, "the proof does not need: n", advisory=True)],
                   compile_output="\n".join(f"line {i}" for i in range(50)), elapsed_s=1.234)
    text = r.render()
    assert text.startswith("gate: FAIL (1.2s)\n  [ok ] no new Admitted / admit / Axiom / Parameter\n  [FAIL] compiles (coqc): Error: x\n")
    assert "  [ok ] rests on open stubs: a (expected" in text and "  [warn] unused-premise report:" in text
    assert text.endswith("line 49") and "line 9\n" not in text and "line 10\n" in text
    js = r.to_json()
    assert set(js) == {"ok", "elapsed_s", "checks", "assumptions", "unused_premises"}
    assert GateResult.from_json(js).checks == r.checks and not GateResult.from_json(js).infrastructure
    infra = GateResult(ok=False, checks=[gate_mod.Check(CHECK_COMPILES, False, f"{GATE_COULD_NOT_RUN} no coqc")])
    assert GateResult.from_json(infra.to_json()).infrastructure
    assert GateResult(ok=True, elapsed_s=9.8).render() == "gate: PASS (9.8s)"


# ------------------------------------------------------------------ run() without coqc

def _fake_compile(monkeypatch, **fields):
    calls: list[str] = []

    def fake(text, **kw):
        calls.append(text)
        return CompileResult(**{"ok": True, **fields})

    monkeypatch.setattr(gate_mod, "compile_text", fake)
    return calls


def test_static_failure_skips_the_compile(tmp_path, monkeypatch):
    calls = _fake_compile(monkeypatch)
    started = time.perf_counter()
    r = Gate(_dev(tmp_path)).run("target", [], target_body="intros H. admit.")
    assert time.perf_counter() - started < 1.0
    assert not r.ok and not calls
    names = [c.name for c in r.checks]
    assert names == [CHECK_NO_ADMIT, CHECK_ESCAPE, CHECK_AMBIENT, CHECK_PINNING, CHECK_PROOF_USING, CHECK_STRUCTURE, CHECK_COMPILES]
    assert _by_name(r)[CHECK_COMPILES].detail == "skipped: static checks failed"


def test_structural_recheck_catches_declaration_changes(tmp_path, monkeypatch):
    _fake_compile(monkeypatch)
    r = Gate(_dev(tmp_path)).run("target", [], target_body="Abort.\nLemma target : True.\nProof. exact I.")
    c = _by_name(r)[CHECK_STRUCTURE]
    assert not c.ok and "introduces target" in c.detail
    r = Gate(_dev(tmp_path)).run("target", [], target_body="")
    assert _by_name(r)[CHECK_STRUCTURE].detail == "empty proof body"


def test_missing_coqc_and_timeout_are_infrastructure(tmp_path, monkeypatch):
    _fake_compile(monkeypatch, ok=False, unavailable="no coqc on PATH -- run ./scripts/setup-toolchain.sh")
    r = Gate(_dev(tmp_path)).run("target", [], target_body="intros H. exact H.")
    assert r.infrastructure and not r.ok
    assert _by_name(r)[CHECK_COMPILES].detail.startswith(GATE_COULD_NOT_RUN)
    _fake_compile(monkeypatch, ok=False, timed_out=True, elapsed_s=600)
    r = Gate(_dev(tmp_path)).run("target", [], target_body="intros H. exact H.")
    assert r.infrastructure and "timed out" in _by_name(r)[CHECK_COMPILES].detail
    assert CHECK_AXIOMS not in _by_name(r)


def test_compile_error_is_the_workers_not_infrastructure(tmp_path, monkeypatch):
    _fake_compile(monkeypatch, ok=False, stderr='File "./Dev.v", line 5:\nError: Unable to unify "a" with "b".')
    r = Gate(_dev(tmp_path)).run("target", [], target_body="intros H. exact H.")
    assert not r.ok and not r.infrastructure and "Unable to unify" in _by_name(r)[CHECK_COMPILES].detail
    assert r.compile_output.endswith('with "b".')


def test_assumptions_parsed_from_stdout_with_qualified_marker(tmp_path, monkeypatch):
    stdout = 'Axioms:\ntarget\n     : forall P : Prop, P -> P\nAxioms:\nclassic : forall P : Prop, P \\/ ~ P\nevil : False\n'
    _fake_compile(monkeypatch, stdout=stdout)
    r = Gate(_dev(tmp_path)).run("target", [], target_body="intros H. exact H.")
    c = _by_name(r)[CHECK_AXIOMS]
    assert not c.ok and c.detail == "target: evil" and r.assumptions == {"target": ["classic", "evil"]}
    _fake_compile(monkeypatch, stdout="garbage only")
    r = Gate(_dev(tmp_path)).run("target", [], target_body="intros H. exact H.")
    assert "treat as unverified" in _by_name(r)[CHECK_AXIOMS].detail and not r.ok


def test_run_refuses_impossible_inputs(tmp_path, monkeypatch):
    _fake_compile(monkeypatch)
    g = Gate(_dev(tmp_path))
    with pytest.raises(GateError):
        g.run("missing", [], target_body="exact I.")
    with pytest.raises(GateError):
        g.run("target", [NodeSpec("target", "Lemma target : True.")], target_body="exact I.")
    with pytest.raises(GateError):
        g.run("target", [NodeSpec("child", "Lemma child : True.")], target="child")
    with pytest.raises(GateError):
        g.run("target", [NodeSpec("child", "Lemma child : True.", mockable=False)], target_body="exact I.")


def test_run_design_scans_fragments_and_results(tmp_path, monkeypatch):
    _fake_compile(monkeypatch, stdout="spec\n     : True\nClosed under the global context\n")
    dev = _dev(tmp_path, "Set Default Proof Using \"Type\".\nDefinition value := 1.\nLemma spec : True.\nProof. exact I. Qed.\n")
    contract = DesignContract(mutable=frozenset({"value"}), results=frozenset({"spec"}))
    good = dev.source.replace("value := 1", "value := 2") + "Lemma helper : True.\nProof. Admitted.\n"
    r = Gate(dev).run_design(good, contract)
    assert not r.ok and "helper: added" in _by_name(r)[CHECK_CONTRACT].detail
    ok = dev.source.replace("value := 1", "value := 2")
    r = Gate(dev).run_design(ok, contract)
    assert r.ok and [c.name for c in r.checks][-2:] == [CHECK_COMPILES, CHECK_AXIOMS_DESIGN]
    hatch = "Set Nested Proofs Allowed.\n" + ok
    r = Gate(dev).run_design(hatch, contract)
    assert not _by_name(r)[CHECK_ESCAPE].ok and "Nested Proofs" in _by_name(r)[CHECK_ESCAPE].detail
    guard = ok + "Unset Guard Checking.\n"
    assert not _by_name(Gate(dev).run_design(guard, contract))[CHECK_ESCAPE].ok
    admitted = ok.replace("Proof. exact I. Qed.", "Proof. Admitted.")
    r = Gate(dev).run_design(admitted, contract)
    assert not _by_name(r)[CHECK_NO_ADMIT].ok and "spec: Admitted (a result must be proved)" in _by_name(r)[CHECK_NO_ADMIT].detail
    axiom = ok + "Axiom cheat : False.\n"
    assert "new Axiom" in _by_name(Gate(dev).run_design(axiom, contract))[CHECK_NO_ADMIT].detail


def test_run_design_allows_admitted_non_result_stubs(tmp_path, monkeypatch):
    dev = _dev(tmp_path, "Set Default Proof Using \"Type\".\nDefinition value := 1.\nLemma spec : True.\nProof. exact I. Qed.\n")
    contract = DesignContract(mutable=frozenset({"value"}), results=frozenset({"spec"}))
    cand = dev.source + "Lemma helper : True.\nProof. Admitted.\nLemma spec2 : True.\nProof. exact helper. Qed.\n"
    contract = DesignContract(mutable=frozenset({"value"}), results=frozenset({"spec"}), addable_heads=(*contract.addable_heads, "Lemma"))
    _fake_compile(monkeypatch, stdout="spec\n     : True\nClosed under the global context\nspec2\n     : True\nAxioms:\nhelper : True\n")
    r = Gate(dev).run_design(cand, contract)
    assert r.ok and _by_name(r)[CHECK_STUBS].detail.startswith("helper")
    _fake_compile(monkeypatch, stdout="spec\n     : True\nClosed under the global context\nspec2\n     : True\nAxioms:\nspec : True\n")
    r = Gate(dev).run_design(cand, contract)
    assert not r.ok and "spec2: spec" in _by_name(r)[CHECK_AXIOMS_DESIGN].detail


# ------------------------------------------------------------------ with coqc

@needs_rocq
def test_honest_proof_passes_on_the_canary(canary_dir):
    dev = Development(canary_dir / "Canary.v")
    sibs = [NodeSpec("canary_swap", "Lemma canary_swap (A B : PROP) : A ∗ B -∗ B ∗ A."),
            NodeSpec("canary_assoc", "Lemma canary_assoc (A B C : PROP) : A ∗ (B ∗ C) -∗ (A ∗ B) ∗ C.")]
    body = 'iIntros "H". iDestruct (canary_swap with "H") as "[HQR HP]". iDestruct "HQR" as "[HQ HR]". iFrame.'
    r = Gate(dev).run("canary_main", sibs, target_body=body, stub_prefix=True)
    assert r.ok, r.render()
    assert r.assumptions == {"canary_main": ["canary_swap"]}
    assert _by_name(r)[CHECK_STUBS].detail == "canary_swap (expected until they are discharged)"
    assert [c.name for c in r.checks] == [CHECK_NO_ADMIT, CHECK_ESCAPE, CHECK_AMBIENT, CHECK_PINNING, CHECK_PROOF_USING,
                                          CHECK_STRUCTURE, CHECK_COMPILES, CHECK_AXIOMS, CHECK_STUBS]
    child = [NodeSpec("canary_swap", sibs[0].statement, body='iIntros "[HA HB]". iFrame.'), sibs[1]]
    r2 = Gate(dev).run("canary_main", child, target="canary_swap", stub_prefix=True)
    assert r2.ok and r2.assumptions == {"canary_swap": []}


@needs_rocq
def test_module_qualified_target_and_stub(tmp_path):
    dev = _dev(tmp_path, MODULE)
    stub = NodeSpec("stub_in_module", "Lemma stub_in_module (n m : nat) : n = n.")
    r = Gate(dev).run("target", [stub], target_body="apply (stub_in_module n n).")
    assert r.ok, r.render()
    assert r.assumptions == {"target": ["M.stub_in_module"]}
    assert _by_name(r)[CHECK_STUBS].detail.startswith("M.stub_in_module")


@needs_rocq
def test_wrapped_binder_stub_names_are_read_correctly(tmp_path):
    dev = _dev(tmp_path)
    r = Gate(dev).run("target", [NodeSpec("stub_wrapped", WRAPPED_STUB)], target_body="intros H. pose proof stub_wrapped. exact H.")
    assert r.ok, r.render()
    assert r.assumptions == {"target": ["stub_wrapped"]}


@needs_rocq
def test_classic_is_whitelisted_by_suffix(tmp_path):
    dev = _dev(tmp_path, CLASSIC)
    r = Gate(dev).run("target", [], target_body="apply classic.")
    assert r.ok, r.render()
    assert r.assumptions == {"target": ["classic"]} and CHECK_STUBS not in _by_name(r)
    strict = Gate(dev, axiom_whitelist=())
    r = strict.run("target", [], target_body="apply classic.")
    assert not r.ok and _by_name(r)[CHECK_AXIOMS].detail == "target: classic"


@needs_rocq
def test_concurrent_gates_do_not_cross_contaminate(tmp_path):
    dev = _dev(tmp_path)
    gate = Gate(dev)
    results: dict[str, GateResult] = {}

    def run(name: str) -> None:
        stub = NodeSpec(name, f"Lemma {name} : True.")
        results[name] = gate.run("target", [stub], target_body=f"intros H. pose proof {name}. exact H.")

    threads = [threading.Thread(target=run, args=(n,)) for n in ("stub_a", "stub_b", "stub_c", "stub_d")]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    for name, r in results.items():
        assert r.ok, r.render()
        assert r.assumptions == {"target": [name]}


@needs_rocq
def test_compile_timeout_marks_infrastructure(tmp_path):
    r = Gate(_dev(tmp_path), timeout=0.001).run("target", [], target_body="intros H. exact H.")
    assert r.infrastructure and not r.ok and "timed out" in _by_name(r)[CHECK_COMPILES].detail


@needs_rocq
def test_unused_premise_report_by_removal(tmp_path):
    src = 'Set Default Proof Using "Type".\nLemma over (n : nat) (Hn : n > 0) (m : nat) : m = m.\nProof. reflexivity. Qed.\n'
    dev = _dev(tmp_path, src)
    r = Gate(dev).run("over", [], target_body="reflexivity.", unused_premise_report=True)
    assert r.ok and r.unused_premises == ["Hn"]
    assert _by_name(r)[CHECK_UNUSED].detail == "the proof does not need: Hn" and _by_name(r)[CHECK_UNUSED].advisory


@needs_rocq
def test_fast_and_full_paths_agree(tmp_path):
    src = PLAIN + "\nLemma later (Q : Prop) : Q -> Q.\nProof. intros q. exact q. Qed.\n"
    dev = _dev(tmp_path, src)
    for body, expected in (("intros H. exact H.", True), ("intros H. exact (H : False).", False)):
        fast = Gate(dev).run("target", [], target_body=body, stub_prefix=True)
        full = Gate(dev).run("target", [], target_body=body, truncate=False)
        assert fast.ok is expected and full.ok is expected


@needs_rocq
def test_the_real_gate_rejects_a_body_that_aborts_and_declares(tmp_path):
    dev_path, _ = write_plain(tmp_path, plan=None)
    dev = Development(dev_path)
    spec = NodeSpec("c1", "Lemma c1 (P : Prop) : P -> P.", "intros H. Abort. Lemma evil : False. admit. Qed.")
    result = Gate(dev).run("root", [spec], target="c1", truncate=True, stub_prefix=True)
    assert not result.ok and any(not c.ok and not c.advisory for c in result.checks)
    assert all(c.name != "compiles (coqc)" or c.detail.startswith("skipped") for c in result.checks), "refused before any compile"


# ------------------------------------------------------------------ Proof using, assumptions and escape hatches


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


UNSAFE_HIERARCHY = "Constant dev.Dev.spec\nAxioms:\nu relies on an unsafe hierarchy.\n"


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


def test_definition_and_proofless_anchors_assemble_verbatim_for_integration(tmp_path):
    dev = _dev(tmp_path, PU + "Definition d := 0.\nLemma a : True.\nexact I.\nQed.\n")
    text = dev.assemble("d", [], truncate=False).text
    assert "Definition d := 0.\n" in text and "Admitted." not in text and text.count("Qed.") == 1
    text = dev.assemble("a", [], anchor_body="exact I.", truncate=False).text
    assert text.count("exact I.") == 1 and text.count("Qed.") == 1


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
