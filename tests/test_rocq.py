"""The Rocq text foundation, as the orchestrator core relies on it."""

from __future__ import annotations

import shutil

import pytest

from pcp.errors import UsageError
from pcp.rocq.assemble import (
    PROOF_USING_DIRECTIVE,
    Development,
    NodeSpec,
    ensure_proof_using,
    has_proof_using_directive,
    insert_preamble,
    parse_plan,
    plan_preamble,
    stub_proof_bodies,
)
from pcp.rocq.assumptions import Assumption, classify_assumptions, parse_assumptions, trailer
from pcp.rocq.body import is_placeholder, strip_proof_wrapper, validate_body
from pcp.rocq.decls import find_block, parse_blocks, scopes_at
from pcp.rocq.lexer import identifiers, split_sentences, strip_comments
from pcp.rocq.project import compile_text, coq_project_flags
from pcp.rocq.statement import (
    normalize_statement,
    remove_binder,
    split_head,
    statement_binders,
    statement_hash,
)
from tests.conftest import needs_rocq


def test_bullets_after_comments_and_selector_braces_are_their_own_sentences():
    src = "Proof.\n  split.\n  (* first *)\n  - exact I.\n  - 2: { exact I. }\nQed."
    assert [s.code for s in split_sentences(src)] == ["Proof.", "split.", "-", "exact I.", "-", "2: {", "exact I.", "}", "Qed."]
    block = parse_blocks("Lemma x : True /\\ True.\n" + src)[0]
    assert block.tactics() == ["split.", "-", "exact I.", "-", "2: {", "exact I.", "}"]


def test_sentence_ends_only_at_dot_blank():
    assert [s.code for s in split_sentences("apply Foo.bar. exact x.1. rewrite H.(1).")] == ["apply Foo.bar.", "exact x.1.", "rewrite H.(1)."]


def test_lemma_without_proof_sentence_has_a_script():
    blocks = parse_blocks("Lemma x : True.\nexact I.\nQed.\nLemma y : True.\nAdmitted.")
    assert [(b.name, b.kind, b.ender) for b in blocks] == [("x", "script", "Qed"), ("y", "script", "Admitted")]
    assert blocks[1].admitted and blocks[0].body("Lemma x : True.\nexact I.\nQed.\nLemma y : True.\nAdmitted.").strip() == "exact I."


def test_term_proofs_and_abort_all_do_not_swallow_the_next_declaration():
    src = "Lemma a : True. Proof exact_term. Lemma b : True. Proof. exact I. Qed. Lemma c : True. Proof (I). Lemma d : True. Proof. Abort All. Lemma e : True. Proof. exact I. Qed."
    assert [(b.name, b.kind, b.ender) for b in parse_blocks(src)] == [
        ("a", "term", None), ("b", "script", "Qed"), ("c", "term", None), ("d", "script", "Abort"), ("e", "script", "Qed")]
    assert find_block(src, "e") is not None


def test_module_import_and_alias_scope_stack():
    src = "Module Import Foo.\nLemma f : True. Proof. exact I. Qed.\nEnd Foo.\nModule Alias := Foo.\nModule Type T. End T.\nSection s.\nModule M.\nLemma inner : True. Proof. exact I. Qed.\n"
    scopes = scopes_at(split_sentences(src), len(src))
    assert [(s.kind, s.name) for s in scopes] == [("section", "s"), ("module", "M")]
    assert [(b.qualified_name, b.modules, b.sections) for b in parse_blocks(src)] == [("Foo.f", ("Foo",), ()), ("M.inner", ("M",), ("s",))]


def test_statement_hash_ignores_nested_comments_and_respects_strings():
    assert statement_hash("Lemma a (* outer (* inner *) tail *) : True.") == statement_hash("Lemma a : True.")
    assert normalize_statement('Lemma a : "(*" = "(*".') == 'Lemma a : "(*" = "(*".'
    assert strip_comments('x (* "*)" *) y') == "x   y"


def test_plan_preamble_lands_before_a_section():
    out = insert_preamble("From iris Require Import base.\nSection p.\nContext (x : nat).\nLemma q : True.\n", "From X Require Import y.")
    assert out.index("From X Require Import y.") < out.index("Section p.")
    assert plan_preamble("(* c *)\nFrom iris.algebra Require Import auth.\nLemma a : True. Proof. Admitted.") == "From iris.algebra Require Import auth."


def test_proof_using_directive_is_detected_by_sentence_not_substring():
    assert not has_proof_using_directive('(* Set Default Proof Using "Type". *)\nLemma x : True.')
    assert has_proof_using_directive('Set   Default Proof Using "Type*".')
    assert ensure_proof_using("Lemma x : True.").startswith(PROOF_USING_DIRECTIVE)


def test_stub_proof_bodies_returns_qualified_names_and_keeps_term_proofs():
    src = "Module A. Lemma a : True. Proof. exact I. Qed. End A. Module B. Lemma a : True. Proof using Type. exact I. Qed. End B. Definition foo : nat. Proof (0). Lemma b : True. Proof. exact I. Qed."
    text, stubbed = stub_proof_bodies(src)
    assert stubbed == ["A.a", "B.a", "b"]
    assert "Proof (0)." in text and "Proof using Type.\nAdmitted." in text and "Lemma b" in text


def test_parse_plan_shapes():
    specs = parse_plan("Lemma a : True.\nProof. exact I. Abort.\nLemma b : True.\nProof. Admitted.\nLemma c : True.\nProof. exact I. Defined.\nLemma d : True.\nProof. exact I. Qed.")
    assert [(s.name, s.body, s.transparent) for s in specs] == [("a", None, False), ("b", None, False), ("c", "exact I.", True), ("d", "exact I.", False)]


def test_print_assumptions_parser_on_wrapped_types_and_guarded_entries():
    stdout = ("foo\n     : nat\nAxioms:\ncd19 :\n  forall (γ : gname)\n    (N : namespace) (Φ : val → iProp Σ),\n  True\n"
              "result is assumed to be guarded.\nClosed under the global context\n")
    report = parse_assumptions(stdout, ["foo"])
    assert report.ok and report.to_json() == {"foo": ["cd19", "result (assumed guarded)"]}
    _ok, leaning, bad = classify_assumptions(report.by_name["foo"], whitelist=set(), stubs={"M.cd19"})
    assert [a.name for a in leaning] == ["cd19"] and [a.name for a in bad] == ["result"]


def test_print_assumptions_parser_ignores_injected_junk_before_the_markers():
    stdout = ("Axioms:\nClosed under the global context\nM.target\n     : forall n : nat, n = n\nAxioms:\n"
              "M.stub : forall n : nat, n = n\nclassic : forall P : Prop, P \\/ ~ P\noutside\n     : True\nClosed under the global context\n")
    report = parse_assumptions(stdout, ["M.target", "outside"])
    assert report.to_json() == {"M.target": ["M.stub", "classic"], "outside": []}
    assert parse_assumptions("nothing here", ["x"]).failed == ["x"]
    assert trailer(["M.x"]) == "Locate M.x.\nPrint Assumptions M.x."


def test_classify_assumptions_matches_by_suffix():
    report = parse_assumptions("t\n     : True\nAxioms:\nclassic : forall P : Prop, P \\/ ~ P\nImpl.child : True\n", ["t"])
    allowed, leaning, bad = classify_assumptions(report.by_name["t"], whitelist={"Classical_Prop.classic"}, stubs={"child"})
    assert [a.name for a in allowed] == ["classic"] and [a.name for a in leaning] == ["Impl.child"] and not bad


def test_identifiers_skip_comments_and_strings():
    assert identifiers('WP (! #l) (* wp *) {{ v, ⌜v = "WP"⌝ }}') == ["WP", "l", "v", "v"]


def test_statement_binders_handle_nesting_and_stop_at_the_colon():
    assert statement_binders("Lemma f (g : (nat -> (nat -> nat))) (n m : nat) {A : Type} `{!heapGS Σ} : (forall (x : nat), g n n = x).") == ["g", "n", "m"]
    assert remove_binder("Lemma f (g : (nat -> (nat -> nat))) (n m : nat) : g n m = n.", "n") == "Lemma f (g : (nat -> (nat -> nat))) (m : nat) : g n m = n."
    assert remove_binder("Lemma f (n : nat) : n = n.", "n") == "Lemma f : n = n."
    assert remove_binder("Lemma f {n : nat} : n = n.", "n") is None
    assert split_head("Lemma foo (l : loc) : (∀ x : nat, P x) -∗ Q.")[1] == "(l : loc)"


def test_validate_body_and_wrappers():
    assert validate_body("split.\n(* c *)\n- exact I.\n- 2: { exact I. }") == []
    assert [v.reason for v in validate_body("exact I")] == ["unterminated tactic sentence (missing the final `.`)"]
    assert strip_proof_wrapper("Proof with auto.\n iFrame.\nQed.") == "iFrame."
    assert strip_proof_wrapper("Proof using Type.\n iFrame.\nDefined.") == "iFrame."
    assert is_placeholder("admit.") and is_placeholder("Admitted.") and not is_placeholder("exact I.")


def test_assembly_spans_point_at_bodies(canary_dir):
    dev = Development(canary_dir / "Canary.v")
    asm = dev.assemble("canary_main", [NodeSpec("s", "Lemma s : True.", body="exact I.")], anchor_body="exact I.", truncate=True)
    for name, (a, b) in asm.spans.items():
        block = next(x for x in parse_blocks(asm.text) if x.name == name)
        assert (block.body_start, block.body_end) == (a, b)
    assert asm.text.rstrip().endswith("End canary.") and asm.open_scopes[0].name == "canary"


def test_whitelist_matching_is_component_wise():
    wl = {"Classical_Prop.classic", "JMeq_eq"}
    ok, _, bad = classify_assumptions(
        [Assumption("classic"), Assumption("Stdlib.Logic.Classical_Prop.classic"), Assumption("Evil.classic"), Assumption("M.JMeq_eq")],
        whitelist=wl, stubs=set(),
    )
    assert [a.name for a in ok] == ["classic", "Stdlib.Logic.Classical_Prop.classic", "M.JMeq_eq"]
    assert [a.name for a in bad] == ["Evil.classic"]
    _, leaning, bad = classify_assumptions([Assumption("Outer.Inner.stub"), Assumption("Other.stub")], whitelist=set(), stubs={"Inner.stub"})
    assert [a.name for a in leaning] == ["Outer.Inner.stub"] and [a.name for a in bad] == ["Other.stub"]


def test_strip_proof_wrapper_tolerates_comments_around_the_wrapper():
    assert strip_proof_wrapper("(* strategy *)\nProof.\n iFrame.\nQed. (* done *)") == "iFrame."
    assert strip_proof_wrapper("Proof with auto.\n iFrame.\nQed.") == "iFrame."
    assert strip_proof_wrapper("Proof (I).") == "Proof (I)."
    assert strip_proof_wrapper("exact I. Qed. Lemma d : True. Proof. exact I.") == "exact I. Qed. Lemma d : True. Proof. exact I."
    assert strip_proof_wrapper("Qed.") == "" and strip_proof_wrapper("") == ""


def test_coqproject_quoting_and_comments(tmp_path):
    (tmp_path / "_CoqProject").write_text('-Q . dev  # the library\n# -Q secret hidden\n-arg "-w -deprecated"\n-arg -w -arg -notation-overridden\nDev.v\n')
    assert coq_project_flags(tmp_path) == ["-Q", ".", "dev", "-w", "-deprecated", "-w", "-notation-overridden"]


@needs_rocq
def test_a_rocq_binary_is_invoked_as_rocq_compile(tmp_path, monkeypatch):
    rocq = shutil.which("rocq")
    if rocq is None:
        pytest.skip("no rocq front end")
    monkeypatch.setenv("PCP_COQC", rocq)
    res = compile_text("Lemma t : True. Proof. exact I. Qed.\n", filename="T.v", root=tmp_path)
    assert res.ok, res.output
    assert res.argv[:2] == [rocq, "compile"]


def test_plan_preamble_refuses_scopes_and_parse_plan_refuses_definitions():
    assert plan_preamble("From iris Require Import base.\n(* c *)\nLocal Open Scope Z_scope.\nLemma c : True.\nProof. Admitted.\n") == "From iris Require Import base.\nLocal Open Scope Z_scope."
    with pytest.raises(UsageError, match="opens a scope"):
        plan_preamble("From iris Require Import base.\nSection p.\nContext (x : nat).\nLemma c : True.\nProof. Admitted.\n")
    with pytest.raises(UsageError, match="not an obligation"):
        parse_plan("Definition helper := 0.\nLemma c : helper = 0.\nProof. Admitted.\n")
    assert [s.name for s in parse_plan("Lemma a : True.\nProof. Admitted.\nTheorem b : True.\nProof. exact I. Qed.\n")] == ["a", "b"]
