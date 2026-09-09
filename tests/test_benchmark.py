"""The benchmark builder and its contamination controls (docs/BENCHMARKS.md).

Every test here is a way the corpus could silently stop measuring what it claims to
measure: a holdout that leaves the proof behind, an anonymisation that leaves a name
behind, a scrub that leaves the ghost-state plan behind, or an answer key that ends up
inside the corpus.  The legacy bug list (map-eval §6: primed names never renamed,
one-line ``Require`` regex, names matched inside the keyword ``Definition``, a probe
whose failure was silent, a class body ended at the first ``}``, only the last stacked
comment dropped) is covered by tests named after each scenario.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from eval.make_benchmark import (  # noqa: E402
    Benchmark,
    add_persistence_obligation,
    anonymise,
    binder_names,
    definition_types,
    drop_declarations,
    hold_out,
    local_names,
    main,
    minimize_class,
    module_name,
    parse_about,
    pseudonym,
    rename_text,
    render_design,
    set_imports,
    spec_only_brief,
    stub_definitions,
)
from pcp.errors import UsageError  # noqa: E402
from pcp.rocq.decls import parse_blocks  # noqa: E402
from pcp.rocq.lexer import strip_comments  # noqa: E402
from tests.conftest import needs_rocq  # noqa: E402

SCRIPT = ROOT / "eval" / "make_benchmark.py"
BENCH = ROOT / "eval" / "corpus" / "bench"
REFERENCE = ROOT / ".pcp" / "reference"

SAMPLE = """\
From iris.proofmode Require Import proofmode.

(* The main invariant: it protects the cell. *)
Definition my_inv (l : loc) : iProp Σ := True.

Lemma helper_agree (x : nat) : x = x.
Proof. reflexivity. Qed.

Lemma target_spec (l : loc) : my_inv l -∗ my_inv l.
Proof.
  iIntros "H". iFrame.
Qed.

Lemma bare_spec (x : nat) : x = x.
  reflexivity.
Qed.
"""


def _survives(name: str, text: str) -> bool:
    """Whether ``name`` occurs as a whole identifier (primes are identifier characters)."""
    return re.search(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])", text) is not None


# ------------------------------------------------------------------- holdout

def test_holdout_removes_the_proof_and_keeps_the_statement() -> None:
    out, held = hold_out(SAMPLE, ["target_spec"])
    assert 'iIntros "H". iFrame.' not in out
    assert "Lemma target_spec (l : loc) : my_inv l -∗ my_inv l." in out
    assert out.count("Admitted.") == 1
    # Everything else the original had is still there -- the design is *given*.
    assert "reflexivity." in out and "Definition my_inv" in out
    assert held[0].name == "target_spec" and held[0].tactics == 2 and held[0].lines == 1
    block = next(b for b in parse_blocks(out) if b.name == "target_spec")
    assert block.admitted and block.body(out).strip() == ""


def test_holdout_of_a_lemma_without_a_proof_sentence_gets_the_canonical_shape() -> None:
    """A proof written without ``Proof.`` is still a proof; the stub gets the same
    ``Proof.\\nAdmitted.`` shape the gate's assembler produces."""
    out, held = hold_out(SAMPLE, ["bare_spec"])
    assert "Lemma bare_spec (x : nat) : x = x.\nProof.\nAdmitted." in out
    assert held[0].tactics == 1 and held[0].reference_body.strip() == "reflexivity."
    block = next(b for b in parse_blocks(out) if b.name == "bare_spec")
    assert block.admitted


def test_holdout_of_a_primed_lemma_name() -> None:
    src = "Lemma read'_spec : True.\nProof. exact I. Qed.\n"
    out, held = hold_out(src, ["read'_spec"])
    assert held[0].name == "read'_spec" and "exact I" not in out


def test_holdout_captures_the_reference_but_it_is_not_serialised_into_the_corpus() -> None:
    _out, held = hold_out(SAMPLE, ["target_spec"])
    bench = Benchmark(source="/upstream/x.v", file="f", anonymised=False, holdout=held, dropped=["registry_inv"])
    blob = json.dumps(bench.to_json())
    assert "iFrame" not in blob, "the answer key must never reach the corpus metadata"
    assert "registry_inv" not in blob and "/upstream" not in blob
    assert bench.to_json()["dropped"] == 1
    assert held[0].reference_sha256
    key = bench.reference_json()
    assert key["holdout"][0]["reference_body"] == held[0].reference_body and key["dropped"] == ["registry_inv"]
    # The corpus view round-trips, minus exactly the answer-key fields.
    back = Benchmark.from_json(bench.to_json())
    assert back.file == "f" and back.holdout[0].reference_body == "" and back.dropped == []


def test_holdout_rejects_a_name_that_is_not_there() -> None:
    with pytest.raises(UsageError, match="no proof block named"):
        hold_out(SAMPLE, ["nope"])


# ------------------------------------------------------------ stubbing the design

DESIGN_SAMPLE = """\
Section s.
  Context `{!fooG Σ}.
  Definition value γ (n : Z) := ghost_var γ (1/2) n.
  Definition registry_inv γ n (requests : list (gname * Z)) : iProp Σ := True%I.
  Definition rwcas_inv γᵣ l 'γ : iProp Σ := value γ 0.
  Definition fin (n : nat) : iProp Σ := ghost_var n 1 0.
  Definition poly `{!barG Σ} {A : Type} (x : A) γ := ghost_var γ 1 x.
End s.
"""


def test_binder_parsing_survives_nested_parens_and_pattern_binders() -> None:
    """``(requests : list (gname * Z))`` closes twice; a regex that stops at the first
    ``)`` invents a phantom binder and shifts every subsequent type by one."""
    assert binder_names("γ n (requests : list (gname * Z))") == ["γ", "n", "requests"]
    assert binder_names("(Φ : val → iProp Σ) γ (γₗ γₜ : gname)") == ["Φ", "γ", "γₗ", "γₜ"]
    # `'γ` is a pattern binder and cannot take an annotation; the name is normalised.
    assert binder_names("γᵣ l 'γ") == ["γᵣ", "l", "γ"]


def test_stubbing_a_definition_blanks_the_body_and_keeps_the_signature() -> None:
    out, stubs = stub_definitions(
        DESIGN_SAMPLE, ["value"],
        types={"value": "∀ {Σ : gFunctors}, fooG Σ → gname → Z → iProp Σ"},
    )
    assert "ghost_var γ (1/2) n" not in out
    assert "Definition value (γ : gname) (n : Z) : iProp Σ := True%I." in out
    assert stubs[0].name == "value" and stubs[0].original_sha256


def test_stubbing_keeps_implicit_and_typeclass_binders_and_types_the_bare_ones() -> None:
    out, _ = stub_definitions(
        DESIGN_SAMPLE, ["poly"],
        types={"poly": "∀ {Σ : gFunctors} {H : fooG Σ} {H0 : barG Σ} {A : Type}, A → gname → iProp Σ"},
    )
    assert "Definition poly `{!barG Σ} {A : Type} (x : A) (γ : gname) : iProp Σ := True%I." in out


def test_stubbing_a_name_that_is_a_substring_of_the_keyword_definition() -> None:
    """``fin`` occurs inside ``Definition``; the legacy split on the first substring
    match and produced binders ``ition fin n``."""
    out, stubs = stub_definitions(DESIGN_SAMPLE, ["fin"])
    assert stubs[0].stub == "Definition fin (n : nat) : iProp Σ := True%I."
    assert out.count("Definition fin") == 1 and "(ition" not in out


def test_a_stub_without_a_signature_still_annotates_its_return_type() -> None:
    """``:= True`` alone elaborates in Prop, and every use site then fails."""
    out, _ = stub_definitions(DESIGN_SAMPLE, ["value"])
    assert "Definition value γ (n : Z) : iProp Σ := True%I." in out


def test_stubbed_originals_never_reach_the_corpus_metadata() -> None:
    _out, stubs = stub_definitions(DESIGN_SAMPLE, ["rwcas_inv"])
    blob = json.dumps(Benchmark(source="s", file="f", anonymised=False, stubbed=stubs).to_json())
    assert "value γ 0" not in blob, "the original invariant leaked into the corpus"
    assert stubs[0].original_sha256 in blob


def test_stubbing_an_unknown_definition_is_an_error() -> None:
    with pytest.raises(UsageError, match="no Definition named"):
        stub_definitions(DESIGN_SAMPLE, ["nope"])


ABOUT_OUTPUT = """\
value : ∀ {Σ : gFunctors}, ghost_varG Σ Z → gname → Z → iProp Σ

value is not universe polymorphic
Arguments value {Σ ghost_varG0} γ n%_Z_scope
value is transparent
Expands to: Constant bench.P.value
is_cell :
∀ {Σ : gFunctors},
  heapGS Σ
  → loc → (val → iProp Σ) → (val → val → iProp Σ) → gname → gname → iProp Σ

is_cell is not universe polymorphic
Arguments is_cell {Σ heapGS0} l (Φ Ψ)%_function_scope γ₁ γ₂
M.inner : nat → nat

M.inner is not universe polymorphic
"""


def test_about_output_is_parsed_including_wrapped_types_and_qualified_names() -> None:
    types = parse_about(ABOUT_OUTPUT, {"value": "value", "is_cell": "is_cell", "M.inner": "inner"})
    assert types["value"] == "∀ {Σ : gFunctors}, ghost_varG Σ Z → gname → Z → iProp Σ"
    assert types["is_cell"] == "∀ {Σ : gFunctors}, heapGS Σ → loc → (val → iProp Σ) → (val → val → iProp Σ) → gname → gname → iProp Σ"
    assert types["inner"] == "nat → nat"
    assert "Arguments" not in json.dumps(types) and "polymorphic" not in json.dumps(types)


def test_a_failed_signature_probe_is_an_error_not_an_empty_answer(monkeypatch) -> None:
    """The legacy returned ``{}`` on a failed compile and the failure surfaced later as
    an unrelated type error in the final verify."""
    import eval.make_benchmark as mb
    from pcp.rocq.project import CompileResult

    monkeypatch.setattr(mb, "compile_source", lambda *a, **k: CompileResult(False, stdout="Error: The reference ghost_var was not found."))
    with pytest.raises(UsageError, match="signature probe did not compile"):
        definition_types(DESIGN_SAMPLE, ["value"])


# ----------------------------------------------------------------- scrubbing

SCRUB_SRC = """\
From iris.base_logic.lib Require Import token ghost_var invariants.
From iris.heap_lang Require Import lang proofmode notation.

(** The whole proof strategy, narrated in prose. *)

(* the registry resource algebra *)
Definition registryUR := authUR (gmapUR nat unitR).

Class fooG Σ := {
  foo_reg :: inG Σ registryUR;
  foo_tok :: tokenG Σ;
  foo_heap :: heapGS Σ;
}.

Definition prog : val := #0.
"""


def test_dropping_a_declaration_takes_its_introducing_comment_with_it() -> None:
    out, dropped = drop_declarations(SCRUB_SRC, ["registryUR"])
    assert dropped == ["registryUR"]
    assert "registryUR" not in out.replace("foo_reg :: inG Σ registryUR", "")
    assert "the registry resource algebra" not in out
    # Everything else survives -- an earlier version swallowed the whole preamble; the
    # header set off by a blank line is the file's, not the declaration's.
    assert "Definition prog : val := #0." in out
    assert "From iris.heap_lang" in out and "Class fooG" in out
    assert "proof strategy" in out, "a comment separated by code is not the declaration's"


def test_dropping_takes_the_whole_stacked_comment_block() -> None:
    """The legacy dropped only the *last* comment of a stack; the first one, which
    describes the answer as surely as the invariant does, survived."""
    src = "Definition a := 0.\n\n(* the registry RA *)\n(* it maps requests to flags *)\nDefinition registry_inv := 1.\n\nDefinition b := 2.\n"
    out, _ = drop_declarations(src, ["registry_inv"])
    assert "registry RA" not in out and "maps requests" not in out
    assert out == "Definition a := 0.\n\nDefinition b := 2.\n"


def test_dropping_several_declarations_keeps_the_rest_intact() -> None:
    out, _ = drop_declarations(SCRUB_SRC, ["registryUR", "prog"])
    assert "Class fooG" in out and "From iris.heap_lang" in out


def test_dropping_a_proved_lemma_removes_its_proof_too() -> None:
    out, _ = drop_declarations(SAMPLE, ["helper_agree"])
    assert "helper_agree" not in out and "reflexivity. Qed." not in out
    assert "Lemma target_spec" in out and "Lemma bare_spec" in out


def test_dropping_an_unknown_name_is_an_error() -> None:
    with pytest.raises(UsageError, match="nothing named"):
        drop_declarations(SCRUB_SRC, ["nope"])


def test_imports_can_be_replaced_wholesale_including_dotted_module_names() -> None:
    """``Require Import token ghost_var`` names most of the ghost-state plan, and a
    ``[^.]*\\.`` pattern could not cross the dot in ``lib.mono_nat``."""
    source = (
        "From iris.program_logic Require Import atomic.\n"
        "From iris.algebra Require Import auth gmap list lib.mono_nat.\n"
        "From iris.base_logic.lib Require Import token ghost_var mono_nat invariants.\n"
        "Require Import stdpp.sorting.\n"
        "\nDefinition f := 1.\n"
    )
    out = set_imports(source, ["From iris.heap_lang Require Import lang proofmode notation"])
    for leak in ("auth", "gmap", "mono_nat", "ghost_var", "token", "stdpp.sorting"):
        assert leak not in out, f"{leak!r} survived import scrubbing"
    assert out.startswith("From iris.heap_lang Require Import lang proofmode notation.\n")
    assert "Definition f := 1." in out


def test_a_multi_line_require_is_removed_by_set_imports() -> None:
    """``From iris.base_logic.lib Require Import\\n  ghost_var token.`` has no ``.`` on
    its first line; the legacy one-line regex left it in place."""
    source = "From iris.base_logic.lib Require Import\n  ghost_var token.\nFrom iris.heap_lang Require Import\n  lang\n  proofmode.\n\nDefinition f := 1.\n"
    out = set_imports(source, ["From iris.heap_lang Require Import lang proofmode notation."])
    assert "ghost_var" not in out and "token" not in out
    assert out == "From iris.heap_lang Require Import lang proofmode notation.\n\nDefinition f := 1.\n"


def test_set_imports_leaves_comments_alone_and_handles_a_file_without_requires() -> None:
    source = "(* From iris Require Import secret. *)\nDefinition f := 1.\n"
    out = set_imports(source, ["Require Import x."])
    assert out.startswith("Require Import x.\n\n") and "secret" in out and "Definition f" in out


def test_minimizing_a_class_removes_the_ghost_state_plan() -> None:
    out = minimize_class(SCRUB_SRC, "fooG", ["foo_heap :: heapGS Σ"])
    assert "foo_heap :: heapGS Σ;" in out
    for leaked in ("foo_reg", "foo_tok", "inG Σ registryUR", "tokenG Σ"):
        assert leaked not in out
    # The class must still close properly -- an index slip once dropped the brace.
    assert "}.\n" in out.split("Class fooG")[1][:200]


def test_class_minimisation_handles_annotated_and_generalising_binders() -> None:
    """``Class seqlockG (Σ : gFunctors) := {`` must reduce like ``Class rwcasG Σ := {``;
    the legacy binder pattern stopped at the ``:`` inside the annotation."""
    for header in ("Class rwcasG Σ", "Class seqlockG (Σ : gFunctors)", "Class odd `{!heapGS Σ}"):
        name = header.split()[1]
        src = header + " := {\n  a :: heapGS Σ;\n  secret :: inG Σ SomeRA;\n}.\n"
        out = minimize_class(src, name, ["keep :: heapGS Σ"])
        assert "secret" not in out and "keep :: heapGS Σ" in out, header


def test_class_minimisation_survives_a_brace_inside_a_field_type() -> None:
    """The legacy ended the body at the first ``}``, so a ``{[ ... ]}`` in a field's
    type left the old tail -- and the ghost state -- in place."""
    src = "Class fooG Σ := {\n  a :: inG Σ (authR (gsetUR {[ 1 ]}));\n  secret :: inG Σ X;\n}.\nDefinition p := 0.\n"
    out = minimize_class(src, "fooG", ["keep :: heapGS Σ"])
    assert "secret" not in out and "gsetUR" not in out
    assert out == "Class fooG Σ := {\n  keep :: heapGS Σ;\n}.\nDefinition p := 0.\n"


def test_minimizing_an_unknown_class_is_an_error() -> None:
    with pytest.raises(UsageError, match="no Class named"):
        minimize_class("Definition x := 0.\n", "nope", ["y"])
    with pytest.raises(UsageError, match="cannot minimise"):
        minimize_class("Class c := field : nat.\n", "c", ["y"])


def test_stripping_comments_removes_the_narrated_strategy() -> None:
    out = strip_comments(SCRUB_SRC)
    assert "proof strategy" not in out and "registry resource algebra" not in out
    assert "Definition prog : val := #0." in out


# ------------------------------------------------------- the persistence guard

@pytest.mark.parametrize(
    ("definition", "expected"),
    [
        ("  Definition is_a (γ : gname) (v : val) : iProp Σ := True%I.",
         "Lemma is_a_persistent (γ : gname) (v : val) : Persistent (is_a γ v)."),
        ("  Definition is_b (v : val) (γₕ : gname) (n : nat) : iProp Σ := True%I.",
         "Lemma is_b_persistent (v : val) (γₕ : gname) (n : nat) : Persistent (is_b v γₕ n)."),
        # implicit binders must stay implicit, or the statement will not typecheck.
        ("  Definition is_c {γ : gname} (v : val) : iProp Σ := True%I.",
         "Lemma is_c_persistent (γ : gname) (v : val) : Persistent (@is_c γ v)."),
        ("  Definition is_d : iProp Σ := True%I.",
         "Lemma is_d_persistent : Persistent (is_d)."),
        ("  Definition is_e (x y : val) : iProp Σ := True%I.",
         "Lemma is_e_persistent (x y : val) : Persistent (is_e x y)."),
        # bare and pattern binders are applied positionally.
        ("  Definition is_f γ (v : val) 'p := True%I.",
         "Lemma is_f_persistent γ (v : val) p : Persistent (is_f γ v p)."),
        # a name that is a substring of the keyword `Definition`.
        ("  Definition fin (n : nat) : iProp Σ := True%I.",
         "Lemma fin_persistent (n : nat) : Persistent (fin n)."),
    ],
)
def test_the_persistence_obligation_is_not_shaped_around_one_example(definition: str, expected: str) -> None:
    name = definition.split()[1]
    out = add_persistence_obligation(definition + "\n", name)
    assert expected in out
    assert "  Proof. apply _. Qed." in out


def test_the_persistence_obligation_lands_after_the_definition_with_its_indentation() -> None:
    src = "Section s.\n  Definition d (x : nat) : iProp Σ :=\n    True%I.\n  Definition e := 1.\nEnd s.\n"
    out = add_persistence_obligation(src, "d")
    assert "    True%I.\n\n  Lemma d_persistent (x : nat) : Persistent (d x).\n  Proof. apply _. Qed.\n  Definition e := 1." in out
    assert [b.name for b in parse_blocks(out)] == ["d", "d_persistent", "e"]


def test_the_persistence_obligation_refuses_what_it_cannot_state() -> None:
    with pytest.raises(UsageError, match="no such declaration"):
        add_persistence_obligation("Definition foo : nat := 0.\n", "nope")
    with pytest.raises(UsageError, match="not a definition"):
        add_persistence_obligation("Lemma foo : True.\nProof. done. Qed.\n", "foo")
    with pytest.raises(UsageError, match="generalising"):
        add_persistence_obligation("Definition foo `{!heapGS Σ} (l : loc) : iProp Σ := True%I.\n", "foo")


# ---------------------------------------------------------------- anonymisation

def test_anonymisation_renames_local_names_only() -> None:
    out, mapping = anonymise(SAMPLE, salt="t")
    assert set(mapping) >= {"my_inv", "helper_agree", "target_spec", "bare_spec"}
    assert "iProp" in out and "iIntros" in out and "iris.proofmode" in out
    for original in mapping:
        assert not _survives(original, out), f"{original} survived anonymisation"
        assert _survives(mapping[original], out)


def test_anonymisation_keeps_role_suffixes_so_the_task_stays_readable() -> None:
    assert pseudonym("write_spec", 3, "s").endswith("_spec")
    assert pseudonym("rwcas_inv", 4, "s").endswith("_inv")
    assert not pseudonym("rwcas_inv", 4, "s").startswith("rwcas")
    assert pseudonym("extract_result", 5, "s") == pseudonym("extract_result", 5, "s")
    assert pseudonym("x", 1, "a") != pseudonym("x", 1, "b"), "the salt must change the mapping"
    assert pseudonym("write_spec", 3, "pcp") == "fc3_spec"


def test_local_names_covers_declarations_instance_fields_and_sections_only() -> None:
    src = "Section outer.\nClass fooG Σ := {\n  foo_reg :: inG Σ X;\n  foo_heap :: heapGS Σ;\n}.\nDefinition ab := 0.\n" + SAMPLE + "End outer.\n"
    names = local_names(src)
    assert names[:2] == ["fooG", "my_inv"] and names[-3:] == ["foo_reg", "foo_heap", "outer"]
    assert "ab" not in names, "names of two characters are left alone"
    assert "iProp" not in names and "loc" not in names and "Σ" not in names


def test_primed_identifiers_are_renamed_as_whole_names() -> None:
    """``\\bread'\\b`` never matched: primed names survived every legacy build while
    their unprimed prefix was renamed *inside* them (``read'`` -> ``f6'``)."""
    src = (
        "Definition read : val := #0.\nDefinition read' : val := #1.\n"
        "Lemma wp_array_copy_to' (l : loc) : read' = read'.\nProof. rewrite /read'. reflexivity. Qed.\n"
        "Lemma read'_spec : read = read.\nProof. reflexivity. Qed.\n"
    )
    out, mapping = anonymise(src, salt="t", drop_comments=False)
    assert set(mapping) == {"read", "read'", "wp_array_copy_to'", "read'_spec"}
    for original in mapping:
        assert not _survives(original, out), f"{original} survived"
        assert _survives(mapping[original], out), f"{mapping[original]} is not in the file"
    assert mapping["read"] + "'" not in out, "the prefix was renamed inside the primed name"
    assert mapping["read'_spec"].endswith("_spec")


def test_unicode_identifiers_are_renamed_at_identifier_boundaries() -> None:
    src = "Definition γₕ_own (n : nat) : nat := n.\nLemma valueγ_agree : γₕ_own 0 = γₕ_own 0.\nProof. reflexivity. Qed.\nDefinition xγₕ_own := γₕ_own.\n"
    out, mapping = anonymise(src, salt="t", drop_comments=False)
    assert set(mapping) == {"γₕ_own", "valueγ_agree", "xγₕ_own"}
    for original in mapping:
        assert not _survives(original, out), original
    assert mapping["γₕ_own"].endswith("_own") and mapping["valueγ_agree"].endswith("_agree")
    # `xγₕ_own` is its own identifier: `γₕ_own` was not renamed inside it.
    assert mapping["xγₕ_own"] in out and "x" + mapping["γₕ_own"] not in out


def test_anonymisation_respects_word_boundaries() -> None:
    text = "Definition write : val := #().\nLemma l : True.\nProof. rewrite /write. exact I. Qed.\n"
    out, mapping = anonymise(text, salt="t", drop_comments=False)
    assert "rewrite" in out and "/write." not in out and mapping["write"] in out


def test_renaming_is_one_pass_so_a_pseudonym_is_never_renamed_again() -> None:
    assert rename_text("a b c", {"a": "b", "b": "c"}) == "b c c"
    assert rename_text("foo foo' foo'' foobar", {"foo": "x1", "foo'": "x2", "foo''": "x3"}) == "x1 x2 x3 foobar"


def test_anonymisation_leaves_no_dangling_comment_terminator() -> None:
    text = "(* a (* b *) c *)\nLemma foo : True.\nProof. exact I. Qed.\n"
    out, _ = anonymise(text, salt="t", drop_comments=True)
    assert "*)" not in out and "(*" not in out and "Lemma" in out


def test_comment_stripping_handles_nesting() -> None:
    stripped = strip_comments("A (* outer (* inner *) still *) B")
    assert stripped.split() == ["A", "B"] and "*)" not in stripped
    assert '"str (* not *)"' in strip_comments('X "str (* not *)" Y')


# ---------------------------------------------------------------------- the brief

def _sample_bench() -> tuple[Benchmark, str]:
    stubbed, held = hold_out(SAMPLE, ["target_spec"])
    stubbed, stubs = stub_definitions(stubbed, ["my_inv"])
    return Benchmark(source="s", file="F.v", anonymised=False, holdout=held, stubbed=stubs, dropped=["gone"]), stubbed


def test_render_design_levels_control_roles_and_prose() -> None:
    bench, stubbed = _sample_bench()
    roles = {"my_inv": "the main invariant", "helper_agree": "agreement on the ghost state"}
    none = render_design(SAMPLE, stubbed, bench, roles, notes="none")
    glossary = render_design(SAMPLE, stubbed, bench, roles, notes="glossary")
    full = render_design(SAMPLE, stubbed, bench, roles, notes="full")
    for brief in (none, glossary, full):
        assert brief.startswith("# Design brief: `F.v`\n")
        assert "## What you must prove" in brief and "### `target_spec`" in brief
        assert "## Given definitions" in brief and "- `my_inv` **(blank -- yours to define)**" in brief
        assert "## Given lemmas (already proved -- use them)" in brief and "- `helper_agree`" in brief
        assert "Lemma target_spec (l : loc) : my_inv l -∗ my_inv l." in brief
    assert "the main invariant" not in none and "agreement" not in none and "Design notes" not in none
    assert "-- the main invariant" in glossary and "-- agreement on the ghost state" in glossary and "Design notes" not in glossary
    assert "-- the main invariant" in full
    with pytest.raises(UsageError):
        render_design(SAMPLE, stubbed, bench, roles, notes="lots")


def test_render_design_quotes_only_long_author_comments_and_renames_doc_spans() -> None:
    long_note = "(** " + "The registry maps requests to flags [write_spec]. " * 5 + "*)\n"
    src = long_note + SAMPLE
    bench, stubbed = _sample_bench()
    bench.rename_map = {"write_spec": "fc3_spec"}
    full = render_design(src, stubbed, bench, {}, notes="full")
    assert "## Design notes from the author" in full and "> The registry maps requests to flags [fc3_spec]." in full
    assert "The main invariant: it protects the cell" not in full, "short comments are not quoted"


def test_spec_only_brief_renders_just_the_held_out_statements(bench_dir: Path) -> None:
    corpus = bench_dir / "rwcas_design"
    if not (corpus / "bench.json").exists():
        pytest.skip("rwcas_design corpus not built")
    brief = spec_only_brief(corpus)
    meta = json.loads((corpus / "bench.json").read_text(encoding="utf-8"))
    assert brief.startswith("# Design brief: `Rwcas.v`\n\n## What you must prove\n")
    for h in meta["holdout"]:
        assert f"### `{h['anonymised']}`" in brief and h["statement"].strip() in brief
    assert "Given definitions" not in brief and "Given lemmas" not in brief and "Design notes" not in brief
    assert "-- " not in brief, "no role descriptions in the spec-only brief"


# --------------------------------------------------------------------- the CLI

def _run_main(argv: list[str]) -> int:
    return main(argv)


def test_the_builder_refuses_to_put_the_key_inside_the_corpus(tmp_path: Path, capsys) -> None:
    src = tmp_path / "src.v"
    src.write_text(SAMPLE, encoding="utf-8")
    out = tmp_path / "corpus"
    rc = _run_main([str(src), "--holdout", "target_spec", "--out", str(out), "--reference", str(out / "key"), "--skip-verify"])
    assert rc != 0 and "answer key" in capsys.readouterr().err
    assert not out.exists(), "nothing may be written when the layout is refused"
    proc = subprocess.run(
        [sys.executable, str(SCRIPT), str(src), "--holdout", "target_spec", "--out", str(out), "--reference", str(out), "--skip-verify"],
        capture_output=True, text=True, cwd=str(tmp_path), check=False,
    )
    assert proc.returncode != 0 and "answer key" in proc.stderr


def test_a_built_corpus_keeps_the_answer_key_outside_itself(tmp_path: Path, capsys) -> None:
    """The one invariant the whole exercise rests on."""
    src = tmp_path / "src.v"
    src.write_text(SAMPLE, encoding="utf-8")
    out, ref = tmp_path / "corpus", tmp_path / "key"
    proc = subprocess.run(
        [sys.executable, str(SCRIPT), str(src), "--holdout", "target_spec", "--out", str(out), "--reference", str(ref), "--skip-verify"],
        capture_output=True, text=True, cwd=str(tmp_path), check=False,
    )
    assert proc.returncode == 0, proc.stderr
    assert "held out" in proc.stdout and "answer key" in proc.stdout
    corpus_text = "\n".join(p.read_text(encoding="utf-8") for p in out.rglob("*") if p.is_file())
    assert "iFrame" not in corpus_text, "the proof leaked into the corpus"
    assert "reference_body" not in corpus_text and str(src) not in corpus_text
    name = module_name(src, "pcp", True)
    assert sorted(p.name for p in out.iterdir()) == sorted(["DESIGN.md", f"{name}.v", "_CoqProject", "bench.json", "design.json"])
    assert (out / "_CoqProject").read_text(encoding="utf-8") == "-Q . bench\n"
    meta = json.loads((out / "bench.json").read_text(encoding="utf-8"))
    assert meta["file"] == f"{name}.v" and meta["anonymised"] is True and meta["dropped"] == 0
    assert meta["holdout"][0]["anonymised"] == meta["rename_map"]["target_spec"]
    assert json.loads((out / "design.json").read_text(encoding="utf-8")) == {"mutable": [], "results": [], "allow_additions": True}
    key = json.loads((ref / "reference.json").read_text(encoding="utf-8"))
    assert key["holdout"][0]["reference_body"].strip() == 'iIntros "H". iFrame.' and key["source"] == str(src)
    assert "iFrame" in (ref / f"{name}_reference.v").read_text(encoding="utf-8")
    assert not str(ref.resolve()).startswith(str(out.resolve()))


def test_design_notes_none_writes_a_spec_only_brief(tmp_path: Path) -> None:
    src = tmp_path / "src.v"
    src.write_text(SAMPLE, encoding="utf-8")
    out, ref = tmp_path / "corpus", tmp_path / "key"
    rc = _run_main([
        str(src), "--holdout", "target_spec", "--stub-definition", "my_inv", "--out", str(out), "--reference", str(ref),
        "--skip-verify", "--no-anonymise", "--design-notes", "none", "--role", "my_inv=the main invariant", "--name", "Tiny",
    ])
    assert rc == 0
    brief = (out / "DESIGN.md").read_text(encoding="utf-8")
    assert "## What you must prove" in brief and "## Given definitions" in brief
    assert "the main invariant" not in brief and "Design notes" not in brief
    meta = json.loads((out / "bench.json").read_text(encoding="utf-8"))
    assert meta["rename_map"] == {} and meta["mutable"] == ["my_inv"] and meta["stubbed"][0]["stub"].endswith(":= True%I.")
    assert "original" not in meta["stubbed"][0]


IRIS_SAMPLE = """\
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import lang proofmode notation.

(* A tiny development: one cell, one persistent handle on it.  This comment is long
   enough to be quoted as an author note by the full brief, and says nothing about
   the proofs that a reader could not take from the code itself. *)
Definition cellN : namespace := nroot .@ "cell".

Section cell.
  Context `{!heapGS Σ}.

  Definition owns (l : loc) (n : Z) : iProp Σ := l ↦ #n.
  Definition is_cell (l : loc) : iProp Σ := inv cellN (∃ n : Z, owns l n).

  Lemma owns_frame (l : loc) (n : Z) : owns l n -∗ owns l n.
  Proof. iIntros "H". iFrame. Qed.

  Lemma cell_dup (l : loc) : is_cell l -∗ is_cell l ∗ is_cell l.
  Proof.
    iIntros "#H". iSplit; iAssumption.
  Qed.

  Lemma cell_spec (l : loc) : is_cell l -∗ is_cell l.
  iIntros "$".
  Qed.
End cell.
"""


@needs_rocq
def test_end_to_end_build_compiles_and_isolates_the_answer_key(tmp_path: Path, capsys) -> None:
    from eval.make_benchmark import compile_source

    src = tmp_path / "cell.v"
    src.write_text(IRIS_SAMPLE, encoding="utf-8")
    out, ref = tmp_path / "corpus", tmp_path / "key"
    rc = _run_main([
        str(src), "--holdout", "cell_dup", "--stub-definition", "is_cell", "--persistent", "is_cell",
        "--drop", "owns_frame", "--out", str(out), "--reference", str(ref),
    ])
    captured = capsys.readouterr()
    assert rc == 0, captured.err
    assert "verified: reference proves 1 persistence obligation(s)" in captured.out
    assert "compiles with 1 proof(s) held out" in captured.out
    assert "resolved signatures: is_cell :" in captured.err

    meta = json.loads((out / "bench.json").read_text(encoding="utf-8"))
    mapping = meta["rename_map"]
    text = (out / meta["file"]).read_text(encoding="utf-8")
    assert meta["results"] == [mapping["is_cell_persistent"]] and meta["results"][0].endswith("_persistent")
    assert meta["mutable"] == [mapping["is_cell"]] and meta["dropped"] == 1 and meta["allow_additions"] is True
    assert meta["stubbed"][0]["stub"] == f"Definition {mapping['is_cell']} (l : loc) : iProp Σ := True%I."
    blocks = {b.name: b for b in parse_blocks(text)}
    assert blocks[mapping["cell_dup"]].admitted
    assert blocks[mapping["is_cell_persistent"]].ender == "Qed"
    assert blocks[mapping["cell_spec"]].ender == "Qed", "the given lemma is still proved"
    assert "owns_frame" not in text and "owns_frame" not in mapping, "dropped before anonymisation, so never named"
    for original in mapping:
        assert not _survives(original, text), f"{original} survived anonymisation"
    assert "(*" not in text and "iAssumption" not in text
    corpus_blob = "\n".join(p.read_text(encoding="utf-8") for p in out.rglob("*") if p.is_file())
    assert "iAssumption" not in corpus_blob and "reference_body" not in corpus_blob and str(src) not in corpus_blob
    assert json.loads((out / "design.json").read_text(encoding="utf-8")) == {
        "mutable": meta["mutable"], "results": meta["results"], "allow_additions": True,
    }
    brief = (out / "DESIGN.md").read_text(encoding="utf-8")
    assert "## What you must prove" in brief and f"### `{mapping['cell_dup']}`" in brief
    assert f"- `{mapping['is_cell']}` **(blank -- yours to define)**" in brief

    key = json.loads((ref / "reference.json").read_text(encoding="utf-8"))
    assert not str(ref.resolve()).startswith(str(out.resolve()))
    assert key["dropped"] == ["owns_frame"] and "iAssumption" in key["holdout"][0]["reference_body"]
    reference_text = (ref / f"{Path(meta['file']).stem}_reference.v").read_text(encoding="utf-8")
    assert "iAssumption" in reference_text and f"Lemma {mapping['is_cell_persistent']}" in reference_text
    assert compile_source(reference_text, "Reference.v").ok, "the answer key must compile in the corpus's names"


# ------------------------------------------------------------- corpus hygiene

def _rungs() -> list[str]:
    return sorted(p.name for p in BENCH.glob("*") if (p / "bench.json").exists())


@pytest.mark.skipif(not _rungs(), reason="benchmark corpora not built")
@pytest.mark.parametrize("rung", _rungs())
def test_a_checked_in_rung_is_well_formed_and_carries_no_answer(rung: str) -> None:
    corpus = BENCH / rung
    meta = json.loads((corpus / "bench.json").read_text(encoding="utf-8"))
    assert {"file", "anonymised", "holdout", "rename_map", "notes"} <= set(meta)
    assert isinstance(meta["holdout"], list) and meta["holdout"]
    assert isinstance(meta["rename_map"], dict) and isinstance(meta["anonymised"], bool)
    if "dropped" in meta:
        # A count; `cached_strong` predates the count and ships `[]`, which names nothing.
        assert isinstance(meta["dropped"], int) or meta["dropped"] == [], "dropped names must never be listed in the corpus"
    for key in ("stubbed", "mutable", "results"):
        if key in meta:
            assert isinstance(meta[key], list)
    for h in meta["holdout"]:
        assert {"name", "anonymised", "statement", "reference_sha256", "lines", "tactics"} <= set(h)
        assert "reference_body" not in h and h["reference_sha256"]
    for s in meta.get("stubbed", []):
        assert "original" not in s and s["stub"]

    source = corpus / meta["file"]
    assert source.exists()
    text = source.read_text(encoding="utf-8")
    blocks = {b.name: b for b in parse_blocks(text) if b.name}
    for h in meta["holdout"]:
        block = blocks.get(h["anonymised"])
        assert block is not None, f"{h['anonymised']} is missing from {source.name}"
        assert block.admitted, f"{h['anonymised']} still has a proof"

    blob = "\n".join(p.read_text(encoding="utf-8", errors="ignore") for p in corpus.rglob("*") if p.is_file())
    assert "reference_body" not in blob
    assert not (corpus / "reference.json").exists()

    assert (corpus / "_CoqProject").read_text(encoding="utf-8") == "-Q . bench\n"
    brief = (corpus / "DESIGN.md").read_text(encoding="utf-8")
    assert "What you must prove" in brief and "Given definitions" in brief

    design = corpus / "design.json"
    if meta.get("stubbed"):
        assert design.exists(), "a design rung must ship its contract"
    if design.exists():
        contract = json.loads(design.read_text(encoding="utf-8"))
        assert set(contract) <= {"mutable", "results", "allow_additions", "mutable_lemmas", "allow_imports"}
        assert isinstance(contract.get("mutable", []), list) and isinstance(contract.get("results", []), list)
        assert isinstance(contract.get("allow_additions", True), bool)

    key = REFERENCE / rung / "reference.json"
    assert (ROOT / "eval") not in key.resolve().parents
    if key.exists():
        data = json.loads(key.read_text(encoding="utf-8"))
        assert data["file"] == meta["file"] and all("reference_body" in h for h in data["holdout"])
