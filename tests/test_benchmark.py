"""The benchmark builder and its contamination controls (docs/BENCHMARKS.md).

These tests exist because every one of them corresponds to a way the corpus could
silently stop measuring what it claims to measure: a holdout that leaves the proof
behind, an anonymisation that breaks the file, a comment stripper that corrupts it,
or an answer key that ends up inside the corpus.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from eval.make_benchmark import anonymise, hold_out, local_names, pseudonym  # noqa: E402
from pcp.core.vernac import parse_blocks, strip_comments  # noqa: E402

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
"""


def test_holdout_removes_the_proof_and_keeps_the_statement() -> None:
    out, held = hold_out(SAMPLE, ["target_spec"])
    assert 'iIntros "H". iFrame.' not in out
    assert "Lemma target_spec (l : loc) : my_inv l -∗ my_inv l." in out
    assert out.count("Admitted.") == 1
    # Everything else the original had is still there -- the design is *given*.
    assert "reflexivity." in out
    assert "Definition my_inv" in out
    assert held[0].name == "target_spec"
    assert held[0].tactics == 2


def test_holdout_captures_the_reference_but_it_is_not_serialised_into_the_corpus() -> None:
    from eval.make_benchmark import Benchmark

    _out, held = hold_out(SAMPLE, ["target_spec"])
    bench = Benchmark(source="s", file="f", anonymised=False, holdout=held)
    blob = json.dumps(bench.to_json())
    assert "iFrame" not in blob, "the answer key must never reach the corpus metadata"
    assert held[0].reference_sha256


def test_holdout_rejects_a_name_that_is_not_there() -> None:
    with pytest.raises(SystemExit, match="no proof block named"):
        hold_out(SAMPLE, ["nope"])


def test_anonymisation_renames_local_names_only() -> None:
    out, mapping = anonymise(SAMPLE, salt="t")
    assert set(mapping) >= {"my_inv", "helper_agree", "target_spec"}
    # Library names are never touched.
    assert "iProp" in out and "iIntros" in out and "iris.proofmode" in out
    for original in mapping:
        assert original not in out, f"{original} survived anonymisation"


def test_anonymisation_keeps_role_suffixes_so_the_task_stays_readable() -> None:
    assert pseudonym("write_spec", 3, "s").endswith("_spec")
    assert pseudonym("rwcas_inv", 4, "s").endswith("_inv")
    assert not pseudonym("rwcas_inv", 4, "s").startswith("rwcas")
    assert pseudonym("extract_result", 5, "s") == pseudonym("extract_result", 5, "s")
    assert pseudonym("x", 1, "a") != pseudonym("x", 1, "b"), "the salt must change the mapping"


def test_local_names_ignores_short_and_library_identifiers() -> None:
    names = local_names(SAMPLE)
    assert "my_inv" in names and "target_spec" in names
    assert "iProp" not in names and "loc" not in names


def test_comment_stripping_handles_nesting() -> None:
    """Rocq comments nest; a non-greedy regex leaves a dangling `*)` that becomes a
    syntax error a thousand lines away from its cause."""
    text = "A (* outer (* inner *) still *) B"
    assert strip_comments(text) == "A  B"
    # ... and does not touch a comment delimiter inside a string literal.
    assert '"str (* not *)"' in strip_comments('X "str (* not *)" Y')


def test_anonymisation_leaves_no_dangling_comment_terminator() -> None:
    text = "(* a (* b *) c *)\nLemma foo : True.\nProof. exact I. Qed.\n"
    out, _ = anonymise(text, salt="t", drop_comments=True)
    assert "*)" not in out and "(*" not in out
    assert "Lemma" in out


def test_a_built_corpus_keeps_the_answer_key_outside_itself(tmp_path: Path) -> None:
    """The one invariant the whole exercise rests on."""
    import subprocess

    src = tmp_path / "src.v"
    src.write_text(SAMPLE, encoding="utf-8")
    out = tmp_path / "corpus"
    ref = tmp_path / "key"
    proc = subprocess.run(
        [sys.executable, "eval/make_benchmark.py", str(src), "--holdout", "target_spec",
         "--out", str(out), "--reference", str(ref), "--skip-verify"],
        cwd=str(Path(__file__).resolve().parents[1]),
        capture_output=True, text=True,
    )
    assert proc.returncode == 0, proc.stderr
    corpus_text = "\n".join(p.read_text(encoding="utf-8") for p in out.rglob("*") if p.is_file())
    assert "iFrame" not in corpus_text, "the proof leaked into the corpus"
    assert ref.exists() and (ref / "reference.json").exists()
    assert not str(ref.resolve()).startswith(str(out.resolve()))


def test_the_builder_refuses_to_put_the_key_inside_the_corpus(tmp_path: Path) -> None:
    import subprocess

    src = tmp_path / "src.v"
    src.write_text(SAMPLE, encoding="utf-8")
    out = tmp_path / "corpus"
    proc = subprocess.run(
        [sys.executable, "eval/make_benchmark.py", str(src), "--holdout", "target_spec",
         "--out", str(out), "--reference", str(out / "key"), "--skip-verify"],
        cwd=str(Path(__file__).resolve().parents[1]),
        capture_output=True, text=True,
    )
    assert proc.returncode != 0
    assert "answer key" in proc.stderr


# ------------------------------------------------------------- the built corpora

BENCH = Path(__file__).resolve().parents[1] / "eval" / "corpus" / "bench"


def _rungs() -> list[Path]:
    return sorted(p for p in BENCH.glob("*") if (p / "bench.json").exists())


@pytest.mark.skipif(not _rungs(), reason="benchmark corpora not built")
@pytest.mark.parametrize("rung", [p.name for p in _rungs()])
def test_a_built_rung_is_well_formed_and_carries_no_answer(rung: str) -> None:
    corpus = BENCH / rung
    meta = json.loads((corpus / "bench.json").read_text(encoding="utf-8"))
    source = corpus / meta["file"]
    assert source.exists()
    text = source.read_text(encoding="utf-8")

    blocks = {b.name: b for b in parse_blocks(text)}
    for h in meta["holdout"]:
        block = blocks.get(h["anonymised"])
        assert block is not None, f"{h['anonymised']} is missing from {source.name}"
        assert block.admitted, f"{h['anonymised']} still has a proof"
        assert h["reference_sha256"], "the reference must be recorded by hash"

    # Nothing in the corpus may contain a reference body.
    blob = "\n".join(p.read_text(encoding="utf-8", errors="ignore")
                     for p in corpus.rglob("*") if p.is_file())
    assert "reference_body" not in blob

    # Anonymisation actually happened: no original name survives as a *token*.
    # Substring matching would be wrong -- `write` occurs inside `rewrite`, and the
    # anonymiser is right not to touch it.
    import re as _re

    for original in meta["rename_map"]:
        assert not _re.search(rf"\b{_re.escape(original)}\b", text), (
            f"{original} survived anonymisation in {rung}"
        )

    # On a "given design" rung the helper lemmas are still proved; on a design rung
    # they are deliberately absent, because inventing them is the task.
    proved = [b for b in parse_blocks(text) if b.has_proof and b.ender == "Qed"]
    if meta.get("stubbed"):
        # A design guard is proved on purpose -- it constrains the design rather than
        # handing over any of it, and it is exactly the compile that enforces it.
        guards = set(meta.get("results", []))
        leaked = [b.name for b in proved if b.name not in guards]
        assert not leaked, f"{rung} is a design rung but still ships proved lemmas: {leaked}"
    else:
        assert proved, f"{rung} has no given lemmas -- the design was not preserved"


@pytest.mark.skipif(not _rungs(), reason="benchmark corpora not built")
def test_every_rung_has_a_design_brief() -> None:
    for corpus in _rungs():
        design = corpus / "DESIGN.md"
        assert design.exists(), f"{corpus.name} has no DESIGN.md"
        text = design.read_text(encoding="utf-8")
        assert "What you must prove" in text and "Given definitions" in text


def test_anonymisation_respects_word_boundaries() -> None:
    """Renaming `write` must not touch `rewrite` -- and the builder's compile check
    is what catches it when a rename would break the file anyway."""
    text = "Definition write : val := #().\nLemma l : True.\nProof. rewrite /write. exact I. Qed.\n"
    out, mapping = anonymise(text, salt="t", drop_comments=False)
    assert "rewrite" in out
    assert "/write." not in out
    assert mapping["write"] in out


# ------------------------------------------------------- stubbing the design out

DESIGN_SAMPLE = """\
Section s.
  Context `{!fooG Σ}.
  Definition value γ (n : Z) := ghost_var γ (1/2) n.
  Definition registry_inv γ n (requests : list (gname * Z)) : iProp Σ := True%I.
  Definition rwcas_inv γᵣ l 'γ : iProp Σ := value γ 0.
End s.
"""


def test_binder_parsing_survives_nested_parens_and_pattern_binders() -> None:
    """`(requests : list (gname * Z))` closes twice; a regex that stops at the first
    `)` invents a phantom binder and shifts every subsequent type by one."""
    from eval.make_benchmark import _binder_names_of

    assert _binder_names_of("  Definition registry_inv γ n (requests : list (gname * Z))",
                            "registry_inv") == ["γ", "n", "requests"]
    assert _binder_names_of("  Definition write_inv (Φ : val → iProp Σ) γ (γₗ γₜ : gname)",
                            "write_inv") == ["Φ", "γ", "γₗ", "γₜ"]
    # `'γ` is a pattern binder and cannot take an annotation; the name is normalised.
    assert _binder_names_of("  Definition rwcas_inv γᵣ l 'γ", "rwcas_inv") == ["γᵣ", "l", "γ"]


def test_stubbing_a_definition_blanks_the_body_and_keeps_the_signature() -> None:
    from eval.make_benchmark import stub_definitions

    out, stubs = stub_definitions(
        DESIGN_SAMPLE, ["value"],
        types={"value": "∀ {Σ : gFunctors}, fooG Σ → gname → Z → iProp Σ"},
    )
    assert "ghost_var γ (1/2) n" not in out
    assert "Definition value (γ : gname) (n : Z) : iProp Σ := True%I." in out
    assert stubs[0].name == "value" and stubs[0].original_sha256


def test_a_stub_without_a_signature_still_annotates_its_return_type() -> None:
    """`:= True` alone elaborates in Prop, and every use site then fails."""
    from eval.make_benchmark import stub_definitions

    out, _ = stub_definitions(DESIGN_SAMPLE, ["value"])
    assert ": iProp Σ := True%I." in out


def test_stubbed_originals_never_reach_the_corpus_metadata() -> None:
    from eval.make_benchmark import Benchmark, stub_definitions

    _out, stubs = stub_definitions(DESIGN_SAMPLE, ["rwcas_inv"])
    blob = json.dumps(Benchmark(source="s", file="f", anonymised=False, stubbed=stubs).to_json())
    assert "value γ 0" not in blob, "the original invariant leaked into the corpus"
    assert stubs[0].original_sha256 in blob


def test_stubbing_an_unknown_definition_is_an_error() -> None:
    from eval.make_benchmark import stub_definitions

    with pytest.raises(SystemExit, match="no Definition named"):
        stub_definitions(DESIGN_SAMPLE, ["nope"])


def test_signature_helpers() -> None:
    from eval.make_benchmark import _split_arrows, _strip_implicit_prefix

    ty = "∀ {Σ : gFunctors}, fooG Σ → (val → iProp Σ) → gname → iProp Σ"
    inner = _strip_implicit_prefix(ty)
    # The parenthesised argument must stay one component.
    assert _split_arrows(inner) == ["fooG Σ", "(val → iProp Σ)", "gname", "iProp Σ"]


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
    """A comment explaining an invariant describes the answer as surely as the
    invariant does."""
    from eval.make_benchmark import drop_declarations

    out, dropped = drop_declarations(SCRUB_SRC, ["registryUR"])
    assert dropped == ["registryUR"]
    assert "registryUR" not in out.replace("foo_reg :: inG Σ registryUR", "")
    assert "the registry resource algebra" not in out
    # Everything else survives -- an earlier version swallowed the whole preamble.
    assert "Definition prog : val := #0." in out
    assert "From iris.heap_lang" in out
    assert "Class fooG" in out


def test_dropping_several_declarations_keeps_the_rest_intact() -> None:
    from eval.make_benchmark import drop_declarations

    out, _ = drop_declarations(SCRUB_SRC, ["registryUR", "prog"])
    assert "Class fooG" in out and "From iris.heap_lang" in out


def test_minimizing_a_class_removes_the_ghost_state_plan() -> None:
    """`inG Σ registryUR`, `tokenG Σ` and friends *are* the design."""
    from eval.make_benchmark import minimize_class

    out = minimize_class(SCRUB_SRC, "fooG", ["foo_heap :: heapGS Σ"])
    assert "foo_heap :: heapGS Σ;" in out
    for leaked in ("foo_reg", "foo_tok", "inG Σ registryUR", "tokenG Σ"):
        assert leaked not in out
    # The class must still close properly -- an index slip once dropped the brace.
    assert "}.\n" in out.split("Class fooG")[1][:200]


def test_minimizing_an_unknown_class_is_an_error() -> None:
    from eval.make_benchmark import minimize_class

    # `SCRUB_SRC` has one class; asking for another must fail loudly rather than
    # silently leaving the ghost-state plan in place.
    with pytest.raises(SystemExit, match="no Class named"):
        minimize_class("Definition x := 0.\n", "nope", ["y"])


def test_imports_can_be_replaced_wholesale() -> None:
    """`Require Import token ghost_var` names most of the ghost-state plan."""
    from eval.make_benchmark import set_imports

    out = set_imports(SCRUB_SRC, ["From iris.heap_lang Require Import lang proofmode notation"])
    assert "token" not in out.split("Definition")[0]
    assert "ghost_var" not in out
    assert out.strip().startswith("From iris.heap_lang Require Import lang proofmode notation.")
    assert "Definition prog" in out


def test_stripping_comments_removes_the_narrated_strategy() -> None:
    from pcp.core.vernac import strip_comments

    out = strip_comments(SCRUB_SRC)
    assert "proof strategy" not in out and "registry resource algebra" not in out
    assert "Definition prog : val := #0." in out


@pytest.mark.skipif(
    not (BENCH / "rwcas_design" / "bench.json").exists(), reason="design corpus not built"
)
def test_the_design_corpus_gives_only_code_and_specifications() -> None:
    """The point of the rung: the worker invents the invariant, it is not handed one."""
    corpus = BENCH / "rwcas_design"
    text = (corpus / "Rwcas.v").read_text(encoding="utf-8")

    # The two client-facing predicates are present but empty.  (A regex over the
    # binders would trip on the colon inside `(γ : gname)`; match the whole line.)
    for pred in ("value", "is_rwcas"):
        line = next((l for l in text.splitlines() if l.strip().startswith(f"Definition {pred} ")), None)
        assert line is not None, f"{pred} is missing"
        assert line.rstrip().endswith(":= True%I."), f"{pred} is not blank: {line.strip()}"

    # The invariant is dropped outright, not stubbed.  A stub keeps its signature and
    # a signature is a hint: `rwcas_inv (γᵣ : gname) (l : loc) (γ : gname)` says a
    # second ghost name is needed and what it ranges over.  Dropping is safe because
    # no frozen specification and no given lemma mentions the invariant, so the only
    # ghost name left anywhere is the client-facing one the specs themselves require
    # -- and any further ghost state must then be existential inside `is_rwcas`.
    assert "rwcas_inv" not in text, "the invariant must be dropped, not stubbed"

    # No ghost state, no helping scaffolding, no narration.
    for leaked in ("ghost_var", "token", "requestRegUR", "registry_inv", "write_inv",
                   "AU_write", "linearize_writes", "extract_result", "prophec"):
        assert leaked not in text, f"{leaked} leaked into the design corpus"
    assert "(*" not in text, "comments must be stripped: they narrate the strategy"

    # The program and the specifications are intact.
    assert "Definition write : val" in text and "NewProph" in text
    assert text.count("Admitted.") == 3
    # `is_rwcas_persistent` is the anti-cheat, and it is given *proved*, not held out.
    # Without it the rung has a degenerate solution -- define `is_rwcas` as
    # *exclusive* ownership of the cell rather than an invariant, and all three
    # specifications go through with no interference, hence no failing CmpXchg, hence
    # none of the prophecy-and-helping argument the development exists to
    # demonstrate; that design compiles and `Print Assumptions` is clean.  Holding the
    # guard out would make it inert: the stub is `True`, which is persistent, so it
    # would sit there as an `Admitted.` proving nothing.  Left proved, every compile
    # enforces it -- including the design-compile check, so a degenerate design is
    # rejected at adoption, before a worker is dispatched.
    assert "Lemma is_rwcas_persistent" in text
    assert "Proof. apply _. Qed." in text
    for spec in ("new_rwcas_spec", "read_spec", "write_spec"):
        assert f"Lemma {spec}" in text


# --- the persistence guard, on shapes unlike the one it was written for -----------

@pytest.mark.parametrize(
    "definition, expected",
    [
        # rwcas: the shape it was written against.
        ("  Definition is_a (γ : gname) (v : val) : iProp Σ := True%I.",
         "Lemma is_a_persistent (γ : gname) (v : val) : Persistent (is_a γ v)."),
        # seqlock: three binders, a different order, a unicode subscript.
        ("  Definition is_b (v : val) (γₕ : gname) (n : nat) : iProp Σ := True%I.",
         "Lemma is_b_persistent (v : val) (γₕ : gname) (n : nat) : Persistent (is_b v γₕ n)."),
        # implicit binders must stay implicit, or the statement will not typecheck.
        ("  Definition is_c {γ : gname} (v : val) : iProp Σ := True%I.",
         "Lemma is_c_persistent (γ : gname) (v : val) : Persistent (@is_c γ v)."),
        # no binders at all.
        ("  Definition is_d : iProp Σ := True%I.",
         "Lemma is_d_persistent : Persistent (is_d)."),
        # several names in one group.
        ("  Definition is_e (x y : val) : iProp Σ := True%I.",
         "Lemma is_e_persistent (x y : val) : Persistent (is_e x y)."),
    ],
)
def test_the_persistence_obligation_is_not_shaped_around_one_example(definition, expected) -> None:
    from eval.make_benchmark import add_persistence_obligation

    name = definition.split()[1]
    out = add_persistence_obligation(definition + "\n", name)
    assert expected in out
    assert "Proof. apply _. Qed." in out


def test_the_persistence_obligation_refuses_what_it_cannot_state() -> None:
    from eval.make_benchmark import add_persistence_obligation

    with pytest.raises(SystemExit):
        add_persistence_obligation("Definition foo : nat := 0.\n", "nope")
    with pytest.raises(SystemExit):
        # A lemma has no body to split on, so there is nothing to build a signature from.
        add_persistence_obligation("Lemma foo : True.\nProof. done. Qed.\n", "foo")
