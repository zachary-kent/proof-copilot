"""pcp.orch.contract: the design contract."""

from __future__ import annotations

import json

import pytest

from pcp.errors import UsageError
from pcp.orch.contract import DesignContract
from pcp.orch.gate import CHECK_CONTRACT

ORIG = (
    "From iris.algebra Require Import auth lib.mono_nat.\n"
    "Definition value := 1.\n"
    "Definition frozen_def := 2.\n"
    "Lemma helper : True. Proof. exact I. Qed.\n"
    "Lemma spec : True. Proof. exact I. Qed.\n"
)


def _kinds(contract, cand, orig=ORIG):
    return [(v.name, v.kind) for v in contract.violations(orig, cand)]


def test_from_corpus_reads_design_json_and_holdouts(bench_dir):
    c = DesignContract.from_corpus(bench_dir / "rwcas_design")
    assert c.mutable == {"is_rwcas", "rwcasG", "value"}
    assert {"is_rwcas_persistent", "new_rwcas_spec", "read_spec", "write_spec"} <= c.results
    assert c.allow_additions and c.lemmas_are_mutable
    assert "may change" in c.describe() and "frozen results" in c.describe()


def test_from_corpus_missing_dir_is_an_error(tmp_path):
    with pytest.raises(UsageError):
        DesignContract.from_corpus(tmp_path / "nope")


def test_from_corpus_fallbacks(tmp_path):
    assert DesignContract.from_corpus(tmp_path) == DesignContract.everything_frozen()
    (tmp_path / "bench.json").write_text(json.dumps({"holdout": [{"name": "r"}], "stubbed": [{"name": "s"}]}))
    c = DesignContract.from_corpus(tmp_path)
    assert c.mutable == {"s"} and c.results == {"r"}


def test_json_roundtrip():
    c = DesignContract(mutable=frozenset({"a"}), results=frozenset({"r"}), allow_imports=False)
    assert DesignContract.from_json(c.to_json()) == c


def test_mutable_definition_may_change_frozen_may_not():
    c = DesignContract(mutable=frozenset({"value"}), results=frozenset({"spec"}))
    assert _kinds(c, ORIG.replace("Definition value := 1.", "Definition value := 42.")) == []
    assert _kinds(c, ORIG.replace("frozen_def := 2", "frozen_def := 3")) == [("frozen_def", "changed")]


def test_results_are_frozen_even_when_lemmas_are_mutable():
    c = DesignContract(mutable=frozenset(), results=frozenset({"spec"}))
    assert _kinds(c, ORIG.replace("Lemma helper : True.", "Lemma helper : True /\\ True.")) == []
    assert _kinds(c, ORIG.replace("Lemma spec : True.", "Lemma spec : False -> True.")) == [("spec", "changed")]


def test_without_named_results_every_lemma_is_frozen():
    c = DesignContract(mutable=frozenset())
    assert _kinds(c, ORIG.replace("Lemma helper : True.", "Lemma helper : True /\\ True.")) == [("helper", "changed")]


def test_deletions_and_additions():
    c = DesignContract(mutable=frozenset(), results=frozenset({"spec"}))
    assert ("helper", "deleted") in _kinds(c, ORIG.replace("Lemma helper : True. Proof. exact I. Qed.\n", ""))
    assert _kinds(c, ORIG + "Definition ghost := 3.\n") == []
    assert _kinds(c, ORIG + "Lemma extra : True. Proof. exact I. Qed.\n") == [("extra", "added")]
    strict = DesignContract(mutable=frozenset(), results=frozenset({"spec"}), allow_additions=False)
    assert _kinds(strict, ORIG + "Definition ghost := 3.\n") == [("ghost", "added")]


def test_imports_are_additive_and_dotted_names_are_compared_whole():
    c = DesignContract(mutable=frozenset(), results=frozenset({"spec"}))
    swapped = ORIG.replace("lib.mono_nat", "lib.frac_auth")
    assert [k for _n, k in _kinds(c, swapped)] == ["import removed"]
    assert _kinds(c, "From iris Require Import base.\n" + ORIG) == []
    fixed = DesignContract(mutable=frozenset(), results=frozenset({"spec"}), allow_imports=False)
    assert [k for _n, k in _kinds(fixed, "From iris Require Import base.\n" + ORIG)] == ["import added"]


def test_nested_comments_and_whitespace_are_not_changes():
    c = DesignContract.everything_frozen()
    cand = ORIG.replace("Definition value := 1.", "Definition   value (* a (* nested *) b *) :=\n  1.")
    assert c.check(ORIG, cand).ok


def test_same_name_in_two_modules_are_distinct_declarations():
    orig = "Module A. Lemma x : True. Proof. exact I. Qed. End A.\nModule B. Lemma x : True. Proof. exact I. Qed. End B.\n"
    cand = orig.replace("Module B. Lemma x : True.", "Module B. Lemma x : False -> True.")
    c = DesignContract(mutable=frozenset())
    assert [(v.name, v.kind) for v in c.violations(orig, cand)] == [("x", "changed")]
    assert c.violations(orig, orig) == []


def test_check_is_a_gate_check():
    chk = DesignContract.everything_frozen().check(ORIG, ORIG + "Definition g := 1.\n")
    assert chk.name == CHECK_CONTRACT and not chk.ok and "g: added" in chk.detail
    assert DesignContract.everything_frozen().describe() == "nothing may change"


def test_a_definition_the_design_added_stays_amendable(tmp_path):
    """spec-only seqlock_wf: the approver's fix to the design's own registry definition
    was refused as 'not contract-mutable'.  Only the corpus is frozen."""
    from pcp.orch.contract import DesignContract

    (tmp_path / "bench.json").write_text('{"file": "D.v", "holdout": [{"name": "spec"}], "mutable": ["pred"]}', encoding="utf-8")
    (tmp_path / "D.v").write_text("Definition pred : Prop := True.\nLemma spec : pred.\nProof.\nAdmitted.\n", encoding="utf-8")
    c = DesignContract.from_corpus(tmp_path)
    assert c.frozen_names == {"pred", "spec"}
    assert c.may_amend("pred") and not c.may_amend("spec")
    assert c.may_amend("registry_added_by_the_design") and c.is_design_addition("registry_added_by_the_design")
    # The staged design.json (spec-only) carries the names, so the staged contract knows too.
    again = DesignContract.from_json(c.to_json())
    assert again.frozen_names == c.frozen_names and again.may_amend("registry_added_by_the_design")
    # A changed design-added definition is not a contract violation; a changed frozen one is.
    designed = "Definition pred : Prop := True.\nDefinition reg : Prop := True.\nLemma spec : pred.\nProof.\nAdmitted.\n"
    amended = designed.replace("Definition reg : Prop := True.", "Definition reg : Prop := False.")
    assert c.check(designed, amended).ok
    assert not c.check(designed, designed.replace("Lemma spec : pred.", "Lemma spec : True.")).ok
    # Unknown original (no names recorded) fails closed to the mutable list.
    bare = DesignContract.from_names(["pred"])
    assert bare.may_amend("pred") and not bare.may_amend("reg")
