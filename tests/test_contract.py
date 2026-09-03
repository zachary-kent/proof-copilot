"""The design contract (`pcp/orch/contract.py`).

A design task needs *some* definitions to be mutable -- you cannot invent an
invariant without writing one -- but the set must be declared by the developer, not
chosen by the thing being constrained.  An earlier version derived the protected set
from whatever the decomposer proposed, which let the decomposer grant itself
permissions; these tests pin the inversion.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from pcp.orch.contract import DesignContract

ORIGINAL = """\
Definition prog : val := #0.

Definition abstract_state (n : nat) : Prop := True.

Definition main_inv (n : nat) : Prop := True.

Lemma spec (n : nat) : main_inv n.
Proof.
Admitted.
"""


def _rewrite(src: str, name: str, body: str) -> str:
    """Replace a definition's body, keeping its binders and its terminating period.

    Dropping the `.` merges the definition into the next sentence, which the lexer
    then reads as one declaration -- and the contract correctly reports the next
    declaration as deleted.
    """
    import re

    return re.sub(
        rf"(Definition {name}[^=]*:=)[^\n]*",
        lambda m: f"{m.group(1)} {body}.",
        src,
    )


def test_a_declared_mutable_definition_may_change() -> None:
    contract = DesignContract.from_names(["main_inv", "abstract_state"])
    changed = _rewrite(ORIGINAL, "main_inv", "n = n")
    assert contract.check(ORIGINAL, changed).ok


def test_anything_not_declared_mutable_may_not() -> None:
    contract = DesignContract.from_names(["main_inv"])
    changed = _rewrite(ORIGINAL, "abstract_state", "n = n")
    check = contract.check(ORIGINAL, changed)
    assert not check.ok
    assert "abstract_state" in check.detail and "not declared mutable" in check.detail


def test_the_program_is_never_mutable_unless_declared() -> None:
    """Editing the program edits the theorem (PLAN.md 9.1)."""
    contract = DesignContract.from_names(["main_inv", "abstract_state"])
    changed = ORIGINAL.replace("Definition prog : val := #0.", "Definition prog : val := #1.")
    assert not contract.check(ORIGINAL, changed).ok


def test_lemmas_stay_frozen_when_no_result_is_named() -> None:
    """The intermediate-lemma relaxation must fail closed.

    Without a declared result there is nothing to tell a helper apart from the goal,
    so `mutable_lemmas` grants nothing -- otherwise a contract that merely forgot to
    name its results would permit the design to weaken the goal itself.
    """
    contract = DesignContract.from_names(["main_inv"])
    assert not contract.lemmas_are_mutable
    weakened = ORIGINAL.replace("Lemma spec (n : nat) :", "Lemma spec (n : nat) (H : False) :")
    assert not contract.check(ORIGINAL, weakened).ok


def test_a_named_result_is_frozen_even_though_lemmas_are_mutable() -> None:
    contract = DesignContract(mutable=frozenset({"main_inv"}), results=frozenset({"spec"}))
    assert contract.lemmas_are_mutable
    weakened = ORIGINAL.replace("Lemma spec (n : nat) :", "Lemma spec (n : nat) (H : False) :")
    check = contract.check(ORIGINAL, weakened)
    assert not check.ok
    assert "result to be proved" in check.detail
    # ... and it may not be dropped either.
    dropped = ORIGINAL.replace("Lemma spec (n : nat) : main_inv n.\nProof.\nAdmitted.\n", "")
    assert not contract.check(ORIGINAL, dropped).ok


def test_an_intermediate_lemma_may_be_restated() -> None:
    """A helper may gain a hypothesis: its callers must then supply it, and the
    compiler -- not this contract -- is what checks that they can."""
    original = ORIGINAL + "\nLemma helper (n : nat) : main_inv n.\nProof.\nAdmitted.\n"
    restated = original.replace("Lemma helper (n : nat) :", "Lemma helper (n : nat) (Hn : n = n) :")
    contract = DesignContract(mutable=frozenset({"main_inv"}), results=frozenset({"spec"}))
    assert contract.check(original, restated).ok


def test_a_specification_is_never_mutable_unless_declared() -> None:
    contract = DesignContract.from_names(["main_inv"])
    weakened = ORIGINAL.replace("Lemma spec (n : nat) :", "Lemma spec (n : nat) (H : False) :")
    assert not contract.check(ORIGINAL, weakened).ok


def test_deletion_is_never_permitted() -> None:
    contract = DesignContract.from_names(["main_inv", "prog"])
    deleted = ORIGINAL.replace("Definition prog : val := #0.\n", "")
    check = contract.check(ORIGINAL, deleted)
    assert not check.ok and "deleted" in check.detail


def test_ghost_state_may_be_added_because_it_has_to_come_from_somewhere() -> None:
    contract = DesignContract.from_names(["main_inv"])
    added = ORIGINAL + "\nDefinition registryUR := authUR (gmapUR nat unitR).\n"
    assert contract.check(ORIGINAL, added).ok


def test_additions_can_be_forbidden() -> None:
    contract = DesignContract(mutable=frozenset({"main_inv"}), allow_additions=False)
    added = ORIGINAL + "\nDefinition helper : Prop := True.\n"
    check = contract.check(ORIGINAL, added)
    assert not check.ok and "no additions" in check.detail


def test_a_new_obligation_is_not_a_design_edit() -> None:
    """New lemmas go through the statement pipeline, not through a definition patch."""
    contract = DesignContract.from_names(["main_inv"])
    added = ORIGINAL + "\nLemma smuggled : False.\nProof.\nAdmitted.\n"
    check = contract.check(ORIGINAL, added)
    assert not check.ok and "statement pipeline" in check.detail


def test_whitespace_is_not_a_change() -> None:
    contract = DesignContract.from_names([])
    reflowed = ORIGINAL.replace("Definition prog : val := #0.", "Definition prog\n  : val := #0.")
    assert contract.check(ORIGINAL, reflowed).ok


def test_the_default_contract_freezes_everything() -> None:
    """A development that declares nothing gets no design latitude at all."""
    contract = DesignContract.everything_frozen()
    assert not contract.check(ORIGINAL, _rewrite(ORIGINAL, "main_inv", "n = n")).ok
    assert contract.describe() == "nothing may change"


def test_the_contract_is_read_from_the_corpus(tmp_path: Path) -> None:
    corpus = tmp_path / "c"
    corpus.mkdir()
    (corpus / "design.json").write_text(
        json.dumps({"mutable": ["main_inv"], "allow_additions": False}), encoding="utf-8"
    )
    contract = DesignContract.from_corpus(corpus)
    assert contract.mutable == frozenset({"main_inv"})
    assert contract.allow_additions is False


def test_the_contract_falls_back_to_the_stubbed_predicates(tmp_path: Path) -> None:
    """A corpus that blanked a predicate plainly intends it to be filled in."""
    corpus = tmp_path / "c"
    corpus.mkdir()
    (corpus / "bench.json").write_text(
        json.dumps({"stubbed": [{"anonymised": "value"}, {"anonymised": "main_inv"}]}),
        encoding="utf-8",
    )
    assert DesignContract.from_corpus(corpus).mutable == frozenset({"value", "main_inv"})


def test_an_undeclared_corpus_grants_nothing(tmp_path: Path) -> None:
    assert DesignContract.from_corpus(tmp_path).mutable == frozenset()


@pytest.mark.skipif(
    not Path("eval/corpus/bench/rwcas_design/bench.json").exists(), reason="corpus not built"
)
def test_the_design_rung_declares_what_the_designer_may_touch() -> None:
    """The two blanked predicates, plus the typeclass.

    `rwcasG` is mutable because a designer that invents ghost state has to be able
    to declare it (`inG Σ …`, `ghost_varG Σ …`); with the class frozen the task
    would be impossible rather than hard.  Everything else -- the program, the
    specifications, the namespace -- stays frozen and is checked.

    The invariant is *dropped* rather than stubbed, so it is not mutable: it does not
    exist.  A stub keeps its signature, and `rwcas_inv (γᵣ : gname) (l : loc) …`
    announces a second ghost name and its role, which is a large part of the ghost
    construction the rung exists to make someone invent.
    """
    contract = DesignContract.from_corpus(Path("eval/corpus/bench/rwcas_design"))
    assert contract.mutable == frozenset({"value", "is_rwcas", "rwcasG"})
    assert "rwcas_inv" not in contract.mutable
    assert contract.allow_additions, "ghost state has to come from somewhere"

    source = Path("eval/corpus/bench/rwcas_design/Rwcas.v").read_text(encoding="utf-8")
    assert "rwcas_inv" not in source, "the invariant is dropped, not stubbed"
    for frozen in ("new_rwcas", "read", "write", "rwcasN",
                   "new_rwcas_spec", "read_spec", "write_spec"):
        assert frozen not in contract.mutable
        assert frozen in source


# --------------------------------------------------- role -> model attribution

def test_a_tier_binding_only_applies_to_its_own_provider(monkeypatch) -> None:
    """`prover = ["codex/luna"]` must not hand `--model luna` to the Claude CLI.

    Pinned against an explicit config rather than the detected defaults: a test whose
    expectations depend on which CLIs happen to be installed tells you about the
    machine, not the code.
    """
    import pcp.cli.main as cli
    from pcp.orch.providers import Config, Tiers

    cfg = Config(tiers=Tiers(decomposer=["anthropic/claude-fable-5"], prover=["codex/luna"]))
    monkeypatch.setattr("pcp.orch.providers.load", lambda *a, **k: cfg)

    assert cli._model_for("prover", "codex")[0] == "luna"
    assert cli._model_for("prover", "anthropic")[0] is None
    assert cli._model_for("decomposer", "anthropic")[0] == "claude-fable-5"
    assert cli._model_for("auditor", "anthropic") == (None, None), "an unbound role pins nothing"


def test_defaults_follow_the_detected_provider() -> None:
    """Hardcoding `codex/luna` on a machine with no codex produced a tier that
    resolved to nothing at all."""
    from pcp.orch.providers import default_tiers

    only_claude = default_tiers(["anthropic"])
    assert only_claude.prover == ["anthropic/claude-sonnet-5"]
    assert only_claude.decomposer == ["anthropic/claude-fable-5"]

    both = default_tiers(["codex", "anthropic"])
    # The flat-rate workhorse takes the prover tier; judgement roles do not.
    assert both.prover[0].startswith("codex/")
    assert both.decomposer[0].startswith("anthropic/")

    assert default_tiers([]).prover == [], "no provider, no binding"


def test_every_attempt_records_the_resolved_model(tmp_path: Path) -> None:
    """A run whose most consequential decision cannot be attributed to a model is a
    run you cannot draw a conclusion from."""
    from pcp.orch.graph import Graph, Node

    graph = Graph(tmp_path / "g.db")
    try:
        graph.add_node(Node(id="n", name="n", statement="Lemma n : True.", statement_status="frozen"))
        attempt = graph.start_attempt("n", runner="claude:default", owner="decomposer", role="decomposer")
        graph.finish_attempt(attempt, status="qed", model="claude-opus-5[1m]")
        row = graph.db.execute("SELECT role, model FROM attempts WHERE id=?", (attempt,)).fetchone()
        assert row["role"] == "decomposer"
        assert row["model"] == "claude-opus-5[1m]", "the runner label is not a model"
    finally:
        graph.close()


# ------------------------------------------------- effort, imports, compilation

def test_effort_defaults_put_the_thinking_where_the_expensive_error_is() -> None:
    """A bad decomposition is discovered only after the children's budget is spent."""
    from pcp.orch.providers import EFFORT_LEVELS, resolve_effort

    assert resolve_effort("decomposer") == "xhigh"
    assert resolve_effort("auditor") == "high"
    assert resolve_effort("prover") == "medium"
    for role in ("decomposer", "prover", "auditor"):
        assert resolve_effort(role) in EFFORT_LEVELS


def test_effort_is_overridable_and_validated(tmp_path: Path, monkeypatch) -> None:
    from pcp.orch.providers import Config, resolve_effort

    cfg = Config(effort={"prover": "max"})
    assert resolve_effort("prover", cfg) == "max"
    assert resolve_effort("decomposer", cfg) == "xhigh", "unset roles keep their default"

    bad = tmp_path / "config.toml"
    bad.write_text('[effort]\nprover = "turbo"\n', encoding="utf-8")
    from pcp.orch.providers import load

    with pytest.raises(SystemExit, match="expected one of"):
        load(bad)


def test_effort_reaches_the_runner_argv() -> None:
    from pcp.orch.runners.cli import claude_headless_runner

    argv = claude_headless_runner("claude-fable-5", effort="xhigh").argv
    assert "--effort" in argv and argv[argv.index("--effort") + 1] == "xhigh"
    assert "--effort" not in claude_headless_runner("claude-fable-5").argv


def test_a_design_may_contain_any_non_proof_vernacular() -> None:
    """The run this was written for died on `The reference ghost_varG was not found`.

    The cause was a *restriction*: a design fragment had to be a named declaration,
    so an inline `Require` was rejected outright and the design had no permitted way
    to import the ghost state it had chosen.  The fix is to stop disallowing it, not
    to add a special channel for it.
    """
    from pcp.orch.decompose import parse_proposal, validate_proposal

    def problems(defs):
        p = parse_proposal(json.dumps({"definitions": defs, "children": [
            {"name": "c", "statement": "Lemma c : True."}]}))
        return validate_proposal(p)

    assert problems([{"text": "From iris.base_logic.lib Require Import ghost_var."}]) == []
    assert problems([{"text": "Open Scope Z_scope."}]) == []
    assert problems([{"text": "Notation foo := bar."}]) == []
    assert problems([{"name": "value",
                      "text": "Definition value (g : gname) : iProp Σ := True%I."}]) == []


def test_a_design_may_still_not_contain_a_proof_or_a_new_obligation() -> None:
    from pcp.orch.decompose import ProofEngineeringAttempt, parse_proposal, validate_proposal

    with pytest.raises(ProofEngineeringAttempt):
        parse_proposal(
            '{"definitions":[{"name":"y","text":"Definition y := 0.\nProof. exact I. Qed."}]}'
        )
    smuggled = parse_proposal('{"definitions":[{"name":"x","text":"Lemma x : True."}]}')
    assert any("goes in `children`" in p for p in validate_proposal(smuggled))


def test_preamble_vernacular_is_placed_for_the_designer() -> None:
    """`Require` is illegal inside a Section, so where it goes is not the model's
    problem to get right."""
    from pcp.orch.prove import _add_imports, _is_preamble_vernacular

    assert _is_preamble_vernacular("From iris.base_logic.lib Require Import ghost_var.")
    assert _is_preamble_vernacular("Open Scope Z_scope.")
    assert not _is_preamble_vernacular("Definition v := 0.")

    src = "From A Require Import x.\n\nSection S.\nDefinition p := 0.\nEnd S.\n"
    out = _add_imports(src, ["From B Require Import y."])
    assert out.index("Require Import y") < out.index("Section S")


def test_imports_are_appended_after_the_existing_ones_without_duplicates() -> None:
    from pcp.orch.prove import _add_imports

    src = "From iris.heap_lang Require Import lang.\n\nDefinition x := 0.\n"
    out = _add_imports(src, [
        "From iris.base_logic.lib Require Import ghost_var.",
        "From iris.heap_lang Require Import lang.",
    ])
    assert out.count("Require Import lang.") == 1
    assert "ghost_var" in out
    assert out.index("ghost_var") < out.index("Definition x")


# ------------------------------------------------------- additive changes

def test_imports_may_be_added_but_never_removed() -> None:
    """Choosing ghost state means choosing the library it comes from, so a design
    task that forbids adding imports is unsatisfiable.  Removing one is different:
    it changes what the surrounding code means."""
    contract = DesignContract.from_names([])
    src = "From iris.heap_lang Require Import lang.\nDefinition prog : val := #0.\n"

    added = src.replace(
        "lang.\n", "lang.\nFrom iris.base_logic.lib Require Import ghost_var.\n"
    )
    assert contract.check(src, added).ok

    removed = "Definition prog : val := #0.\n"
    check = contract.check(src, removed)
    assert not check.ok and "import removed" in check.detail


def test_import_order_is_not_a_change() -> None:
    contract = DesignContract.from_names([])
    a = "From A Require Import x.\nFrom B Require Import y.\nDefinition p := 0.\n"
    b = "From B Require Import y.\nFrom A Require Import x.\nDefinition p := 0.\n"
    assert contract.check(a, b).ok


def test_imports_can_be_frozen_for_a_task_that_should_not_add_them() -> None:
    contract = DesignContract(mutable=frozenset(), allow_additions=True, allow_imports=False)
    src = "From A Require Import x.\nDefinition p := 0.\n"
    check = contract.check(src, src + "From B Require Import y.\n")
    assert not check.ok and "no imports" in check.detail


def test_the_design_rung_allows_imports() -> None:
    """The first orchestrated run died on `The reference ghost_varG was not found`:
    the design named ghost state it had no way to import."""
    contract = DesignContract.from_corpus(Path("eval/corpus/bench/rwcas_design"))
    assert contract.allow_imports


def test_auto_reports_only_the_runner_it_chose(monkeypatch, capsys) -> None:
    """`auto` builds every candidate to see which is installed; only one is used.

    `_model_for` used to announce from inside that probe, so a run whose prover tier
    is `codex/luna` on a machine with no codex printed "config binds codex/luna, but
    this run uses codex; falling back to the provider default" -- a fallback for a
    provider it never ran -- and then contradicted it on the next line with the
    Claude binding it actually used. A report that argues with itself is worse than
    no report: the whole point of the line is to make two runs comparable.
    """
    import pcp.cli.main as cli
    from pcp.orch.providers import Config, Tiers

    class Absent:
        name = "codex"

        def available(self) -> bool:
            return False

    cfg = Config(tiers=Tiers(prover=["anthropic/claude-sonnet-5", "codex/luna"]))
    monkeypatch.setattr("pcp.orch.providers.load", lambda *a, **k: cfg)
    # codex is first in priority order, so it is always *probed*; force it absent.
    monkeypatch.setattr("pcp.orch.runners.cli.codex_cli_runner", lambda *a, **k: Absent())

    runner = cli._pick_runner("auto", None, role="prover")
    err = capsys.readouterr().err
    assert "falling back" not in err, err
    assert err.count("prover:") == 1, err
    assert "claude-sonnet-5" in getattr(runner, "model", "") or "claude" in runner.name


def test_class_minimisation_handles_an_annotated_binder() -> None:
    """`Class seqlockG (Σ : gFunctors) := {` must reduce like `Class rwcasG Σ := {`.

    The binder pattern was `[^:=]*`, so the `:` inside `(Σ : gFunctors)` ended the
    match before the `:=` arrived and `--class-fields` silently refused. Only the one
    development spelled without an annotated binder could be made into a design rung
    -- which is exactly how the ladder ended up with a single design rung.
    """
    import sys
    from pathlib import Path

    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "eval"))
    from make_benchmark import minimize_class

    # The two spellings that actually occur across the corpus.
    for header in ("Class rwcasG Σ", "Class seqlockG (Σ : gFunctors)"):
        name = header.split()[1]
        src = header + " := {\n  a :: heapGS Σ;\n  secret :: inG Σ SomeRA;\n}.\n"
        out = minimize_class(src, name, ["keep :: heapGS Σ"])
        assert "secret" not in out, header
        assert "keep :: heapGS Σ" in out, header

    # A spelling it cannot parse must fail loudly. Silently leaving the class intact
    # would ship a design rung that still advertises its own ghost state.
    import pytest

    with pytest.raises(SystemExit):
        minimize_class("Class odd `{!heapGS Σ} := {\n  secret :: inG Σ X;\n}.\n",
                       "odd", ["keep :: heapGS Σ"])


def test_import_scrubbing_catches_dotted_module_names() -> None:
    """`--imports` promises a design benchmark does not name the ghost-state plan.

    The pattern was `[^.]*\\.`, which cannot cross the dot inside `lib.mono_nat`, so
    `From iris.algebra Require Import auth gmap list lib.mono_nat.` survived into the
    corpus -- handing over `auth`, `gmap` and `mono_nat` in a rung whose whole point
    is that the ghost state is not given. The one design rung that existed was clean
    only because its imports contain no dotted module names.
    """
    import sys
    from pathlib import Path

    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "eval"))
    from make_benchmark import set_imports

    source = (
        "From iris.program_logic Require Import atomic.\n"
        "From iris.algebra Require Import auth gmap list lib.mono_nat.\n"
        "From iris.base_logic.lib Require Import token ghost_var mono_nat invariants.\n"
        "From iris.heap_lang Require Import lang proofmode notation lib.array.\n"
        "Require Import stdpp.sorting.\n"
        "\nDefinition f := 1.\n"
    )
    out = set_imports(source, ["From iris.heap_lang Require Import lang proofmode notation."])

    for leak in ("auth", "gmap", "mono_nat", "ghost_var", "token", "stdpp.sorting"):
        assert leak not in out, f"{leak!r} survived import scrubbing"
    assert "Definition f := 1." in out, "non-import content must be preserved"
