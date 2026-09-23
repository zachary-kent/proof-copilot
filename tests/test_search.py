"""Premise search quoting, output parsing, notation resolution (pcp.state.search)."""

from __future__ import annotations

from pathlib import Path

import pytest
from conftest import needs_petanque

from pcp.errors import StateError
from pcp.state.search import (
    notation_resolve,
    parse_locate_output,
    parse_search_output,
    premise_search,
    quote_term,
    tactics_for,
)


class FakeSession:
    def __init__(self, answers: dict[str, list[str]] | None = None, fail: set[str] = frozenset()) -> None:
        self.commands: list[str] = []
        self.answers = answers or {}
        self.fail = fail
        self.file = Path("/nonexistent/Dev.v")

    def query(self, command: str, state=None) -> list[str]:
        self.commands.append(command)
        if command in self.fail:
            raise StateError(f"{command}: reference not found")
        return self.answers.get(command, [])


def test_query_terms_are_quoted_substrings_and_negations_stay_bare() -> None:
    assert quote_term("add_comm") == '"add_comm"'
    assert quote_term("-foo") == "-foo"
    assert quote_term('"already"') == '"already"'
    assert quote_term('a"b') == '"a""b"'
    s = FakeSession({'Search "add_comm" -assoc.': ["Nat.add_comm: forall n m : nat, n + m = m + n"]})
    res = premise_search(s, query="add_comm -assoc")
    assert s.commands == ['Search "add_comm" -"assoc".'] or s.commands == ['Search "add_comm" -assoc.']
    assert res.count == 1 and res.hits[0].name == "Nat.add_comm" and "Nat.add_comm" in res.answer


def test_pattern_goes_to_searchpattern_then_search_and_scope_is_validated() -> None:
    s = FakeSession({"SearchPattern (_ ↦ _) inside iris.base_logic.": ["pointsto_agree: ..."]})
    res = premise_search(s, pattern="_ ↦ _", scope="iris.base_logic")
    assert s.commands[0] == "SearchPattern (_ ↦ _) inside iris.base_logic."
    assert s.commands[1] == "Search _ ↦ _ inside iris.base_logic."
    assert res.queries == s.commands and res.count == 1
    bad = premise_search(FakeSession(), pattern="(P ∗ Q", scope="not a module!")
    assert "unbalanced" in bad.note and "not a module path" in bad.note


def test_failed_query_is_a_note_not_a_crash_and_grep_is_the_fallback() -> None:
    s = FakeSession(fail={'Search "nothing_here".'})
    res = premise_search(s, query="nothing_here", roots=[])
    assert res.count == 0 and "failed" in res.note and res.answer.startswith("no premises found")
    assert any(q.startswith("grep") for q in res.queries)


def test_search_output_parser_handles_continuations_and_unicode_names() -> None:
    hits = parse_search_output("Nat.add_comm:\n  forall n m : nat,\n  n + m = m + n\nγ_lemma: P\n")
    assert [(h.name, h.statement) for h in hits] == [("Nat.add_comm", "forall n m : nat, n + m = m + n"), ("γ_lemma", "P")]


def test_locate_output_parser_isolates_each_interpretation() -> None:
    out = (
        'Notation "x + y" := (Init.Nat.add x y)\n  (* x in scope _nat_scope *) : nat_scope\n'
        "  (default interpretation) (from Corelib.Init.Peano)\n"
        'Notation "A + { B }" := (sumor A B) : type_scope (from Corelib.Init.Specif)\n'
    )
    interps = parse_locate_output(out)
    assert interps[0].term == "(Init.Nat.add x y)" and interps[0].scope == "nat_scope"
    assert interps[0].origin == "Corelib.Init.Peano" and interps[1].notation == "A + { B }"
    assert interps[1].term == "(sumor A B)"


def test_notation_resolve_uses_locate_then_print() -> None:
    s = FakeSession({
        'Locate "={ E }=∗".': ['Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q) : bi_scope (from iris.bi.updates)'],
        "Print P.": ["P : iProp"],
    })
    text = notation_resolve(s, "={ E }=∗")
    assert s.commands[0] == 'Locate "={ E }=∗".' and not any("Locate Notation" in c for c in s.commands)
    assert "unfolds to: (P -∗ |={E}=> Q)" in text and "iMod" in text
    empty = notation_resolve(FakeSession(), "⟿")
    assert "did not recognise" in empty


def test_tactic_table_keys_on_standalone_connectives() -> None:
    assert "iSplitL" not in tactics_for("P -∗ Q") and "iApply" in tactics_for("P -∗ Q")
    assert "iSplitL" not in tactics_for("l ↦∗ vs") and "wp_load" in tactics_for("l ↦∗ vs")
    assert tactics_for("P ∗ Q")[0] == "iSplitL"
    assert "iMod" in tactics_for("={E}=∗") and "iMod" in tactics_for("|={⊤}=> P")
    assert "wp_apply" in tactics_for("WP e {{ Φ }}") and "wp_apply" not in tactics_for("wp_x")
    assert tactics_for("") == []


@needs_petanque
def test_live_search_finds_nat_add_comm(pool, scratch_dir) -> None:
    pytest.importorskip("pcp.state.session")
    from pcp.state.explain import open_session

    session = open_session(pool, scratch_dir / "Basic.v", "sep_comm")
    session.start()
    res = premise_search(session, query="add_comm")
    assert any(h.name.endswith("add_comm") for h in res.hits), res.answer
    assert res.queries == ['Search "add_comm".']
    text = notation_resolve(session, "+")
    assert "Notation" in text and "unfolds to" in text
