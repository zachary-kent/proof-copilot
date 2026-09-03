"""The source lexer, on which every span in the gate depends."""

from __future__ import annotations

import glob
import os
from pathlib import Path

import pytest

from pcp.core.vernac import find_block, parse_blocks, split_sentences, strip_leading_comments

IRIS = Path(os.path.expanduser("~/.opam/pcp/lib/coq/user-contrib/iris"))


def test_sentences_respect_comments_strings_and_qualids() -> None:
    src = 'Definition x := "a. b". (* a. comment *) Lemma foo.bar : True. Proof. exact I. Qed.'
    texts = [s.stripped for s in split_sentences(src)]
    assert texts[0] == 'Definition x := "a. b".'
    assert any("Lemma foo.bar : True." in t for t in texts)
    assert texts[-1] == "Qed."


def test_a_comment_before_a_lemma_does_not_hide_it() -> None:
    """A comment attaches to the sentence that follows it, and nearly every real
    Iris declaration has one.  Missing this hid 13% of the library."""
    src = "(* why this lemma exists *)\nLemma foo : True.\nProof. exact I. Qed."
    blocks = parse_blocks(src)
    assert [b.name for b in blocks] == ["foo"]
    # And the frozen statement excludes the comment.
    assert blocks[0].statement == "Lemma foo : True."
    assert src[blocks[0].statement_start : blocks[0].statement_end] == "Lemma foo : True."


def test_proof_body_span_is_exactly_the_body() -> None:
    src = "Lemma foo : True.\nProof.\n  exact I.\nQed.\n"
    block = find_block(src, "foo")
    assert block is not None
    assert block.body(src).strip() == "exact I."
    assert block.ender == "Qed"
    assert block.tactics() == ["exact I."]


def test_bullets_and_braces_are_their_own_sentences() -> None:
    block = find_block("Lemma f : True /\\ True.\nProof. split.\n- exact I.\n- exact I.\nQed.", "f")
    assert block is not None
    assert "-" in "".join(block.tactics())
    assert block.ender == "Qed"


def test_admitted_is_detected() -> None:
    block = find_block("Lemma f : True.\nProof. Admitted.", "f")
    assert block is not None and block.admitted


def test_nested_comments_and_strings_inside_comments() -> None:
    src = 'Lemma f : True.\nProof. (* outer (* inner "." *) still *) exact I. Qed.'
    block = find_block(src, "f")
    assert block is not None and block.ender == "Qed"


@pytest.mark.skipif(not IRIS.exists(), reason="Iris library not installed")
def test_survives_the_whole_iris_library() -> None:
    """A stress test on 170 real files: no exceptions, and every span is coherent."""
    files = sorted(glob.glob(str(IRIS / "**" / "*.v"), recursive=True))
    assert len(files) > 100
    total = with_proof = 0
    for path in files:
        src = Path(path).read_text(encoding="utf-8")
        blocks = parse_blocks(src)
        total += len(blocks)
        for b in blocks:
            assert b.statement_start < b.statement_end <= len(src)
            assert src[b.statement_start : b.statement_end] == b.statement
            if b.has_proof:
                with_proof += 1
                assert b.statement_end <= b.proof_start  # type: ignore[operator]
                assert b.proof_start <= b.body_start <= b.body_end  # type: ignore[operator]
    assert total > 7000, total
    assert with_proof > 5500, with_proof


def test_strip_leading_comments() -> None:
    assert strip_leading_comments("  (* a *) (* b *)  Lemma x") == "Lemma x"
    assert strip_leading_comments("Lemma x") == "Lemma x"
