"""Rocq source structure: sentences, declarations, proof spans.

Load-bearing in two places that look unrelated:

* the golden extractor replays real proof scripts through petanque, and needs the
  tactic sentences;
* the integrity gate (PLAN.md 8.7) pins statements **by construction** -- worker
  patches are constrained to proof-body spans, so the proved statement is
  byte-identical to the frozen one.  That constraint is only as good as the span
  arithmetic here.

This is a lexer, not a parser.  It knows about comments, strings and sentence
terminators, and nothing about the grammar above them -- which is exactly the amount
of understanding the two jobs need.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Iterator

#: Vernacular heads that declare something with a name we care about.
DECL_HEADS = (
    "Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark", "Property",
    "Definition", "Fixpoint", "CoFixpoint", "Inductive", "CoInductive", "Record",
    "Structure", "Class", "Instance", "Program", "Example", "Let", "Variant",
)
PROOF_ENDERS = ("Qed", "Defined", "Admitted", "Abort", "Save")

_NAME_RE = re.compile(
    r"^\s*(?:#\[[^\]]*\]\s*)?(?:Local\s+|Global\s+|Program\s+|Polymorphic\s+|Monomorphic\s+|"
    r"NonCumulative\s+|Cumulative\s+|Private\s+)*"
    r"(?P<head>[A-Z][A-Za-z]*)\s+(?P<name>[A-Za-z_][\w']*)"
)


@dataclass
class Sentence:
    """One vernacular sentence, with byte offsets into the source."""

    text: str
    start: int
    end: int  # exclusive, includes the terminating `.`

    @property
    def stripped(self) -> str:
        return self.text.strip()

    @property
    def code(self) -> str:
        """The sentence with leading comments removed.

        A comment attaches to the sentence that follows it, so nearly every real
        declaration in Iris is preceded by one inside its own sentence span.  Every
        classification below must look past that or it sees a comment and concludes
        the sentence declares nothing.
        """
        return strip_leading_comments(self.text)

    @property
    def head(self) -> str:
        m = _NAME_RE.match(self.code)
        return m.group("head") if m else ""

    @property
    def name(self) -> str | None:
        m = _NAME_RE.match(self.code)
        if m and m.group("head") in DECL_HEADS:
            return m.group("name")
        return None

    def is_proof_start(self) -> bool:
        return bool(re.match(r"^\s*Proof\b", self.code))

    def proof_ender(self) -> str | None:
        m = re.match(r"^\s*(" + "|".join(PROOF_ENDERS) + r")\s*\.", self.code)
        return m.group(1) if m else None


def iter_comments(source: str) -> Iterator[tuple[int, int, str]]:
    """Every comment, as ``(start, end, text)``, with nesting handled.

    Rocq comments nest: ``(* a (* b *) c *)`` is one comment.  A non-greedy regex
    stops at the first ``*)`` and leaves ``c *)`` behind, which turns a
    comment-stripping pass into a syntax error a thousand lines later.
    """
    i, n = 0, len(source)
    while i < n:
        if source.startswith("(*", i):
            end = _skip_comment(source, i)
            yield i, end, source[i:end]
            i = end
            continue
        if source[i] == '"':
            i = _skip_string(source, i)
            continue
        i += 1


def strip_comments(source: str) -> str:
    """Remove every comment, respecting nesting and string literals."""
    out: list[str] = []
    cursor = 0
    for start, end, _text in iter_comments(source):
        out.append(source[cursor:start])
        cursor = end
    out.append(source[cursor:])
    return "".join(out)


def strip_leading_comments(text: str) -> str:
    """Drop `(* ... *)` blocks (and whitespace) from the front of a sentence."""
    i = 0
    n = len(text)
    while i < n:
        if text[i].isspace():
            i += 1
            continue
        if text.startswith("(*", i):
            i = _skip_comment(text, i)
            continue
        break
    return text[i:]


def split_sentences(source: str) -> list[Sentence]:
    """Split Rocq source into sentences.

    A sentence ends at a ``.`` followed by whitespace or end of input -- which is
    Rocq's own rule, and is why ``Foo.bar`` and ``..`` do not terminate one.  Bullets
    and braces are emitted as their own sentences so a proof body can be re-indented
    without changing what the gate sees.
    """
    out: list[Sentence] = []
    i, n = 0, len(source)
    start = 0
    while i < n:
        ch = source[i]
        if ch == "(" and source.startswith("(*", i):
            i = _skip_comment(source, i)
            continue
        if ch == '"':
            i = _skip_string(source, i)
            continue
        if ch == ".":
            # `..` is Ltac notation, `.(` is projection, `.` inside a qualid is not
            # a terminator.
            if source.startswith("..", i):
                i += 2
                continue
            nxt = source[i + 1] if i + 1 < n else " "
            if nxt.isspace() or i + 1 == n:
                text = source[start : i + 1]
                if text.strip():
                    out.append(Sentence(text=text, start=start, end=i + 1))
                i += 1
                start = i
                continue
        if ch in "-+*{}" and _is_bullet(source, i, start):
            j = i
            while j < n and source[j] == ch:
                j += 1
            if ch in "{}":
                j = i + 1
            out.append(Sentence(text=source[start:j], start=start, end=j))
            i = start = j
            continue
        i += 1
    if source[start:].strip():
        out.append(Sentence(text=source[start:], start=start, end=n))
    return out


def _is_bullet(source: str, i: int, start: int) -> bool:
    """A bullet is a run of -/+/* (or a brace) that begins a sentence."""
    return not source[start:i].strip()


def _skip_comment(source: str, i: int) -> int:
    depth = 0
    n = len(source)
    while i < n:
        if source.startswith("(*", i):
            depth += 1
            i += 2
        elif source.startswith("*)", i):
            depth -= 1
            i += 2
            if depth == 0:
                return i
        elif source[i] == '"' and depth:
            i = _skip_string(source, i)
        else:
            i += 1
    return n


def _skip_string(source: str, i: int) -> int:
    n = len(source)
    i += 1
    while i < n:
        if source[i] == '"':
            if i + 1 < n and source[i + 1] == '"':  # Rocq escapes `"` as `""`
                i += 2
                continue
            return i + 1
        i += 1
    return n


# ------------------------------------------------------------------- declarations

@dataclass
class ProofBlock:
    """A named declaration plus, if present, its proof.

    ``body_start``/``body_end`` bound the *proof body only*: everything strictly
    between the ``Proof.`` sentence and the terminator.  That span is the only region
    a worker patch may touch.
    """

    name: str
    head: str
    statement: str
    statement_start: int
    statement_end: int
    proof_start: int | None = None
    body_start: int | None = None
    body_end: int | None = None
    ender: str | None = None
    ender_start: int | None = None
    ender_end: int | None = None
    sentences: list[Sentence] = None  # type: ignore[assignment]

    @property
    def admitted(self) -> bool:
        return self.ender == "Admitted"

    @property
    def has_proof(self) -> bool:
        return self.body_start is not None

    def body(self, source: str) -> str:
        if self.body_start is None or self.body_end is None:
            return ""
        return source[self.body_start : self.body_end]

    def tactics(self) -> list[str]:
        return [s.stripped for s in (self.sentences or []) if s.stripped]


def parse_blocks(source: str) -> list[ProofBlock]:
    """Find every named declaration and its proof span."""
    sentences = split_sentences(source)
    blocks: list[ProofBlock] = []
    i = 0
    while i < len(sentences):
        sent = sentences[i]
        name = sent.name
        if not name:
            i += 1
            continue
        # A leading comment lives inside the sentence span but is not part of the
        # statement: the frozen text, its hash, and its binders must all be about
        # the declaration itself.
        offset = len(sent.text) - len(sent.code)
        block = ProofBlock(
            name=name,
            head=sent.head,
            statement=sent.code,
            statement_start=sent.start + offset,
            statement_end=sent.end,
            sentences=[],
        )
        j = i + 1
        if j < len(sentences) and sentences[j].is_proof_start():
            block.proof_start = sentences[j].start
            block.body_start = sentences[j].end
            j += 1
            depth_guard = 0
            while j < len(sentences):
                ender = sentences[j].proof_ender()
                if ender is not None:
                    block.ender = ender
                    block.ender_start = sentences[j].start
                    block.ender_end = sentences[j].end
                    block.body_end = sentences[j].start
                    j += 1
                    break
                block.sentences.append(sentences[j])
                j += 1
                depth_guard += 1
                if depth_guard > 100_000:  # pathological input; do not spin
                    break
            if block.body_end is None:
                block.body_end = sentences[j - 1].end if j > 0 else block.body_start
        blocks.append(block)
        i = j if j > i else i + 1
    return blocks


def find_block(source: str, name: str) -> ProofBlock | None:
    for block in parse_blocks(source):
        if block.name == name:
            return block
    return None


def iter_admits(source: str) -> Iterator[Sentence]:
    """Sentences that introduce an axiom-by-another-name (gate item 5)."""
    pattern = re.compile(r"\b(admit|Admitted|Axiom|Parameter|Hypothesis|Variable|Conjecture)\b")
    for sent in split_sentences(source):
        if pattern.search(sent.text):
            yield sent
