"""Declarations, proof spans, and the section/module stack.

Built on :mod:`pcp.rocq.lexer`.  This is the only place that knows which vernacular
heads declare a named thing, which of those can carry a proof script, and how a proof
script begins and ends.  The freeze (PLAN.md 8.3) is enforced by the byte spans here:
a worker patch may reach exactly one ``[body_start, body_end)`` and nothing else.

Rocq accepts several shapes a naive scanner misses, and each is handled:

* ``Lemma x : T.`` + tactics + ``Qed.`` with **no** ``Proof.`` sentence;
* ``Proof term.`` / ``Proof (term).`` -- a complete proof with no ender;
* ``Definition d : T.`` + ``Proof. ... Defined.`` -- a definition built by tactics;
* anonymous ``Instance : C.`` and ``Next Obligation.`` blocks (``name`` is ``None``);
* ``Module Import M.``, ``Module M := N.`` (no ``End``), ``Module Type``, ``Module M <: T.``,
  and mismatched ``End`` lines, for the scope stack that qualifies names.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from pcp.rocq.lexer import Sentence, first_word, has_top_level_token, split_sentences

#: Heads that declare a *named* thing (the name is the next token).
DECL_HEADS: frozenset[str] = frozenset({
    "Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark", "Property", "Example",
    "Definition", "Fixpoint", "CoFixpoint", "Let", "Instance", "Inductive", "CoInductive",
    "Record", "Structure", "Class", "Variant", "Axiom", "Axioms", "Parameter", "Parameters",
    "Hypothesis", "Hypotheses", "Variable", "Variables", "Conjecture", "Ltac", "Ltac2",
    "Notation", "Canonical", "Coercion", "Equations",
})

#: Heads whose declaration may be followed by a proof script.
PROOF_HEADS: frozenset[str] = frozenset({
    "Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark", "Property", "Example",
    "Definition", "Fixpoint", "CoFixpoint", "Let", "Instance", "Goal", "Obligation",
})

#: Heads that are theorem-like: always a proof, never a term.
THEOREM_HEADS: frozenset[str] = frozenset({
    "Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark", "Property", "Example",
})

PROOF_ENDERS: tuple[str, ...] = ("Qed", "Defined", "Admitted", "Abort", "Save")

_MODIFIERS = (
    "Local", "Global", "Program", "Polymorphic", "Monomorphic", "NonCumulative", "Cumulative",
    "Private", "Canonical", "Export",
)
_IDENT = r"[^\W\d][\w']*"
_ATTRS = r"(?:#\[[^\]]*\]\s*)*"
_MODS = r"(?:(?:" + "|".join(_MODIFIERS) + r")\s+)*"
_NAMED = re.compile(_ATTRS + _MODS + r"(?P<head>[A-Z][A-Za-z0-9]*)\s+(?P<name>" + _IDENT + r")")
_ANON_INSTANCE = re.compile(_ATTRS + _MODS + r"Instance\s*:")
_GOAL = re.compile(r"Goal\b")
_OBLIGATION = re.compile(r"(?:Next\s+Obligation|Obligation\s+\d+)\b")
_ENDER = re.compile(r"(" + "|".join(PROOF_ENDERS) + r")\b")
_PROOF = re.compile(r"Proof\b")
_PROOF_OPENER = re.compile(r"Proof\s*(?:\.|using\b|with\b)")
_PROOF_USING = re.compile(r"Proof\s+using\s+(?P<what>[^.]*)\.")
_SECTION = re.compile(r"Section\s+(?P<name>" + _IDENT + r")")
_MODULE = re.compile(
    r"Module\s+(?P<type>Type\s+)?(?:(?:Import|Export)\s+)?(?P<name>" + _IDENT + r")"
)
_END = re.compile(r"End\s+(?P<name>" + _IDENT + r")")
_SCOPE_WORDS = ("Section", "Module", "End")


@dataclass(frozen=True)
class Scope:
    kind: str  # section | module | module_type
    name: str


@dataclass
class ProofBlock:
    """A named (or anonymous) declaration plus, if present, its proof.

    ``body_start``/``body_end`` bound the *proof body only*: everything strictly between
    the ``Proof.`` sentence (or the statement, when there is none) and the ender.
    """

    name: str | None
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
    #: ``script`` (tactics, possibly unterminated), ``term`` (``Proof term.``), ``none``.
    kind: str = "none"
    proof_using: str | None = None
    #: The ``Proof`` sentence that opened the script, whitespace-collapsed
    #: (``Proof using Hn.``, ``Proof with auto.``); empty when there was none.  Part of
    #: the frozen spec: an assembly that re-emits a bare ``Proof.`` rejects a proof
    #: that is valid in situ under ``Set Default Proof Using "Type"``.
    proof_opener: str = ""
    sentences: list[Sentence] = field(default_factory=list)
    #: Enclosing modules (outermost first) -- what qualifies the name after ``End``.
    modules: tuple[str, ...] = ()
    #: Enclosing sections (outermost first).
    sections: tuple[str, ...] = ()

    # -- derived ----------------------------------------------------------
    @property
    def has_proof(self) -> bool:
        return self.kind == "script"

    @property
    def admitted(self) -> bool:
        return self.ender == "Admitted"

    @property
    def end(self) -> int:
        """Offset just past the whole block (statement, proof and ender)."""
        if self.ender_end is not None:
            return self.ender_end
        if self.kind == "term" and self.proof_start is not None and self.body_end is not None:
            return self.body_end
        if self.sentences:
            return self.sentences[-1].end
        if self.body_start is not None and self.kind == "script":
            return self.body_start
        return self.statement_end

    @property
    def qualified_name(self) -> str | None:
        if self.name is None:
            return None
        return ".".join((*self.modules, self.name))

    @property
    def has_top_level_definition(self) -> bool:
        return has_top_level_token(self.statement, ":=")

    def body(self, source: str) -> str:
        if self.body_start is None or self.body_end is None:
            return ""
        return source[self.body_start : self.body_end]

    def tactics(self) -> list[str]:
        """The body's sentences with comments stripped -- what a replay sends to Rocq."""
        return [s.code for s in self.sentences if s.code.strip()]


def _classify(code: str) -> tuple[str, str | None] | None:
    """(head, name) for a declaration sentence, else ``None``."""
    m = _NAMED.match(code)
    if m and m.group("head") in DECL_HEADS:
        return m.group("head"), m.group("name")
    if _ANON_INSTANCE.match(code):
        return "Instance", None
    if _GOAL.match(code):
        return "Goal", None
    if _OBLIGATION.match(code):
        return "Obligation", None
    return None


def is_proof_opener(code: str) -> bool:
    return bool(_PROOF_OPENER.match(code))


def proof_ender(code: str) -> str | None:
    m = _ENDER.match(code)
    return m.group(1) if m else None


def is_scope_sentence(code: str) -> bool:
    return first_word(code) in _SCOPE_WORDS


def _scope_step(stack: list[Scope], code: str) -> None:
    fw = first_word(code)
    if fw == "Section":
        m = _SECTION.match(code)
        if m:
            stack.append(Scope("section", m.group("name")))
    elif fw == "Module":
        if has_top_level_token(code, ":="):
            return  # `Module M := N.` -- an alias, no End
        m = _MODULE.match(code)
        if m:
            stack.append(Scope("module_type" if m.group("type") else "module", m.group("name")))
    elif fw == "End":
        m = _END.match(code)
        if not m:
            return
        name = m.group("name")
        for i in range(len(stack) - 1, -1, -1):
            if stack[i].name == name:
                del stack[i:]
                return


def scopes_at(sentences: list[Sentence], offset: int) -> list[Scope]:
    """Scopes still open just before ``offset`` (outermost first)."""
    stack: list[Scope] = []
    for sent in sentences:
        if sent.start >= offset:
            break
        _scope_step(stack, sent.code)
    return stack


def parse_blocks(source: str, *, sentences: list[Sentence] | None = None) -> list[ProofBlock]:
    """Every declaration in ``source`` with its proof span, in order."""
    sents = split_sentences(source) if sentences is None else sentences
    blocks: list[ProofBlock] = []
    stack: list[Scope] = []
    i = 0
    n = len(sents)
    while i < n:
        sent = sents[i]
        code = sent.code
        _scope_step(stack, code)
        decl = _classify(code)
        if decl is None:
            i += 1
            continue
        head, name = decl
        block = ProofBlock(
            name=name,
            head=head,
            statement=code,
            statement_start=sent.code_start,
            statement_end=sent.end,
            modules=tuple(s.name for s in stack if s.kind == "module"),
            sections=tuple(s.name for s in stack if s.kind == "section"),
        )
        j = i + 1
        proof_capable = head in PROOF_HEADS and (head in THEOREM_HEADS or not block.has_top_level_definition)
        if j < n and _PROOF.match(sents[j].code):
            opener = sents[j]
            if is_proof_opener(opener.code):
                block.kind = "script"
                block.proof_start = opener.start
                block.body_start = opener.end
                block.proof_opener = " ".join(opener.code.split())
                m = _PROOF_USING.match(opener.code)
                if m:
                    block.proof_using = m.group("what").strip()
                j = _collect_body(block, sents, j + 1)
            else:
                block.kind = "term"
                block.proof_start = opener.start
                block.body_start = opener.start
                block.body_end = opener.end
                j += 1
        elif proof_capable and j < n and _looks_like_script(sents, j):
            block.kind = "script"
            block.body_start = sent.end
            j = _collect_body(block, sents, j)
        blocks.append(block)
        i = max(j, i + 1)
    return blocks


def _looks_like_script(sents: list[Sentence], j: int) -> bool:
    """A proof-capable declaration followed by tactics and an ender, with no ``Proof.``."""
    k = j
    while k < len(sents):
        code = sents[k].code
        if proof_ender(code):
            return True
        if _classify(code) is not None or is_scope_sentence(code) or _PROOF.match(code):
            return False
        k += 1
    return False


def _collect_body(block: ProofBlock, sents: list[Sentence], j: int) -> int:
    """Fill the body up to the ender (or to the next declaration/scope, if unterminated)."""
    n = len(sents)
    while j < n:
        sent = sents[j]
        code = sent.code
        ender = proof_ender(code)
        if ender is not None:
            block.ender = ender
            block.ender_start = sent.start
            block.ender_end = sent.end
            block.body_end = sent.start
            return j + 1
        if _classify(code) is not None or is_scope_sentence(code):
            break
        block.sentences.append(sent)
        j += 1
    block.body_end = block.sentences[-1].end if block.sentences else block.body_start
    return j


def find_block(source: str, name: str) -> ProofBlock | None:
    for block in parse_blocks(source):
        if block.name == name:
            return block
    return None
