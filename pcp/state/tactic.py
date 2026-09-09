"""One tactic sentence as tokens: head, quoted names, ``as`` clause (PLAN.md 4.1, 7).

The ledger classifies a step by what the tactic *is* (``iFrame`` vs ``iDestruct``), and
the diagnosis needs the pattern-bearing tactic's subject, binders and pattern.  Both
used to be ``re`` over the raw sentence, which mis-read ``iCombine "H1" "H2" as "H"``
and ``iDestruct (lem with "H") as ...`` alike.  This tokenizer is built on the lexer's
string/comment primitives (ARCHITECTURE.md 3 rule 2): a quoted name inside a nested
term is not a top-level argument, and a ``with`` inside a string is not a keyword.
"""

from __future__ import annotations

from dataclasses import dataclass

from pcp.rocq.lexer import first_word, skip_comment, skip_string, strip_comments

_OPEN = {"(": ")", "[": "]", "{": "}"}


@dataclass(frozen=True)
class Token:
    #: ``word`` (identifier-like), ``string`` (unquoted contents), ``group`` (bracketed
    #: text, delimiters included) or ``punct`` (one character).
    kind: str
    text: str
    start: int

    @property
    def is_lemma_term(self) -> bool:
        """A parenthesised application or a bare identifier: a lemma, not a hypothesis."""
        return (self.kind == "group" and self.text.startswith("(")) or self.kind == "word"


@dataclass(frozen=True)
class AsClause:
    keyword: str  # ``as`` or ``gives``
    binders: tuple[str, ...]
    pattern: str | None
    #: Index of the keyword token in ``TacticCall.tokens``.
    index: int


@dataclass(frozen=True)
class TacticCall:
    text: str
    head: str
    tokens: tuple[Token, ...]

    @property
    def strings(self) -> list[str]:
        return [t.text for t in self.tokens if t.kind == "string"]

    @property
    def all_strings(self) -> list[str]:
        """Every quoted name, including those nested in terms (``(lem with "H")``)."""
        out: list[str] = []
        i, n = 0, len(self.text)
        while i < n:
            if self.text.startswith("(*", i):
                i = skip_comment(self.text, i)
            elif self.text[i] == '"':
                end = skip_string(self.text, i)
                out.append(self.text[i + 1 : end - 1].replace('""', '"'))
                i = end
            else:
                i += 1
        return out

    @property
    def words(self) -> list[str]:
        return [t.text for t in self.tokens if t.kind == "word"]

    def mentions(self, word: str) -> bool:
        return self.head == word or word in self.words

    def clause(self, *keywords: str) -> AsClause | None:
        """The ``as (x y) "pattern"`` / ``gives "pattern"`` clause, if any."""
        for i, tok in enumerate(self.tokens):
            if tok.kind != "word" or tok.text not in (keywords or ("as",)):
                continue
            binders: tuple[str, ...] = ()
            j = i + 1
            if j < len(self.tokens) and self.tokens[j].kind == "group" and self.tokens[j].text.startswith("("):
                binders = tuple(_binder_names(self.tokens[j].text[1:-1]))
                j += 1
            pattern = self.tokens[j].text if j < len(self.tokens) and self.tokens[j].kind == "string" else None
            return AsClause(tok.text, binders, pattern, i)
        return None

    def subject(self, before: int | None = None) -> Token | None:
        """The first argument token (a hypothesis name, a lemma term, ...)."""
        upto = len(self.tokens) if before is None else before
        for tok in self.tokens[:upto]:
            if tok.kind in ("string", "group", "word"):
                return tok
        return None


def _binder_names(text: str) -> list[str]:
    names: list[str] = []
    depth = 0
    buf = ""
    for ch in text:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if depth == 0 and (ch.isspace() or ch == ":"):
            if buf and buf != "_":
                names.append(buf)
            buf = ""
            if ch == ":":
                break
        else:
            buf += ch
    if buf and buf != "_" and depth == 0:
        names.append(buf)
    return names


def _matching(text: str, i: int) -> int:
    """``i`` points at an opening bracket; return the offset just past its match."""
    close = _OPEN[text[i]]
    depth = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if text.startswith("(*", i):
            i = skip_comment(text, i)
            continue
        if ch == '"':
            i = skip_string(text, i)
            continue
        if ch in _OPEN:
            depth += 1
        elif ch in ")]}":
            depth -= 1
            if depth == 0 and ch == close:
                return i + 1
            if depth == 0:
                return i + 1
        i += 1
    return n


def parse_tactic(sentence: str) -> TacticCall:
    """Tokenize one tactic sentence at the top level."""
    code = strip_comments(sentence).strip()
    head = first_word(code)
    tokens: list[Token] = []
    i, n = 0, len(code)
    # Skip the head itself (and any goal selector / attribute before it).
    if head:
        i = code.find(head)
        i = i + len(head) if i >= 0 else 0
    while i < n:
        ch = code[i]
        if ch.isspace():
            i += 1
        elif ch == '"':
            end = skip_string(code, i)
            tokens.append(Token("string", code[i + 1 : end - 1].replace('""', '"'), i))
            i = end
        elif ch in _OPEN:
            end = _matching(code, i)
            tokens.append(Token("group", code[i:end], i))
            i = end
        elif ch.isalnum() or ch == "_":
            j = i
            while j < n and (code[j].isalnum() or code[j] in "_'."):
                j += 1
            if code[j - 1] == "." and j == n:
                j -= 1  # the sentence terminator
            tokens.append(Token("word", code[i:j], i))
            i = j
        else:
            if ch != ".":
                tokens.append(Token("punct", ch, i))
            i += 1
    return TacticCall(text=code, head=head, tokens=tuple(tokens))
