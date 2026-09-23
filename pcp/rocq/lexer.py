"""The one Rocq lexer.

Everything in the tree that needs to look at Rocq text -- the gate, the assembler, the
statement hasher, the replay in ``pcp check``, the golden extractor -- goes through
here.  It knows exactly three things, which is the amount of Rocq the jobs need:

* **comments** nest: ``(* a (* b *) c *)`` is one comment, and a string inside a
  comment does not end it;
* **strings** escape ``"`` as ``""``;
* a **sentence** ends at a ``.`` followed by whitespace or end of input (Rocq's own
  rule -- ``Foo.bar``, ``..`` and ``.(`` do not terminate), and bullets, braces and
  goal-selected braces are sentences of their own.

The offsets are byte-exact into the source, because the freeze is enforced by span
arithmetic: a worker patch may reach exactly one proof-body span and nothing else.
"""

from __future__ import annotations

import re
from collections.abc import Iterator
from dataclasses import dataclass

_BULLET_CHARS = "-+*"
_SELECTOR_BEFORE_BRACE = re.compile(r"^\s*(?:\d+(?:\s*,\s*\d+)*|all|!|\[[^\]]*\])\s*:\s*$")


@dataclass(frozen=True)
class Sentence:
    """One vernacular sentence with byte offsets ``[start, end)`` into the source."""

    text: str
    start: int
    end: int

    @property
    def stripped(self) -> str:
        return self.text.strip()

    @property
    def code(self) -> str:
        """The sentence with leading comments and whitespace removed.

        A comment attaches to the sentence that follows it, so nearly every real
        declaration in Iris is preceded by one inside its own sentence span.
        """
        return strip_leading_comments(self.text)

    @property
    def code_start(self) -> int:
        """Offset of :attr:`code` within the source."""
        return self.start + (len(self.text) - len(self.code))

    @property
    def is_bullet(self) -> bool:
        c = self.code
        return bool(c) and c[0] in _BULLET_CHARS and set(c) <= set(c[0])

    @property
    def is_brace(self) -> bool:
        c = self.code
        return c in ("{", "}") or bool(_SELECTOR_BEFORE_BRACE.match(c[:-1] if c.endswith("{") else "")) and c.endswith("{")

    @property
    def first_word(self) -> str:
        """The first identifier-like token of the code (after goal selectors)."""
        return first_word(self.code)


_WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
_SELECTOR = re.compile(r"^\s*(?:\d+(?:\s*,\s*\d+)*|all|!|\[[^\]]*\])\s*:\s*")


def first_word(code: str) -> str:
    text = _SELECTOR.sub("", code, count=1)
    # Attributes precede the command they modify.
    while text.startswith("#["):
        close = text.find("]")
        if close < 0:
            break
        text = text[close + 1 :].lstrip()
    m = _WORD.match(text)
    return m.group(0) if m else ""


def skip_comment(source: str, i: int) -> int:
    """``i`` points at ``(*``; return the offset just past the matching ``*)``."""
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
        elif source[i] == '"':
            i = skip_string(source, i)
        else:
            i += 1
    return n


def skip_string(source: str, i: int) -> int:
    """``i`` points at an opening ``"``; return the offset just past the closing one."""
    n = len(source)
    i += 1
    while i < n:
        if source[i] == '"':
            if i + 1 < n and source[i + 1] == '"':
                i += 2
                continue
            return i + 1
        i += 1
    return n


def iter_comments(source: str) -> Iterator[tuple[int, int, str]]:
    """Every top-level comment as ``(start, end, text)``."""
    i, n = 0, len(source)
    while i < n:
        if source.startswith("(*", i):
            end = skip_comment(source, i)
            yield i, end, source[i:end]
            i = end
        elif source[i] == '"':
            i = skip_string(source, i)
        else:
            i += 1


def strip_comments(source: str, *, replacement: str = " ") -> str:
    """Remove every comment, respecting nesting and string literals."""
    out: list[str] = []
    cursor = 0
    for start, end, _ in iter_comments(source):
        out.append(source[cursor:start])
        out.append(replacement)
        cursor = end
    out.append(source[cursor:])
    return "".join(out)


def strip_leading_comments(text: str) -> str:
    i, n = 0, len(text)
    while i < n:
        if text[i].isspace():
            i += 1
        elif text.startswith("(*", i):
            i = skip_comment(text, i)
        else:
            break
    return text[i:]


def _only_blank_or_comments(text: str) -> bool:
    return strip_leading_comments(text) == ""


def split_sentences(source: str) -> list[Sentence]:
    """Split Rocq source into sentences (see the module docstring for the rules)."""
    out: list[Sentence] = []
    i, n = 0, len(source)
    start = 0

    def emit(end: int) -> None:
        nonlocal start
        text = source[start:end]
        if text.strip():
            out.append(Sentence(text, start, end))
        start = end

    while i < n:
        ch = source[i]
        if ch == "(" and source.startswith("(*", i):
            i = skip_comment(source, i)
            continue
        if ch == '"':
            i = skip_string(source, i)
            continue
        if ch == ".":
            if source.startswith("..", i):
                i += 2
                while i < n and source[i] == ".":
                    i += 1
                continue
            nxt = source[i + 1] if i + 1 < n else None
            if nxt is None or nxt.isspace():
                emit(i + 1)
                i += 1
                continue
            i += 1
            continue
        if ch in _BULLET_CHARS and _only_blank_or_comments(source[start:i]):
            j = i
            while j < n and source[j] == ch:
                j += 1
            emit(j)
            i = j
            continue
        if ch == "{":
            before = source[start:i]
            if _only_blank_or_comments(before) or _SELECTOR_BEFORE_BRACE.match(strip_leading_comments(before)):
                emit(i + 1)
                i += 1
                continue
        if ch == "}" and _only_blank_or_comments(source[start:i]):
            emit(i + 1)
            i += 1
            continue
        i += 1
    if source[start:].strip():
        out.append(Sentence(source[start:], start, n))
    return out


def identifiers(code: str) -> list[str]:
    """Every identifier-like token in ``code`` outside comments and strings, in order.

    The sentinels ask "does this statement mention ``WP``/``twp``?" and the gate asks
    "which option does this ``Set``/``Unset`` name?"; both are token questions, and
    answering them here keeps every Rocq scan in the lexer (ARCHITECTURE.md §3 rule 2).
    """
    out: list[str] = []
    i, n = 0, len(code)
    while i < n:
        if code.startswith("(*", i):
            i = skip_comment(code, i)
            continue
        if code[i] == '"':
            i = skip_string(code, i)
            continue
        m = _WORD.match(code, i)
        if m:
            out.append(m.group(0))
            i = m.end()
            continue
        i += 1
    return out


def has_top_level_token(code: str, token: str) -> bool:
    """Whether ``token`` occurs outside any bracket, comment or string in ``code``."""
    depth = 0
    i, n = 0, len(code)
    while i < n:
        ch = code[i]
        if ch == "(" and code.startswith("(*", i):
            i = skip_comment(code, i)
            continue
        if ch == '"':
            i = skip_string(code, i)
            continue
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and code.startswith(token, i):
            return True
        i += 1
    return False


def terminate_sentence(tactic: str) -> str:
    """``tactic`` with its final sentence terminated: an MCP client sends one tactic and
    often omits the ``.``, which Rocq reports as an opaque syntax error.  Bullets and
    goal braces need no period; a sentence that already ends in one is left alone."""
    stripped = tactic.rstrip()
    sentences = split_sentences(stripped)
    last = sentences[-1].text.strip() if sentences else stripped
    if not last or last.endswith((".", "{", "}")) or set(last) <= set(_BULLET_CHARS):
        return stripped
    return stripped + "."
