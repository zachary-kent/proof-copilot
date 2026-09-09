"""Statement text: normalisation, hashing, binder surgery (PLAN.md 8.3, 8.7)."""

from __future__ import annotations

import re

from pcp.rocq.lexer import skip_comment, skip_string, strip_comments
from pcp.util.hashing import content_hash


def normalize_statement(text: str) -> str:
    """Comments removed (nesting-aware), whitespace collapsed, trailing ``.`` kept."""
    return " ".join(strip_comments(text).split())


def statement_hash(text: str) -> str:
    return content_hash(normalize_statement(text), prefix="s:")


def same_statement(a: str, b: str) -> bool:
    return normalize_statement(a) == normalize_statement(b)


def split_head(statement: str) -> tuple[str, str, str]:
    """``(head_and_name, binders, type)`` for ``Lemma foo (x : T) : P.``

    The split is at the first top-level ``:``; ``binders`` is the text between the name
    and that colon.  Returns ``("", "", statement)`` when no top-level colon exists.
    """
    code = strip_comments(statement)
    depth = 0
    i, n = 0, len(code)
    while i < n:
        ch = code[i]
        if ch == '"':
            i = skip_string(code, i)
            continue
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0 and not code.startswith(":=", i) and not code.startswith("::", i):
            prefix = code[:i]
            parts = prefix.split(None, 2)
            head_and_name = " ".join(parts[:2])
            binders = parts[2] if len(parts) > 2 else ""
            return head_and_name, binders.strip(), code[i + 1 :].strip()
        i += 1
    return "", "", code


def _binder_groups(binders: str) -> list[tuple[int, int, list[str], str]]:
    """Explicit ``(x y : T)`` groups of a binder list as ``(start, end, names, type)``.

    Depth-counted rather than matched by a regex: ``(g : (nat -> (nat -> nat)))``
    nests two levels and a one-level pattern made it invisible.  Implicit ``{x : T}``
    and typeclass `` `{...} `` binders are skipped: they are plumbing, not premises.
    """
    out: list[tuple[int, int, list[str], str]] = []
    i, n = 0, len(binders)
    while i < n:
        ch = binders[i]
        if ch == '"':
            i = skip_string(binders, i)
            continue
        if ch == "(":
            close = _matching(binders, i, "(", ")")
            inner = binders[i + 1 : close]
            colon = _top_level_colon(inner)
            if colon is not None:
                names = [t for t in inner[:colon].split() if t]
                out.append((i, close + 1, names, inner[colon + 1 :].strip()))
            i = close + 1
            continue
        if ch == "{":
            i = _matching(binders, i, "{", "}") + 1
            continue
        if ch == "[":
            i = _matching(binders, i, "[", "]") + 1
            continue
        i += 1
    return out


def _matching(text: str, i: int, open_ch: str, close_ch: str) -> int:
    depth = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch == '"':
            i = skip_string(text, i)
            continue
        if ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return n - 1


def _top_level_colon(text: str) -> int | None:
    depth = 0
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch == '"':
            i = skip_string(text, i)
            continue
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0 and not text.startswith(":=", i) and not text.startswith("::", i):
            return i
        i += 1
    return None


def statement_binders(statement: str) -> list[str]:
    """Names bound by explicit ``(x y : T)`` groups before the statement's colon.

    Implicit ``{x : T}`` and typeclass `` `{...} `` binders are excluded: they are
    plumbing, not premises, and probing them produces noise.
    """
    _, binders, _ = split_head(statement)
    names: list[str] = []
    for _s, _e, group, _ty in _binder_groups(binders):
        names.extend(n for n in group if n and n != "_")
    return names


def remove_binder(statement: str, name: str) -> str | None:
    """``statement`` with binder ``name`` dropped, or ``None`` when it is not explicit.

    Used only by the unused-premise probe, which compiles the result in a scratch
    directory and throws it away.
    """
    head, binders, ty = split_head(statement)
    if not head:
        return None
    for start, end, names, group_type in _binder_groups(binders):
        if name not in names:
            continue
        rest = [n for n in names if n != name]
        replacement = f"({' '.join(rest)} : {group_type})" if rest else ""
        new_binders = (binders[:start] + replacement + binders[end:]).strip()
        out = f"{head} {new_binders} : {ty}" if new_binders else f"{head} : {ty}"
        return re.sub(r"[ \t]{2,}", " ", out)
    return None


def statement_name(statement: str) -> str | None:
    from pcp.rocq.decls import parse_blocks

    blocks = parse_blocks(statement)
    return blocks[0].name if blocks else None


def _unused(_: str) -> None:  # keep the lexer import honest for type checkers
    skip_comment("", 0)
