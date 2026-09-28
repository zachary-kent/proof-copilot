"""Printed terms as token sequences: matching, substitution and change sites (D2).

The tactic-effect report compares a printed term *before* a step with one *after* it:
which subterm a ``rewrite`` changed, what an evar ``?x`` or an ``∃ x`` binder became.
Both are answered on tokens rather than characters, so ``x`` never matches inside
``xs`` and a captured value is always a bracket-balanced subterm.  Everything here is
total and bounded: a term the matcher cannot explain yields ``None``, never a guess.
"""

from __future__ import annotations

import difflib
import re
from dataclasses import dataclass

#: A quoted heap_lang binder, an identifier (``?x`` evars, ``#l`` literals, ``@f``,
#: qualified ``Nat.add``), a number, a bracket, or any other single character.
_TOKEN = re.compile(r'"(?:[^"]|"")*"|[?#@]?[^\W\d][\w\']*(?:\.[^\W\d][\w\']*)*|#?\d+|\S', re.U)
_OPENERS, _CLOSERS = "([{", ")]}"
#: Matching work per call; a real printed prop needs a few hundred steps at most.
_BUDGET = 20000


@dataclass(frozen=True)
class Tok:
    text: str
    start: int
    end: int


def tokens(text: str) -> list[Tok]:
    return [Tok(m.group(0), m.start(), m.end()) for m in _TOKEN.finditer(text)]


def _balanced(seq: list[Tok]) -> bool:
    depth = 0
    for t in seq:
        if t.text in _OPENERS:
            depth += 1
        elif t.text in _CLOSERS:
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


def _slice(text: str, seq: list[Tok]) -> str:
    return " ".join(text[seq[0].start : seq[-1].end].split()) if seq else ""


def unparen(text: str) -> str:
    t = text.strip()
    while t.startswith("(") and t.endswith(")") and _balanced(tokens(t[1:-1])):
        t = t[1:-1].strip()
    return t


def match_template(template: str, variables: set[str] | frozenset[str], text: str) -> dict[str, str] | None:
    """Bind each variable of ``template`` to a balanced subterm so it prints as ``text``.

    ``P x ∗ Q`` against ``P (S n) ∗ Q`` with ``{x}`` gives ``{"x": "S n"}``.  A
    variable bound twice must capture the same tokens both times.  ``None`` when there
    is no match (or the search exceeds its budget).
    """
    tt, st = tokens(template), tokens(text)
    budget = [_BUDGET]

    def go(i: int, j: int, env: dict[str, tuple[int, int]]) -> dict[str, tuple[int, int]] | None:
        budget[0] -= 1
        if budget[0] < 0:
            return None
        if i == len(tt):
            return env if j == len(st) else None
        tok = tt[i].text
        if tok in variables:
            if tok in env:
                a, b = env[tok]
                seg = [t.text for t in st[a:b]]
                if [t.text for t in st[j : j + len(seg)]] != seg:
                    return None
                return go(i + 1, j + len(seg), env)
            # Tokens the rest of the template still needs bound the capture's length.
            rest = sum(1 for t in tt[i + 1 :] if t.text not in variables)
            for k in range(j + 1, len(st) - rest + 1):
                if not _balanced(st[j:k]):
                    continue
                got = go(i + 1, k, {**env, tok: (j, k)})
                if got is not None:
                    return got
            return None
        if j < len(st) and st[j].text == tok:
            return go(i + 1, j + 1, env)
        return None

    env = go(0, 0, {})
    if env is None:
        return None
    return {v: unparen(_slice(text, st[a:b])) for v, (a, b) in env.items()}


def substitute(text: str, env: dict[str, str]) -> str:
    """Replace whole-token occurrences of each variable, parenthesising compound values."""
    out: list[str] = []
    last = 0
    for t in tokens(text):
        if t.text in env:
            val = env[t.text]
            if not _atomic(val):
                val = f"({val})"
            out.append(text[last : t.start])
            out.append(val)
            last = t.end
    out.append(text[last:])
    return " ".join("".join(out).split())


def _atomic(text: str) -> bool:
    """No whitespace outside brackets: safe to splice in without parentheses."""
    depth = 0
    for ch in text.strip():
        if ch in _OPENERS:
            depth += 1
        elif ch in _CLOSERS:
            depth -= 1
        elif ch.isspace() and depth == 0:
            return False
    return True


def count_occurrences(needle: list[str], hay: list[str]) -> list[int]:
    """Start indices of non-overlapping occurrences of ``needle`` in ``hay``."""
    out: list[int] = []
    n = len(needle)
    i = 0
    while n and i + n <= len(hay):
        if hay[i : i + n] == needle:
            out.append(i)
            i += n
        else:
            i += 1
    return out


@dataclass(frozen=True)
class Change:
    """One site where ``before`` and ``after`` differ: balanced old and new subterms."""

    old: str
    new: str
    #: Token index of the site in ``before``.
    at: int
    old_tokens: tuple[str, ...]


def changes(before: str, after: str) -> list[Change]:
    """The change sites between two printings of a term, each a balanced subterm.

    Compared as bracket trees, level by level: a group that differs on both sides is
    descended into, so ``P (x + 0) ∗ Q (x + 0)`` -> ``P x ∗ Q (x + 0)`` is one site,
    ``(x + 0)`` -> ``x``, at the first occurrence.  A pure insertion or deletion at a
    level (``n + 0 = m`` -> ``n = m``) is widened by its left neighbour so each site has
    an old and a new side.
    """
    a, b = tokens(before), tokens(after)
    at = [t.text for t in a]
    sites: list[tuple[int, int, int, int]] = []
    _diff_level(_tree(a, 0, len(a)), _tree(b, 0, len(b)), sites)
    return [Change(_slice(before, a[i1:i2]), _slice(after, b[j1:j2]), i1, tuple(at[i1:i2])) for i1, i2, j1, j2 in sites]


@dataclass(frozen=True)
class _Node:
    key: str
    start: int
    end: int
    children: tuple[_Node, ...] = ()
    group: bool = False


def _tree(toks: list[Tok], lo: int, hi: int) -> list[_Node]:
    out: list[_Node] = []
    i = lo
    while i < hi:
        t = toks[i].text
        if t in _OPENERS:
            depth, j = 0, i
            while j < hi:
                if toks[j].text in _OPENERS:
                    depth += 1
                elif toks[j].text in _CLOSERS:
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            j = min(j, hi - 1)
            inner = _tree(toks, i + 1, j)
            out.append(_Node(" ".join(x.text for x in toks[i : j + 1]), i, j + 1, tuple(inner), True))
            i = j + 1
        else:
            out.append(_Node(t, i, i + 1))
            i += 1
    return out


def _diff_level(xs: list[_Node], ys: list[_Node], sites: list[tuple[int, int, int, int]]) -> None:
    sm = difflib.SequenceMatcher(None, [x.key for x in xs], [y.key for y in ys], autojunk=False)
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == "equal":
            continue
        if op == "replace" and i2 - i1 == j2 - j1 and all(xs[i].group and ys[j].group and xs[i].key[0] == ys[j].key[0]
                                                           for i, j in zip(range(i1, i2), range(j1, j2), strict=True)):
            for i, j in zip(range(i1, i2), range(j1, j2), strict=True):
                _diff_level(list(xs[i].children), list(ys[j].children), sites)
            continue
        if i1 == i2 or j1 == j2:
            if i1 > 0 and j1 > 0:
                i1, j1 = i1 - 1, j1 - 1
            elif i2 < len(xs) and j2 < len(ys):
                i2, j2 = i2 + 1, j2 + 1
            if i1 == i2 or j1 == j2:
                continue
        site = (xs[i1].start, xs[i2 - 1].end, ys[j1].start, ys[j2 - 1].end)
        if sites and site[0] < sites[-1][1]:
            prev = sites.pop()
            site = (prev[0], max(prev[1], site[1]), prev[2], max(prev[3], site[3]))
        sites.append(site)


#: ``▷?p`` / ``□?p`` / ``<affine>?p``: a conditional modality's flag, not an evar.
_COND_MODALITY_END = ("▷", "□", "■", ">", "◇")


def evars(text: str) -> list[str]:
    """The evars of a printed term, in order of first appearance (``?x``, ``?Φ``)."""
    return list(dict.fromkeys(
        t.text for t in tokens(text)
        if t.text.startswith("?") and len(t.text) > 1 and not (t.start and text[t.start - 1] in _COND_MODALITY_END)
    ))
