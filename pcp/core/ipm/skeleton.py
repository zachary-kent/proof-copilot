"""The connective skeleton of a printed Iris prop (PLAN.md 3.2).

Props carry their ∗ / −∗ / ∃ / ⌜⌝ / □ / ▷ tree alongside the printed form.  That
skeleton is what turns ``iDestruct``-pattern handling into a deterministic *compile*
instead of a model guess (PLAN.md 7), and it is what the unification-failure aligner
walks when a pattern does not fit its object.

Scope, honestly stated: this parses Iris's *standard* notation.  Project-local
notation that hides a connective is invisible to it, so every node records the source
span it came from and unparsable input yields an ``atom`` -- never a guess.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Iterator, Literal

Kind = Literal[
    "sep", "and", "or", "wand", "impl", "iff", "wand_iff",
    "exists", "forall", "pure", "persistently", "intuitionistically",
    "later", "fupd", "bupd", "except0", "affinely", "absorbingly", "atom",
]

#: Connectives ``iDestruct`` can take apart, and how.
SPLITTABLE = {"sep", "and", "or", "exists", "pure"}
#: Modalities ``iDestruct`` descends through transparently -- `▷ (P ∗ Q)` really
#: does destruct into `▷ P` and `▷ Q`.
TRANSPARENT = {"later", "except0", "affinely", "absorbingly"}
#: Update modalities ``iDestruct`` does *not* see through: they must be eliminated
#: first (``iMod``, or a `>` marker in the pattern).
UPDATE = {"fupd", "bupd"}


@dataclass
class Skel:
    kind: Kind
    children: list["Skel"] = field(default_factory=list)
    binders: list[str] = field(default_factory=list)
    text: str = ""

    def __repr__(self) -> str:  # compact, for diagnostics
        if self.kind == "atom":
            return f"atom({self.text!r})"
        b = "".join(f" {x}" for x in self.binders)
        return f"{self.kind}{b}({', '.join(map(repr, self.children))})"

    def render(self, indent: int = 0) -> str:
        pad = "  " * indent
        if self.kind == "atom":
            return f"{pad}{self.text}"
        head = self.kind + ("".join(f" {b}" for b in self.binders))
        lines = [f"{pad}{head}"]
        for c in self.children:
            lines.append(c.render(indent + 1))
        return "\n".join(lines)

    def walk(self) -> Iterator["Skel"]:
        yield self
        for c in self.children:
            yield from c.walk()

    def strip_transparent(self) -> "Skel":
        """Descend past modalities ``iDestruct`` sees through."""
        node = self
        while node.kind in TRANSPARENT and len(node.children) == 1:
            node = node.children[0]
        return node

    def to_notation(self) -> str:
        """Render back to Iris notation, parenthesised by precedence.

        Round-trips with :func:`parse_skeleton` (``tests/test_skeleton_fuzz.py``),
        which is what lets the aligner show the prop it *thinks* it is looking at.
        """
        return _render(self, 0)

    def to_json(self) -> dict:
        return {
            "kind": self.kind,
            "binders": self.binders,
            "text": self.text if self.kind == "atom" else "",
            "children": [c.to_json() for c in self.children],
        }


# --------------------------------------------------------------------------- lexer

# Tight prefixes: Iris levels ~20, they bind their immediate argument only.
_PREFIX_OPS: list[tuple[str, Kind]] = [
    ("<pers>", "persistently"),
    ("<affine>", "affinely"),
    ("<absorb>", "absorbingly"),
    ("□", "intuitionistically"),
    ("■", "persistently"),
    ("▷", "later"),
    ("◇", "except0"),
]

# Loose prefixes: Iris level 99 with the body at level 200, i.e. they extend as far
# right as they can.  `|==> P ∗ Q` is `|==> (P ∗ Q)`, not `(|==> P) ∗ Q`.
_LOOSE_PREFIX_OPS: list[tuple[str, Kind]] = [("|==>", "bupd")]

# Prefix fupd: `|={E}=>`, `|={E1,E2}=>`.
_FUPD_RE = re.compile(r"\|=\{([^}]*)\}=>")
# Infix modal wands: `P ={E}=∗ Q` is `P -∗ |={E}=> Q`, `P ==∗ Q` is `P -∗ |==> Q`.
# They are extremely common in Iris and parsing them as opaque atoms would hide the
# wand from every consumer of the skeleton.
_FUPD_WAND_RE = re.compile(r"=\{([^}]*)\}=(?:∗|\*)")
_BUPD_WAND = "==∗"

_BINOPS: list[tuple[str, Kind, int]] = [
    # (token, kind, precedence)  -- lower binds looser, all right-associative
    ("∗-∗", "wand_iff", 1),
    ("-∗", "wand", 1),
    ("−∗", "wand", 1),
    ("↔", "iff", 1),
    ("→", "impl", 1),
    ("->", "impl", 1),
    ("∨", "or", 2),
    ("\\/", "or", 2),
    ("∧", "and", 3),
    ("/\\", "and", 3),
    ("∗", "sep", 3),
]

_BINDERS = {"∀": "forall", "∃": "exists"}
_MAX_PREC = 4


class _Cursor:
    def __init__(self, text: str) -> None:
        self.s = text
        self.i = 0

    def skip_ws(self) -> None:
        while self.i < len(self.s) and self.s[self.i].isspace():
            self.i += 1

    def eof(self) -> bool:
        self.skip_ws()
        return self.i >= len(self.s)

    def peek(self, token: str) -> bool:
        self.skip_ws()
        return self.s.startswith(token, self.i)

    def eat(self, token: str) -> bool:
        if self.peek(token):
            self.i += len(token)
            return True
        return False

    def rest(self) -> str:
        self.skip_ws()
        return self.s[self.i :]


def parse_skeleton(prop: str) -> Skel:
    """Parse a printed Iris prop into its connective skeleton.

    Total: any input produces a tree.  Unrecognised text becomes an ``atom``.
    """
    cur = _Cursor(prop.strip())
    try:
        node = _parse(cur, 0)
    except _ParseGaveUp:
        return Skel("atom", text=prop.strip())
    if not cur.eof():
        # Trailing junk means our grammar does not cover this prop; be honest.
        return Skel("atom", text=prop.strip())
    return node


class _ParseGaveUp(Exception):
    pass


def _parse(cur: _Cursor, prec: int) -> Skel:
    if prec >= _MAX_PREC:
        return _parse_prefix(cur)

    # Binders bind loosest and extend as far right as they can.
    if prec == 0:
        cur.skip_ws()
        for sym, kind in _BINDERS.items():
            if cur.peek(sym):
                start = cur.i
                cur.eat(sym)
                binders = _parse_binders(cur)
                if binders is None:
                    cur.i = start
                    break
                body = _parse(cur, 0)
                return Skel(kind, [body], binders=binders, text=cur.s[start : cur.i].strip())

    left = _parse(cur, prec + 1)

    if prec == 1:
        modal = _match_modal_wand(cur)
        if modal is not None:
            token, mask = modal
            cur.i += len(token)
            body = _parse(cur, 1)
            inner = Skel("bupd", [body]) if mask is None else Skel("fupd", [body], binders=[mask])
            return Skel("wand", [left, inner])

    op = _match_op(cur)
    if op is not None and op[2] == prec:
        token, kind, _ = op
        cur.eat(token)
        right = _parse(cur, prec)  # right-associative
        node = Skel(kind, [left, right])
        # `∗`/`∧`/`∨` associate to the right, so `P ∗ (Q ∗ R)` *is* `P ∗ Q ∗ R`:
        # flatten the right spine into one n-ary node.  A left-nested `(P ∗ Q) ∗ R`
        # is a different term and stays nested -- IPM destructs the two differently.
        if right.kind == kind and kind in ("sep", "and", "or"):
            node = Skel(kind, [left] + right.children)
        return node
    return left


def _match_op(cur: _Cursor) -> tuple[str, Kind, int] | None:
    """Longest *standalone* operator match at the cursor.

    Two traps, both of which occur in ordinary Iris output:

    * Longest match: `∗-∗` starts with `∗` and `->` with `-`, so shortest-first
      silently reads `P ∗-∗ Q` as a separating conjunction with an unparsable
      right operand.
    * Standalone: `∗` is also a *letter* in several notations -- `l ↦∗ vs`
      (heap_lang arrays), `={E}=∗` (fupd wand).  Iris always prints the binary
      connectives space-delimited, so an operator glued to the token before it is
      part of that token, not a connective.
    """
    cur.skip_ws()
    best: tuple[str, Kind, int] | None = None
    for token, kind, prec in _BINOPS:
        if cur.peek(token) and _standalone(cur.s, cur.i, token):
            if best is None or len(token) > len(best[0]):
                best = (token, kind, prec)
    return best


def _match_modal_wand(cur: _Cursor) -> tuple[str, str | None] | None:
    """`={E}=∗` / `==∗` at the cursor -> (token, mask or None for bupd)."""
    cur.skip_ws()
    if cur.i > 0 and not cur.s[cur.i - 1].isspace():
        return None
    if cur.s.startswith(_BUPD_WAND, cur.i):
        return (_BUPD_WAND, None)
    m = _FUPD_WAND_RE.match(cur.s, cur.i)
    if m:
        return (m.group(0), m.group(1).strip())
    return None


def _standalone(text: str, i: int, token: str) -> bool:
    """Is ``token`` at ``i`` a connective rather than part of a bigger notation?"""
    if i > 0 and not text[i - 1].isspace():
        return False
    j = i + len(token)
    return j >= len(text) or text[j].isspace() or text[j] in "(⌜"


def _parse_binders(cur: _Cursor) -> list[str] | None:
    """``x y (z : T),`` -- returns the names, positioned after the comma."""
    start = cur.i
    names: list[str] = []
    depth = 0
    buf = ""
    while cur.i < len(cur.s):
        ch = cur.s[cur.i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == "," and depth == 0:
            cur.i += 1
            names.extend(_binder_names(buf))
            return names or None
        buf += ch
        cur.i += 1
    cur.i = start
    return None


def _binder_names(buf: str) -> list[str]:
    """Names bound by `x y : T`, `(x : T) (y : U)`, or a bare `x y`.

    The un-parenthesised `∃ n : nat, ...` form is what Iris actually prints, and
    naively tokenising it yields `n` *and* `nat` -- which then becomes a second
    `iDestruct` binder for a variable that does not exist.
    """
    text = buf.strip()
    if text and not text.lstrip().startswith("("):
        # `x y : T` -- everything before the top-level colon is names.
        depth = 0
        for i, ch in enumerate(text):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif ch == ":" and depth == 0 and not text.startswith("::", i):
                text = text[:i]
                break
    names: list[str] = []
    for group in re.findall(r"\(([^)]*)\)|([^\s()]+)", text):
        item = group[0] or group[1]
        head = item.split(":")[0]
        names.extend(n for n in head.split() if n and n not in {":", "_"})
    return names


def _parse_prefix(cur: _Cursor) -> Skel:
    cur.skip_ws()
    fupd = _FUPD_RE.match(cur.rest())
    if fupd:
        cur.i += fupd.end()
        body = _parse(cur, 0)
        return Skel("fupd", [body], binders=[fupd.group(1).strip()])
    for token, kind in _LOOSE_PREFIX_OPS:
        if cur.peek(token):
            cur.eat(token)
            return Skel(kind, [_parse(cur, 0)])
    for token, kind in _PREFIX_OPS:
        if cur.peek(token):
            cur.eat(token)
            body = _parse_prefix(cur)
            return Skel(kind, [body])
    return _parse_atom(cur)


def _parse_atom(cur: _Cursor) -> Skel:
    cur.skip_ws()
    if cur.i >= len(cur.s):
        raise _ParseGaveUp
    if cur.eat("⌜"):
        inner = _take_until_balanced(cur, "⌜", "⌝")
        return Skel("pure", [Skel("atom", text=inner)], text=inner)
    if cur.eat("("):
        inner_start = cur.i
        node = _parse(cur, 0)
        if not cur.eat(")"):
            # Unbalanced under our grammar (application, tuples, notation): take the
            # whole parenthesised span as one atom rather than mis-parsing it.
            cur.i = inner_start
            inner = _take_until_balanced(cur, "(", ")")
            return Skel("atom", text=f"({inner})")
        return node
    # An application / identifier / anything else, up to the next top-level operator.
    text = _take_atom_span(cur)
    if not text:
        raise _ParseGaveUp
    return Skel("atom", text=text)


def _take_until_balanced(cur: _Cursor, open_tok: str, close_tok: str) -> str:
    depth = 1
    buf = ""
    while cur.i < len(cur.s):
        if cur.s.startswith(open_tok, cur.i):
            depth += 1
            buf += open_tok
            cur.i += len(open_tok)
            continue
        if cur.s.startswith(close_tok, cur.i):
            depth -= 1
            cur.i += len(close_tok)
            if depth == 0:
                return buf.strip()
            buf += close_tok
            continue
        buf += cur.s[cur.i]
        cur.i += 1
    return buf.strip()


_STOP_CHARS = (")", "⌝", ",")


def _match_modal_wand_at(text: str, i: int) -> bool:
    if i > 0 and not text[i - 1].isspace():
        return False
    return text.startswith(_BUPD_WAND, i) or _FUPD_WAND_RE.match(text, i) is not None


def _take_atom_span(cur: _Cursor) -> str:
    """Consume an application/identifier up to the next top-level connective.

    Uses the same standalone test as :func:`_match_op`, so `l ↦∗ vs` stays one atom.
    """
    start = cur.i
    depth = 0
    while cur.i < len(cur.s):
        ch = cur.s[cur.i]
        if ch in "([{":
            depth += 1
            cur.i += 1
            continue
        if ch in ")]}":
            if depth == 0:
                break
            depth -= 1
            cur.i += 1
            continue
        if depth == 0:
            if any(cur.s.startswith(t, cur.i) for t in _STOP_CHARS):
                break
            if any(
                cur.s.startswith(t, cur.i) and _standalone(cur.s, cur.i, t)
                for t, _, _ in _BINOPS
            ):
                break
            if cur.i > start and _match_modal_wand_at(cur.s, cur.i):
                break
            if cur.s.startswith("⌜", cur.i) and cur.i > start:
                break
        cur.i += 1
    return cur.s[start : cur.i].strip()


def is_splittable(skel: Skel) -> bool:
    """Would ``iDestruct`` take this apart (possibly after an ``iMod``)?"""
    node = skel
    while node.kind in TRANSPARENT | UPDATE and len(node.children) == 1:
        node = node.children[0]
    return node.kind in SPLITTABLE


# ------------------------------------------------------------------------- render

_KIND_OP: dict[str, tuple[str, int]] = {
    "wand": ("-∗", 1),
    "wand_iff": ("∗-∗", 1),
    "iff": ("↔", 1),
    "impl": ("→", 1),
    "or": ("∨", 2),
    "and": ("∧", 3),
    "sep": ("∗", 3),
}
_TIGHT_PREFIX: dict[str, str] = {
    "persistently": "■",
    "intuitionistically": "□",
    "later": "▷",
    "except0": "◇",
    "affinely": "<affine>",
    "absorbingly": "<absorb>",
}


def _render(node: Skel, prec: int) -> str:
    """``prec`` is the binding strength of the context; parenthesise when looser."""
    if node.kind == "atom":
        return node.text
    if node.kind == "pure":
        inner = node.children[0].text if node.children else node.text
        return f"⌜{inner}⌝"
    if node.kind in _KIND_OP:
        op, p = _KIND_OP[node.kind]
        # Right-associative: the last child may stay at this level, the rest tighten.
        parts = [_render(c, p + 1) for c in node.children[:-1]]
        parts.append(_render(node.children[-1], p))
        text = f" {op} ".join(parts)
        return f"({text})" if prec > p else text
    if node.kind in _TIGHT_PREFIX:
        # Tight prefixes bind at Iris level ~20, tighter than every binop here, so
        # they never need outer parentheses.
        body = _render(node.children[0], _MAX_PREC)
        return f"{_TIGHT_PREFIX[node.kind]} {body}"
    if node.kind == "bupd":
        text = f"|==> {_render(node.children[0], 0)}"
        return f"({text})" if prec > 0 else text
    if node.kind == "fupd":
        mask = node.binders[0] if node.binders else "⊤"
        text = f"|={{{mask}}}=> {_render(node.children[0], 0)}"
        return f"({text})" if prec > 0 else text
    if node.kind in ("exists", "forall"):
        sym = "∃" if node.kind == "exists" else "∀"
        text = f"{sym} {' '.join(node.binders)}, {_render(node.children[0], 0)}"
        return f"({text})" if prec > 0 else text
    raise AssertionError(node.kind)
