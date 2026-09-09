"""The connective skeleton of a printed Iris prop (PLAN.md 3.2, 7).

Props carry their ∗ / −∗ / ∃ / ⌜⌝ / □ / ▷ tree alongside the printed form; that tree is
what turns ``iDestruct``-pattern handling into a deterministic compile, and what the
aligner walks when a pattern does not fit its object.

A precedence-climbing parser over Iris's *declared* levels (``iris/bi/notation.v``):

    level 20   ▷ ▷^n ▷?p □ ■ <pers> <affine> <absorb> ◇      tight prefixes, right assoc
    level 80   ∗ ∧                                          right assoc
    level 85   ∨                                            right assoc
    level 95   ↔ ∗-∗ ⊣⊢                                     no assoc
    level 99   -∗ → ⊢ ={E}=∗ ==∗ ={E}▷=∗                    right assoc, rhs at 200
    level 99   |==> |={E}=> |={E}▷=> |={E1}[E2]▷=>          body at 200
    level 200  ∃ x, ∀ x,                                    body at 200

Binders and loose prefixes are accepted wherever an *operand* starts -- Coq prints
``P -∗ ∃ x, Q x`` without parentheses (89 golden states) -- and they extend as far
right as they can.  Modal wands desugar (``P ={E}=∗ Q`` is ``P -∗ |={E}=> Q``).  The
parser is total: anything it does not understand becomes an ``atom`` for the whole
prop, never a partial guess.
"""

from __future__ import annotations

import re
from collections.abc import Iterator
from dataclasses import dataclass, field
from typing import Any, Literal

Kind = Literal[
    "sep", "and", "or", "wand", "impl", "iff", "wand_iff", "entails", "equiv",
    "exists", "forall", "pure",
    "persistently", "intuitionistically", "plainly", "later", "except0", "affinely", "absorbingly",
    "fupd", "fupd_step", "bupd",
    "atom",
]

#: Connectives ``iDestruct`` can take apart.
SPLITTABLE = frozenset({"sep", "and", "or", "exists", "pure"})
#: Modalities ``iDestruct`` descends through: ``▷ (P ∗ Q)`` destructs into ``▷ P`` and ``▷ Q``.
TRANSPARENT = frozenset({"later", "except0", "affinely", "absorbingly"})
#: Update modalities ``iDestruct`` does *not* see through: ``iMod`` or a ``>`` marker first.
UPDATE = frozenset({"fupd", "fupd_step", "bupd"})
#: ``□`` / ``<pers>``: a ``#`` marker introduces them into the intuitionistic context.
PERSISTENT = frozenset({"intuitionistically", "persistently"})
BINOPS = frozenset({"sep", "and", "or", "wand", "impl", "iff", "wand_iff", "entails", "equiv"})
BINDERS = frozenset({"exists", "forall"})

#: Iris level of each node kind (what ``render`` parenthesises by).
LEVEL: dict[str, int] = {
    "atom": 0, "pure": 0,
    "later": 20, "intuitionistically": 20, "persistently": 20, "plainly": 20,
    "except0": 20, "affinely": 20, "absorbingly": 20,
    "sep": 80, "and": 80, "or": 85, "iff": 95, "wand_iff": 95, "equiv": 95,
    "wand": 99, "impl": 99, "entails": 99, "bupd": 99, "fupd": 99, "fupd_step": 99,
    "exists": 200, "forall": 200,
}


@dataclass
class Skel:
    """A node.  ``binders``: quantified names; the mask(s) of a ``fupd``/``fupd_step``;
    the ``^n`` / ``?p`` annotation of a ``later``/``persistently``."""

    kind: Kind
    children: list[Skel] = field(default_factory=list)
    binders: list[str] = field(default_factory=list)
    text: str = ""

    def __repr__(self) -> str:
        if self.kind == "atom":
            return f"atom({self.text!r})"
        b = "".join(f" {x}" for x in self.binders)
        return f"{self.kind}{b}({', '.join(map(repr, self.children))})"

    def render(self, indent: int = 0) -> str:
        """Indented one-kind-per-line tree (what the alignment report shows)."""
        pad = "  " * indent
        if self.kind == "atom":
            return f"{pad}{self.text}"
        head = self.kind + "".join(f" {b}" for b in self.binders)
        return "\n".join([f"{pad}{head}", *(c.render(indent + 1) for c in self.children)])

    def walk(self) -> Iterator[Skel]:
        yield self
        for c in self.children:
            yield from c.walk()

    def strip_transparent(self) -> Skel:
        node = self
        while node.kind in TRANSPARENT and len(node.children) == 1:
            node = node.children[0]
        return node

    @property
    def level(self) -> int:
        return LEVEL[self.kind]

    def to_notation(self) -> str:
        """Back to Iris notation, parenthesised by level; round-trips with :func:`parse_skeleton`."""
        return render(self)

    def to_json(self) -> dict[str, Any]:
        return {
            "kind": self.kind,
            "binders": list(self.binders),
            "text": self.text if self.kind in ("atom", "pure") else "",
            "children": [c.to_json() for c in self.children],
        }

    @classmethod
    def from_json(cls, d: dict[str, Any]) -> Skel:
        return cls(
            kind=d["kind"],
            children=[cls.from_json(c) for c in d.get("children", [])],
            binders=list(d.get("binders", [])),
            text=d.get("text", ""),
        )


@dataclass(frozen=True)
class Markers:
    """What sits above a node once modalities are peeled (one definition, used everywhere)."""

    laters: int = 0
    update: bool = False
    intuit: bool = False
    except0: bool = False


def peel(skel: Skel) -> tuple[Markers, Skel]:
    """Descend every modality ``iDestruct`` (after ``iMod``/``#``) can see through."""
    laters = 0
    update = intuit = except0 = False
    node = skel
    while len(node.children) == 1:
        if node.kind == "later":
            laters += 1
        elif node.kind in UPDATE:
            update = True
        elif node.kind in PERSISTENT:
            intuit = True
        elif node.kind == "except0":
            except0 = True
        elif node.kind not in TRANSPARENT:
            break
        node = node.children[0]
    return Markers(laters=laters, update=update, intuit=intuit, except0=except0), node


def is_splittable(skel: Skel) -> bool:
    """Would ``iDestruct`` take this apart (possibly after an ``iMod``)?"""
    return peel(skel)[1].kind in SPLITTABLE


# --------------------------------------------------------------------------- lexing

#: Binary operators: token, kind, level, right-associative.  Longest match wins.
_BINOPS: list[tuple[str, str, int, bool]] = [
    ("∗-∗", "wand_iff", 95, False),
    ("⊣⊢", "equiv", 95, False),
    ("-∗", "wand", 99, True),
    ("−∗", "wand", 99, True),
    ("<->", "iff", 95, False),
    ("↔", "iff", 95, False),
    ("->", "impl", 99, True),
    ("→", "impl", 99, True),
    ("⊢", "entails", 99, True),
    ("∨", "or", 85, True),
    ("\\/", "or", 85, True),
    ("∧", "and", 80, True),
    ("/\\", "and", 80, True),
    ("∗", "sep", 80, True),
]
_RIGHT_OPERAND_LEVEL = {"wand": 200, "impl": 200, "entails": 200}

_TIGHT_PREFIX: list[tuple[str, str]] = [
    ("<pers>", "persistently"),
    ("<affine>", "affinely"),
    ("<absorb>", "absorbingly"),
    ("□", "intuitionistically"),
    ("■", "plainly"),
    ("▷", "later"),
    ("◇", "except0"),
]
_ANNOTATED = {"later", "persistently", "plainly"}

#: ``|={E}=>``, ``|={E1,E2}=>``, ``|={E}▷=>``, ``|={E1}[E2]▷=>`` (a ``^n`` power may follow).
_FUPD_PREFIX = re.compile(r"\|=\{(?P<e1>[^}]*)\}(?:\[(?P<e2>[^\]]*)\])?(?P<step>▷)?=>")
#: Infix modal wands: ``={E}=∗``, ``={E1,E2}=∗``, ``==∗``, ``={E}▷=∗``, ``={E1}[E2]▷=∗`` (+ ``^n``).
_FUPD_WAND = re.compile(r"=\{(?P<e1>[^}]*)\}(?:\[(?P<e2>[^\]]*)\])?(?P<step>▷)?=(?:∗|\*)")
_BUPD_PREFIX = "|==>"
_BUPD_WAND = "==∗"
_BINDER_SYMBOLS = {"∃": "exists", "∀": "forall"}
_STOP_CHARS = (")", "⌝", ",")
_OPERAND_STARTERS = ("⌜", "∃", "∀", "|==>", "|={")


class _GaveUp(Exception):
    pass


def _annotation(text: str, i: int, marks: str = "^?") -> tuple[str, int]:
    """A ``^n`` / ``?p`` annotation at ``i`` (``n`` bare or a balanced ``( ... )``); ``("", i)`` if none."""
    if i >= len(text) or text[i] not in marks:
        return "", i
    mark = text[i]
    j = i + 1
    while j < len(text) and text[j].isspace():
        j += 1
    if j < len(text) and text[j] == "(":
        k = _matching(text, j)
        return mark + text[j : k + 1], k + 1
    k = j
    while k < len(text) and not text[k].isspace() and text[k] not in ")⌝,":
        k += 1
    if k == j:
        return "", i
    return mark + text[j:k], k


class _Cursor:
    __slots__ = ("i", "s")

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

    def standalone(self, token: str) -> bool:
        """Is ``token`` at the cursor a connective, not part of a bigger notation?

        Iris prints binary connectives space-delimited; ``∗`` glued to the token before
        it (``l ↦∗ vs``, ``={E}=∗``) is a letter of that notation.
        """
        i = self.i
        if i > 0 and not self.s[i - 1].isspace():
            return False
        j = i + len(token)
        return j >= len(self.s) or self.s[j].isspace() or self.s[j] in "(⌜"


def parse_skeleton(prop: str) -> Skel:
    """Parse a printed Iris prop into its skeleton.  Total; unparsable -> one ``atom``."""
    text = " ".join(prop.split())
    if not text:
        return Skel("atom", text="")
    cur = _Cursor(text)
    try:
        node = _parse_expr(cur, 200)
    except (_GaveUp, RecursionError):
        # Total means total: a prop nested past the interpreter's stack is one atom,
        # not an exception escaping into the diff, the render or a tool call.
        return Skel("atom", text=text)
    if not cur.eof():
        return Skel("atom", text=text)
    return node


# --------------------------------------------------------------------------- parser


def _parse_expr(cur: _Cursor, level: int) -> Skel:
    left = _parse_operand(cur, level)
    while True:
        op = _match_binop(cur)
        if op is None:
            break
        token, kind, lvl, right_assoc, mask = op
        if lvl > level:
            break
        cur.i += len(token)
        rhs_level = _RIGHT_OPERAND_LEVEL.get(kind, lvl if right_assoc else lvl - 1)
        right = _parse_expr(cur, rhs_level)
        if mask is not None:  # a modal wand: P ={E}=∗ Q  ==  P -∗ |={E}=> Q
            right = _modal_node(mask, right)
            kind = "wand"
        left = _combine(kind, left, right)
    return left


def _combine(kind: str, left: Skel, right: Skel) -> Skel:
    # ∗/∧/∨ associate to the right, so `P ∗ (Q ∗ R)` *is* `P ∗ Q ∗ R`: flatten the right
    # spine into one n-ary node.  A left-nested `(P ∗ Q) ∗ R` is a different term and
    # stays nested -- IPM destructs the two differently.
    if right.kind == kind and kind in ("sep", "and", "or"):
        return Skel(kind, [left, *right.children])  # type: ignore[arg-type]
    return Skel(kind, [left, right])  # type: ignore[arg-type]


def _match_binop(cur: _Cursor) -> tuple[str, str, int, bool, dict[str, str | None] | None] | None:
    cur.skip_ws()
    if cur.i >= len(cur.s):
        return None
    if cur.i > 0 and not cur.s[cur.i - 1].isspace():
        return None
    if cur.s.startswith(_BUPD_WAND, cur.i) and cur.standalone(_BUPD_WAND):
        return _BUPD_WAND, "wand", 99, True, {"kind": "bupd"}
    m = _FUPD_WAND.match(cur.s, cur.i)
    if m:
        power, end = _annotation(cur.s, m.end(), "^")
        if end >= len(cur.s) or cur.s[end].isspace():
            mask = {"kind": "fupd", **m.groupdict(), "n": power[1:]}
            return cur.s[cur.i : end], "wand", 99, True, mask
    best: tuple[str, str, int, bool, None] | None = None
    for token, kind, lvl, right in _BINOPS:
        if cur.s.startswith(token, cur.i) and cur.standalone(token) and (best is None or len(token) > len(best[0])):
            best = (token, kind, lvl, right, None)
    return best


def _modal_node(mask: dict[str, str | None], body: Skel) -> Skel:
    if mask.get("kind") == "bupd":
        return Skel("bupd", [body])
    e1 = (mask.get("e1") or "").strip()
    e2 = (mask.get("e2") or "").strip()
    n = (mask.get("n") or "").strip()
    if mask.get("step"):
        binders = [e1, e2 or e1] + ([n] if n else [])
        return Skel("fupd_step", [body], binders=binders)
    return Skel("fupd", [body], binders=[e1])


def _parse_operand(cur: _Cursor, level: int) -> Skel:
    cur.skip_ws()
    if cur.i >= len(cur.s):
        raise _GaveUp
    for sym, kind in _BINDER_SYMBOLS.items():
        if cur.peek(sym):
            start = cur.i
            cur.i += len(sym)
            binders = _parse_binders(cur)
            if binders is None:
                cur.i = start
                break
            body = _parse_expr(cur, 200)
            return Skel(kind, [body], binders=binders)  # type: ignore[arg-type]
    m = _FUPD_PREFIX.match(cur.s, cur.i)
    if m:
        power, cur.i = _annotation(cur.s, m.end(), "^")
        return _modal_node({"kind": "fupd", **m.groupdict(), "n": power[1:]}, _parse_expr(cur, 200))
    if cur.eat(_BUPD_PREFIX):
        return Skel("bupd", [_parse_expr(cur, 200)])
    for token, kind in _TIGHT_PREFIX:
        if cur.peek(token):
            cur.i += len(token)
            annotation: list[str] = []
            if kind in _ANNOTATED:
                ann, cur.i = _annotation(cur.s, cur.i)
                if ann:
                    annotation = [ann]
            body = _parse_expr(cur, 20)
            return Skel(kind, [body], binders=annotation)  # type: ignore[arg-type]
    return _parse_atom(cur)


def _parse_binders(cur: _Cursor) -> list[str] | None:
    """``x y (z : T),`` -> the names, positioned after the comma; ``None`` if no comma."""
    start = cur.i
    depth = 0
    buf = ""
    while cur.i < len(cur.s):
        ch = cur.s[cur.i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
            if depth < 0:
                break
        elif ch == "," and depth == 0:
            cur.i += 1
            names = binder_names(buf)
            return names or None
        buf += ch
        cur.i += 1
    cur.i = start
    return None


def binder_names(text: str) -> list[str]:
    """Names bound by ``x y : T``, ``(x : T) (y : U)``, or bare ``x y``.

    The un-parenthesised ``∃ n : nat, ...`` form is what Iris prints; tokenising it
    naively yields ``nat`` as a second binder for a variable that does not exist.  Groups
    are scanned with balanced parentheses because binder types nest arbitrarily
    (``(stateI : state Λ → list (observation Λ) → iProp Σ)``).
    """
    names: list[str] = []
    bare = ""
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch in "({":
            names.extend(_group_head(bare, typed=False))
            bare = ""
            close = _matching(text, i)
            names.extend(_group_head(text[i + 1 : close]))
            i = close + 1
            continue
        if ch == ":" and not text.startswith("::", i):
            break  # bare form: everything after the top-level colon is the type
        bare += ch
        i += 1
    names.extend(_group_head(bare, typed=False))
    return names


def _matching(text: str, i: int) -> int:
    depth = 0
    for j in range(i, len(text)):
        if text[j] in "([{":
            depth += 1
        elif text[j] in ")]}":
            depth -= 1
            if depth == 0:
                return j
    return len(text)


def _group_head(content: str, *, typed: bool = True) -> list[str]:
    head = content
    if typed:
        depth = 0
        for i, ch in enumerate(content):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif ch == ":" and depth == 0 and not content.startswith("::", i):
                head = content[:i]
                break
    return [tok for tok in head.split() if tok not in {"_", ":"}]


def _parse_atom(cur: _Cursor) -> Skel:
    cur.skip_ws()
    if cur.i >= len(cur.s):
        raise _GaveUp
    if cur.eat("⌜"):
        inner = _take_balanced(cur, "⌜", "⌝")
        return Skel("pure", [Skel("atom", text=inner)], text=inner)
    if cur.s[cur.i] == "(":
        start = cur.i
        cur.i += 1
        try:
            node = _parse_expr(cur, 200)
            closed = cur.eat(")")
        except _GaveUp:
            closed = False
        if closed:
            cur.skip_ws()
            if cur.i >= len(cur.s) or cur.s[cur.i] in _STOP_CHARS or _match_binop(cur) is not None:
                if node.kind == "atom" and " " in node.text:
                    node = Skel("atom", text=f"({node.text})")  # `(P ≡ Q)`: the parens are content
                return node
        # Not a grouping: application, tuple, notation.  The whole balanced span --
        # plus whatever application tail follows it -- is one atom.
        cur.i = start
        text = _take_atom_span(cur)
        if not text:
            raise _GaveUp
        return Skel("atom", text=text)
    text = _take_atom_span(cur)
    if not text:
        raise _GaveUp
    return Skel("atom", text=text)


def _take_balanced(cur: _Cursor, open_tok: str, close_tok: str) -> str:
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


def _take_atom_span(cur: _Cursor) -> str:
    """An application / identifier up to the next top-level connective or terminator."""
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
        if depth == 0 and (ch in _STOP_CHARS or (cur.i > start and _at_connective(cur, start))):
            break
        cur.i += 1
    return cur.s[start : cur.i].strip()


def _at_connective(cur: _Cursor, start: int) -> bool:
    save = cur.i
    try:
        if _match_binop(cur) is not None:
            return True
    finally:
        cur.i = save
    if cur.i > start and cur.s[cur.i - 1].isspace():
        return any(cur.s.startswith(t, cur.i) for t in _OPERAND_STARTERS)
    return False


# --------------------------------------------------------------------------- render

_BINOP_TOKEN = {
    "sep": "∗", "and": "∧", "or": "∨", "wand": "-∗", "impl": "→", "iff": "↔",
    "wand_iff": "∗-∗", "entails": "⊢", "equiv": "⊣⊢",
}
_PREFIX_TOKEN = {
    "persistently": "<pers>", "affinely": "<affine>", "absorbingly": "<absorb>",
    "intuitionistically": "□", "plainly": "■", "later": "▷", "except0": "◇",
}
_RIGHT_ASSOC = {"sep", "and", "or", "wand", "impl", "entails"}


def render(node: Skel, level: int = 200) -> str:
    """Iris notation for ``node``, parenthesised when its level exceeds ``level``."""
    text = _render(node)
    if node.level > level and node.kind not in ("atom", "pure"):
        return f"({text})"
    return text


def _render(node: Skel) -> str:
    kind = node.kind
    if kind == "atom":
        return node.text
    if kind == "pure":
        inner = node.children[0].text if node.children else node.text
        return f"⌜{inner}⌝"
    if kind in _BINOP_TOKEN:
        lvl = node.level
        op = _BINOP_TOKEN[kind]
        if kind in _RIGHT_ASSOC:
            last_level = _RIGHT_OPERAND_LEVEL.get(kind, lvl)
            parts = [render(c, lvl - 1) for c in node.children[:-1]]
            parts.append(render(node.children[-1], last_level))
        else:
            parts = [render(c, lvl - 1) for c in node.children]
        return f" {op} ".join(parts)
    if kind in _PREFIX_TOKEN:
        ann = node.binders[0] if node.binders else ""
        return f"{_PREFIX_TOKEN[kind]}{ann} {render(node.children[0], 20)}"
    if kind == "bupd":
        return f"|==> {render(node.children[0], 200)}"
    if kind == "fupd":
        mask = node.binders[0] if node.binders and node.binders[0] else "⊤"
        return f"|={{{mask}}}=> {render(node.children[0], 200)}"
    if kind == "fupd_step":
        e1 = node.binders[0] if node.binders and node.binders[0] else "⊤"
        e2 = node.binders[1] if len(node.binders) > 1 and node.binders[1] else e1
        n = node.binders[2] if len(node.binders) > 2 else ""
        head = f"|={{{e1}}}▷=>" if e2 == e1 else f"|={{{e1}}}[{e2}]▷=>"
        if n:
            head += f"^{n}"
        return f"{head} {render(node.children[0], 200)}"
    if kind in BINDERS:
        sym = "∃" if kind == "exists" else "∀"
        names = " ".join(node.binders) or "_"
        return f"{sym} {names}, {render(node.children[0], 200)}"
    raise AssertionError(kind)
