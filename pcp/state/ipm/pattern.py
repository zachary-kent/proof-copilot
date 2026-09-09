"""Intro patterns: grammar, compiler and aligner (PLAN.md 7).

Complex intro patterns are a known agent choke point, and they are entirely mechanical
given the prop's skeleton.  So no model hand-assembles a nested pattern string:
:func:`compile_auto` / :func:`compile_spec` synthesise it, and :func:`align` walks a
pattern against a skeleton and reports the *first* mismatch -- by construction on
every failing pattern-bearing tactic.

The grammar mirrors ``iris/proofmode/intro_patterns.v`` (Iris 4.5) token for token, and
the aligner mirrors ``_iDestructHypGo``, whose rules were verified against Rocq:

* conjunction and disjunction patterns are **binary**: ``[a b c]`` fails with "has too
  many conjuncts", ``[a]`` with "has just a single conjunct"; nest (``[a [b c]]``) or
  use the ``(a & b & c)`` sugar;
* ``%``/``#``/``>``/``-#`` are markers; a bare ``%`` is an anonymous pure intro and
  ``[% H]`` is *two* patterns;
* ``//``, ``*``, ``**``, ``!>``, ``!%`` are ``iIntros``-level actions and are not
  hypothesis patterns at all.

Honesty rule (PLAN.md 4.4): the aligner only reports a mismatch it is sure of.  An
``atom`` may hide a connective behind project notation, so anything is accepted on it.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass, field
from typing import Any, Literal

from pcp.errors import UsageError
from pcp.state.ipm.skeleton import BINDERS, BINOPS, Skel, parse_skeleton, peel

PatKind = Literal[
    "name", "fresh", "drop", "frame", "list", "or", "empty", "rewrite", "clear",
    "pure_intro", "modal_intro", "simpl", "done", "forall", "all",
]
#: Patterns that act on the goal rather than destructure a hypothesis.
ACTIONS = frozenset({"pure_intro", "modal_intro", "simpl", "done", "forall", "all", "clear"})
_ACTION_TEXT = {"pure_intro": "!%", "modal_intro": "!>", "simpl": "/=", "done": "//", "forall": "*", "all": "**"}


@dataclass
class Pat:
    kind: PatKind
    name: str = ""
    children: list[Pat] = field(default_factory=list)
    #: ``%`` -- pure intro (only meaningful on ``name``/``fresh``).
    pure: bool = False
    #: ``#`` -- into the intuitionistic context.
    intuit: bool = False
    #: ``>`` -- eliminate a modality on the way in.
    modal: bool = False
    #: ``-#`` -- back into the spatial context.
    spatial: bool = False
    #: A ``(a & b & c)`` group (rendered as such).
    amp: bool = False
    #: Several patterns in one disjunct, ``[a b|c]`` -- parses, IPM rejects it at run time.
    bare: bool = False

    def render(self) -> str:
        prefix = ("-#" if self.spatial else "") + ("#" if self.intuit else "") + (">" if self.modal else "")
        k = self.kind
        if k == "name":
            return prefix + ("%" if self.pure else "") + self.name
        if k == "fresh":
            return prefix + ("%" if self.pure else "?")
        if k == "drop":
            return prefix + "_"
        if k == "frame":
            return prefix + "$"
        if k == "empty":
            return prefix + "[]"
        if k == "rewrite":
            return prefix + (self.name or "->")
        if k == "clear":
            return prefix + "{" + self.name + "}"
        if k in _ACTION_TEXT:
            return prefix + _ACTION_TEXT[k]
        if k == "list":
            if self.amp:
                return prefix + "(" + " & ".join(c.render() for c in self.spine()) + ")"
            inner = " ".join(c.render() for c in self.children)
            return prefix + (inner if self.bare else f"[{inner}]")
        if k == "or":
            return prefix + "[" + "|".join(c.render() for c in self.children) + "]"
        raise AssertionError(k)

    def spine(self) -> list[Pat]:
        """The right spine of nested binary conjunctions: ``[a [b c]]`` -> ``a, b, c``."""
        out: list[Pat] = []
        node = self
        while node.kind == "list" and len(node.children) == 2 and (node is self or not node.amp):
            out.append(node.children[0])
            node = node.children[1]
        out.append(node)
        return out

    def tree(self, indent: int = 0) -> str:
        pad = "  " * indent
        mark = "".join(m for m, on in (("-#", self.spatial), ("#", self.intuit), (">", self.modal), ("%", self.pure)) if on)
        label = {"list": "conjunction", "or": "disjunction"}.get(self.kind, self.kind)
        head = f"{pad}{label}{' ' + mark if mark else ''}"
        if self.kind in ("name", "rewrite", "clear"):
            head += f" {self.name}"
        return "\n".join([head, *(c.tree(indent + 1) for c in self.children)])

    @property
    def destructs(self) -> bool:
        return self.kind in ("list", "or", "empty")


# ------------------------------------------------------------------------ tokens


class PatternSyntaxError(ValueError):
    """The text is not an IPM intro pattern (IPM's own ``intro_pat.parse`` would fail)."""


@dataclass(frozen=True)
class _Tok:
    kind: str
    text: str = ""


_SINGLE = {"?": "anon", "$": "frame", "[": "lbrack", "]": "rbrack", "|": "bar", "(": "lparen", ")": "rparen",
           "&": "amp", "{": "lbrace", "}": "rbrace", "#": "intuit", ">": "modal", "∗": "sep"}
_SPECIAL = set(_SINGLE) | {"%", "!", "/", "*", "-", "<"}


def tokenize(text: str) -> list[_Tok]:
    """``iris/proofmode/tokens.v``, token for token."""
    out: list[_Tok] = []
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch.isspace():
            i += 1
            continue
        two = text[i : i + 2]
        three = text[i : i + 3]
        if three == "//=":
            out += [_Tok("simpl"), _Tok("done")]
            i += 3
        elif two in ("!%", "!#", "!>"):
            out.append(_Tok({"!%": "pure_intro", "!#": "modal_intro", "!>": "modal_intro"}[two]))
            i += 2
        elif two == "//":
            out.append(_Tok("done"))
            i += 2
        elif two == "/=":
            out.append(_Tok("simpl"))
            i += 2
        elif two == "**":
            out.append(_Tok("all"))
            i += 2
        elif ch == "*":
            out.append(_Tok("forall"))
            i += 1
        elif two == "->" or two == "<-":
            out.append(_Tok("arrow", two))
            i += 2
        elif ch == "-":
            out.append(_Tok("minus"))
            i += 1
        elif ch == "%":
            j = i + 1
            while j < n and not text[j].isspace() and text[j] not in _SPECIAL:
                j += 1
            out.append(_Tok("pure", text[i + 1 : j]))
            i = j
        elif ch in _SINGLE:
            out.append(_Tok(_SINGLE[ch]))
            i += 1
        else:
            j = i
            while j < n and not text[j].isspace() and text[j] not in _SPECIAL:
                j += 1
            if j == i:  # a lone `!` or `<` or `/`
                j = i + 1
            out.append(_Tok("name", text[i:j]))
            i = j
    return out


# ----------------------------------------------------------------------- parsing


def parse_pattern(text: str) -> Pat:
    """Exactly one pattern.  Raises :class:`PatternSyntaxError` only when IPM would."""
    pats = parse_patterns(text)
    if len(pats) != 1:
        raise PatternSyntaxError(f"expected exactly one pattern, got {len(pats)}: {text!r}")
    return pats[0]


def parse_patterns(text: str) -> list[Pat]:
    """A whitespace-separated sequence, as ``iIntros`` takes."""
    toks = tokenize(text)
    try:
        pats, i = _parse_seq(toks, 0, closers=())
    except RecursionError:
        # `[[[[...` a thousand deep is not a pattern anyone wrote; it must still be a
        # *syntax* error, which `diagnose` reports, not a crash of the tool call.
        raise PatternSyntaxError(f"pattern nested too deeply: {text[:40]!r}…") from None
    if i != len(toks):
        raise PatternSyntaxError(f"unexpected {toks[i].text or toks[i].kind!r} in pattern {text!r}")
    return pats


def _parse_seq(toks: list[_Tok], i: int, *, closers: tuple[str, ...]) -> tuple[list[Pat], int]:
    out: list[Pat] = []
    while i < len(toks) and toks[i].kind not in closers:
        pat, i = _parse_one(toks, i)
        out.append(pat)
    return out, i


def _parse_one(toks: list[_Tok], i: int) -> tuple[Pat, int]:
    if i >= len(toks):
        raise PatternSyntaxError("unexpected end of pattern")
    t = toks[i]
    k = t.kind
    if k in ("intuit", "modal"):
        if i + 1 >= len(toks) or toks[i + 1].kind in ("rbrack", "rparen", "bar", "amp", "rbrace"):
            sym = "#" if k == "intuit" else ">"
            raise PatternSyntaxError(f"`{sym}` must be followed by a pattern")
        pat, i = _parse_one(toks, i + 1)
        if k == "intuit":
            pat.intuit = True
        else:
            pat.modal = True
        return pat, i
    if k == "minus":
        if i + 1 < len(toks) and toks[i + 1].kind == "intuit":
            pat, i = _parse_one(toks, i + 2)
            pat.spatial = True
            return pat, i
        raise PatternSyntaxError("`-` is only legal as `-#pat` (move back to the spatial context)")
    if k == "pure":
        return (Pat("name", t.text, pure=True) if t.text else Pat("fresh", pure=True)), i + 1
    if k == "name":
        if t.text == "_":
            return Pat("drop"), i + 1
        if t.text.isdigit():
            raise PatternSyntaxError(f"{t.text!r} is a number, not an intro pattern")
        return Pat("name", t.text), i + 1
    if k == "anon":
        return Pat("fresh"), i + 1
    if k == "frame":
        return Pat("frame"), i + 1
    if k == "arrow":
        return Pat("rewrite", t.text), i + 1
    if k in ("pure_intro", "modal_intro", "simpl", "done", "forall", "all"):
        return Pat(k), i + 1  # type: ignore[arg-type]
    if k == "lbrack":
        return _parse_list(toks, i + 1)
    if k == "lparen":
        return _parse_group(toks, i + 1)
    if k == "lbrace":
        return _parse_clear(toks, i + 1)
    raise PatternSyntaxError(f"unexpected {t.text or t.kind!r} in pattern")


def _parse_list(toks: list[_Tok], i: int) -> tuple[Pat, int]:
    parts: list[list[Pat]] = []
    while True:
        seq, i = _parse_seq(toks, i, closers=("rbrack", "bar"))
        parts.append(seq)
        if i >= len(toks):
            raise PatternSyntaxError("unbalanced `[` in pattern")
        if toks[i].kind == "rbrack":
            i += 1
            break
        i += 1  # the bar
    if len(parts) == 1:
        seq = parts[0]
        return (Pat("empty") if not seq else Pat("list", children=seq)), i

    def disjunct(seq: list[Pat]) -> Pat:
        if not seq:
            return Pat("empty")
        if len(seq) == 1:
            return seq[0]
        return Pat("list", children=seq, bare=True)

    return Pat("or", children=[disjunct(p) for p in parts]), i


def _parse_group(toks: list[_Tok], i: int) -> tuple[Pat, int]:
    items: list[Pat] = []
    while True:
        seq, i = _parse_seq(toks, i, closers=("rparen", "amp"))
        if len(seq) > 1:
            raise PatternSyntaxError("each `&`-separated component must be exactly one pattern")
        if seq:
            items.append(seq[0])
        elif items or (i < len(toks) and toks[i].kind == "amp"):
            raise PatternSyntaxError("empty component in `( ... & ... )`")
        if i >= len(toks):
            raise PatternSyntaxError("unbalanced `(` in pattern")
        if toks[i].kind == "rparen":
            i += 1
            break
        i += 1  # the ampersand
    if not items:
        return Pat("empty"), i
    pat = conj(items)
    pat.amp = len(items) > 1
    return pat, i


def _parse_clear(toks: list[_Tok], i: int) -> tuple[Pat, int]:
    items: list[str] = []
    while i < len(toks) and toks[i].kind != "rbrace":
        t = toks[i]
        if t.kind == "frame" and i + 1 < len(toks) and toks[i + 1].kind in ("name", "pure", "intuit", "sep"):
            nxt = toks[i + 1]
            items.append("$" + {"pure": "%", "intuit": "#", "sep": "∗"}.get(nxt.kind, nxt.text))
            i += 2
        elif t.kind == "name":
            items.append(t.text)
            i += 1
        elif t.kind == "pure" and not t.text:
            items.append("%")
            i += 1
        elif t.kind in ("intuit", "sep"):
            items.append("#" if t.kind == "intuit" else "∗")
            i += 1
        else:
            raise PatternSyntaxError(f"unexpected {t.text or t.kind!r} inside a clear pattern `{{...}}`")
    if i >= len(toks):
        raise PatternSyntaxError("unbalanced `{` in pattern")
    return Pat("clear", " ".join(items)), i + 1


def conj(items: list[Pat]) -> Pat:
    """IPM's ``big_conj``: a right-nested binary conjunction of ``items``."""
    if not items:
        return Pat("empty")
    if len(items) == 1:
        return Pat("list", children=[items[0]])
    if len(items) == 2:
        return Pat("list", children=list(items))
    return Pat("list", children=[items[0], conj(items[1:])])


def disj(items: list[Pat]) -> Pat:
    """A right-nested binary disjunction ``[a|[b|c]]``."""
    if len(items) <= 2:
        return Pat("or", children=list(items))
    return Pat("or", children=[items[0], disj(items[1:])])


# ----------------------------------------------------------------------- compile


@dataclass
class Destructuring:
    """A compiled ``iDestruct`` / ``iIntros``: binders + pattern + the tactic text."""

    binders: list[str]
    pattern: Pat
    #: Names that land in the Coq (pure) context (``%`` markers and witnesses).
    pure_names: list[str] = field(default_factory=list)

    @property
    def pattern_text(self) -> str:
        return self.pattern.render()

    def idestruct(self, hyp: str) -> str:
        """A complete tactic *sentence*, terminator included -- downstream feeds it to Rocq."""
        binder = f" ({' '.join(self.binders)})" if self.binders else ""
        return f'iDestruct "{hyp}" as{binder} "{self.pattern_text}".'

    def iintros(self) -> str:
        binder = f" ({' '.join(self.binders)})" if self.binders else ""
        return f'iIntros{binder} "{self.pattern_text}".'


class _Namer:
    """Fresh names that avoid the live context (v1 emitted ``H1`` next to an existing ``H1``)."""

    def __init__(self, base: str, taken: Iterable[str]) -> None:
        self.base = base.strip('"') or "H"
        self.used: set[str] = set(taken)

    def next(self, hint: str = "") -> str:
        stem = hint or self.base
        n = 1
        while f"{stem}{n}" in self.used:
            n += 1
        name = f"{stem}{n}"
        self.used.add(name)
        return name

    def witness(self, preferred: str) -> str:
        if preferred and preferred not in self.used:
            self.used.add(preferred)
            return preferred
        return self.next(preferred or "x")


def compile_auto(skel: Skel, base: str = "H", *, taken: Iterable[str] = ()) -> Destructuring:
    """Synthesise a destructuring from a skeleton.

    Leading ``∃`` become ``iDestruct`` binders; ``∗``/``∧`` a (binary, right-nested)
    conjunction; ``∨`` a disjunction; ``⌜⌝`` a ``%`` intro; ``□``/``<pers>`` a ``#``;
    ``fupd``/``bupd`` a ``>``; ``▷``/``◇``/``<affine>``/``<absorb>`` are descended silently.
    Generated names avoid ``taken`` (pass every hypothesis id in the context).
    """
    namer = _Namer(base, taken)
    binders: list[str] = []
    node = skel
    while True:
        node = node.strip_transparent()
        if node.kind == "exists" and node.children:
            binders.extend(namer.witness(b) for b in (node.binders or [""]))
            node = node.children[0]
            continue
        break
    pure_names: list[str] = []
    pat = _compile_node(node, namer, pure_names)
    return Destructuring(binders=binders, pattern=pat, pure_names=pure_names)


def _compile_node(skel: Skel, namer: _Namer, pure_names: list[str]) -> Pat:
    markers, core = peel(skel)
    if core.kind == "pure":
        name = namer.next("H")
        pure_names.append(name)
        pat = Pat("name", name, pure=True)
    elif core.kind in ("sep", "and"):
        pat = conj([_compile_node(c, namer, pure_names) for c in core.children])
    elif core.kind == "or":
        pat = disj([_compile_node(c, namer, pure_names) for c in core.children])
    elif core.kind == "exists" and core.children:
        witnesses = [namer.witness(b) for b in (core.binders or [""])]
        pure_names.extend(witnesses)
        pat = _compile_node(core.children[0], namer, pure_names)
        for w in reversed(witnesses):
            pat = Pat("list", children=[Pat("name", w, pure=True), pat])
    else:
        pat = Pat("name", namer.next())
    pat.intuit = pat.intuit or markers.intuit
    pat.modal = pat.modal or markers.update
    return pat


@dataclass
class DestructSpec:
    """A structured destructuring request: intent, not syntax (PLAN.md 7).

    ``{"names": ["Hl", "Hn"], "pure": ["Hn"]}`` on ``l ↦ v ∗ ⌜n = 3⌝`` compiles to
    ``[Hl %Hn]``; a nested ``{"names": [...]}`` entry follows the corresponding
    sub-skeleton (so a nested group on a disjunction compiles to ``[a|b]``).
    """

    names: list[str | DestructSpec | dict[str, Any]] = field(default_factory=list)
    pure: list[str] = field(default_factory=list)
    intuit: list[str] = field(default_factory=list)
    binders: list[str] = field(default_factory=list)

    _KEYS = ("names", "pure", "intuit", "binders")

    @classmethod
    def from_json(cls, d: dict[str, Any]) -> DestructSpec:
        unknown = sorted(set(d) - set(cls._KEYS))
        if unknown:
            raise UsageError(f"unknown destruct spec key(s) {unknown}; expected {list(cls._KEYS)}")
        names = d.get("names") or []
        if not isinstance(names, list):
            raise UsageError("destruct spec `names` must be a list")
        out = cls(
            names=[cls.from_json(n) if isinstance(n, dict) else n for n in names],
            pure=list(d.get("pure") or []),
            intuit=list(d.get("intuit") or []),
            binders=list(d.get("binders") or []),
        )
        for n in out.names:
            if not isinstance(n, str | DestructSpec):
                raise UsageError(f"destruct spec names must be strings or nested specs, not {n!r}")
        return out

    def to_json(self) -> dict[str, Any]:
        return {
            "names": [n.to_json() if isinstance(n, DestructSpec) else n for n in self.names],
            "pure": list(self.pure),
            "intuit": list(self.intuit),
            "binders": list(self.binders),
        }


def compile_spec(spec: DestructSpec | dict[str, Any], skel: Skel | str) -> Destructuring:
    """Compile a spec against the skeleton it will be applied to."""
    if isinstance(spec, dict):
        spec = DestructSpec.from_json(spec)
    node = parse_skeleton(skel) if isinstance(skel, str) else skel
    body, shortfall = _peel_binders(node, len(spec.binders))
    if shortfall:
        raise UsageError(
            f"{len(spec.binders)} binders were given but the hypothesis has only "
            f"{len(spec.binders) - shortfall} to introduce"
        )
    pure_names = list(spec.binders)
    pat = _compile_entries(spec, body, pure_names, top=True)
    return Destructuring(binders=list(spec.binders), pattern=pat, pure_names=pure_names)


def _compile_entries(spec: DestructSpec, skel: Skel, pure_names: list[str], *, top: bool) -> Pat:
    markers, core = peel(skel)
    entries = spec.names

    def leaf(name: str) -> Pat:
        if name in spec.pure:
            pure_names.append(name)
        return Pat("name", name, pure=name in spec.pure, intuit=name in spec.intuit)

    def entry(e: str | DestructSpec | dict[str, Any], sub: Skel) -> Pat:
        if isinstance(e, DestructSpec):
            return _compile_entries(e, sub, pure_names, top=False)
        if isinstance(e, dict):
            return _compile_entries(DestructSpec.from_json(e), sub, pure_names, top=False)
        return leaf(e)

    if not entries:
        if _is_false(core):
            pat = Pat("empty")
        else:
            raise UsageError("an empty `names` list eliminates False, but the hypothesis is " + describe_kind(core))
    elif core.kind == "exists" and core.children:
        first = entries[0]
        if not isinstance(first, str):
            raise UsageError("the first name for an existential is its witness and must be a string")
        pure_names.append(first)
        rest = DestructSpec(names=list(entries[1:]), pure=spec.pure, intuit=spec.intuit)
        residual = Skel("exists", core.children, binders=core.binders[1:]) if len(core.binders) > 1 else core.children[0]
        inner = _compile_entries(rest, residual, pure_names, top=False) if rest.names else Pat("fresh")
        pat = Pat("list", children=[Pat("name", first, pure=True), inner])
    elif core.kind in ("sep", "and", "or") and len(entries) > 1:
        kids = core.children
        if len(entries) > len(kids):
            raise UsageError(f"{len(entries)} names were given but the hypothesis has {len(kids)} {describe_kind(core)} parts")
        parts: list[Pat] = []
        for idx, e in enumerate(entries):
            last = idx == len(entries) - 1
            sub = Skel(core.kind, kids[idx:]) if last and len(kids) - idx > 1 else kids[idx]
            parts.append(entry(e, sub))
        pat = disj(parts) if core.kind == "or" else conj(parts)
    elif len(entries) == 1:
        pat = entry(entries[0], core)
    else:
        # No visible connective (an atom may hide one behind notation): trust the caller.
        pat = conj([entry(e, core) for e in entries])
    pat.intuit = pat.intuit or markers.intuit
    pat.modal = pat.modal or markers.update
    return pat


def _is_false(node: Skel) -> bool:
    if node.kind == "pure":
        return (node.children[0].text if node.children else node.text).strip() == "False"
    return node.kind == "atom" and node.text.strip() in ("False", "⌜False⌝")


# ------------------------------------------------------------------------- align


@dataclass
class Mismatch:
    path: str
    reason: str
    pattern_at: str
    prop_at: str
    hint: str = ""


@dataclass
class Alignment:
    ok: bool
    pattern: Pat
    skel: Skel
    mismatch: Mismatch | None = None
    suggestion: str = ""

    def render(self) -> str:
        return render_alignment(self)


def render_alignment(a: Alignment) -> str:
    lines: list[str] = []
    if a.ok:
        lines.append("pattern aligns with the hypothesis' structure")
    else:
        m = a.mismatch
        assert m is not None
        lines.append(f"pattern/prop mismatch at {m.path}: {m.reason}")
        lines.append(f"  pattern here : {m.pattern_at}")
        lines.append(f"  prop here    : {m.prop_at}")
        if m.hint:
            lines.append(f"  hint         : {m.hint}")
    lines += ["", "prop skeleton:", a.skel.render(1), "", "pattern tree:", a.pattern.tree(1)]
    if a.suggestion:
        lines += ["", f"a pattern that fits: {a.suggestion}"]
    return "\n".join(lines)


_KIND_WORD = {
    "sep": "a separating conjunction (∗)",
    "and": "a conjunction (∧)",
    "or": "a disjunction (∨)",
    "exists": "an existential (∃)",
    "forall": "a universal (∀); destructing it is not possible, specialize it",
    "pure": "a pure fact (⌜⌝)",
    "wand": "a wand (−∗); destructing it is not possible, specialize or apply it",
    "impl": "an implication (→); destructing it is not possible, specialize it",
    "iff": "a bi-implication (↔)",
    "wand_iff": "a bi-wand (∗-∗)",
    "entails": "an entailment (⊢)",
    "equiv": "an equivalence (⊣⊢)",
    "atom": "an opaque proposition",
}


def describe_kind(node: Skel) -> str:
    return _KIND_WORD.get(node.kind, node.kind)


def align(pattern: Pat | str, skel: Skel | str, *, binders: list[str] | None = None) -> Alignment:
    """Align a pattern against a skeleton; report the first mismatch point.

    ``binders`` are the names of the ``iDestruct "H" as (x y) "..."`` form: they consume
    that many leading ``∃``/``∀`` binders before the pattern is matched.  Never raises
    for a syntactically valid pattern.
    """
    pat = parse_pattern(pattern) if isinstance(pattern, str) else pattern
    node = parse_skeleton(skel) if isinstance(skel, str) else skel
    body, unconsumed = _peel_binders(node, len(binders or []))
    if unconsumed:
        given = len(binders or [])
        return Alignment(
            ok=False,
            pattern=pat,
            skel=node,
            mismatch=Mismatch(
                "root",
                f"{given} binders were given but the hypothesis has {given - unconsumed} to introduce",
                " ".join(binders or []),
                describe_kind(body),
                hint="drop the extra binder names",
            ),
        )
    mismatch = _align(pat, body, "root")
    suggestion = compile_auto(body).pattern_text if mismatch is not None else ""
    return Alignment(ok=mismatch is None, pattern=pat, skel=body, mismatch=mismatch, suggestion=suggestion)


def _peel_binders(skel: Skel, count: int) -> tuple[Skel, int]:
    """Consume ``count`` quantified variables; return the body and any shortfall."""
    node = skel
    while count > 0:
        node = node.strip_transparent()
        if node.kind not in BINDERS or not node.children:
            return node, count
        take = min(len(node.binders) or 1, count)
        if take < (len(node.binders) or 1):
            return Skel(node.kind, node.children, binders=node.binders[take:]), 0
        count -= take
        node = node.children[0]
    return node, 0


def _residual(node: Skel, start: int) -> Skel:
    rest = node.children[start:]
    return rest[0] if len(rest) == 1 else Skel(node.kind, rest)


def _align(pat: Pat, skel: Skel, path: str) -> Mismatch | None:
    markers, core = peel(skel)
    definite = core.kind in BINOPS or core.kind in BINDERS or core.kind == "pure"
    if pat.modal and not (markers.update or markers.laters or markers.except0) and definite:
        return Mismatch(
            path, "the pattern eliminates a modality with `>`, but the hypothesis is not under one",
            pat.render(), describe_kind(core), hint="drop the `>`",
        )
    if pat.destructs and markers.update and not pat.modal:
        return Mismatch(
            path, "the hypothesis is under an update modality, but the pattern does not eliminate it",
            pat.render(), "an update modality", hint="prefix the pattern with `>` (or use iMod) before destructing",
        )
    if pat.kind in ACTIONS or pat.kind in ("drop", "frame"):
        return None
    if pat.kind in ("name", "fresh", "rewrite"):
        if not pat.pure and pat.kind != "rewrite":
            return None
        return _align_pure(pat, core, path)
    if pat.kind == "empty":
        if core.kind == "atom" or _is_false(core):
            return None
        return Mismatch(
            path, "`[]` eliminates False, but the hypothesis is not False", pat.render(), describe_kind(core),
            hint="name the hypothesis instead of eliminating it",
        )
    if pat.kind == "or":
        return _align_or(pat, core, path)
    return _align_list(pat, core, path)


def _align_pure(pat: Pat, core: Skel, path: str) -> Mismatch | None:
    verdict = _pure_compatible(core)
    if verdict is not False:
        return None
    if core.kind == "exists":
        return Mismatch(
            path, "a `%` intro needs a pure fact, but the hypothesis is an existential",
            pat.render(), describe_kind(core), hint="write [%x H] to name the witness and keep the body",
        )
    return Mismatch(
        path, "a `%`/rewrite intro needs a pure fact, but the hypothesis is not pure",
        pat.render(), describe_kind(core), hint="drop the `%` and name the hypothesis",
    )


def _pure_compatible(node: Skel) -> bool | None:
    """``True``: pure; ``False``: definitely not; ``None``: unknown (an atom may be ``IntoPure``)."""
    kind = node.kind
    if kind == "pure":
        return True
    if kind == "atom":
        return None
    if kind in ("exists", "forall"):
        return False if kind == "exists" else _pure_compatible(node.children[0])
    if kind in ("sep", "and", "or", "wand", "impl", "iff", "wand_iff"):
        verdicts = [_pure_compatible(c) for c in node.children]
        if any(v is False for v in verdicts):
            return False
        return True if all(v is True for v in verdicts) else None
    if len(node.children) == 1:
        return _pure_compatible(node.children[0])
    return None


def _align_or(pat: Pat, core: Skel, path: str) -> Mismatch | None:
    if len(pat.children) > 2:
        return Mismatch(
            path, "IPM disjunction patterns are binary: this one has too many disjuncts",
            pat.render(), describe_kind(core), hint="nest them: [a|[b|c]]",
        )
    if core.kind == "atom":
        return _align_bare(pat, path)
    if core.kind == "pure":
        return _align_bare(pat, path) or _align_pure_inner(pat, core, path, ("or",))
    if core.kind != "or":
        return Mismatch(
            path, "the pattern splits a disjunction, but the hypothesis is not one",
            pat.render(), describe_kind(core), hint="use [p1 p2] (spaces) for a conjunction, [p1|p2] (bars) for a disjunction",
        )
    for i, child in enumerate(pat.children):
        sub = core.children[i] if i < len(pat.children) - 1 else _residual(core, i)
        m = _align_bare(child, f"{path}.{i + 1}") or _align(child, sub, f"{path}.{i + 1}")
        if m is not None:
            return m
    return None


def _align_pure_inner(pat: Pat, core: Skel, path: str, kinds: tuple[str, ...]) -> Mismatch | None:
    """``⌜φ ∧ ψ⌝`` / ``⌜φ ∨ ψ⌝`` / ``⌜∃ x, φ⌝`` split through the ``IntoAnd``/``IntoOr``/
    ``IntoExist`` pure instances; a pure fact with nothing of the kind inside does not."""
    inner = parse_skeleton(core.children[0].text if core.children else core.text)
    if inner.kind in kinds:
        return None
    return Mismatch(
        path, "the pattern destructs, but the pure fact has no connective of that shape inside ⌜ ⌝",
        pat.render(), describe_kind(core), hint="introduce it with %H and destruct it in the Coq context",
    )


def _align_bare(pat: Pat, path: str) -> Mismatch | None:
    if pat.kind == "list" and pat.bare:
        return Mismatch(
            path, "a disjunct has multiple patterns", pat.render(), "one disjunct",
            hint="bracket the sub-patterns of that disjunct: [[a b]|c]",
        )
    if pat.kind == "or":
        for i, child in enumerate(pat.children):
            m = _align_bare(child, f"{path}.{i + 1}")
            if m is not None:
                return m
    return None


def _align_list(pat: Pat, core: Skel, path: str) -> Mismatch | None:
    n = len(pat.children)
    if pat.bare:
        return _align_bare(pat, path)
    if n == 1:
        return Mismatch(
            path, "a single-element list is not a pattern (IPM: \"has just a single conjunct\")",
            pat.render(), describe_kind(core), hint=f"write {pat.children[0].render()} without the brackets",
        )
    if n > 2:
        spine = " & ".join(c.render() for c in pat.children)
        return Mismatch(
            path, "IPM conjunction patterns are binary: this one has too many conjuncts",
            pat.render(), describe_kind(core), hint=f"nest them, e.g. {conj(pat.children).render()}, or write ({spine})",
        )
    first, second = pat.children
    if core.kind == "exists" and core.children:
        if not (first.kind in ("name", "fresh") and first.pure):
            return Mismatch(
                path, "the hypothesis is an existential; its witness must be introduced first",
                pat.render(), describe_kind(core),
                hint='use iDestruct "H" as (x) "..." for the witness, or a leading `%x` in the pattern',
            )
        rest = Skel("exists", core.children, binders=core.binders[1:]) if len(core.binders) > 1 else core.children[0]
        return _align(second, rest, f"{path}.∃-body")
    if core.kind in ("sep", "and"):
        # Right-associative: `[H1 H2]` on `P ∗ Q ∗ R` gives `H2 : Q ∗ R`.
        m = _align(first, core.children[0], f"{path}.1")
        if m is not None:
            return m
        return _align(second, _residual(core, 1), f"{path}.2")
    if core.kind == "atom":
        return None  # notation may hide a connective: unknown, accepted
    if core.kind == "pure":
        return _align_pure_inner(pat, core, path, ("and", "sep", "exists"))
    if core.kind == "or":
        return Mismatch(
            path, "the pattern splits a conjunction, but the hypothesis is a disjunction",
            pat.render(), describe_kind(core), hint="separate the sub-patterns with | rather than spaces",
        )
    return Mismatch(
        path, "the pattern destructs, but the hypothesis has no top-level connective to destruct",
        pat.render(), describe_kind(core), hint="name it instead of destructing it",
    )
