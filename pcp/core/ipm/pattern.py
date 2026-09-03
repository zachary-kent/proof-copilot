"""Intro-pattern compiler and aligner (PLAN.md 7).

Complex intro patterns are a known agent choke point, and they are *entirely
mechanical* given the prop's connective skeleton.  So no model ever hand-assembles a
nested pattern string:

* ``compile`` synthesizes the pattern (and the ``iDestruct`` binder list) from the
  skeleton, either automatically or from a structured spec;
* ``align`` walks a pattern against a skeleton and reports the exact first mismatch.

The aligner is not opt-in.  ``proof_step`` runs it automatically on any failing
pattern-bearing tactic, so the agent sees the object and the pattern side by side
every time by construction, not by discipline.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Literal

from pcp.core.ipm.skeleton import TRANSPARENT, UPDATE, Skel, parse_skeleton

PatKind = Literal["name", "list", "or", "drop", "fresh", "empty", "rewrite"]


@dataclass
class Pat:
    kind: PatKind
    name: str = ""
    children: list["Pat"] = field(default_factory=list)
    #: `%` -- introduce into the pure Coq context
    pure: bool = False
    #: `#` -- introduce into the intuitionistic context
    intuit: bool = False
    #: `>` -- eliminate a modality on the way in (`iMod`)
    modal: bool = False

    def render(self) -> str:
        prefix = ("%" if self.pure else "") + ("#" if self.intuit else "") + (">" if self.modal else "")
        if self.kind == "name":
            return prefix + self.name
        if self.kind == "drop":
            return prefix + "_"
        if self.kind == "fresh":
            return prefix + "?"
        if self.kind == "empty":
            return prefix + "[]"
        if self.kind == "rewrite":
            return prefix + (self.name or "->")
        if self.kind == "list":
            return prefix + "[" + " ".join(c.render() for c in self.children) + "]"
        if self.kind == "or":
            return prefix + "[" + "|".join(c.render() for c in self.children) + "]"
        raise AssertionError(self.kind)

    def tree(self, indent: int = 0) -> str:
        pad = "  " * indent
        mark = "".join(m for m, on in (("%", self.pure), ("#", self.intuit), (">", self.modal)) if on)
        label = {"list": "conjunction", "or": "disjunction"}.get(self.kind, self.kind)
        head = f"{pad}{label}{' ' + mark if mark else ''}"
        if self.kind in ("name", "rewrite"):
            head += f" {self.name}"
        lines = [head]
        for c in self.children:
            lines.append(c.tree(indent + 1))
        return "\n".join(lines)


# --------------------------------------------------------------------------- parse

class PatternSyntaxError(ValueError):
    pass


def parse_pattern(text: str) -> Pat:
    """Parse an IPM intro pattern.  Raises ``PatternSyntaxError`` on malformed input."""
    pats, rest = _parse_seq(text.strip())
    if rest.strip():
        raise PatternSyntaxError(f"trailing input after pattern: {rest.strip()!r}")
    if len(pats) != 1:
        raise PatternSyntaxError(f"expected exactly one pattern, got {len(pats)}")
    return pats[0]


def parse_patterns(text: str) -> list[Pat]:
    """Parse a whitespace-separated sequence, as ``iIntros`` takes."""
    pats, rest = _parse_seq(text.strip())
    if rest.strip():
        raise PatternSyntaxError(f"trailing input after patterns: {rest.strip()!r}")
    return pats


def _parse_seq(s: str, stop: str = "") -> tuple[list[Pat], str]:
    out: list[Pat] = []
    while True:
        s = s.lstrip()
        if not s or (stop and s[0] in stop):
            return out, s
        pat, s = _parse_one(s)
        out.append(pat)


def _parse_one(s: str) -> tuple[Pat, str]:
    s = s.lstrip()
    if not s:
        raise PatternSyntaxError("unexpected end of pattern")
    pure = intuit = modal = False
    while s and s[0] in "%#>":
        if s[0] == "%":
            pure = True
        elif s[0] == "#":
            intuit = True
        else:
            modal = True
        s = s[1:]

    def finish(p: Pat) -> Pat:
        p.pure, p.intuit, p.modal = pure, intuit, modal
        return p

    if not s:
        # A bare `%` / `#` / `>` is a legal anonymous pattern.
        return finish(Pat("fresh")), s

    if s.startswith("[]"):
        return finish(Pat("empty")), s[2:]
    if s[0] == "[":
        body, rest = _split_bracket(s, "[", "]")
        return finish(_parse_bracket_body(body)), rest
    if s[0] == "(":
        # `(p1 & p2 & p3)` is sugar for a right-nested conjunction.
        body, rest = _split_bracket(s, "(", ")")
        parts = _split_top(body, "&")
        if len(parts) == 1:
            inner, tail = _parse_one(parts[0])
            if tail.strip():
                raise PatternSyntaxError(f"unparsed input in group: {tail!r}")
            return finish(inner), rest
        return finish(Pat("list", children=[parse_pattern(p) for p in parts])), rest
    if s.startswith("->") or s.startswith("<-"):
        return finish(Pat("rewrite", name=s[:2])), s[2:]
    if s[0] == "_":
        return finish(Pat("drop")), s[1:]
    if s[0] == "?":
        return finish(Pat("fresh")), s[1:]

    i = 0
    while i < len(s) and (s[i].isalnum() or s[i] in "_'."):
        i += 1
    if i == 0:
        raise PatternSyntaxError(f"cannot parse pattern at {s[:12]!r}")
    return finish(Pat("name", name=s[:i])), s[i:]


def _parse_bracket_body(body: str) -> Pat:
    parts = _split_top(body, "|")
    if len(parts) > 1:
        return Pat("or", children=[parse_pattern(p) if p.strip() else Pat("empty") for p in parts])
    kids, rest = _parse_seq(body)
    if rest.strip():
        raise PatternSyntaxError(f"unparsed input in bracket: {rest!r}")
    if not kids:
        return Pat("empty")
    return Pat("list", children=kids)


def _split_bracket(s: str, open_c: str, close_c: str) -> tuple[str, str]:
    depth = 0
    for i, ch in enumerate(s):
        if ch in "[(":
            depth += 1
        elif ch in "])":
            depth -= 1
            if depth == 0:
                return s[1:i], s[i + 1 :]
    raise PatternSyntaxError(f"unbalanced {open_c!r} in {s!r}")


def _split_top(s: str, sep: str) -> list[str]:
    out, depth, buf = [], 0, ""
    for ch in s:
        if ch in "[(":
            depth += 1
        elif ch in "])":
            depth -= 1
        if ch == sep and depth == 0:
            out.append(buf)
            buf = ""
        else:
            buf += ch
    out.append(buf)
    return out


# ------------------------------------------------------------------------- compile

@dataclass
class Destructuring:
    """A compiled ``iDestruct`` / ``iIntros``: binders + pattern + the tactic text."""

    binders: list[str]
    pattern: Pat
    #: Names bound in the Coq (pure) context by `%` markers.
    pure_names: list[str] = field(default_factory=list)

    @property
    def pattern_text(self) -> str:
        return self.pattern.render()

    def idestruct(self, hyp: str) -> str:
        """A complete tactic *sentence* -- terminator included.

        Returning it without the `.` is a trap: everything downstream feeds it
        straight to Rocq, which rejects it with a syntax error that reads like a
        pattern problem and is not one.
        """
        binder = f" ({' '.join(self.binders)})" if self.binders else ""
        return f'iDestruct "{hyp}" as{binder} "{self.pattern_text}".'

    def iintros(self) -> str:
        binder = f" ({' '.join(self.binders)})" if self.binders else ""
        return f'iIntros{binder} "{self.pattern_text}".'


class _Namer:
    def __init__(self, base: str) -> None:
        self.base = base.strip('"') or "H"
        self.n = 0
        self.used: set[str] = set()

    def next(self, hint: str = "") -> str:
        while True:
            self.n += 1
            name = f"{hint or self.base}{self.n}"
            if name not in self.used:
                self.used.add(name)
                return name


def compile_auto(skel: Skel, base: str = "H") -> Destructuring:
    """Synthesize a destructuring pattern from a prop's skeleton.

    Follows the shape exactly: leading ``∃`` become ``iDestruct`` binders, ``∗``/``∧``
    become a conjunction list, ``∨`` a disjunction, ``⌜⌝`` a ``%`` pure intro, ``□`` a
    ``#`` persistent intro.  Modalities that ``iDestruct`` sees through are descended
    silently; ``fupd``/``bupd`` get a ``>`` marker because they need eliminating.
    """
    namer = _Namer(base)
    binders: list[str] = []
    node = skel

    # Peel leading existentials into `iDestruct "H" as (x y) "..."` binders.
    while True:
        node = node.strip_transparent()
        if node.kind == "exists" and node.children:
            binders.extend(node.binders or [namer.next("x")])
            node = node.children[0]
            continue
        break

    pure_names: list[str] = []
    pat = _compile_node(node, namer, pure_names, modal=False)
    return Destructuring(binders=binders, pattern=pat, pure_names=pure_names)


def _compile_node(skel: Skel, namer: _Namer, pure_names: list[str], modal: bool) -> Pat:
    node = skel
    intuit = False
    while True:
        if node.kind in ("fupd", "bupd"):
            modal = True
            node = node.children[0]
            continue
        if node.kind in ("later", "except0", "affinely", "absorbingly"):
            node = node.children[0]
            continue
        if node.kind in ("intuitionistically", "persistently"):
            intuit = True
            node = node.children[0]
            continue
        break

    def mark(p: Pat) -> Pat:
        p.intuit = p.intuit or intuit
        p.modal = p.modal or modal
        return p

    if node.kind == "pure":
        name = namer.next("H")
        pure_names.append(name)
        return mark(Pat("name", name=name, pure=True))
    if node.kind in ("sep", "and"):
        return mark(Pat("list", children=[_compile_node(c, namer, pure_names, False) for c in node.children]))
    if node.kind == "or":
        return mark(Pat("or", children=[_compile_node(c, namer, pure_names, False) for c in node.children]))
    if node.kind == "exists":
        # A nested existential: `%x` introduces the witness inline.
        witness = (node.binders or ["x"])[0]
        pure_names.append(witness)
        inner = _compile_node(node.children[0], namer, pure_names, False)
        return mark(Pat("list", children=[Pat("name", name=witness, pure=True), inner]))
    return mark(Pat("name", name=namer.next()))


@dataclass
class DestructSpec:
    """A structured destructuring request: names, not a pattern string.

    ``{"names": ["Hl", "Hn"], "pure": ["Hn"]}`` and nested forms compile to
    ``"[Hl %Hn]"``.  The agent supplies intent; the compiler supplies syntax.
    """

    names: list[str | dict] = field(default_factory=list)
    pure: list[str] = field(default_factory=list)
    intuit: list[str] = field(default_factory=list)
    binders: list[str] = field(default_factory=list)


def compile_spec(spec: DestructSpec, skel: Skel | None = None) -> Destructuring:
    """Compile a structured spec into a pattern, shaped by the skeleton if given."""
    node = skel.strip_transparent() if skel is not None else None
    kind = "or" if node is not None and node.kind == "or" else "list"

    def leaf(name: str) -> Pat:
        return Pat("name", name=name, pure=name in spec.pure, intuit=name in spec.intuit)

    children: list[Pat] = []
    for entry in spec.names:
        if isinstance(entry, dict):
            sub = DestructSpec(
                names=entry.get("names", []),
                pure=entry.get("pure", []),
                intuit=entry.get("intuit", []),
            )
            children.append(compile_spec(sub).pattern)
        else:
            children.append(leaf(entry))
    if len(children) == 1 and kind == "list":
        pat = children[0]
    else:
        pat = Pat(kind, children=children)  # type: ignore[arg-type]
    return Destructuring(binders=list(spec.binders), pattern=pat, pure_names=list(spec.pure))


# --------------------------------------------------------------------------- align

@dataclass
class Mismatch:
    path: str
    reason: str
    pattern_at: str
    prop_at: str
    hint: str = ""


@dataclass
class AlignReport:
    ok: bool
    pattern: Pat
    skel: Skel
    mismatch: Mismatch | None = None
    suggestion: str = ""

    def render(self) -> str:
        lines = []
        if self.ok:
            lines.append("pattern aligns with the hypothesis' structure")
        else:
            m = self.mismatch
            assert m is not None
            lines.append(f"pattern/prop mismatch at {m.path}: {m.reason}")
            lines.append(f"  pattern here : {m.pattern_at}")
            lines.append(f"  prop here    : {m.prop_at}")
            if m.hint:
                lines.append(f"  hint         : {m.hint}")
        lines.append("")
        lines.append("prop skeleton:")
        lines.append(self.skel.render(1))
        lines.append("")
        lines.append("pattern tree:")
        lines.append(self.pattern.tree(1))
        if self.suggestion:
            lines.append("")
            lines.append(f"a pattern that fits: {self.suggestion}")
        return "\n".join(lines)


def align(pattern: Pat | str, prop: Skel | str, binders: list[str] | None = None) -> AlignReport:
    """Align a pattern against a prop's skeleton; report the first mismatch point.

    This is the answer to the single most common IPM failure loop.  Instead of a
    200-line goal dump and "cannot destruct", the agent gets the two trees and the
    exact node where they diverge.

    ``binders`` are the names introduced by the ``iDestruct "H" as (x y) "..."``
    form: they consume that many leading ``∃``/``∀`` binders before the pattern is
    matched against what remains.  Without them a pattern for the *body* would be
    matched against the quantifier and mis-diagnosed.
    """
    pat = parse_pattern(pattern) if isinstance(pattern, str) else pattern
    skel = parse_skeleton(prop) if isinstance(prop, str) else prop
    body, unconsumed = _peel_binders(skel, len(binders or []))
    if unconsumed:
        return AlignReport(
            ok=False,
            pattern=pat,
            skel=skel,
            mismatch=Mismatch(
                "root",
                f"{len(binders or [])} binders were given but the hypothesis has "
                f"{len(binders or []) - unconsumed} to introduce",
                " ".join(binders or []),
                _KIND_WORD.get(body.kind, body.kind),
                hint="drop the extra binder names",
            ),
        )
    mismatch = _align(pat, body, "root")
    suggestion = ""
    if mismatch is not None:
        suggestion = compile_auto(body).pattern_text
    return AlignReport(ok=mismatch is None, pattern=pat, skel=body, mismatch=mismatch, suggestion=suggestion)


def _peel_binders(skel: Skel, count: int) -> tuple[Skel, int]:
    """Consume ``count`` quantified variables; return the body and any shortfall."""
    node = skel
    while count > 0:
        node = node.strip_transparent()
        if node.kind not in ("exists", "forall") or not node.children:
            return node, count
        take = min(len(node.binders) or 1, count)
        if take < (len(node.binders) or 1):
            # Partially applied binder group: the remaining names stay quantified.
            return Skel(node.kind, node.children, binders=node.binders[take:]), 0
        count -= take
        node = node.children[0]
    return node, 0


_KIND_WORD = {
    "sep": "a separating conjunction (∗)",
    "and": "a conjunction (∧)",
    "or": "a disjunction (∨)",
    "exists": "an existential (∃)",
    "pure": "a pure fact (⌜⌝)",
    "wand": "a wand (−∗); destructing it is not possible, specialize or apply it",
    "forall": "a universal (∀); destructing it is not possible, specialize it",
    "impl": "an implication (→); destructing it is not possible, specialize it",
    "atom": "an opaque proposition",
}


def _align(pat: Pat, skel: Skel, path: str) -> Mismatch | None:
    node = skel
    # Peel the modalities a pattern may or may not mention.  One loop, not two:
    # `|==> □ (P ∧ Q)` interleaves the two kinds and must peel all the way down.
    while True:
        if node.kind in TRANSPARENT | {"intuitionistically", "persistently"}:
            node = node.children[0]
            continue
        if node.kind in UPDATE:
            if not pat.modal and pat.kind in ("list", "or"):
                return Mismatch(
                    path,
                    "the hypothesis is under an update modality, but the pattern does not eliminate it",
                    pat.render(),
                    node.kind,
                    hint="prefix the pattern with `>` (or use iMod) before destructing",
                )
            node = node.children[0]
            continue
        break

    if pat.kind in ("name", "drop", "fresh", "rewrite"):
        return None  # a name accepts anything
    if pat.kind == "empty":
        if node.kind == "atom" and node.text.strip() in ("False", "⌜False⌝"):
            return None
        return None  # `[]` on an inductive with no constructors -- not our business

    # Existentials must be peeled by binders or by a `%witness` sub-pattern.
    if node.kind == "exists":
        if pat.kind == "list" and pat.children and pat.children[0].pure:
            return _align(
                Pat("list", children=pat.children[1:]) if len(pat.children) > 2 else pat.children[1],
                node.children[0],
                f"{path}.∃-body",
            )
        return Mismatch(
            path,
            "the hypothesis is an existential; its witness must be introduced first",
            pat.render(),
            _KIND_WORD["exists"],
            hint="use iDestruct \"H\" as (x) \"...\" for the witness, or a leading `%x` in the pattern",
        )

    if pat.kind == "or":
        if node.kind != "or":
            return Mismatch(
                path,
                "the pattern splits a disjunction, but the hypothesis is not one",
                pat.render(),
                _KIND_WORD.get(node.kind, node.kind),
                hint="use [p1 p2] (spaces) for a conjunction, [p1|p2] (bars) for a disjunction",
            )
        return _align_children(pat, node, path, "disjuncts")

    if pat.kind == "list":
        if node.kind not in ("sep", "and"):
            if node.kind == "or":
                return Mismatch(
                    path,
                    "the pattern splits a conjunction, but the hypothesis is a disjunction",
                    pat.render(),
                    _KIND_WORD["or"],
                    hint="separate the sub-patterns with | rather than spaces",
                )
            return Mismatch(
                path,
                "the pattern destructs, but the hypothesis has no top-level connective to destruct",
                pat.render(),
                _KIND_WORD.get(node.kind, node.kind),
                hint="name it instead of destructing it",
            )
        return _align_children(pat, node, path, "conjuncts")
    return None


def _align_children(pat: Pat, node: Skel, path: str, word: str) -> Mismatch | None:
    n_pat, n_prop = len(pat.children), len(node.children)
    if n_pat > n_prop:
        return Mismatch(
            path,
            f"the pattern has {n_pat} {word} but the hypothesis has {n_prop}",
            pat.render(),
            f"{n_prop} {word}",
            hint="drop a component with _, or merge the extra ones",
        )
    if n_pat < n_prop:
        # ∗ / ∧ / ∨ associate to the right, so a shorter pattern is legal: its last
        # sub-pattern covers the residual chain.  `[H1 H2]` on `P ∗ Q ∗ R` gives
        # H2 : Q ∗ R.  Only asking for *more* components than exist is an error.
        if n_pat < 2:
            return None
        for i, (p, s) in enumerate(zip(pat.children[:-1], node.children), start=1):
            m = _align(p, s, f"{path}.{i}")
            if m is not None:
                return m
        residual = Skel(node.kind, node.children[n_pat - 1 :])
        return _align(pat.children[-1], residual, f"{path}.{n_pat}+")
    for i, (p, s) in enumerate(zip(pat.children, node.children), start=1):
        m = _align(p, s, f"{path}.{i}")
        if m is not None:
            return m
    return None
