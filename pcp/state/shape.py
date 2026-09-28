"""Skeleton shape assertions: "the goal here should have this shape" (issues MF5, D5).

An agent restating a WP continuation (``WP ! #(l +ₗ 1) {{ v, Φ v }}``) usually gets it
*almost* right, and the difference -- ``#(l +ₗ 1)`` against ``#(l +ₗ (0 + 1))`` -- is
exactly what the next ``wp_load`` trips over.  :func:`expect_shape` answers two
questions about an expected shape, never moving the session:

1. **Does it hold?**  Asked of Rocq, in one speculative ``run`` per target: the expected
   text is elaborated *at the target's type* in the current state (``_`` and ``?x`` are
   holes, each occurrence its own evar so coercions still insert), then ``unify``-ed
   with the target (convertible) and compared with ``constr_eq_nounivs`` (syntactic, the
   form tactics match on).  Ltac *patterns* were the obvious alternative and do not
   work: patterns are not typed, so heap_lang's ``#l`` never gets its ``LitLoc``
   coercion and nothing with a literal ever matches (verified, Rocq 9.1 / Iris 4.5).
2. **Where does it differ?**  A structural diff of the two *Rocq-printed* terms (the
   elaborated expectation, holes shown as evars, against the target), over the Iris
   connective skeleton (``ipm/skeleton.py``) and, inside atoms, a bracket-tree of
   tokens aligned with holes.  It reports the minimal differing subterms with a path.

Iris hypotheses are checked by reverting them in the probe (``iRevert "H"``: the target
is the premise of the resulting wand); Coq hypotheses by ``type of``.  Without a session
(a plain :class:`IrisGoal` or a printed string) only the structural diff runs, and the
verdict says so.  Repeated ``?x`` must agree: Rocq instantiates each occurrence
separately and the printed instantiations are compared here.
"""

from __future__ import annotations

import re
from collections.abc import Callable, Sequence
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any, Literal

from pcp.state.ipm.model import IrisGoal
from pcp.state.ipm.parse import goals_from_petanque, looks_like_ipm, parse_goal
from pcp.state.ipm.skeleton import Skel, parse_skeleton

if TYPE_CHECKING:
    from pcp.state.petanque import StateHandle
    from pcp.state.session import ProofSession

Verdict = Literal["syntactic", "convertible", "mismatch", "error", "structural"]

#: One speculative probe per target; elaboration and unification never compute much.
PROBE_TIMEOUT = 10.0
ENVS_ENTAILS = "iris.proofmode.environments.envs_entails"
_TAG = "PCPSHAPE:"


@dataclass
class ShapeDiff:
    """One minimal difference.  ``path`` locates it; ``context_*`` is the enclosing group."""

    path: str
    expected: str
    actual: str
    note: str = ""
    context_expected: str = ""
    context_actual: str = ""

    def to_json(self) -> dict[str, Any]:
        d = {"path": self.path, "expected": self.expected, "actual": self.actual}
        for k in ("note", "context_expected", "context_actual"):
            if getattr(self, k):
                d[k] = getattr(self, k)
        return d

    def describe(self) -> str:
        if not self.expected:
            what = f"goal has extra `{self.actual}`"
        elif not self.actual:
            what = f"expected `{self.expected}`, goal has nothing there"
        else:
            what = f"expected `{self.expected}`, goal has `{self.actual}`"
        if self.context_actual and self.context_actual != self.actual:
            what += f" (in `{self.context_actual}`)"
        if self.note:
            what += f" -- {self.note}"
        return f"at {self.path}: {what}"


@dataclass
class ShapePart:
    """The check of one target: the conclusion, or one named hypothesis."""

    target: str
    expected: str
    actual: str = ""
    verdict: Verdict = "structural"
    diffs: list[ShapeDiff] = field(default_factory=list)
    #: ``?x`` -> the printed term Rocq (or the structural matcher) bound it to.
    bindings: dict[str, str] = field(default_factory=dict)
    #: The expectation as Rocq elaborated it (holes print as evars).
    elaborated: str | None = None
    #: Rocq's ``unify`` answer; ``None`` when Rocq was not asked (or could not elaborate).
    unified: bool | None = None
    error: str | None = None

    def ok(self, *, strict: bool = True) -> bool:
        if self.verdict == "syntactic":
            return True
        if self.verdict == "convertible":
            return not strict
        if self.verdict == "structural":
            return not self.diffs and self.error is None
        return False

    def to_json(self, *, strict: bool = True) -> dict[str, Any]:
        d: dict[str, Any] = {
            "target": self.target,
            "ok": self.ok(strict=strict),
            "verdict": self.verdict,
            "expected": self.expected,
            "actual": self.actual,
            "diffs": [x.to_json() for x in self.diffs],
        }
        if self.bindings:
            d["bindings"] = dict(self.bindings)
        if self.elaborated is not None:
            d["elaborated"] = self.elaborated
        if self.error:
            d["error"] = self.error
        return d


@dataclass
class ShapeReport:
    parts: list[ShapePart]
    #: ``True``: only a syntactic match counts; ``False``: convertible is enough.
    strict: bool = True

    @property
    def ok(self) -> bool:
        return all(p.ok(strict=self.strict) for p in self.parts)

    def to_json(self) -> dict[str, Any]:
        return {
            "ok": self.ok,
            "parts": [p.to_json(strict=self.strict) for p in self.parts],
            "answer": self.render(),
        }

    def render(self) -> str:
        lines = []
        for p in self.parts:
            head = {
                "syntactic": "ok (syntactic match)",
                "convertible": "convertible but NOT syntactically equal"
                + ("" if self.strict else " (accepted)"),
                "mismatch": "MISMATCH (unifies, but a repeated ?x differs)"
                if p.unified
                else "MISMATCH (does not unify)",
                "error": "expected shape does not elaborate",
                "structural": "ok (structural; not checked by Rocq)" if p.ok() else "MISMATCH (structural)",
            }[p.verdict]
            lines.append(f"{p.target}: {head}")
            if p.error:
                lines.append(f"  rocq: {p.error.strip().splitlines()[-1][:300]}")
            lines.extend(f"  {d.describe()}" for d in p.diffs)
            if p.verdict == "convertible" and not p.diffs:
                lines.append("  prints identically: they differ in hidden coercions or implicit arguments")
            if p.bindings:
                lines.append("  bindings: " + ", ".join(f"?{k} := {v}" for k, v in p.bindings.items()))
        return "\n".join(lines)


# ============================================================================ tokens


@dataclass(eq=False)
class _T:
    """A token (``leaf``), a hole (``_``/``?x``), or a bracket group (``node``)."""

    kind: Literal["leaf", "hole", "node"]
    text: str
    start: int
    end: int
    children: list[_T] = field(default_factory=list)
    close: str = ""


_OPENERS = {"{{": "}}", "[{": "}]", "(": ")", "[": "]", "{": "}", "⌜": "⌝"}
_WORD = re.compile(r"[\w'][\w'.]*")
_HOLE = re.compile(r"\?[\w'][\w']*")
_BINDER_HEADS = frozenset({"λ", "fun", "∀", "∃", "forall", "exists"})


def _tokenize(src: str, *, holes: bool = True) -> list[_T]:
    """A bracket tree of ``src``.  Total: unbalanced closers become leaves.

    Scope delimiters glued to a term (``(0 ≤ n)%Z``) are dropped: they are the printer's
    annotation, not structure.  ``holes=False`` for the goal side, where ``_`` is an
    unused binder the printer shows, not a wildcard.
    """
    root = _T("node", "", 0, len(src))
    stack: list[_T] = [root]
    i, n = 0, len(src)
    prev_end = -1
    while i < n:
        ch = src[i]
        if ch.isspace():
            i += 1
            continue
        top = stack[-1]
        # closers first: `}}` / `}]` only when they close the matching opener
        if top is not root and src.startswith(top.close, i):
            top.end = i + len(top.close)
            stack.pop()
            i = prev_end = top.end
            continue
        opener = next((o for o in ("{{", "[{", "(", "[", "{", "⌜") if src.startswith(o, i)), None)
        if opener is not None:
            node = _T("node", opener, i, n, close=_OPENERS[opener])
            stack[-1].children.append(node)
            stack.append(node)
            i += len(opener)
            continue
        if ch == '"':
            j = src.find('"', i + 1)
            j = n if j < 0 else j + 1
            stack[-1].children.append(_T("leaf", src[i:j], i, j))
            i = prev_end = j
            continue
        if ch == "%" and prev_end == i:
            m = _WORD.match(src, i + 1)
            if m:
                i = prev_end = m.end()
                continue
        if ch == "?":
            m = _HOLE.match(src, i) if holes else None
            if m:
                j = m.end()
                if src.startswith("@{", j):  # a printed evar instance ?y@{x:=...}
                    depth = 0
                    for k in range(j + 1, n):
                        depth += {"{": 1, "}": -1}.get(src[k], 0)
                        if depth == 0:
                            j = k + 1
                            break
                stack[-1].children.append(_T("hole", m.group(0)[1:], i, j))
                i = prev_end = j
                continue
        m = _WORD.match(src, i)
        if m:
            word = m.group(0).rstrip(".") or m.group(0)
            j = i + len(word)
            kind: Literal["leaf", "hole"] = "hole" if holes and word == "_" else "leaf"
            stack[-1].children.append(_T(kind, "" if kind == "hole" else word, i, j))
            i = prev_end = j
            continue
        j = i
        while (
            j < n
            and not src[j].isspace()
            and not _WORD.match(src, j)
            and src[j] not in '"?' + "".join({o[0] for o in _OPENERS} | {c[0] for c in _OPENERS.values()})
        ):
            j += 1
        if j == i:
            j = i + 1
        stack[-1].children.append(_T("leaf", src[i:j], i, j))
        i = prev_end = j
    return _simplify(root.children)


def _simplify(items: list[_T]) -> list[_T]:
    """``((X))`` is ``(X)``, and one group around the whole text is no group at all."""
    for t in items:
        if t.kind == "node":
            t.children = _simplify(t.children)
            while (
                t.text == "("
                and len(t.children) == 1
                and t.children[0].kind == "node"
                and t.children[0].text == "("
            ):
                inner = t.children[0]
                t.children, t.end = inner.children, t.end
    while len(items) == 1 and items[0].kind == "node" and items[0].text == "(":
        items = items[0].children
    return items


# ======================================================================== alignment


@dataclass
class _Op:
    kind: Literal["eq", "sub", "del", "ins", "hole"]
    i: int = -1  # expected index
    j0: int = -1  # goal slice
    j1: int = -1


def _align(
    exp: Sequence[Any],
    goal: Sequence[Any],
    *,
    is_hole: Callable[[Any], bool],
    same: Callable[[Any, Any], bool],
    near: Callable[[Any, Any], bool],
) -> list[_Op]:
    """Edit-distance alignment where a hole absorbs one or more goal elements for free.

    ``near`` pairs (same bracket, same connective) substitute cheaper than unrelated ones,
    so the diff recurses into them instead of reporting the whole group.
    """
    n, m = len(exp), len(goal)
    inf = float("inf")
    cost = [[inf] * (m + 1) for _ in range(n + 1)]
    choice: list[list[_Op | None]] = [[None] * (m + 1) for _ in range(n + 1)]
    cost[n][m] = 0.0
    for i in range(n, -1, -1):
        for j in range(m, -1, -1):
            if i == n and j == m:
                continue
            best, op = inf, None
            if i < n and is_hole(exp[i]):
                for k in range(j + 1, m + 1):
                    if cost[i + 1][k] < best:
                        best, op = cost[i + 1][k], _Op("hole", i, j, k)
            if i < n and j < m and not is_hole(exp[i]):
                if same(exp[i], goal[j]):
                    c, kind = 0.0, "eq"
                else:
                    c, kind = (0.5 if near(exp[i], goal[j]) else 1.0), "sub"
                if c + cost[i + 1][j + 1] < best:
                    best, op = c + cost[i + 1][j + 1], _Op(kind, i, j, j + 1)  # type: ignore[arg-type]
            if i < n and 1.0 + cost[i + 1][j] < best:
                best, op = 1.0 + cost[i + 1][j], _Op("del", i, j, j)
            if j < m and 1.0 + cost[i][j + 1] < best:
                best, op = 1.0 + cost[i][j + 1], _Op("ins", i, j, j + 1)
            cost[i][j], choice[i][j] = best, op
    ops: list[_Op] = []
    i = j = 0
    while (i, j) != (n, m):
        op = choice[i][j]
        assert op is not None
        ops.append(op)
        if op.kind in ("eq", "sub", "hole"):
            i, j = op.i + 1, op.j1
        elif op.kind == "del":
            i += 1
        else:
            j += 1
    return ops


def _chunks(ops: list[_Op]) -> list[list[_Op]]:
    """Maximal runs of non-matching operations: each is one reported difference."""
    out: list[list[_Op]] = []
    cur: list[_Op] = []
    for op in ops:
        if op.kind in ("eq", "hole"):
            if cur:
                out.append(cur)
                cur = []
        else:
            cur.append(op)
    if cur:
        out.append(cur)
    return out


# ============================================================================ differ


class _Differ:
    """Diffs two printed props.  ``bindings`` collects what each named ``?x`` absorbed."""

    def __init__(self, exp_src: str, goal_src: str) -> None:
        self.exp_src = exp_src
        self.goal_src = goal_src
        self.bindings: dict[str, list[str]] = {}

    # -- prop level (Iris connectives) -------------------------------------------
    def prop(self, exp: str, goal: str, path: list[str], ren: dict[str, str]) -> list[ShapeDiff]:
        se, sg = parse_skeleton(exp), parse_skeleton(goal)
        return self.skel(se, sg, path, ren)

    def skel(self, se: Skel, sg: Skel, path: list[str], ren: dict[str, str]) -> list[ShapeDiff]:
        if se.kind == "atom" and _is_hole_text(se.text):
            self._bind(se.text, sg.to_notation())
            return []
        if se.kind in ("atom", "pure") and sg.kind in ("atom", "pure") and se.kind == sg.kind:
            e = se.children[0].text if se.kind == "pure" and se.children else se.text
            g = sg.children[0].text if sg.kind == "pure" and sg.children else sg.text
            return self.terms(e, g, path + (["⌜…⌝"] if se.kind == "pure" else []), ren)
        if se.kind != sg.kind:
            if se.kind == "atom" or sg.kind == "atom":
                # One side has no visible connective (a notation, a hole inside): compare as terms.
                return self.terms(se.to_notation(), sg.to_notation(), path, ren)
            return [
                ShapeDiff(
                    _path(path),
                    se.to_notation(),
                    sg.to_notation(),
                    note=f"expected {_kind(se)}, goal has {_kind(sg)}",
                )
            ]
        # same connective
        out: list[ShapeDiff] = []
        ren2 = dict(ren)
        if se.kind in ("exists", "forall"):
            if len(se.binders) != len(sg.binders):
                return [
                    ShapeDiff(
                        _path(path),
                        se.to_notation(),
                        sg.to_notation(),
                        note=f"expected {len(se.binders)} binder(s), goal has {len(sg.binders)}",
                    )
                ]
            ren2.update(zip(se.binders, sg.binders, strict=True))
        elif se.binders or sg.binders:  # masks, ▷^n annotations
            for k, (be, bg) in enumerate(zip(se.binders, sg.binders, strict=False)):
                out += self.terms(
                    be, bg, path + [f"{_head(se)} mask {k + 1}" if "fupd" in se.kind else _head(se)], ren
                )
        if len(se.children) == len(sg.children):
            for k, (ce, cg) in enumerate(zip(se.children, sg.children, strict=True)):
                out += self.skel(ce, cg, path + [_child_label(se, k)], ren2)
            return out
        ops = _align(
            se.children,
            sg.children,
            is_hole=lambda c: c.kind == "atom" and _is_hole_text(c.text),
            same=lambda a, b: not _Differ(self.exp_src, self.goal_src).skel(a, b, [], ren2),
            near=lambda a, b: a.kind == b.kind,
        )
        for op in ops:
            if op.kind == "hole":
                self._bind(
                    se.children[op.i].text, " ∗ ".join(c.to_notation() for c in sg.children[op.j0 : op.j1])
                )
        for chunk in _chunks(ops):
            if len(chunk) == 1 and chunk[0].kind == "sub":
                op = chunk[0]
                out += self.skel(se.children[op.i], sg.children[op.j0], path + [_child_label(se, op.i)], ren2)
                continue
            es = [se.children[op.i].to_notation() for op in chunk if op.kind in ("sub", "del")]
            gs = [
                sg.children[j].to_notation()
                for op in chunk
                if op.kind in ("sub", "ins")
                for j in range(op.j0, op.j1)
            ]
            sym = f" {_head(se)} "
            out.append(
                ShapeDiff(_path(path), sym.join(es), sym.join(gs), note=f"{_head(se)}-conjuncts differ")
            )
        return out

    # -- term level (inside atoms) -----------------------------------------------
    def terms(self, exp: str, goal: str, path: list[str], ren: dict[str, str]) -> list[ShapeDiff]:
        e, g = _tokenize(exp), _tokenize(goal, holes=False)
        return self.seq(e, g, exp, goal, path, ren, ctx=None)

    def seq(
        self,
        e: list[_T],
        g: list[_T],
        es: str,
        gs: str,
        path: list[str],
        ren: dict[str, str],
        ctx: tuple[str, str] | None,
    ) -> list[ShapeDiff]:
        ren = _binder_renaming(e, g, ren)
        # A printed evar under a binder is applied to it (`{{ v, ?b v }}`): the whole
        # application is the hole.
        e = [
            t
            for k, t in enumerate(e)
            if not (k and e[k - 1].kind == "hole" and t.kind == "leaf" and t.text in ren)
        ]
        memo: dict[tuple[int, int], bool] = {}

        def same(a: _T, b: _T) -> bool:
            key = (id(a), id(b))
            if key not in memo:
                memo[key] = not _Differ(self.exp_src, self.goal_src).elem(a, b, es, gs, [], ren, None)
            return memo[key]

        ops = _align(
            e,
            g,
            is_hole=lambda t: t.kind == "hole",
            same=same,
            near=lambda a, b: a.kind == "node" and b.kind == "node" and a.text == b.text,
        )
        out: list[ShapeDiff] = []
        for op in ops:
            if op.kind == "hole" and e[op.i].text:
                self._bind(e[op.i].text, _span(gs, g[op.j0 : op.j1]))
        for chunk in _chunks(ops):
            if (
                len(chunk) == 1
                and chunk[0].kind == "sub"
                and e[chunk[0].i].kind == g[chunk[0].j0].kind == "node"
            ):
                a, b = e[chunk[0].i], g[chunk[0].j0]
                if a.text == b.text:
                    out += self.elem(a, b, es, gs, path, ren, (_span(es, [a]), _span(gs, [b])))
                    continue
            ei = [e[op.i] for op in chunk if op.kind in ("sub", "del")]
            gj = [g[j] for op in chunk if op.kind in ("sub", "ins") for j in range(op.j0, op.j1)]
            out.append(
                ShapeDiff(
                    _path(path),
                    _span(es, ei),
                    _span(gs, gj),
                    context_expected=ctx[0] if ctx else "",
                    context_actual=ctx[1] if ctx else "",
                )
            )
        return out

    def elem(
        self,
        a: _T,
        b: _T,
        es: str,
        gs: str,
        path: list[str],
        ren: dict[str, str],
        ctx: tuple[str, str] | None,
    ) -> list[ShapeDiff]:
        if a.kind == "hole":
            if a.text:
                self._bind(a.text, _span(gs, [b]))
            return []
        if a.kind == "leaf" and b.kind == "leaf":
            return [] if ren.get(a.text, a.text) == b.text else [ShapeDiff(_path(path), a.text, b.text)]
        if a.kind == "node" and b.kind == "node" and a.text == b.text:
            label = _group_label(gs, b)
            if a.text in ("{{", "[{"):
                return self.post(a, b, es, gs, path + [label], ren)
            if a.text == "⌜":
                return self.prop(_inner(es, a), _inner(gs, b), path + [label], ren)
            return self.seq(a.children, b.children, es, gs, path + [label], ren, ctx)
        return [ShapeDiff(_path(path), _span(es, [a]), _span(gs, [b]))]

    def post(self, a: _T, b: _T, es: str, gs: str, path: list[str], ren: dict[str, str]) -> list[ShapeDiff]:
        """A WP postcondition ``{{ v, Q }}``: rename the binder, compare ``Q`` as a prop."""
        ea, ga = a.children, b.children
        ren = dict(ren)
        be, bg = _post_binder(ea), _post_binder(ga)
        if be is not None and bg is not None:
            if ea[0].kind == "leaf":
                ren[ea[0].text] = ga[0].text
            ea, ga = ea[2:], ga[2:]
        elif (be is None) != (bg is None):
            # `{{ Φ }}` against `{{ v, Φ v }}`: eta; only Rocq's convertibility check knows.
            return self.seq(ea, ga, es, gs, path, ren, None)
        if not ea or not ga:
            return self.seq(ea, ga, es, gs, path, ren, None)
        return self.prop(es[ea[0].start : ea[-1].end], gs[ga[0].start : ga[-1].end], path, ren)

    def _bind(self, name: str, text: str) -> None:
        name = name.lstrip("?")
        if name and name != "_":
            self.bindings.setdefault(name, []).append(" ".join(text.split()))


def _is_hole_text(text: str) -> bool:
    t = text.strip()
    return t == "_" or bool(_HOLE.fullmatch(t))


def _post_binder(items: list[_T]) -> str | None:
    if (
        len(items) >= 2
        and items[0].kind in ("leaf", "hole")
        and items[1].kind == "leaf"
        and items[1].text == ","
    ):
        return items[0].text or "_"
    return None


def _binder_renaming(e: list[_T], g: list[_T], ren: dict[str, str]) -> dict[str, str]:
    """``λ x y, …`` against ``λ a b, …``: the bound names correspond."""
    if not (
        e and g and e[0].kind == g[0].kind == "leaf" and e[0].text == g[0].text and e[0].text in _BINDER_HEADS
    ):
        return ren

    def names(items: list[_T]) -> list[str] | None:
        out: list[str] = []
        for t in items[1:]:
            if t.kind == "leaf" and t.text in (",", "=>"):
                return out
            if t.kind == "leaf" and _WORD.fullmatch(t.text):
                out.append(t.text)
            elif t.kind == "hole" and not t.text:
                out.append("_")
            else:
                return None
        return None

    ne, ng = names(e), names(g)
    if ne is None or ng is None or len(ne) != len(ng):
        return ren
    out = dict(ren)
    out.update(zip(ne, ng, strict=True))
    return out


def _span(src: str, items: Sequence[_T]) -> str:
    if not items:
        return ""
    return " ".join(src[items[0].start : items[-1].end].split())


def _inner(src: str, node: _T) -> str:
    return src[node.start + len(node.text) : node.end - len(node.close)]


def _group_label(src: str, node: _T) -> str:
    """The group as it prints, prefixed by a glued symbol (``#(…)``), elided past 40 chars."""
    text = " ".join(src[node.start : node.end].split())
    k = node.start
    while k > 0 and not src[k - 1].isspace() and not src[k - 1].isalnum() and src[k - 1] not in "({[⌜":
        k -= 1
    text = src[k : node.start] + text
    return text if len(text) <= 40 else text[:37] + "…"


_CHILD = {"sep": "∗", "and": "∧", "or": "∨"}


def _child_label(node: Skel, k: int) -> str:
    if node.kind in _CHILD:
        return f"{_CHILD[node.kind]}[{k + 1}]"
    if node.kind in ("wand", "impl", "entails", "iff", "wand_iff", "equiv"):
        return f"{_head(node)} {'lhs' if k == 0 else 'rhs'}"
    return f"{_head(node)} body"


def _head(node: Skel) -> str:
    return {
        "sep": "∗",
        "and": "∧",
        "or": "∨",
        "wand": "-∗",
        "impl": "→",
        "iff": "↔",
        "wand_iff": "∗-∗",
        "entails": "⊢",
        "equiv": "⊣⊢",
        "exists": "∃",
        "forall": "∀",
        "later": "▷",
        "except0": "◇",
        "persistently": "<pers>",
        "intuitionistically": "□",
        "plainly": "■",
        "affinely": "<affine>",
        "absorbingly": "<absorb>",
        "fupd": "|={…}=>",
        "fupd_step": "|={…}▷=>",
        "bupd": "|==>",
    }.get(node.kind, node.kind)


def _kind(node: Skel) -> str:
    if node.kind == "atom":
        return "an atom"
    return f"a `{_head(node)}`"


def _path(parts: list[str]) -> str:
    return " › ".join(parts) if parts else "top"


def compare_shape(
    expected: str, actual: str, *, root: str = "conclusion"
) -> tuple[list[ShapeDiff], dict[str, str]]:
    """The structural diff alone: ``(diffs, bindings)``.  Pure; no Rocq.

    A repeated ``?x`` bound to two different texts is itself a difference.
    """
    exp, act = _strip_print(expected), _strip_print(actual)
    d = _Differ(exp, act)
    diffs = d.prop(exp, act, [root], {})
    bindings: dict[str, str] = {}
    for name, seen in d.bindings.items():
        bindings[name] = seen[0]
        if any(s != seen[0] for s in seen[1:]):
            diffs.append(
                ShapeDiff(
                    root,
                    f"?{name}",
                    " / ".join(dict.fromkeys(seen)),
                    note=f"?{name} must be the same term everywhere",
                )
            )
    return diffs, bindings


# ======================================================================= Rocq probe


def _strip_print(text: str) -> str:
    """``((X)%I : iPropI Σ)`` / ``(X)%I`` (how ``idtac`` prints a cast term) -> ``X``."""
    t = " ".join(text.split())
    for _ in range(4):
        before = t
        if t.startswith("(") and t.endswith(")") and _closes_at_end(t):
            inner = t[1:-1]
            cut = _top_level_colon(inner)
            t = (inner[:cut] if cut is not None else inner).strip()
        m = re.fullmatch(r"\((.*)\)%\w+", t)
        if m and _closes_at_end(t[: m.end(1) + 1]):
            t = m.group(1).strip()
        if t == before:
            break
    return t


def _closes_at_end(t: str) -> bool:
    depth = 0
    for k, ch in enumerate(t):
        depth += {"(": 1, ")": -1}.get(ch, 0)
        if depth == 0 and k < len(t) - 1:
            return False
    return depth == 0


def _top_level_colon(t: str) -> int | None:
    depth = 0
    last = None
    for k, ch in enumerate(t):
        if ch in "([{⌜":
            depth += 1
        elif ch in ")]}⌝":
            depth -= 1
        elif depth == 0 and t.startswith(" : ", k - 1) and ch == ":":
            last = k
    return last


#: heap_lang's value and literal injections: a hole standing for ``#l`` binds ``LitLoc l``.
_INJECTIONS = frozenset({"LitV", "LitLoc", "LitInt", "LitBool", "LitProphecy", "Val", "of_val"})


def _uncoerce(text: str) -> str:
    """``LitLoc l`` -> ``l``: two occurrences of one ``?x`` agree up to the injections."""
    t = text.strip()
    while True:
        head, _, rest = t.partition(" ")
        if head not in _INJECTIONS or not rest:
            return t
        t = _strip_print(rest)


_META = re.compile(r"(?<![\w'])\?([A-Za-z_][\w']*)")


def rocq_term(expected: str) -> tuple[str, list[tuple[str, str]]]:
    """``expected`` with every ``?x`` occurrence replaced by its own Ltac variable.

    Returns ``(term, [(ltac_var, name), ...])``.  One evar per *occurrence*: sharing one
    across ``#?x`` and ``?x +ₗ 1`` fixes its type before the ``#`` coercion can insert.
    """
    occurrences: list[tuple[str, str]] = []

    def sub(m: re.Match[str]) -> str:
        # `▷?p`, `□?p`: the conditional modalities, not metavariables.
        k = m.start()
        if k > 0 and expected[k - 1] in "▷□◇■>":
            return m.group(0)
        var = f"pcpmv_{len(occurrences)}"
        occurrences.append((var, m.group(1)))
        return f"({var})"

    return _META.sub(sub, expected), occurrences


def probe_tactic(
    target: str, expected: str, *, kind: Literal["ipm", "coq", "iris_hyp", "coq_hyp"], selector: int = 0
) -> tuple[str, list[tuple[str, str]]]:
    """The one speculative sentence that checks ``expected`` against ``target``.

    ``target`` is the hypothesis name for the ``*_hyp`` kinds and ignored otherwise.
    It prints ``PCPSHAPE:`` records and always succeeds once the expectation elaborates.
    """
    term, metas = rocq_term(expected)
    scope = "%I" if kind in ("ipm", "iris_hyp") else ""
    lets = "".join(f"let {v} := open_constr:(_) in " for v, _ in metas)
    shows = "".join(f'idtac "{_TAG}MV {name} " {v}; ' for v, name in metas)
    check = (
        f"let T := type of P in {lets}"
        f"let Q := open_constr:(({term}){scope} : T) in "
        f'idtac "{_TAG}EXP " Q; idtac "{_TAG}GOAL " P; '
        f'first [ unify P Q; idtac "{_TAG}CONV"; '
        f'first [ constr_eq_nounivs P Q; idtac "{_TAG}SYN" | idtac "{_TAG}NOSYN" ]; '
        f'idtac "{_TAG}INST " Q; {shows}idtac "{_TAG}END" | idtac "{_TAG}NOCONV" ]'
    )
    if kind == "ipm":
        body = f"lazymatch goal with |- {ENVS_ENTAILS} _ ?P => {check} end"
    elif kind == "coq":
        body = f"lazymatch goal with |- ?P => {check} end"
    elif kind == "coq_hyp":
        body = f"let P := type of {target} in {check}"
    else:
        body = (
            f'iRevert "{target}"; lazymatch goal with |- {ENVS_ENTAILS} _ (bi_wand ?H _) => '
            f"let P := lazymatch H with bi_intuitionistically ?H' => H' | _ => H end in {check} end"
        )
    prefix = f"{selector + 1}: " if selector else ""
    return f"{prefix}({body}).", metas


def _records(messages: list[str]) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    for m in messages:
        if not m.startswith(_TAG):
            continue
        tag, _, rest = m[len(_TAG) :].partition(" ")
        tag = tag.strip()
        out.setdefault(tag, []).append(rest.strip())
    return out


def _check(
    session: ProofSession,
    state: StateHandle,
    part: ShapePart,
    *,
    kind: Literal["ipm", "coq", "iris_hyp", "coq_hyp"],
    selector: int,
) -> ShapePart:
    tactic, metas = probe_tactic(part.target, part.expected, kind=kind, selector=selector)
    res = session.run(tactic, from_state=state, commit=False, timeout=PROBE_TIMEOUT)
    rec = _records(res.messages) if res.ok else {}
    if not res.ok or "EXP" not in rec:
        part.verdict = "error"
        part.error = res.error or "the probe printed nothing"
        # Still useful: the text diff against what the goal prints.
        part.diffs, part.bindings = compare_shape(part.expected, part.actual, root=part.target)
        return part
    part.elaborated = _strip_print(rec["EXP"][0])
    printed_goal = _strip_print(rec.get("GOAL", [part.actual])[0])
    if printed_goal:
        part.actual = printed_goal
    part.unified = "CONV" in rec
    if not part.unified:
        part.verdict = "mismatch"
        part.diffs, _ = compare_shape(part.elaborated, part.actual, root=part.target)
        if not part.diffs:
            part.diffs = [
                ShapeDiff(part.target, part.elaborated, part.actual, note="prints alike but does not unify")
            ]
        return part
    inst = _strip_print(rec.get("INST", [part.elaborated])[0])
    seen: dict[str, list[str]] = {}
    for text in rec.get("MV", []):
        name, _, value = text.partition(" ")
        seen.setdefault(name, []).append(_uncoerce(_strip_print(value)))
    part.bindings = {k: v[0] for k, v in seen.items()}
    conflicts = [
        ShapeDiff(
            part.target, f"?{k}", " / ".join(dict.fromkeys(v)), note=f"?{k} must be the same term everywhere"
        )
        for k, v in seen.items()
        if any(x != v[0] for x in v[1:])
    ]
    if "SYN" in rec and not conflicts:
        part.verdict = "syntactic"
        return part
    part.verdict = "mismatch" if conflicts else "convertible"
    part.diffs = [*compare_shape(inst, part.actual, root=part.target)[0], *conflicts]
    return part


# ========================================================================== entry


def expect_shape(
    target: ProofSession | IrisGoal | str,
    expected: str,
    *,
    hyps: dict[str, str] | None = None,
    state: StateHandle | None = None,
    goals: list[IrisGoal] | None = None,
    goal_index: int = 0,
    strict: bool = True,
) -> ShapeReport:
    """Check that the goal (and optionally named hypotheses) has the expected shape.

    ``expected`` is the conclusion, or a whole IPM-style goal (``"H" : P`` lines, the
    ``---∗`` separators, then the conclusion) whose named hypotheses are checked too;
    ``hyps`` adds more.  An empty conclusion checks only hypotheses.  ``_`` and ``?x``
    are holes.  With a session this is one speculative ``run`` per target at ``state``
    (default: the current one); with an :class:`IrisGoal` or printed goal text it is
    the structural diff only (verdict ``structural``).  ``strict``: a match only up to
    conversion is *not* ok -- the form tactics like ``wp_load`` match on is syntactic.
    """
    want_goal, want_hyps = _split_expected(expected)
    want_hyps.update(hyps or {})

    session = None if isinstance(target, IrisGoal | str) else target
    if isinstance(target, str):
        goal: IrisGoal | None = parse_goal(target)
    elif isinstance(target, IrisGoal):
        goal = target
    else:
        base = state if state is not None else target.state()
        state = base
        if goals is None:
            goals = goals_from_petanque(target.goals(base))
        goal = goals[goal_index] if goal_index < len(goals) else None

    parts: list[ShapePart] = []
    if goal is None:
        return ShapeReport(
            [ShapePart("conclusion", want_goal, verdict="error", error="no goal at this state")], strict
        )
    if want_goal.strip():
        part = ShapePart("conclusion", want_goal.strip(), goal.goal)
        if session is not None and state is not None:
            parts.append(
                _check(session, state, part, kind="ipm" if goal.is_ipm else "coq", selector=goal_index)
            )
        else:
            part.diffs, part.bindings = compare_shape(part.expected, part.actual)
            parts.append(part)
    for name, want in want_hyps.items():
        h = goal.by_id(name)
        part = ShapePart(name, want.strip(), h.prop if h is not None else "")
        if h is None:
            part.verdict = "error"
            part.error = f'no hypothesis named "{name}"; have {", ".join(x.id for x in goal.all_hyps)}'
        elif session is not None and state is not None:
            kind: Literal["iris_hyp", "coq_hyp"] = "coq_hyp" if h.klass == "pure" else "iris_hyp"
            part = _check(session, state, part, kind=kind, selector=goal_index)
        else:
            part.diffs, part.bindings = compare_shape(part.expected, part.actual, root=name)
        parts.append(part)
    if not parts:
        parts.append(
            ShapePart(
                "conclusion", "", goal.goal, verdict="error", error="nothing to check: empty expectation"
            )
        )
    return ShapeReport(parts, strict)


def _split_expected(expected: str) -> tuple[str, dict[str, str]]:
    """A whole restated goal -> ``(conclusion, {hyp: prop})``; a bare prop is the conclusion."""
    if not looks_like_ipm(expected):
        return expected, {}
    g = parse_goal(expected)
    return g.goal, {h.id: h.prop for h in g.ipm_hyps if not h.anonymous}


def top_level_terms(text: str) -> list[str]:
    """The top-level tokens and groups of a printed application: ``inv N (P x)`` ->
    ``["inv", "N", "(P x)"]``.  Scope delimiters are dropped, as in the diff."""
    src = " ".join(text.split())
    return [src[t.start : t.end] for t in _tokenize(src, holes=False)]
