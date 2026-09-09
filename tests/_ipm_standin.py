"""Minimal stand-ins for ``pcp.state.ipm.skeleton`` / ``pcp.state.ipm.pattern``.

Installed into ``sys.modules`` only when the real modules are absent (they are written
by another wave); test-only, never imported by the package.  They implement the contract
the ledger/render/diagnosis layer codes against: ``Skel(kind, children, binders, text)``
with ``render()``, ``parse_skeleton``, ``align(pattern, skel) -> Alignment(ok, mismatch,
reason, suggestion)``, ``compile_auto(skel, base) -> Compiled(pattern, ...)`` and
``PatternSyntaxError``.
"""

from __future__ import annotations

import re
import sys
import types
from dataclasses import dataclass, field


def _install() -> None:
    try:
        import pcp.state.ipm.pattern  # noqa: F401
        import pcp.state.ipm.skeleton  # noqa: F401

        return
    except ImportError:
        pass
    sk = types.ModuleType("pcp.state.ipm.skeleton")
    sk.Skel = Skel  # type: ignore[attr-defined]
    sk.parse_skeleton = parse_skeleton  # type: ignore[attr-defined]
    pt = types.ModuleType("pcp.state.ipm.pattern")
    pt.PatternSyntaxError = PatternSyntaxError  # type: ignore[attr-defined]
    pt.align = align  # type: ignore[attr-defined]
    pt.compile_auto = compile_auto  # type: ignore[attr-defined]
    pt.Alignment = Alignment  # type: ignore[attr-defined]
    pt.Compiled = Compiled  # type: ignore[attr-defined]
    sys.modules.setdefault("pcp.state.ipm.skeleton", sk)
    sys.modules.setdefault("pcp.state.ipm.pattern", pt)


# --------------------------------------------------------------------- skeleton

TRANSPARENT = {"later", "except0", "affinely", "absorbingly"}
UPDATE = {"fupd", "bupd"}


@dataclass
class Skel:
    kind: str
    children: list[Skel] = field(default_factory=list)
    binders: list[str] = field(default_factory=list)
    text: str = ""

    def render(self, indent: int = 0) -> str:
        pad = "  " * indent
        if self.kind == "atom":
            return f"{pad}{self.text}"
        head = self.kind + "".join(f" {b}" for b in self.binders)
        return "\n".join([f"{pad}{head}", *(c.render(indent + 1) for c in self.children)])

    def to_notation(self) -> str:
        return _render(self, 0)


_PREFIX = [("<pers>", "persistently"), ("<affine>", "affinely"), ("<absorb>", "absorbingly"),
           ("□", "box"), ("■", "persistently"), ("▷", "later"), ("◇", "except0")]
_FUPD_RE = re.compile(r"\|=\{([^}]*)\}=>")
_FUPD_WAND_RE = re.compile(r"=\{([^}]*)\}=(?:∗|\*)")
_BINOPS = [("∗-∗", "wand_iff", 1), ("-∗", "wand", 1), ("−∗", "wand", 1), ("↔", "iff", 1), ("→", "impl", 1),
           ("->", "impl", 1), ("∨", "or", 2), ("∧", "and", 3), ("∗", "sep", 3)]
_BINDERS = {"∀": "forall", "∃": "exists"}


class _Cur:
    def __init__(self, s: str) -> None:
        self.s, self.i = s, 0

    def ws(self) -> None:
        while self.i < len(self.s) and self.s[self.i].isspace():
            self.i += 1

    def eof(self) -> bool:
        self.ws()
        return self.i >= len(self.s)

    def peek(self, t: str) -> bool:
        self.ws()
        return self.s.startswith(t, self.i)

    def eat(self, t: str) -> bool:
        if self.peek(t):
            self.i += len(t)
            return True
        return False


class _GaveUp(Exception):
    pass


def parse_skeleton(prop: str) -> Skel:
    cur = _Cur(prop.strip())
    try:
        node = _parse(cur, 0)
    except _GaveUp:
        return Skel("atom", text=prop.strip())
    return node if cur.eof() else Skel("atom", text=prop.strip())


def _standalone(text: str, i: int, tok: str) -> bool:
    if i > 0 and not text[i - 1].isspace():
        return False
    j = i + len(tok)
    return j >= len(text) or text[j].isspace() or text[j] in "(⌜"


def _match_op(cur: _Cur):
    cur.ws()
    best = None
    for tok, kind, prec in _BINOPS:
        if cur.peek(tok) and _standalone(cur.s, cur.i, tok) and (best is None or len(tok) > len(best[0])):
            best = (tok, kind, prec)
    return best


def _modal_wand(cur: _Cur):
    cur.ws()
    if cur.i > 0 and not cur.s[cur.i - 1].isspace():
        return None
    if cur.s.startswith("==∗", cur.i):
        return ("==∗", None)
    m = _FUPD_WAND_RE.match(cur.s, cur.i)
    return (m.group(0), m.group(1).strip()) if m else None


def _parse(cur: _Cur, prec: int) -> Skel:
    if prec >= 4:
        return _prefix(cur)
    if prec == 0:
        cur.ws()
        for sym, kind in _BINDERS.items():
            if cur.peek(sym):
                start = cur.i
                cur.eat(sym)
                names = _binders(cur)
                if names is None:
                    cur.i = start
                    break
                return Skel(kind, [_parse(cur, 0)], binders=names, text=cur.s[start : cur.i].strip())
    left = _parse(cur, prec + 1)
    if prec == 1:
        mw = _modal_wand(cur)
        if mw is not None:
            cur.i += len(mw[0])
            body = _parse(cur, 1)
            inner = Skel("bupd", [body]) if mw[1] is None else Skel("fupd", [body], binders=[mw[1]])
            return Skel("wand", [left, inner])
    op = _match_op(cur)
    if op is not None and op[2] == prec:
        cur.eat(op[0])
        right = _parse(cur, prec)
        if right.kind == op[1] and op[1] in ("sep", "and", "or"):
            return Skel(op[1], [left, *right.children])
        return Skel(op[1], [left, right])
    return left


def _binders(cur: _Cur):
    start = cur.i
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
            text = buf.strip()
            if not text.startswith("("):
                text = text.split(":")[0]
            names = []
            for g in re.findall(r"\(([^)]*)\)|([^\s()]+)", text):
                item = (g[0] or g[1]).split(":")[0]
                names += [n for n in item.split() if n not in (":", "_")]
            return names or None
        buf += ch
        cur.i += 1
    cur.i = start
    return None


def _prefix(cur: _Cur) -> Skel:
    cur.ws()
    m = _FUPD_RE.match(cur.s, cur.i)
    if m:
        cur.i = m.end()
        return Skel("fupd", [_parse(cur, 0)], binders=[m.group(1).strip()])
    if cur.eat("|==>"):
        return Skel("bupd", [_parse(cur, 0)])
    for tok, kind in _PREFIX:
        if cur.eat(tok):
            return Skel(kind, [_prefix(cur)])
    return _atom(cur)


def _atom(cur: _Cur) -> Skel:
    cur.ws()
    if cur.i >= len(cur.s):
        raise _GaveUp
    if cur.eat("⌜"):
        inner = _until(cur, "⌜", "⌝")
        return Skel("pure", [Skel("atom", text=inner)], text=inner)
    if cur.eat("("):
        st = cur.i
        node = _parse(cur, 0)
        if not cur.eat(")"):
            cur.i = st
            return Skel("atom", text=f"({_until(cur, '(', ')')})")
        return node
    start = cur.i
    depth = 0
    while cur.i < len(cur.s):
        ch = cur.s[cur.i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            if depth == 0:
                break
            depth -= 1
        elif depth == 0:
            if ch in ")⌝,":
                break
            if any(cur.s.startswith(t, cur.i) and _standalone(cur.s, cur.i, t) for t, _, _ in _BINOPS):
                break
            if cur.i > start and (cur.s.startswith("==∗", cur.i) or _FUPD_WAND_RE.match(cur.s, cur.i)) and cur.s[cur.i - 1].isspace():
                break
            if ch == "⌜" and cur.i > start:
                break
        cur.i += 1
    text = cur.s[start : cur.i].strip()
    if not text:
        raise _GaveUp
    return Skel("atom", text=text)


def _until(cur: _Cur, o: str, c: str) -> str:
    depth, buf = 1, ""
    while cur.i < len(cur.s):
        if cur.s.startswith(o, cur.i):
            depth += 1
        elif cur.s.startswith(c, cur.i):
            depth -= 1
            if depth == 0:
                cur.i += len(c)
                return buf.strip()
        buf += cur.s[cur.i]
        cur.i += 1
    return buf.strip()


_OPS = {"wand": ("-∗", 1), "wand_iff": ("∗-∗", 1), "iff": ("↔", 1), "impl": ("→", 1), "or": ("∨", 2), "and": ("∧", 3), "sep": ("∗", 3)}
_TIGHT = {"persistently": "■", "box": "□", "later": "▷", "except0": "◇", "affinely": "<affine>", "absorbingly": "<absorb>"}


def _render(n: Skel, prec: int) -> str:
    if n.kind == "atom":
        return n.text
    if n.kind == "pure":
        return f"⌜{n.children[0].text if n.children else n.text}⌝"
    if n.kind in _OPS:
        op, p = _OPS[n.kind]
        parts = [_render(c, p + 1) for c in n.children[:-1]] + [_render(n.children[-1], p)]
        t = f" {op} ".join(parts)
        return f"({t})" if prec > p else t
    if n.kind in _TIGHT:
        return f"{_TIGHT[n.kind]} {_render(n.children[0], 4)}"
    if n.kind == "bupd":
        t = f"|==> {_render(n.children[0], 0)}"
        return f"({t})" if prec > 0 else t
    if n.kind == "fupd":
        t = f"|={{{n.binders[0] if n.binders else '⊤'}}}=> {_render(n.children[0], 0)}"
        return f"({t})" if prec > 0 else t
    sym = "∃" if n.kind == "exists" else "∀"
    t = f"{sym} {' '.join(n.binders)}, {_render(n.children[0], 0)}"
    return f"({t})" if prec > 0 else t


# ---------------------------------------------------------------------- pattern


class PatternSyntaxError(ValueError):
    pass


@dataclass
class Pat:
    kind: str
    name: str = ""
    children: list[Pat] = field(default_factory=list)
    pure: bool = False
    intuit: bool = False
    modal: bool = False

    def render(self) -> str:
        pre = ("%" if self.pure else "") + ("#" if self.intuit else "") + (">" if self.modal else "")
        if self.kind == "name":
            return pre + self.name
        if self.kind == "list":
            return pre + "[" + " ".join(c.render() for c in self.children) + "]"
        if self.kind == "or":
            return pre + "[" + "|".join(c.render() for c in self.children) + "]"
        return pre + {"drop": "_", "fresh": "?", "empty": "[]", "rewrite": self.name or "->"}[self.kind]


def parse_pattern(text: str) -> Pat:
    pats, rest = _seq(text.strip())
    if rest.strip():
        raise PatternSyntaxError(f"trailing input after pattern: {rest.strip()!r}")
    if len(pats) != 1:
        raise PatternSyntaxError(f"expected exactly one pattern, got {len(pats)}")
    return pats[0]


def _seq(s: str):
    out = []
    while True:
        s = s.lstrip()
        if not s:
            return out, s
        p, s = _one(s)
        out.append(p)


def _one(s: str):
    s = s.lstrip()
    pure = intuit = modal = False
    while s and s[0] in "%#>":
        pure, intuit, modal = pure or s[0] == "%", intuit or s[0] == "#", modal or s[0] == ">"
        s = s[1:]

    def fin(p: Pat) -> Pat:
        p.pure, p.intuit, p.modal = pure, intuit, modal
        return p

    if not s:
        return fin(Pat("fresh")), s
    if s.startswith("[]"):
        return fin(Pat("empty")), s[2:]
    if s[0] in "[(":
        body, rest = _bracket(s)
        if s[0] == "(":
            parts = _split(body, "&")
            if len(parts) == 1:
                inner, tail = _one(parts[0])
                return fin(inner), rest
            return fin(Pat("list", children=[parse_pattern(p) for p in parts])), rest
        parts = _split(body, "|")
        if len(parts) > 1:
            return fin(Pat("or", children=[parse_pattern(p) if p.strip() else Pat("empty") for p in parts])), rest
        kids, tail = _seq(body)
        return fin(Pat("list", children=kids) if kids else Pat("empty")), rest
    if s.startswith(("->", "<-")):
        return fin(Pat("rewrite", name=s[:2])), s[2:]
    if s[0] == "_":
        return fin(Pat("drop")), s[1:]
    if s[0] == "?":
        return fin(Pat("fresh")), s[1:]
    i = 0
    while i < len(s) and (s[i].isalnum() or s[i] in "_'."):
        i += 1
    if i == 0:
        raise PatternSyntaxError(f"cannot parse pattern at {s[:12]!r}")
    return fin(Pat("name", name=s[:i])), s[i:]


def _bracket(s: str):
    depth = 0
    for i, ch in enumerate(s):
        if ch in "[(":
            depth += 1
        elif ch in "])":
            depth -= 1
            if depth == 0:
                return s[1:i], s[i + 1 :]
    raise PatternSyntaxError(f"unbalanced bracket in {s!r}")


def _split(s: str, sep: str):
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
    return [*out, buf]


@dataclass
class Compiled:
    pattern: str
    binders: list[str] = field(default_factory=list)
    pure_names: list[str] = field(default_factory=list)

    def tactic_for(self, hyp: str) -> str:
        b = f" ({' '.join(self.binders)})" if self.binders else ""
        return f'iDestruct "{hyp}" as{b} "{self.pattern}".'


def compile_auto(skel: Skel, base: str = "H", taken: set[str] | None = None) -> Compiled:
    n = [0]
    used = set(taken or ())

    def fresh(hint: str = "") -> str:
        while True:
            n[0] += 1
            name = f"{hint or base}{n[0]}"
            if name not in used:
                used.add(name)
                return name

    binders: list[str] = []
    node = skel
    while True:
        node = _strip_t(node)
        if node.kind == "exists" and node.children:
            binders += node.binders or [fresh("x")]
            node = node.children[0]
            continue
        break
    pure: list[str] = []

    def go(nd: Skel, modal: bool) -> Pat:
        intuit = False
        while True:
            if nd.kind in UPDATE:
                modal, nd = True, nd.children[0]
            elif nd.kind in TRANSPARENT:
                nd = nd.children[0]
            elif nd.kind in ("box", "persistently"):
                intuit, nd = True, nd.children[0]
            else:
                break

        def mark(p: Pat) -> Pat:
            p.intuit, p.modal = p.intuit or intuit, p.modal or modal
            return p

        if nd.kind == "pure":
            name = fresh("H")
            pure.append(name)
            return mark(Pat("name", name=name, pure=True))
        if nd.kind in ("sep", "and"):
            return mark(Pat("list", children=[go(c, False) for c in nd.children]))
        if nd.kind == "or":
            return mark(Pat("or", children=[go(c, False) for c in nd.children]))
        if nd.kind == "exists":
            w = (nd.binders or ["x"])[0]
            pure.append(w)
            return mark(Pat("list", children=[Pat("name", name=w, pure=True), go(nd.children[0], False)]))
        return mark(Pat("name", name=fresh()))

    return Compiled(go(node, False).render(), binders, pure)


def _strip_t(node: Skel) -> Skel:
    while node.kind in TRANSPARENT and len(node.children) == 1:
        node = node.children[0]
    return node


@dataclass
class Alignment:
    ok: bool
    mismatch: str = ""
    reason: str = ""
    suggestion: str = ""
    skel: Skel | None = None
    pattern: Pat | None = None

    def render(self) -> str:
        if self.ok:
            return "pattern aligns with the hypothesis' structure"
        lines = [f"pattern/prop mismatch at {self.mismatch}: {self.reason}"]
        if self.skel is not None:
            lines += ["", "prop skeleton:", self.skel.render(1)]
        if self.suggestion:
            lines += ["", f"a pattern that fits: {self.suggestion}"]
        return "\n".join(lines)


_WORD = {"sep": "a separating conjunction (∗)", "and": "a conjunction (∧)", "or": "a disjunction (∨)",
         "exists": "an existential (∃)", "pure": "a pure fact (⌜⌝)", "wand": "a wand (−∗)",
         "forall": "a universal (∀)", "impl": "an implication (→)", "atom": "an opaque proposition"}


def align(pattern, prop) -> Alignment:
    pat = parse_pattern(pattern) if isinstance(pattern, str) else pattern
    skel = parse_skeleton(prop) if isinstance(prop, str) else prop
    m = _align(pat, skel, "root")
    if m is None:
        return Alignment(True, skel=skel, pattern=pat)
    return Alignment(False, m[0], m[1], compile_auto(skel).pattern, skel, pat)


def _align(pat: Pat, node: Skel, path: str):
    while True:
        if node.kind in TRANSPARENT | {"box", "persistently"}:
            node = node.children[0]
        elif node.kind in UPDATE:
            if not pat.modal and pat.kind in ("list", "or"):
                return path, "the hypothesis is under an update modality, but the pattern does not eliminate it"
            node = node.children[0]
        else:
            break
    if pat.kind in ("name", "drop", "fresh", "rewrite", "empty"):
        return None
    if node.kind == "exists":
        if pat.kind == "list" and pat.children and pat.children[0].pure:
            rest = Pat("list", children=pat.children[1:]) if len(pat.children) > 2 else pat.children[1]
            return _align(rest, node.children[0], f"{path}.∃-body")
        return path, "the hypothesis is an existential; its witness must be introduced first"
    if pat.kind == "or":
        if node.kind != "or":
            return path, f"the pattern splits a disjunction, but the hypothesis is {_WORD.get(node.kind, node.kind)}"
        return _kids(pat, node, path)
    if node.kind not in ("sep", "and"):
        if node.kind == "or":
            return path, "the pattern splits a conjunction, but the hypothesis is a disjunction"
        return path, f"the pattern destructs, but the hypothesis has no top-level connective to destruct ({_WORD.get(node.kind, node.kind)})"
    return _kids(pat, node, path)


def _kids(pat: Pat, node: Skel, path: str):
    np_, ns = len(pat.children), len(node.children)
    if np_ > ns:
        return path, f"the pattern has {np_} components but the hypothesis has {ns}"
    if np_ < ns:
        if np_ < 2:
            return None
        for i, (p, s) in enumerate(zip(pat.children[:-1], node.children, strict=False), start=1):
            m = _align(p, s, f"{path}.{i}")
            if m:
                return m
        return _align(pat.children[-1], Skel(node.kind, node.children[np_ - 1 :]), f"{path}.{np_}+")
    for i, (p, s) in enumerate(zip(pat.children, node.children, strict=True), start=1):
        m = _align(p, s, f"{path}.{i}")
        if m:
            return m
    return None


_install()
