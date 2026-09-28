"""The next redex of a printed heap_lang WP, and why ``wp_pures`` cannot take it (D2).

``wp_pures`` stops for a handful of reasons, each with its own next move: a heap
operation (``wp_load``), a call to a definition (``wp_apply`` its spec), a branch on an
undecided comparison (``case_bool_decide``), a ``match:`` on an opaque value
(``destruct``).  The printed expression says which, once the evaluation position is
found: ``let:``/``;;`` evaluate their first part, ``if:``/``match:`` their scrutinee, and
applications and operators their arguments right to left (heap_lang's order).

Best effort over the *printed* notation, so every answer carries a ``kind``; an
expression the walker does not recognise gets ``unknown`` -- never a guessed reason.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

from pcp.state.ipm.model import _split_wp  # the WP printer's own term/postcondition split

#: Heap operations and the tactic that steps each.
HEAP_OPS: dict[str, tuple[str, str]] = {
    "!": ("a load", "wp_load"),
    "ref": ("an allocation", "wp_alloc"),
    "AllocN": ("an array allocation", "wp_allocN"),
    "Free": ("a free", "wp_free"),
    "CmpXchg": ("a compare-and-exchange", "wp_cmpxchg (or wp_cmpxchg_suc / wp_cmpxchg_fail)"),
    "Xchg": ("an exchange", "wp_xchg"),
    "FAA": ("a fetch-and-add", "wp_faa"),
    "Fork": ("a fork", "wp_fork"),
    "NewProph": ("a prophecy allocation", "wp_new_proph"),
    "Resolve": ("a prophecy resolution", "wp_resolve"),
    "<-": ("a store", "wp_store"),
}
#: Pure projections/constructors: stuck only on an argument whose shape is not visible.
_PURE_HEADS = frozenset({"Fst", "Snd", "InjL", "InjR", "Pair", "~", "-"})
_INFIX = ("=", "<", "≤", "+", "-", "*", "`quot`", "`rem`", "+ₗ", "≠", "&&", "||", "`and`", "`or`", "≫", "≪")
_KEYWORDS = frozenset({"let:", "if:", "match:", "then", "else", "in", "with", "end", ":=", "=>", "|", ";;", "λ:", "rec:"})
_IDENT = re.compile(r"^[^\W\d][\w'.]*$")
_BOOL_DECIDE = re.compile(r"bool_decide\s*\((?P<prop>.*)\)\s*\)?$", re.S)


@dataclass(frozen=True)
class Redex:
    #: The subterm in evaluation position (a one-line excerpt).
    text: str
    #: ``heap`` | ``call`` | ``beta`` | ``pure`` | ``branch`` | ``match`` | ``opaque`` | ``value`` | ``unknown``
    kind: str
    #: Why ``wp_pures`` stops here and what steps it; ``""`` when not known.
    why: str = ""
    #: The tactic that steps it, when known.
    next: str = ""
    #: For heap operations: the location operand (``#l``), to look for its points-to.
    loc: str = ""


def wp_expr(prop: str) -> str | None:
    """The program term of the WP at the head of ``prop`` (modalities peeled), else ``None``."""
    text = " ".join(prop.split())
    depth = 0
    for i, ch in enumerate(text):
        if ch in "([{":
            depth += 1
        elif ch in ")]}" and depth:
            depth -= 1
        elif depth == 0 and text.startswith("WP ", i) and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")):
            head = text[:i]
            # Only modality prefixes may precede the WP at its head: `P -∗ WP …` is a wand.
            if re.search(r"-∗|∗|→|∧|∨|,", head):
                return None
            expr, _ = _split_wp(text[i + 3 :])
            return expr or None
    return None


def _top(text: str) -> list[str]:
    """Whitespace-separated tokens at bracket depth 0, strings kept whole."""
    out: list[str] = []
    depth = 0
    buf = ""
    in_str = False
    for ch in text:
        if ch == '"':
            in_str = not in_str
        elif not in_str:
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth = max(0, depth - 1)
        if ch.isspace() and depth == 0 and not in_str:
            if buf:
                out.append(buf)
            buf = ""
        else:
            buf += ch
    if buf:
        out.append(buf)
    return out


def _strip(expr: str) -> str:
    e = " ".join(expr.split())
    for _ in range(8):
        if e.endswith("%E"):
            e = e[:-2].strip()
        if e.startswith("(") and e.endswith(")") and _closes_at_end(e):
            e = e[1:-1].strip()
            continue
        break
    return e


def _closes_at_end(e: str) -> bool:
    depth = 0
    for i, ch in enumerate(e):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
            if depth == 0 and i != len(e) - 1:
                return False
    return depth == 0


def is_value(expr: str) -> bool:
    """A visibly-a-value operand: a literal, a ``%V`` term, an injection value, or a Coq
    variable (``v``, ``w1``: of type ``val`` wherever it sits in argument position)."""
    e = " ".join(expr.split())
    if not e:
        return False
    if e.startswith("#") or e.endswith("%V") or e.startswith(("InjLV", "InjRV", "λ:", "rec:")):
        return True
    return bool(_IDENT.match(e)) and e not in HEAP_OPS and not e.startswith('"')


def _kw_index(toks: list[str], start: int, opener: str, closer: str) -> int:
    """The index of the ``closer`` that ends the construct ``opener`` began (nesting aware)."""
    depth = 0
    for i in range(start, len(toks)):
        if toks[i] == opener:
            depth += 1
        elif toks[i] == closer:
            if depth == 0:
                return i
            depth -= 1
    return -1


def _excerpt(text: str, width: int = 80) -> str:
    one = " ".join(text.split())
    return one if len(one) <= width else one[: width - 1] + "…"


def next_redex(expr: str, *, _depth: int = 0) -> Redex:
    e = _strip(expr)
    if not e or _depth > 24:
        return Redex(_excerpt(expr), "unknown")
    toks = _top(e)
    head = toks[0]
    if head == "let:":
        k = toks.index(":=") if ":=" in toks else -1
        end = _kw_index(toks, k + 1, "let:", "in") if k >= 0 else -1
        if k < 0 or end < 0:
            return Redex(_excerpt(e), "unknown")
        bound = " ".join(toks[k + 1 : end])
        if not is_value(bound):
            return next_redex(bound, _depth=_depth + 1)
        return Redex(_excerpt(e), "pure", "a `let:` of a value: a pure step (`wp_pures`, or `wp_let`)", "wp_pures")
    if head == "if:":
        end = _kw_index(toks, 1, "if:", "then")
        cond = " ".join(toks[1:end]) if end > 0 else ""
        if not cond:
            return Redex(_excerpt(e), "unknown")
        if not is_value(cond):
            return next_redex(cond, _depth=_depth + 1)
        return _stuck_if(cond, e)
    if head == "match:":
        end = _kw_index(toks, 1, "match:", "with")
        scrut = " ".join(toks[1:end]) if end > 0 else ""
        if not scrut:
            return Redex(_excerpt(e), "unknown")
        if not is_value(scrut):
            return next_redex(scrut, _depth=_depth + 1)
        return Redex(f"match: {_excerpt(scrut, 40)} with …", "match",
                     f"the scrutinee `{scrut}` is not a visible `InjLV`/`InjRV`, so no branch can be chosen: "
                     "destruct the value it stands for (or rewrite with what you know about it)")
    if ";;" in toks:
        return next_redex(" ".join(toks[: toks.index(";;")]), _depth=_depth + 1)
    if "<-" in toks:
        i = toks.index("<-")
        lhs, rhs = " ".join(toks[:i]), " ".join(toks[i + 1 :])
        for part in (rhs, lhs):
            if not is_value(part):
                return next_redex(part, _depth=_depth + 1)
        return _heap("<-", e, lhs)
    for op in _INFIX:
        if op in toks[1:]:
            i = toks.index(op, 1)
            lhs, rhs = " ".join(toks[:i]), " ".join(toks[i + 1 :])
            for part in (rhs, lhs):
                if not is_value(part):
                    return next_redex(part, _depth=_depth + 1)
            return Redex(_excerpt(e), "unknown")
    args = toks[1:]
    for arg in reversed(args):
        if not is_value(arg):
            return next_redex(arg, _depth=_depth + 1)
    if head in HEAP_OPS:
        return _heap(head, e, args[0] if args else "")
    if head in _PURE_HEADS:
        opaque = [a for a in args if _IDENT.match(a)]
        if opaque:
            return Redex(_excerpt(e), "opaque",
                         f"`{head}` needs a visible pair/injection, but `{opaque[0]}` is a Coq variable whose shape "
                         "the WP cannot see: destruct it or rewrite with its definition")
        return Redex(_excerpt(e), "pure", f"`{head}` of a visible value: a pure step (`wp_pures`)", "wp_pures")
    if head.startswith("(") and not is_value(head):
        return next_redex(head, _depth=_depth + 1)
    if not args:
        return Redex(_excerpt(e), "value" if is_value(e) else "unknown")
    if head.startswith(("(λ:", "(rec:", "λ:", "rec:")):
        return Redex(_excerpt(e), "beta", "a β-redex with value arguments: `wp_pure` (or `wp_rec`/`wp_lam`) steps it",
                     "wp_pure")
    if _IDENT.match(head) and head not in _KEYWORDS:
        return Redex(_excerpt(e), "call",
                     f"a call to `{head}`, a definition `wp_pures` does not unfold: `wp_apply` its specification "
                     f"(or unfold it: `rewrite /{head.split('.')[-1]}` then `wp_pures`)", "wp_apply")
    return Redex(_excerpt(e), "unknown")


def _heap(op: str, e: str, loc: str) -> Redex:
    what, tac = HEAP_OPS[op]
    return Redex(_excerpt(e), "heap", f"{what}: `wp_pures` only takes pure steps; `{tac.split()[0]}` steps it", tac, loc)


def _stuck_if(cond: str, e: str) -> Redex:
    text = f"if: {_excerpt(cond, 60)} then …"
    inner = cond[1:].strip() if cond.startswith("#") else cond
    inner = inner[1:-1].strip() if inner.startswith("(") and inner.endswith(")") else inner
    m = _BOOL_DECIDE.search(inner)
    if m:
        prop = m.group("prop").strip()
        prop = prop[1:-1].strip() if prop.startswith("(") and prop.endswith(")") and _closes_at_end(prop) else prop
        sides = [s.strip() for s in prop.split("=", 1)] if prop.count("=") == 1 else []
        if len(sides) == 2 and sides[0] == sides[1]:
            return Redex(text, "branch",
                         f"the condition `bool_decide ({prop})` compares a term with itself but is not simplified: "
                         "`rewrite bool_decide_eq_true_2 //` (or `case_bool_decide`)", "case_bool_decide")
        return Redex(text, "branch",
                     f"the branch condition `bool_decide ({prop})` is undecided on these variables: case on it "
                     f"(`case_bool_decide`, or `destruct (decide ({prop}))`)", "case_bool_decide")
    if _IDENT.match(inner) and inner not in ("true", "false"):
        return Redex(text, "branch", f"the branch condition is the Coq boolean `{inner}`: `destruct {inner}`",
                     f"destruct {inner}")
    return Redex(text, "unknown")
