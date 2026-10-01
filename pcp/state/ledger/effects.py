"""Tactic effects: what a step did to the *goal*, beside what it did to resources (D2).

The resource ledger answers "where did ``H`` go"; the failures agents actually make are
about the goal instead (pcp-issues, overall assessment): a ``rewrite`` that hit the
wrong occurrence, ``iFrame`` picking an existential witness, ``wp_pures`` stopping at an
undecided comparison, side goals in an unexpected order.  Each is visible in the two
printed states around the step, so each becomes an event:

    GoalsCreated      one goal became several: each new goal, in order, with its shape
    Focus             the focused goal closed; which goal is focused next
    Rewrite           which hypothesis / the goal changed, the subterm, which occurrence,
                      and whether other occurrences of the rewritten instance remain
    FrameClosed       the goal conjuncts ``iFrame`` closed, with the hypothesis for each
    Witness           an ``∃ x`` of the goal that is gone, and what ``x`` became
    EvarInstantiated  an evar ``?x`` that is gone, and what it became
    WpStop            the redex ``wp_pures`` stopped at, and why (``redex.py``)
    CaseSplit         the ``bool_decide``/``decide`` a ``case_*`` tactic split on, and where it
                      came from -- a warning when that was a hypothesis's while the goal has
                      its own (session 5, issue 38)

Same honesty rule as the resource ledger (PLAN.md 4.4): when the states do not say,
the event says ``unknown`` (``confidence="unknown"``) rather than naming a guess.  The
effects are a pure function of (before, after, tactic), so a trace recorded without
them is re-derived, never re-run.
"""

from __future__ import annotations

import re
from collections import Counter
from collections.abc import Sequence
from dataclasses import dataclass
from typing import Any

from pcp.state.ipm.model import Hyp, IrisGoal
from pcp.state.ipm.skeleton import parse_skeleton
from pcp.state.ledger.diff import WARNING, align_goals
from pcp.state.ledger.events import EFFECT_KINDS, Event
from pcp.state.props import normalize_prop
from pcp.state.redex import next_redex, wp_expr
from pcp.state.tactic import TacticCall, parse_tactic
from pcp.state.terms import changes, count_occurrences, evars, match_template, substitute, tokens, unparen

__all__ = ["EFFECT_KINDS", "effect_lines", "shape", "step_effects"]

REWRITE_HEADS: frozenset[str] = frozenset({"rewrite", "erewrite", "setoid_rewrite", "rewrite_all", "iRewrite", "rewrite_strat"})
WP_PURE_HEADS: frozenset[str] = frozenset({
    "wp_pures", "wp_pure", "wp_lam", "wp_rec", "wp_let", "wp_seq", "wp_if", "wp_op", "wp_proj", "wp_match",
    "wp_inj", "wp_closure", "wp_case", "wp_if_true", "wp_if_false", "wp_binop", "wp_unop",
})
#: Modalities looked through to find a goal's ∃ / conjuncts (iExists and iFrame do).
_PEEL = frozenset({"later", "except0", "affinely", "absorbingly", "fupd", "bupd", "fupd_step"})
#: Heap operations whose tactic needs the location's points-to in the context.
_NEEDS_POINTSTO = ("wp_load", "wp_store", "wp_cmpxchg", "wp_xchg", "wp_faa", "wp_free")
_SHAPE_WIDTH = 110
#: stdpp's case splits on a decision: each takes the *first* match in the Coq goal, and
#: the Iris context is part of that goal (hypotheses before the conclusion).
CASE_HEADS: frozenset[str] = frozenset({"case_bool_decide", "case_decide", "case_guard"})
_DECIDERS = {"case_bool_decide": "bool_decide", "case_decide": "decide", "case_guard": "decide"}


def step_effects(prev_goals: Sequence[IrisGoal], next_goals: Sequence[IrisGoal], *, step: int, tactic: str) -> list[Event]:
    """The effect events of one successful step.  Never raises: an effect report that
    breaks the step it describes would be worse than none."""
    try:
        return _effects(list(prev_goals), list(next_goals), step, tactic)
    except Exception:  # noqa: BLE001 -- best effort by contract (module docstring)
        return []


@dataclass(frozen=True)
class _Ctx:
    step: int
    tactic: str
    call: TacticCall

    def event(self, kind: str, goal_id: str, detail: str, *, confidence: str = "certain",
              hyp: str | None = None, data: dict[str, Any] | None = None, **kw: Any) -> Event:
        return Event(step=self.step, kind=kind, tactic=self.tactic, goal_id=goal_id, hyp=hyp,  # type: ignore[arg-type]
                     detail=detail, confidence=confidence, klass="effect", data=dict(data or {}), **kw)  # type: ignore[arg-type]


def _effects(prev: list[IrisGoal], next_: list[IrisGoal], step: int, tactic: str) -> list[Event]:
    if not prev:
        return []
    al = align_goals(prev, next_)
    if al.parent is None or len(al.touched) > 1:
        # Several goals changed at once (`all: …`): per-goal attribution is not reliable.
        return []
    ctx = _Ctx(step, tactic.strip(), parse_tactic(tactic))
    parent, children = al.parent, al.children
    child = children[0] if children else None
    out: list[Event] = []
    if len(children) > 1:
        out.append(_goals_created(ctx, parent, children))
    elif child is None and next_:
        nxt = next_[0]
        out.append(ctx.event("Focus", nxt.goal_id, f"the focused goal closed; now focused: {nxt.goal_id} `{shape(nxt)}`"
                             + (f" ({len(next_) - 1} more after it)" if len(next_) > 1 else ""),
                             targets=[nxt.goal_id]))
    consumed = _consumed(ctx, parent, child)
    witness, wevents = _witnesses(ctx, parent, child, consumed)
    out += wevents
    evenv, eevents = _evars(ctx, prev, next_, al.untouched, parent, child, consumed)
    out += eevents
    head = ctx.call.head
    if head in REWRITE_HEADS:
        out += _rewrite(ctx, parent, child)
    if ctx.call.mentions("iFrame"):
        out.append(_frame(ctx, parent, child, consumed, {**witness, **evenv}))
    if head in WP_PURE_HEADS:
        out.append(_wp_stop(ctx, parent, child))
    if head in CASE_HEADS and len(children) > 1:
        out += _case_split(ctx, parent, children)
    return out


# --------------------------------------------------------------------- shapes


def shape(goal: IrisGoal, width: int = _SHAPE_WIDTH) -> str:
    """One line for a goal: its conclusion, cut at ``width``."""
    one = " ".join(goal.goal.split())
    return one if len(one) <= width else one[: width - 1] + "…"


def _is_side(goal: IrisGoal) -> bool:
    text = goal.goal.strip()
    return not goal.is_ipm or text.startswith("⌜") or getattr(parse_skeleton(text), "kind", "") == "pure"


def _goals_created(ctx: _Ctx, parent: IrisGoal, children: list[IrisGoal]) -> Event:
    items = []
    shapes = Counter(shape(g) for g in children)
    for i, g in enumerate(children, start=1):
        tag = " (pure side condition)" if _is_side(g) else ""
        if shapes[shape(g)] > 1:
            # Case splits print the same conclusion: what tells the cases apart is what each introduced.
            twins = [c for c in children if shape(c) == shape(g)]
            common = set.intersection(*({(h.id, normalize_prop(h.prop)) for h in _fresh_hyps(parent, c)} for c in twins))
            fresh = [h for h in _fresh_hyps(parent, g) if (h.id, normalize_prop(h.prop)) not in common]
            tag += (" with " + ", ".join(f'{h.id} : {_cut(" ".join(h.prop.split()), 50)}' for h in fresh[:3])) if fresh else ""
        items.append(f"[{i}] {g.goal_id}: `{shape(g)}`{tag}")
    data = {"goals": [{"id": g.goal_id, "shape": shape(g), "side": _is_side(g)} for g in children]}
    return ctx.event("GoalsCreated", parent.goal_id,
                     f"one goal became {len(children)}, in order: " + "; ".join(items),
                     targets=[g.goal_id for g in children], data=data)


def _fresh_hyps(parent: IrisGoal, child: IrisGoal) -> list[Hyp]:
    old = {(h.id, normalize_prop(h.prop)) for h in parent.all_hyps}
    return [h for h in child.all_hyps if (h.id, normalize_prop(h.prop)) not in old]


# ------------------------------------------------------------------ conjuncts


def _text(node: Any) -> str:
    if getattr(node, "kind", "") == "atom":
        return str(getattr(node, "text", ""))
    return str(node.to_notation())


def _peel(node: Any) -> Any:
    while getattr(node, "kind", "") in _PEEL and getattr(node, "children", None):
        node = node.children[0]
    return node


def _conjuncts(node: Any) -> list[str]:
    node = _peel(node)
    kind = getattr(node, "kind", "")
    if kind == "sep":
        return [c for ch in node.children for c in _conjuncts(ch)]
    if kind == "exists" and node.children:
        return _conjuncts(node.children[0])
    return [_text(node)]


def _goal_conjuncts(goal: IrisGoal | None) -> list[str]:
    if goal is None or not goal.goal.strip():
        return []
    return [c for c in _conjuncts(parse_skeleton(goal.goal)) if c.strip() not in ("True", "emp")]


def _key(prop: str) -> str:
    """Comparison key of a conjunct: a sep operand prints parenthesised, the whole goal not."""
    return normalize_prop(unparen(prop))


def _consumed(ctx: _Ctx, parent: IrisGoal, child: IrisGoal | None) -> list[Hyp]:
    """Spatial hypotheses the step spent, plus intuitionistic ones it named."""
    kept = {h.id for h in child.spatial} if child is not None else set()
    out = [h for h in parent.spatial if h.id not in kept]
    named = set(ctx.call.all_strings)
    out += [h for h in parent.intuitionistic if h.id in named]
    return out


# ----------------------------------------------------------------- witnesses


#: Tactics that introduce the goal's existential (their witness may be named in the tactic).
_EXISTS_HEADS = frozenset({"iExists", "exists", "eexists", "iFrame", "iSplit", "iSplitL", "iSplitR"})


def _witnesses(ctx: _Ctx, parent: IrisGoal, child: IrisGoal | None, consumed: list[Hyp]) -> tuple[dict[str, str], list[Event]]:
    """``∃ x y, body`` at the head of the goal before; after the step some binders are gone.

    A binder is reported only when the step instantiated it: the body before, with the
    binder as a variable, must match what is there after (whole, or conjunct by conjunct
    against what remains and what was spent), or the tactic must be one that introduces
    the existential.  An ``iApply`` that replaced the goal wholesale did not "instantiate"
    anything, and saying so would be a guess.
    """
    if not parent.goal.strip():
        return {}, []
    node = _peel(parse_skeleton(parent.goal))
    if getattr(node, "kind", "") != "exists" or not node.children:
        return {}, []
    binders = [b for b in node.binders if b != ".."]  # `∃.. x` telescopes print a `..` binder
    if not binders:
        return {}, []
    body = node.children[0]
    after_text: str | None = None
    gone = binders
    if child is not None and child.goal.strip():
        cnode = _peel(parse_skeleton(child.goal))
        cb = [b for b in getattr(cnode, "binders", []) if b != ".."]
        if getattr(cnode, "kind", "") == "exists" and cnode.children and cb:
            if len(cb) >= len(binders):
                return {}, []  # still quantified (at most alpha-renamed): nothing instantiated
            gone = binders[: len(binders) - len(cb)]
            # The remaining binders may be renamed (`x` -> `x0`); rename them back first.
            after_text = substitute(_text(cnode.children[0]), dict(zip(cb, binders[len(gone):], strict=True)))
        else:
            after_text = _text(cnode)
    env: dict[str, str] = {}
    if after_text is not None:
        env = match_template(_text(body), set(gone), after_text) or {}
    if len(env) < len(gone):
        # iFrame also removed conjuncts: match piecewise against what is left and what was spent.
        others = _goal_conjuncts(child) + [h.prop for h in consumed]
        for conj in _conjuncts(body):
            want = {v for v in gone if v not in env and v in {t.text for t in tokens(conj)}}
            if not want:
                continue
            templ = substitute(conj, env)
            for other in others:
                got = match_template(templ, want, other)
                if got:
                    env.update(got)
                    break
    explicit = _explicit_witnesses(ctx.call, gone)
    gid = (child or parent).goal_id
    events = []
    for v in gone:
        if v in env:
            events.append(ctx.event("Witness", gid, f"the goal's `∃ {v}` was instantiated with `{env[v]}`",
                                    data={"binder": v, "value": env[v]}))
        elif v in explicit:
            env[v] = explicit[v]
            events.append(ctx.event("Witness", gid, f"the goal's `∃ {v}` was instantiated with `{explicit[v]}` "
                                    "(as given in the tactic)", data={"binder": v, "value": explicit[v]}))
        elif ctx.call.head in _EXISTS_HEADS or ctx.call.mentions("iFrame"):
            events.append(ctx.event("Witness", gid, f"the goal's `∃ {v}` was instantiated; the witness is unknown "
                                    "(it is not visible in the printed states)", confidence="unknown",
                                    data={"binder": v, "value": None}))
    return env, events


def _explicit_witnesses(call: TacticCall, gone: list[str]) -> dict[str, str]:
    """``iExists a, b`` / ``exists a`` name the witnesses in order; ``_`` names none."""
    if call.head not in ("iExists", "exists", "eexists"):
        return {}
    text = call.text[len(call.head):].split(";", 1)[0].strip().rstrip(".").strip()
    text = text.split(" =>", 1)[0]  # an ssreflect intro suffix (`iExists x => /=`)
    args = [" ".join(a.split()) for a in _top_commas(text)]
    return {v: unparen(a) for v, a in zip(gone, args, strict=False) if a and a != "_"}


def _top_commas(text: str) -> list[str]:
    out, depth, buf = [], 0, ""
    for ch in text:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(buf)
            buf = ""
        else:
            buf += ch
    return [*out, buf] if buf.strip() else out


# --------------------------------------------------------------------- evars


def _texts(goal: IrisGoal) -> dict[str, str]:
    out = {"goal": goal.goal}
    for h in goal.all_hyps:
        out.setdefault(h.id, h.prop)
    return out


def _evars(ctx: _Ctx, prev: list[IrisGoal], next_: list[IrisGoal], untouched: list[IrisGoal],
           parent: IrisGoal, child: IrisGoal | None, consumed: list[Hyp]) -> tuple[dict[str, str], list[Event]]:
    before = {e for g in prev for t in _texts(g).values() for e in evars(t)}
    after = {e for g in next_ for t in _texts(g).values() for e in evars(t)}
    gone = [e for e in dict.fromkeys(e for g in prev for t in _texts(g).values() for e in evars(t)) if e not in after]
    if not gone or not before:
        return {}, []
    pairs: list[tuple[str, str, str]] = []
    counterparts = ([(parent, child)] if child is not None else []) + list(zip(prev[len(prev) - len(untouched):], untouched, strict=True))
    for old, new in counterparts:
        if new is None:
            continue
        nt = _texts(new)
        for where, text in _texts(old).items():
            if where in nt and text != nt[where] and evars(text):
                pairs.append((where, text, nt[where]))
    found: dict[str, tuple[str, str]] = {}
    for where, text, new_text in pairs:
        if all(e in found for e in gone):
            break
        got = match_template(text, set(evars(text)), new_text)
        if got:
            for e, val in got.items():
                if e in gone and e not in found and val != e:
                    found[e] = (val, where)
    # A conjunct `l ↦ ?v` framed away: the spent hypothesis shows what `?v` became.
    for conj in _goal_conjuncts(parent):
        want = {e for e in evars(conj) if e in gone and e not in found}
        if not want:
            continue
        for h in consumed:
            got = match_template(conj, set(evars(conj)), h.prop)
            if got:
                for e in want & set(got):
                    found[e] = (got[e], f'"{h.id}"')
                break
    gid = (child or parent).goal_id
    out = []
    for e in gone:
        if e in found:
            val, where = found[e]
            loc = "the goal" if where == "goal" else (where if where.startswith('"') else f'"{where}"')
            out.append(ctx.event("EvarInstantiated", gid, f"`{e}` := `{val}` (read off {loc})",
                                 data={"evar": e, "value": val, "where": where}))
        else:
            out.append(ctx.event("EvarInstantiated", gid, f"`{e}` was instantiated; its value is unknown "
                                 "(no printed term shows it)", confidence="unknown", data={"evar": e, "value": None}))
    return {e: v for e, (v, _) in found.items()}, out


# ------------------------------------------------------------------- rewrite


def _rewrite(ctx: _Ctx, parent: IrisGoal, child: IrisGoal | None) -> list[Event]:
    if child is None:
        return [ctx.event("Rewrite", parent.goal_id, "the rewrite closed the goal (the result was solved by reflexivity)")]
    targets: list[tuple[str | None, str, str]] = []
    if parent.goal != child.goal:
        targets.append((None, parent.goal, child.goal))
    after = {h.id: h for h in child.all_hyps}
    for h in parent.all_hyps:
        nh = after.get(h.id)
        if nh is not None and normalize_prop(nh.prop) != normalize_prop(h.prop):
            targets.append((h.id, h.prop, nh.prop))
    if not targets:
        return [ctx.event("Rewrite", child.goal_id, "no printed term changed (the rewrite touched only what the printer "
                          "hides, e.g. implicit arguments or coercions)", confidence="unknown")]
    return [_rewrite_site(ctx, child.goal_id, name, old, new) for name, old, new in targets]


def _rewrite_site(ctx: _Ctx, gid: str, name: str | None, before: str, after: str) -> Event:
    where = "the goal" if name is None else f'"{name}"' if name else ""
    sites = changes(before, after)
    data: dict[str, Any] = {"target": name or "goal", "sites": [{"old": s.old, "new": s.new} for s in sites]}
    if not sites:
        return ctx.event("Rewrite", gid, f"rewrote {where}; the change is not localisable", hyp=name,
                         confidence="unknown", data=data)
    olds = {s.old_tokens for s in sites}
    if len(sites) > 3 or len(olds) > 2:
        return ctx.event("Rewrite", gid, f"rewrote {where} in {len(sites)} places (first: `{_cut(sites[0].old)}` → "
                         f"`{_cut(sites[0].new)}`); which occurrences is not determinable", hyp=name,
                         confidence="unknown", data=data)
    btoks, atoks = [t.text for t in tokens(before)], [t.text for t in tokens(after)]
    parts = []
    for old in dict.fromkeys(s.old_tokens for s in sites):
        mine = [s for s in sites if s.old_tokens == old]
        occ = count_occurrences(list(old), btoks)
        # Occurrences inside the replacement itself (`F` -> `↑N ∪ F ∖ ↑N`) were not left behind.
        inside = sum(len(count_occurrences(list(old), [t.text for t in tokens(s.new)])) for s in sites)
        left = max(0, len(count_occurrences(list(old), atoks)) - inside)
        text = f"`{_cut(mine[0].old)}` → `{_cut(mine[0].new)}`"
        if len(occ) <= 1:
            text += " (its only occurrence)" if left == 0 else ""
        elif len(mine) == len(occ):
            text += f" (all {len(occ)} occurrences)"
        else:
            ords = [occ.index(s.at) + 1 for s in mine if s.at in occ]
            nth = ", ".join(str(o) for o in ords) if ords else "?"
            text += f" (occurrence {nth} of {len(occ)})"
        if left:
            text += f"; {left} other occurrence{'s' if left > 1 else ''} of `{_cut(mine[0].old)}` remain{'s' if left == 1 else ''}"
        parts.append(text)
    return ctx.event("Rewrite", gid, f"in {where}: " + "; ".join(parts), hyp=name, data=data)


def _cut(text: str, width: int = 80) -> str:
    return text if len(text) <= width else text[: width - 1] + "…"


# --------------------------------------------------------------------- iFrame


def _frame(ctx: _Ctx, parent: IrisGoal, child: IrisGoal | None, consumed: list[Hyp], witness: dict[str, str]) -> Event:
    before = [substitute(c, witness) if witness else c for c in _goal_conjuncts(parent)]
    after = Counter(_key(c) for c in _goal_conjuncts(child))
    closed: list[str] = []
    for c in before:
        key = _key(c)
        if after[key]:
            after[key] -= 1
        else:
            closed.append(c)
    by_prop: dict[str, list[Hyp]] = {}
    for h in consumed:
        by_prop.setdefault(_key(h.prop), []).append(h)
    items = []
    rows = []
    for c in closed:
        hs = by_prop.get(_key(c)) or []
        by = hs.pop(0).id if hs else None
        items.append(f'`{c}`' + (f' with "{by}"' if by else ""))
        rows.append({"conjunct": c, "by": by})
    spent = [h.id for h in consumed]
    left = [c for c in _goal_conjuncts(child) if _key(c) not in {_key(b) for b in before}]
    gid = (child or parent).goal_id
    data = {"closed": rows, "consumed": spent, "left": left}
    if not closed and not spent:
        return ctx.event("FrameClosed", gid, "no goal conjunct visibly closed and no hypothesis was spent",
                         confidence="unknown", data=data)
    detail = "closed " + (", ".join(items) if items else "no conjunct visibly")
    if spent:
        detail += "; spent " + ", ".join(f'"{n}"' for n in spent)
    if child is None:
        detail += "; the goal is closed"
    elif left:
        detail += "; new or changed conjuncts: " + ", ".join(f"`{c}`" for c in left[:4])
    return ctx.event("FrameClosed", gid, detail, data=data)


# -------------------------------------------------------------------- wp_pures


def _wp_stop(ctx: _Ctx, parent: IrisGoal, child: IrisGoal | None) -> Event:
    if child is None:
        return ctx.event("WpStop", parent.goal_id, "the goal closed", data={"kind": "closed"})
    expr = wp_expr(child.goal)
    if expr is None:
        return ctx.event("WpStop", child.goal_id, f"the program reduced to a value; the goal is now `{shape(child)}`",
                         data={"kind": "value"})
    red = next_redex(expr)
    before = wp_expr(parent.goal)
    stuck = before is not None and normalize_prop(before) == normalize_prop(expr)
    lead = "made no progress: " if stuck else ""
    data = {"kind": red.kind, "redex": red.text, "next": red.next}
    if red.kind in ("pure", "beta") and ctx.call.head == "wp_pures":
        # A pure redex `wp_pures` itself left behind: the printed term does not say why.
        return ctx.event("WpStop", child.goal_id, f"{lead}stopped at `{red.text}`, which looks pure; why "
                         "`wp_pures` did not take it is unknown", confidence="unknown", data=data)
    if red.kind == "unknown":
        return ctx.event("WpStop", child.goal_id, f"{lead}stopped at `{red.text}`; why is unknown",
                         confidence="unknown", data=data)
    detail = f"{lead}stopped at `{red.text}`: {red.why}"
    if red.kind == "heap" and red.loc and red.next.startswith(_NEEDS_POINTSTO):
        loc = red.loc.lstrip("#")
        if not any(_points_to(h.prop, loc) for h in child.spatial + child.intuitionistic):
            detail += (f"; there is no `{loc} ↦ …` in the context yet (`{red.next.split()[0]}` needs one: from an "
                       "invariant or atomic update, or split out of an array/big-op)")
    return ctx.event("WpStop", child.goal_id, detail, data=data)


def _points_to(prop: str, loc: str) -> bool:
    toks = [t.text for t in tokens(prop)]
    return len(toks) >= 2 and toks[0] == loc and toks[1] == "↦"


# ------------------------------------------------------------------ rendering


def effect_lines(events: Sequence[Event]) -> list[str]:
    """The effect events of a step as one line each (what ``proof_step`` shows)."""
    out = []
    for e in events:
        if e.kind in EFFECT_KINDS:
            line = f"{e.kind}: {e.detail}"
            if e.confidence == "unknown":
                line += "  [unknown]"
            out.append(line)
    return out


# ---------------------------------------------------------------- case splits


def _decisions(text: str, fn: str) -> list[str]:
    """The propositions ``P`` of every ``fn P`` / ``fn (P)`` in ``text``, normalized."""
    out: list[str] = []
    flat = " ".join(text.split())
    for m in re.finditer(rf"(?<![\w.']){re.escape(fn)}\s+", flat):
        i = m.end()
        if i < len(flat) and flat[i] == "(":
            depth = 0
            for j in range(i, len(flat)):
                depth += flat[j] == "("
                depth -= flat[j] == ")"
                if depth == 0:
                    out.append(unparen(flat[i:j + 1]).strip())
                    break
        else:
            word = re.match(r"[\w'.]+", flat[i:])
            if word:
                out.append(word.group(0))
    return out


def _case_split(ctx: _Ctx, parent: IrisGoal, children: list[IrisGoal]) -> list[Event]:
    """Which decision a ``case_bool_decide`` split on, and whether it was the goal's (issue 38).

    stdpp's tactic splits on the first ``bool_decide`` in the whole Coq goal, and the
    Iris context comes before the conclusion: right after ``wp_pures`` it can pick one
    inside ``HΦ`` rather than the program's ``if``, and the follow-up tactics then fail
    with messages that mention neither.
    """
    fn = _DECIDERS[ctx.call.head]
    old = {h.id for h in parent.all_hyps}
    fresh = [h for h in children[0].pure if h.id not in old]
    if not fresh:
        return []
    prop = " ".join(fresh[0].prop.split())
    prop = unparen(prop[1:].strip()) if prop.startswith("¬") else prop
    key = _key(prop)
    in_goal = [p for p in _decisions(parent.goal, fn)]
    sources = [h.id for h in parent.all_hyps if any(_key(p) == key for p in _decisions(h.prop, fn))]
    if any(_key(p) == key for p in in_goal) or not sources:
        return [ctx.event("CaseSplit", children[0].goal_id, f"split on `{fn} ({_cut(prop)})`"
                          + (" of the goal" if in_goal else ""), hyp=fresh[0].id, data={"prop": prop})]
    if not in_goal:
        return [ctx.event("CaseSplit", children[0].goal_id, f'split on `{fn} ({_cut(prop)})` from "{sources[0]}"',
                          hyp=fresh[0].id, sources=sources[:1], data={"prop": prop, "from": sources[0]})]
    other = in_goal[0]
    detail = (f'{WARNING}{ctx.call.head} split on `{fn} ({_cut(prop)})` from "{sources[0]}", not on the goal\'s '
              f"`{fn} ({_cut(other)})`: it takes the first `{fn}` anywhere, the Iris context included. To split on "
              f"the goal's: `destruct_decide (bool_decide_reflect ({_cut(other)})) as {fresh[0].id}`"
              if fn == "bool_decide" else
              f'{WARNING}{ctx.call.head} split on `{fn} ({_cut(prop)})` from "{sources[0]}", not on the goal\'s '
              f"`{fn} ({_cut(other)})`: it takes the first `{fn}` anywhere, the Iris context included. To split on "
              f"the goal's: `destruct (decide ({_cut(other)})) as [{fresh[0].id}|{fresh[0].id}]`")
    return [ctx.event("CaseSplit", children[0].goal_id, detail, hyp=fresh[0].id, sources=sources[:1],
                      data={"prop": prop, "from": sources[0], "goal": other})]
