"""The invariant-opening helper: the ``iInv`` pattern from the invariant's definition (MF6).

Opening one invariant fifteen times by hand means fifteen chances to put ``>`` on the
wrong conjunct.  The rule is mechanical once the facts are known: after ``iInv`` the
body sits under ``▷``, and ``>`` (an ``iMod`` of that later, through ``◇``) strips it
*only from a Timeless prop*; a non-Timeless conjunct must stay ``▷``, and a ``>`` on it
fails with "iMod: cannot eliminate modality".  Pure conjuncts are timeless and need the
``>`` too: ``%H`` alone on ``▷ ⌜φ⌝`` is an ``Inhabited`` error, not an intro.

So the facts are asked of Rocq, never guessed from the printed prop:

1. **Structure.**  The body of ``inv N P`` is read from the hypothesis; a named predicate
   (``I γ l``) is unfolded by a speculative ``unfold I.`` and re-read -- Rocq substitutes
   the arguments, so the pattern is about *this* instance.  At most ``MAX_UNFOLDS``.
2. **Timelessness.**  One speculative run opens the invariant with the pattern minus
   every ``>`` and, per non-pure conjunct, reverts it and asks ``Timeless`` by typeclass
   search (the persistence oracle's approach, ``ipm/oracle.py``, asked of the instance
   rather than of a tactic's failure message).
3. **Verification.**  The final tactic is run speculatively; its failure is reported.

Existential binders keep the definition's own names when fresh against the Coq
context; hypothesis names are derived from each conjunct (``l ↦ _`` -> ``"Hl"``,
``ghost_var γ _ _`` -> ``"Hγ"``) and fresh against both contexts.  Nothing moves the
session.  Only ``inv`` is supported: ``na_inv``/``cinv`` need tokens ``iInv`` also takes.
"""

from __future__ import annotations

import re
from collections.abc import Iterable
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any

from pcp.state.ipm.model import Hyp, IrisGoal
from pcp.state.ipm.parse import goals_from_petanque
from pcp.state.ipm.pattern import Pat, conj, disj
from pcp.state.ipm.skeleton import Skel, parse_skeleton
from pcp.state.shape import ENVS_ENTAILS, top_level_terms

if TYPE_CHECKING:
    from pcp.state.petanque import StateHandle
    from pcp.state.session import ProofSession

MAX_UNFOLDS = 3
PROBE_TIMEOUT = 20.0
_TAG = "PCPINV:"
_WORD = re.compile(r"[^\W\d][\w']*")
#: Wrappers ``iInv`` opens with extra tokens this helper does not synthesise.
_OTHER_INVS = frozenset({"na_inv", "cinv", "cinv_own", "inv_heap_inv"})


@dataclass
class Leaf:
    """One conjunct of the opened body: what its hypothesis will be called and hold."""

    name: str
    prop: str
    pure: bool = False
    #: Rocq's ``Timeless`` answer; ``None`` when not asked or unknown.
    timeless: bool | None = None

    def to_json(self) -> dict[str, Any]:
        return {"name": self.name, "prop": self.prop, "pure": self.pure, "timeless": self.timeless}


@dataclass
class OpenPlan:
    """The pattern builder's output: binders, the pattern tree and its leaves in order."""

    binders: list[str]
    pattern: Pat
    leaves: list[Leaf]

    def text(self, *, strip: bool = True) -> str:
        """The intro pattern; ``strip=False`` omits every ``>`` (the timelessness probe's form)."""
        return _render(self.pattern, self.leaves, strip=strip)


@dataclass
class InvariantPattern:
    hyp: str
    invariant: str = ""
    body: str = ""
    unfolded: list[str] = field(default_factory=list)
    binders: list[str] = field(default_factory=list)
    pattern: str = ""
    close: str = "Hclose"
    tactic: str = ""
    leaves: list[Leaf] = field(default_factory=list)
    #: ``True``/``False`` once the tactic was run speculatively; ``None`` if not.
    verified: bool | None = None
    error: str | None = None
    #: The context the verified tactic leaves: hypothesis -> prop.
    opened: dict[str, str] = field(default_factory=dict)
    #: Goals the opening left behind (``↑N ⊆ E``, ``Atomic e``): the mask or the
    #: expression does not allow opening here.
    side_goals: list[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return bool(self.tactic) and self.verified is not False and self.error is None

    @property
    def explanation(self) -> str:
        if not self.tactic:
            return self.error or "no pattern"
        lines = [f'"{self.hyp}" : {self.invariant}']
        if self.unfolded:
            lines.append(f"unfolded {', '.join(self.unfolded)}: {self.body}")
        if self.binders:
            lines.append(f"existentials -> Coq names ({' '.join(self.binders)})")
        for leaf in self.leaves:
            if leaf.pure:
                why = "pure: `>` strips the later, `%` moves it to the Coq context"
            elif leaf.timeless:
                why = "Timeless: `>` strips the later"
            elif leaf.timeless is False:
                why = "not Timeless: stays under ▷ (a `>` here fails)"
            else:
                why = "timelessness unknown: left under ▷"
            lines.append(f'  "{leaf.name}" : {leaf.prop}  -- {why}')
        lines.append(
            f'"{self.close}" closes the invariant (give it the body back before the mask is restored)'
        )
        if self.side_goals:
            lines.append("FAILED: the tactic runs but leaves " + "; ".join(self.side_goals))
        elif self.verified:
            lines.append("verified: the tactic runs in the current state")
        elif self.verified is False:
            lines.append(f"FAILED when run speculatively: {self.error}")
        return "\n".join(lines)

    def to_json(self) -> dict[str, Any]:
        d: dict[str, Any] = {
            "ok": self.ok,
            "hyp": self.hyp,
            "tactic": self.tactic,
            "pattern": self.pattern,
            "binders": list(self.binders),
            "close": self.close,
            "leaves": [x.to_json() for x in self.leaves],
            "verified": self.verified,
            "explanation": self.explanation,
        }
        if self.unfolded:
            d["unfolded"] = list(self.unfolded)
        if self.opened:
            d["opened"] = dict(self.opened)
        if self.side_goals:
            d["side_goals"] = list(self.side_goals)
        if self.error:
            d["error"] = self.error
        return d


# =========================================================================== builder


class _Names:
    """Fresh names against a context, Rocq-style for Coq names (``n``, ``n0``, ``n1``)."""

    def __init__(self, taken: Iterable[str]) -> None:
        self.used = set(taken)

    def take(self, stem: str, *, digits_from: int = 0) -> str:
        stem = stem or "H"
        if stem not in self.used:
            self.used.add(stem)
            return stem
        k = digits_from
        while f"{stem}{k}" in self.used:
            k += 1
        self.used.add(f"{stem}{k}")
        return f"{stem}{k}"


def build_pattern(
    body: Skel | str,
    *,
    coq_names: Iterable[str] = (),
    iris_names: Iterable[str] = (),
    timeless: dict[int, bool | None] | None = None,
) -> OpenPlan:
    """The ``iInv`` binders and pattern for an invariant body.  Pure; no Rocq.

    Leading ``∃`` (nested or not) become the ``as (x y)`` binders; ``∗`` a conjunction,
    ``∨`` a disjunction, an inner ``∃`` a ``%x`` witness; everything else is a leaf.
    ``timeless`` maps a leaf's index to Rocq's answer and decides its ``>``; pure
    leaves always get ``>%``.
    """
    skel = parse_skeleton(body) if isinstance(body, str) else body
    coq = _Names(coq_names)
    iris = _Names(iris_names)
    binders: list[str] = []
    #: The definition's own names: the printed conjuncts still mention them.
    original: set[str] = set()
    node = skel
    while node.kind == "exists" and node.children:
        binders.extend(coq.take(b) for b in node.binders)
        original.update(node.binders)
        node = node.children[0]
    leaves: list[Leaf] = []
    pat = _compile(node, coq, iris, leaves, bound=original)
    for k, leaf in enumerate(leaves):
        if not leaf.pure and timeless is not None:
            leaf.timeless = timeless.get(k)
        elif leaf.pure:
            leaf.timeless = True
    return OpenPlan(binders=binders, pattern=pat, leaves=leaves)


def _compile(node: Skel, coq: _Names, iris: _Names, leaves: list[Leaf], *, bound: set[str]) -> Pat:
    if node.kind == "sep":
        return conj([_compile(c, coq, iris, leaves, bound=bound) for c in node.children])
    if node.kind == "or":
        return disj([_compile(c, coq, iris, leaves, bound=bound) for c in node.children])
    if node.kind == "exists" and node.children:
        witnesses = [coq.take(b) for b in node.binders]
        pat = _compile(node.children[0], coq, iris, leaves, bound=bound | set(node.binders))
        for w in reversed(witnesses):
            pat = Pat("list", children=[Pat("name", w, pure=True), pat])
        return pat
    text = node.to_notation()
    if node.kind == "pure":
        inner = node.children[0].text if node.children else node.text
        stem = _pure_stem(inner, bound)
        name = coq.take(stem, digits_from=1)
        while name in iris.used:  # the probe opens it as an Iris hypothesis first
            name = coq.take(stem, digits_from=1)
        iris.used.add(name)
        leaves.append(Leaf(name, text, pure=True))
    else:
        name = iris.take(_leaf_stem(node, bound), digits_from=1)
        leaves.append(Leaf(name, text))
    # The leaf's index rides in `name` until rendering; markers are set in `_render`.
    return Pat("name", f"\0{len(leaves) - 1}")


def _render(pat: Pat, leaves: list[Leaf], *, strip: bool) -> str:
    def fill(p: Pat) -> Pat:
        if p.kind == "name" and p.name.startswith("\0"):
            leaf = leaves[int(p.name[1:])]
            if leaf.pure:
                return Pat("name", leaf.name, pure=strip, modal=strip)
            return Pat("name", leaf.name, modal=strip and leaf.timeless is True)
        return Pat(p.kind, p.name, [fill(c) for c in p.children], pure=p.pure, amp=p.amp)

    out = fill(pat)
    if out.kind == "list" and not out.amp:
        out.amp = True
    return out.render()


def _leaf_stem(node: Skel, bound: set[str]) -> str:
    """``l ↦ v`` -> ``Hl``; ``own γ …`` -> ``Hγ``; ``is_list l xs`` -> ``His_list``; ``P`` -> ``HP``."""
    while node.kind in ("later", "except0") and node.children:
        node = node.children[0]
    words = [t for t in top_level_terms(node.to_notation()) if _WORD.fullmatch(t)]
    text = node.to_notation()
    if "↦" in text:
        left = text.split("↦", 1)[0]
        m = _WORD.search(left)
        if m:
            return "H" + m.group(0)
    if not words:
        return "H"
    ghost = next((w for w in words[1:] if w.startswith("γ")), None)
    if ghost:
        return "H" + ghost
    head = words[0].rsplit(".", 1)[-1]
    if head in ("True", "False", "emp"):
        return "H"
    return "H" + head


def _pure_stem(phi: str, bound: set[str]) -> str:
    """``⌜0 ≤ n⌝`` with ``n`` bound -> ``Hn``: the fact is about the witness."""
    for m in _WORD.finditer(phi):
        if m.group(0) in bound:
            return "H" + m.group(0)
    return "Hpure"


# ========================================================================= with Rocq


def find_invariant(goal: IrisGoal, which: str) -> Hyp | None:
    """The hypothesis ``which`` names, or the one whose invariant mentions ``which``
    (a predicate such as ``cnt_inv`` or a namespace such as ``N``)."""
    h = goal.by_id(which)
    if h is not None and h.klass != "pure":
        return h
    for h in goal.ipm_hyps:
        terms = top_level_terms(h.prop)
        if terms and terms[0] == "inv" and any(which in re.findall(r"[\w'.]+", t) for t in terms[1:]):
            return h
    return None


def inv_body(prop: str) -> tuple[str, str] | None:
    """``inv N P`` -> ``("N", "P")``; ``None`` for anything else."""
    terms = top_level_terms(prop)
    if len(terms) == 3 and terms[0] == "inv":
        return terms[1], _unparen(terms[2])
    return None


def _unparen(text: str) -> str:
    t = text.strip()
    while t.startswith("(") and t.endswith(")") and _balanced(t[1:-1]):
        t = t[1:-1].strip()
    return t


def _balanced(t: str) -> bool:
    depth = 0
    for ch in t:
        depth += {"(": 1, ")": -1}.get(ch, 0)
        if depth < 0:
            return False
    return depth == 0


def _definition_head(text: str) -> str | None:
    """The head constant of an application-shaped prop worth unfolding, or ``None``."""
    skel = parse_skeleton(text)
    if skel.kind != "atom":
        return None
    terms = top_level_terms(text)
    if not terms or not _WORD.fullmatch(terms[0].split(".")[-1]):
        return None
    return terms[0]


def invariant_pattern(
    session: ProofSession,
    inv: str,
    *,
    state: StateHandle | None = None,
    goals: list[IrisGoal] | None = None,
    verify: bool = True,
    close: str = "Hclose",
) -> InvariantPattern:
    """Generate (and speculatively check) the ``iInv`` that opens ``inv``.

    ``inv`` is the hypothesis name (``"Hinv"``) or a predicate / namespace it mentions.
    Costs at most ``MAX_UNFOLDS`` + 2 speculative runs; never moves the session.
    """
    base = state if state is not None else session.state()
    goal_list = goals if goals is not None else goals_from_petanque(session.goals(base))
    if not goal_list:
        return InvariantPattern(hyp=inv, error="no goal at this state")
    goal = goal_list[0]
    h = find_invariant(goal, inv)
    if h is None:
        names = ", ".join(x.id for x in goal.ipm_hyps)
        return InvariantPattern(
            hyp=inv, error=f"no invariant hypothesis matches {inv!r}; Iris context: {names}"
        )
    out = InvariantPattern(hyp=h.id, invariant=h.prop)

    # 1. the body, unfolded through named predicates (the hypothesis itself may be one)
    coq_taken = [n for x in goal.pure for n in x.names]
    iris_taken = [x.id for x in goal.ipm_hyps]
    prop, at = h.prop, base
    for _ in range(MAX_UNFOLDS):
        parsed = inv_body(prop)
        head = _definition_head(parsed[1] if parsed else prop)
        if head is None or head in out.unfolded or head in coq_taken or head in _OTHER_INVS | {"inv"}:
            break
        res = session.run(f"unfold {head}.", from_state=at, commit=False, timeout=PROBE_TIMEOUT)
        if not res.ok or res.state is None:
            break  # a section variable, an opaque or sealed definition: a leaf
        new = next((g for g in goals_from_petanque(session.goals(res.state))[:1]), None)
        nh = new.by_id(h.id) if new is not None else None
        if nh is None or nh.prop == prop:
            break
        out.unfolded.append(head)
        prop, at = nh.prop, res.state
    parsed = inv_body(prop)
    if parsed is None:
        head = (top_level_terms(prop) or [""])[0]
        why = f"`{head}` needs tokens iInv also takes" if head in _OTHER_INVS else "it is not an `inv N P`"
        out.error = f'cannot open "{h.id}" : {h.prop}: {why}'
        return out
    out.body = parsed[1]

    # 2. names fresh against both contexts, then one probe for timelessness
    out.close = _Names(iris_taken + coq_taken).take(close, digits_from=1)
    plan = build_pattern(out.body, coq_names=coq_taken, iris_names=[*iris_taken, out.close])
    out.binders = plan.binders
    binders = f" ({' '.join(plan.binders)})" if plan.binders else ""
    opener = f'iInv "{h.id}" as{binders}'
    probe = f'{opener} "{plan.text(strip=False)}" "{out.close}"; idtac "{_TAG}OPEN"' + "".join(
        f"; try ({_timeless_probe(leaf.name)}; fail)" for leaf in plan.leaves if not leaf.pure
    )
    res = session.run(probe + ".", from_state=base, commit=False, timeout=PROBE_TIMEOUT)
    answers: dict[int, bool | None] = {}
    if res.ok:
        seen = _answers(res.messages)
        answers = {k: seen.get(leaf.name) for k, leaf in enumerate(plan.leaves)}
    plan = build_pattern(
        out.body,
        coq_names=coq_taken,
        iris_names=[*iris_taken, out.close],
        timeless=answers if res.ok else None,
    )
    out.leaves = plan.leaves
    out.pattern = plan.text()
    out.tactic = f'{opener} "{out.pattern}" "{out.close}".'
    if not res.ok:
        out.error = f"opening without `>` already fails: {res.error}"
    if not verify:
        return out

    # 3. the tactic itself, speculatively
    run = session.run(out.tactic, from_state=base, commit=False, timeout=PROBE_TIMEOUT)
    out.verified = run.ok
    if not run.ok:
        out.error = out.error or run.error
        return out
    out.error = None
    if run.state is not None and not run.proof_finished:
        after = goals_from_petanque(session.goals(run.state))
        # iInv succeeds with the mask inclusion (`↑N ⊆ E`) or `Atomic e` left as a goal
        # when it cannot prove it: that is a failed opening, not a working tactic.
        if len(after) > len(goal_list):
            out.side_goals = [g.goal for g in after if g.by_id(out.close) is None][
                : len(after) - len(goal_list)
            ]
            out.error = "the opening leaves side goals it could not prove: " + "; ".join(out.side_goals)
        for g in after:
            if g.by_id(out.close) is not None:
                before = set(coq_taken + iris_taken)
                out.opened = {n: x.prop for x in g.all_hyps for n in x.names if n not in before}
                break
    return out


def _timeless_probe(name: str) -> str:
    return (
        f'iRevert "{name}"; lazymatch goal with |- {ENVS_ENTAILS} _ (bi_wand ?P _) => '
        "let P := lazymatch P with bi_later ?P' => P' | _ => P end in "
        f'first [ let _ := constr:(_ : Timeless P) in idtac "{_TAG}T {name} 1" | idtac "{_TAG}T {name} 0" ] end'
    )


def _answers(messages: list[str]) -> dict[str, bool]:
    out: dict[str, bool] = {}
    for m in messages:
        if m.startswith(_TAG + "T "):
            parts = m[len(_TAG) + 2 :].split()
            if len(parts) == 2:
                out[parts[0]] = parts[1] == "1"
    return out
