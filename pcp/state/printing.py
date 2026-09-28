"""What the printer hides: coercions, equality carriers, implicit arguments (issue 15).

Rocq prints ``@eq Z (Z.of_nat a) (Z.of_nat b)`` as ``a = b``, exactly like the ``nat``
equality it is not; a model that pattern-matches on rendered hypotheses then tries
``exact`` with the wrong one.  petanque has no printing options on ``goals``, but
states are immutable and options live in the state, so the same state is reprinted
from a speculative run of the printing commands -- nothing moves, nothing is committed.

One reprint per state, two petanque ``run``s and two ``goals`` (a few milliseconds
each), cached by the caller per state:

1. ``Set Printing Coercions`` plus a printing-only notation ``x =@{A} y`` for
   ``@eq A x y`` in ``type_scope`` -- the carrier of every equality, including inside
   ``⌜…⌝`` (verified against Rocq 9.1 / Iris 4.5);
2. then ``Set Printing Implicit`` -- implicit arguments, which are mostly noise
   (``@gmap nat Nat.eq_dec nat_countable Z``), so they are only *shown* when asked for.

A hypothesis is marked as hiding a coercion when its reprint names an identifier
the plain print does not, other than the carrier projections Iris is built on
(``bi_car``, ``ofe_car``, ...) and heap_lang's syntax injections (``Val``, ``LitV``,
...), which every Iris state would otherwise carry.
"""

from __future__ import annotations

import re
from collections import Counter
from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from pcp.errors import PcpError
from pcp.state.ipm.model import Hyp, IrisGoal
from pcp.state.ipm.parse import goals_from_petanque
from pcp.state.petanque import TacticError

if TYPE_CHECKING:
    from pcp.state.petanque import StateHandle
    from pcp.state.session import ProofSession

CARRIER_NOTATION = (
    'Local Notation "x =@{ A } y" := (@eq A x y) (at level 70, no associativity, only printing) : type_scope.'
)
REPRINT_COERCIONS = "Set Printing Coercions. " + CARRIER_NOTATION
REPRINT_IMPLICIT = "Set Printing Implicit."
#: Budget of each reprint ``run``: printing options never compute.
REPRINT_TIMEOUT = 10.0

#: Coercions whose elision never misleads: structure carriers and heap_lang syntax.
QUIET_COERCIONS = frozenset({
    "bi_car", "ofe_car", "cmra_car", "ucmra_car", "sbi_car", "bi_ofeO", "cmra_ofeO", "ucmra_cmraR",
    "Val", "LitV", "LitInt", "LitBool", "LitLoc", "LitProphecy", "LitPoison", "LitUnit", "App", "Var",
    "BNamed", "of_val", "is_true",
})

_CARRIER = re.compile(r"=@\{\s*((?:[^{}]|\{[^{}]*\})*?)\s*\}")
_IDENT = re.compile(r"[A-Za-z_][\w'.]*")


@dataclass(frozen=True)
class Hidden:
    """What the plain print of one prop leaves out."""

    #: Coercions the printer dropped (names, in order of first appearance).
    coercions: tuple[str, ...] = ()
    #: The prop with coercions and equality carriers printed; set when ``coercions`` is.
    explicit: str | None = None
    #: Carrier types of the prop's equalities, in order, deduplicated.
    carriers: tuple[str, ...] = ()
    #: The prop with implicit arguments printed too, when that differs.
    implicit: str | None = None

    def __bool__(self) -> bool:
        return bool(self.coercions or self.carriers or self.implicit)


@dataclass
class GoalHidden:
    """:class:`Hidden` for one goal's hypotheses (by id) and its conclusion."""

    hyps: dict[str, Hidden] = field(default_factory=dict)
    goal: Hidden | None = None

    def get(self, hyp: Hyp) -> Hidden | None:
        return self.hyps.get(f"{hyp.klass}:{hyp.id}")


def compare(plain: str, coerced: str, implicit: str | None = None) -> Hidden:
    """:class:`Hidden` of one prop from its three prints."""
    carriers = tuple(dict.fromkeys(" ".join(c.split()) for c in _CARRIER.findall(coerced)))
    bare = _CARRIER.sub("=", coerced)
    extra = Counter(_IDENT.findall(bare)) - Counter(_IDENT.findall(plain))
    coercions = tuple(dict.fromkeys(t for t in _IDENT.findall(bare) if t in extra and t not in QUIET_COERCIONS))
    explicit = _tidy(coerced) if coercions else None
    implicit_text = None
    if implicit is not None and _flat(implicit) != _flat(coerced):
        implicit_text = _tidy(implicit)
    return Hidden(coercions=coercions, explicit=explicit, carriers=carriers, implicit=implicit_text)


def compare_goals(plain: list[IrisGoal], coerced: list[IrisGoal], implicit: list[IrisGoal] | None) -> list[GoalHidden]:
    """Positional over goals, by class and id over hypotheses; anything unmatched is skipped."""
    out: list[GoalHidden] = []
    for i, goal in enumerate(plain):
        if i >= len(coerced):
            out.append(GoalHidden())
            continue
        c_hyps = {f"{h.klass}:{h.id}": h for h in coerced[i].all_hyps}
        i_hyps = {f"{h.klass}:{h.id}": h for h in implicit[i].all_hyps} if implicit and i < len(implicit) else {}
        entry = GoalHidden()
        for h in goal.all_hyps:
            key = f"{h.klass}:{h.id}"
            if key not in c_hyps:
                continue
            imp = i_hyps.get(key)
            hidden = compare(h.prop, c_hyps[key].prop, imp.prop if imp is not None else None)
            if hidden:
                entry.hyps[key] = hidden
        imp_goal = implicit[i].goal if implicit and i < len(implicit) else None
        hidden_goal = compare(goal.goal, coerced[i].goal, imp_goal)
        entry.goal = hidden_goal or None
        out.append(entry)
    return out


def reprint(session: ProofSession, state: StateHandle, plain: list[IrisGoal] | None = None) -> list[GoalHidden] | None:
    """The hidden details of every goal at ``state``; ``None`` when the reprint is refused.

    ``plain`` is the printer's parse of the same state (fetched when not given -- the
    reflected goals are not a printer's output and would not compare).  A reprint
    failure is never an error of the proof: it only means nothing can be marked.
    """
    try:
        if plain is None:
            plain = goals_from_petanque(session.goals(state))
        s1 = session.run(REPRINT_COERCIONS, from_state=state, commit=False, timeout=REPRINT_TIMEOUT)
        if not s1.ok or s1.state is None:  # a project where the notation clashes: coercions alone
            s1 = session.run("Set Printing Coercions.", from_state=state, commit=False, timeout=REPRINT_TIMEOUT)
            if not s1.ok or s1.state is None:
                return None
        coerced = goals_from_petanque(session.goals(s1.state))
        s2 = session.run(REPRINT_IMPLICIT, from_state=s1.state, commit=False, timeout=REPRINT_TIMEOUT)
        implicit = goals_from_petanque(session.goals(s2.state)) if s2.ok and s2.state is not None else None
    except (TacticError, PcpError):
        return None
    return compare_goals(plain, coerced, implicit)


def _flat(text: str) -> str:
    return " ".join(text.split())


def _tidy(text: str) -> str:
    """``=@{ Z}`` (the notation's own spacing) as ``=@{Z}``; layout kept otherwise."""
    return _CARRIER.sub(lambda m: "=@{" + " ".join(m.group(1).split()) + "}", text).strip()
