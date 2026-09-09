"""The printer parser: petanque's IPM render into an :class:`IrisGoal` (PLAN.md 3.1).

Petanque's ``goal.ty`` is the Iris Proof Mode's own pretty-print of the *conclusion*;
the ordinary Coq context arrives structured in ``goal.hyps`` and is never parsed::

    "Hinv" : inv N (I γ)                     <- intuitionistic context
    _ : steps_lb n                           <- ANONYMOUS hypotheses print unquoted
    --------------------------------------□
    "Hl" : l ↦ v                             <- spatial context
    --------------------------------------∗
    WP e {{ Φ }}                             <- conclusion, may wrap over many lines

Either separator is omitted when its context is empty, so all four shapes occur; a
render with neither is an ordinary Coq goal (``is_ipm=False``).  Iris's own proof-mode
lemmas print ``Γp---------□`` *glued inside a statement*: only a standalone separator
line is a boundary.  Layout-fragile by nature, so it is pinned by the golden corpus
(``tests/test_goldens.py``) and is the fallback behind the reflected dump
(``reflect.py``).
"""

from __future__ import annotations

import re
from collections.abc import Iterable, Sequence
from typing import Any

from pcp.state.ipm.model import Hyp, IrisGoal, scan_modality

#: ``------------□`` / ``------------∗`` on a line of their own, any run of dashes.
_SEP_INTUIT = re.compile(r"^\s*-{3,}\s*□\s*$")
_SEP_SPATIAL = re.compile(r"^\s*-{3,}\s*(?:∗|\*)\s*$")
#: The ordinary Coq goal separator of a *full* render (petanque never sends one).
_SEP_COQ = re.compile(r"^\s*={3,}\s*$")
#: ``"H" : prop`` (one or more quoted names) or the anonymous ``_ : prop`` form.
_HYP_LINE = re.compile(r'^(?:\s*(?P<quoted>"[^"]*"(?:\s+"[^"]*")*)|(?P<anon>_))\s*:\s*(?P<prop>.*)$')
_HYP_NAMES = re.compile(r'"([^"]*)"')
#: A Coq-context line of a full render: unicode names, optional ``:=`` definition.
_COQ_HYP_LINE = re.compile(r"^(?P<names>[^\s:=][^:=]*?)\s*(?::=\s*(?P<def>.*?)\s*)?:\s*(?P<prop>.*)$")

HypLike = Any  # object with ``.names``/``.ty``, a ``(names, ty)`` pair, or a ``{"names","ty"}`` dict


def looks_like_ipm(text: str) -> bool:
    return any(_SEP_SPATIAL.match(line) or _SEP_INTUIT.match(line) for line in text.splitlines())


def parse_goal(ty: str, hyps: Sequence[HypLike] | None = None, *, goal_id: str = "g0") -> IrisGoal:
    """Parse one printed goal.  Total: never raises on Iris output.

    ``hyps`` is petanque's structured Coq context and is authoritative when given.
    """
    lines = ty.rstrip().splitlines()
    idx_intuit = idx_spatial = None
    for i, line in enumerate(lines):
        if idx_intuit is None and idx_spatial is None and _SEP_INTUIT.match(line):
            idx_intuit = i
        elif idx_spatial is None and _SEP_SPATIAL.match(line):
            idx_spatial = i
            break

    if idx_intuit is None and idx_spatial is None:
        return _plain_goal(lines, hyps, goal_id=goal_id, raw=ty)

    if idx_intuit is not None and idx_spatial is None:
        intuit_block, spatial_block, goal_block = lines[:idx_intuit], [], lines[idx_intuit + 1 :]
    elif idx_intuit is None and idx_spatial is not None:
        intuit_block, spatial_block, goal_block = [], lines[:idx_spatial], lines[idx_spatial + 1 :]
    else:
        assert idx_intuit is not None and idx_spatial is not None
        intuit_block = lines[:idx_intuit]
        spatial_block = lines[idx_intuit + 1 : idx_spatial]
        goal_block = lines[idx_spatial + 1 :]

    # A full render prefixes the Coq context and a `====` line above the *first* block.
    coq_block: list[str] = []
    first = intuit_block if idx_intuit is not None else spatial_block
    for i, line in enumerate(first):
        if _SEP_COQ.match(line):
            coq_block, first[:] = first[:i], first[i + 1 :]
            break

    goal_text = _join(goal_block)
    intuit_entries = parse_hyp_block(intuit_block)
    n_anon = sum(1 for e in intuit_entries if e.anonymous)
    goal = IrisGoal(
        goal_id=goal_id,
        pure=_pure_hyps(hyps) if hyps else [_mk(e, "pure") for e in parse_coq_hyp_block(coq_block)],
        intuitionistic=[_mk(e, "intuitionistic") for e in intuit_entries],
        spatial=[_mk(e, "spatial") for e in parse_hyp_block(spatial_block, first_anon=n_anon + 1)],
        goal=goal_text,
        modality=scan_modality(goal_text),
        is_ipm=True,
        raw=ty,
    )
    return goal


def _plain_goal(lines: list[str], hyps: Sequence[HypLike] | None, *, goal_id: str, raw: str) -> IrisGoal:
    body, ctx = lines, []
    for i, line in enumerate(lines):
        if _SEP_COQ.match(line):
            ctx, body = lines[:i], lines[i + 1 :]
            break
    goal_text = _join(body)
    return IrisGoal(
        goal_id=goal_id,
        pure=_pure_hyps(hyps) if hyps else [_mk(e, "pure") for e in parse_coq_hyp_block(ctx)],
        goal=goal_text,
        modality=scan_modality(goal_text),
        is_ipm=False,
        raw=raw,
    )


def goals_from_petanque(goals: Iterable[Any]) -> list[IrisGoal]:
    """Petanque goals (``.ty``, ``.hyps``) in order -> ``g0``, ``g1``, ... (``g0`` is focused)."""
    return [parse_goal(g.ty, list(getattr(g, "hyps", None) or []), goal_id=f"g{i}") for i, g in enumerate(goals)]


# ---------------------------------------------------------------------- entries


class Entry:
    """One parsed context line: names, prop text, anonymity."""

    __slots__ = ("anonymous", "names", "prop")

    def __init__(self, names: list[str], prop: str, *, anonymous: bool = False) -> None:
        self.names = names
        self.prop = prop
        self.anonymous = anonymous


def parse_hyp_block(lines: list[str], *, first_anon: int = 1) -> list[Entry]:
    """``"H" : prop`` / ``_ : prop`` entries with their indented continuation lines.

    Anonymous hypotheses get ids ``_1``, ``_2``, ... in display order across the whole
    goal (``first_anon`` continues the numbering from the previous block), so they stay
    addressable and two anonymous hyps never collide.
    """
    out: list[Entry] = []
    names: list[str] | None = None
    anon = False
    cur: list[str] = []
    n_anon = first_anon - 1
    for line in lines:
        m = _HYP_LINE.match(line)
        if m:
            if names is not None:
                out.append(Entry(names, _join(cur), anonymous=anon))
            if m.group("anon"):
                n_anon += 1
                names, anon = [f"_{n_anon}"], True
            else:
                names, anon = _HYP_NAMES.findall(m.group("quoted")), False
            cur = [m.group("prop")]
        elif names is not None and line.strip():
            cur.append(line)
        # A line before the first entry belongs to nothing; drop it rather than
        # attaching it to the wrong hypothesis.
    if names is not None:
        out.append(Entry(names, _join(cur), anonymous=anon))
    return out


def parse_coq_hyp_block(lines: list[str]) -> list[Entry]:
    """Coq-context lines of a full render (``σ : state Λ``, ``x := 1 : nat``); unicode names."""
    out: list[Entry] = []
    names: list[str] | None = None
    cur: list[str] = []
    for line in lines:
        m = _COQ_HYP_LINE.match(line) if line and not line[0].isspace() else None
        if m:
            if names is not None:
                out.append(Entry(names, _join(cur)))
            names = m.group("names").split()
            cur = [m.group("prop")]
        elif names is not None and line.strip():
            cur.append(line)
    if names is not None:
        out.append(Entry(names, _join(cur)))
    return out


def _pure_hyps(hyps: Sequence[HypLike]) -> list[Hyp]:
    out: list[Hyp] = []
    for h in hyps:
        if isinstance(h, dict):
            names, ty = list(h.get("names") or []), str(h.get("ty") or "")
        elif isinstance(h, tuple | list):
            names, ty = list(h[0]), str(h[1])
        else:
            names, ty = list(getattr(h, "names", []) or []), str(getattr(h, "ty", "") or "")
        if not names:
            continue
        out.append(Hyp(id=names[0], prop=ty.strip(), klass="pure", names=names))
    return out


def _mk(entry: Entry, klass: str) -> Hyp:
    return Hyp(
        id=entry.names[0],
        prop=entry.prop,
        klass=klass,  # type: ignore[arg-type]
        names=list(entry.names),
        persistent=True if klass == "intuitionistic" else None,
        anonymous=entry.anonymous,
    )


def _join(parts: list[str]) -> str:
    """Re-join a wrapped prop.  Indentation is layout, not content."""
    return "\n".join(p.rstrip() for p in parts).strip()
