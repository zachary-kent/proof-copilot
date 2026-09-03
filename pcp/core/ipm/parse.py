"""v1 acquisition path: parse the IPM notation render (PLAN.md 3.1).

Petanque returns a goal whose ``ty`` is the Iris Proof Mode's own pretty-print:

    "Hinv" : inv N (I γ)
    --------------------------------------□
    "Hl" : l ↦ v
    --------------------------------------∗
    WP e {{ Φ }}

Either separator is omitted when its context is empty, so all four shapes occur.
This is cheap and works on day one, and it is *layout-fragile* -- which is why the
reflected dump (``reflect.py``) is the primary path and this stays as the fallback.
The printed goal is always kept alongside as an untrusted display fallback.
"""

from __future__ import annotations

import re

from pcp.core.ipm.model import Hyp, IrisGoal, scan_modality

#: `------------□` / `------------∗`, with any run of dashes.
_SEP_INTUIT = re.compile(r"^\s*-{3,}\s*□\s*$")
_SEP_SPATIAL = re.compile(r"^\s*-{3,}\s*(?:∗|\*)\s*$")
#: The ordinary Coq goal separator, when the render includes the full goal.
_SEP_COQ = re.compile(r"^\s*={3,}\s*$")
#: `"Hname" : prop` -- IPM hypothesis lines are the only ones starting with a quote.
_HYP_LINE = re.compile(r'^\s*("(?P<names>[^"]*)"(?:\s+"[^"]*")*)\s*:\s*(?P<prop>.*)$')
_HYP_NAMES = re.compile(r'"([^"]*)"')


def looks_like_ipm(text: str) -> bool:
    return any(_SEP_SPATIAL.match(l) or _SEP_INTUIT.match(l) for l in text.splitlines())


def parse_goal(
    ty: str,
    *,
    goal_id: str = "g0",
    pure_hyps: list[tuple[list[str], str]] | None = None,
) -> IrisGoal:
    """Parse one printed goal into an :class:`IrisGoal`.

    ``pure_hyps`` is petanque's structured ordinary-Coq context (``names``, ``ty``);
    it is authoritative when supplied, since it needs no parsing at all.
    """
    text = ty.rstrip()
    lines = text.splitlines()

    coq_block: list[str] = []
    idx_intuit = idx_spatial = None
    for i, line in enumerate(lines):
        if idx_intuit is None and _SEP_INTUIT.match(line):
            idx_intuit = i
        elif _SEP_SPATIAL.match(line):
            idx_spatial = i
            break

    if idx_spatial is None and idx_intuit is None:
        # An ordinary Coq goal.  If this is a whole-goal render, split off the
        # context above the `====` line rather than calling it part of the goal.
        body, ctx = lines, []
        for i, line in enumerate(lines):
            if _SEP_COQ.match(line):
                ctx, body = lines[:i], lines[i + 1 :]
                break
        goal = IrisGoal(goal_id=goal_id, goal="\n".join(body).strip(), is_ipm=False, raw=ty)
        goal.modality = scan_modality(goal.goal)
        goal.pure = _pure_from(pure_hyps) or [_mk(h, "pure") for h in _parse_coq_hyp_block(ctx)]
        return goal

    if idx_spatial is None:
        # Only a `□` line: everything after it is the goal, nothing is spatial.
        intuit_block = lines[:idx_intuit]
        spatial_block: list[str] = []
        goal_block = lines[idx_intuit + 1 :]
    elif idx_intuit is None:
        # Only a `∗` line: the intuitionistic context is empty.
        intuit_block = []
        spatial_block = lines[:idx_spatial]
        goal_block = lines[idx_spatial + 1 :]
    else:
        intuit_block = lines[:idx_intuit]
        spatial_block = lines[idx_intuit + 1 : idx_spatial]
        goal_block = lines[idx_spatial + 1 :]

    # A full-goal render may prefix the ordinary Coq context and a `====` line.
    for i, line in enumerate(intuit_block):
        if _SEP_COQ.match(line):
            coq_block = intuit_block[:i]
            intuit_block = intuit_block[i + 1 :]
            break

    goal_text = "\n".join(goal_block).strip()
    goal = IrisGoal(
        goal_id=goal_id,
        intuitionistic=[_mk(h, "intuitionistic") for h in _parse_hyp_block(intuit_block)],
        spatial=[_mk(h, "spatial") for h in _parse_hyp_block(spatial_block)],
        goal=goal_text,
        is_ipm=True,
        raw=ty,
    )
    goal.modality = scan_modality(goal_text)
    if pure_hyps:
        goal.pure = _pure_from(pure_hyps)
    elif coq_block:
        goal.pure = [_mk(h, "pure") for h in _parse_coq_hyp_block(coq_block)]
    return goal


def _pure_from(pure_hyps: list[tuple[list[str], str]] | None) -> list[Hyp]:
    out: list[Hyp] = []
    for names, ty in pure_hyps or []:
        if not names:
            continue
        out.append(Hyp(id=names[0], prop=ty.strip(), klass="pure", names=list(names)))
    return out


def _mk(entry: tuple[list[str], str], klass: str) -> Hyp:
    names, prop = entry
    return Hyp(
        id=names[0],
        prop=prop,
        klass=klass,  # type: ignore[arg-type]
        names=list(names),
        persistent=True if klass == "intuitionistic" else None,
    )


def _parse_hyp_block(lines: list[str]) -> list[tuple[list[str], str]]:
    """Parse ``"H" : prop`` entries, honouring indented continuation lines."""
    out: list[tuple[list[str], str]] = []
    cur_names: list[str] | None = None
    cur: list[str] = []
    for line in lines:
        m = _HYP_LINE.match(line)
        if m:
            if cur_names is not None:
                out.append((cur_names, _join(cur)))
            cur_names = _HYP_NAMES.findall(m.group(1)) or ["_"]
            cur = [m.group("prop")]
        elif cur_names is not None:
            if line.strip():
                cur.append(line)
        # A line before any `"H" :` in an IPM block is unexpected; drop it rather
        # than attach it to the wrong hypothesis.
    if cur_names is not None:
        out.append((cur_names, _join(cur)))
    return out


_COQ_HYP_LINE = re.compile(r"^(?P<names>[A-Za-z_][\w'\s]*?)\s*:\s*(?P<prop>.*)$")


def _parse_coq_hyp_block(lines: list[str]) -> list[tuple[list[str], str]]:
    out: list[tuple[list[str], str]] = []
    cur_names: list[str] | None = None
    cur: list[str] = []
    for line in lines:
        m = _COQ_HYP_LINE.match(line) if not line.startswith((" ", "\t")) else None
        if m:
            if cur_names is not None:
                out.append((cur_names, _join(cur)))
            cur_names = m.group("names").split()
            cur = [m.group("prop")]
        elif cur_names is not None and line.strip():
            cur.append(line)
    if cur_names is not None:
        out.append((cur_names, _join(cur)))
    return out


def _join(parts: list[str]) -> str:
    """Re-join a wrapped prop.  Indentation is layout, not content."""
    head, *rest = parts
    text = head.rstrip()
    for line in rest:
        text += "\n" + line.rstrip()
    return text.strip()
