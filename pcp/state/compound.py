"""A sentence ``head; tail`` taken apart, so a failure can be pinned on the part that failed.

``iMod (…) as "…"; [done|done| | |done|by iFrame].`` fails as a whole with "No applicable
tactic", and a diagnosis of the whole reads the head (``iMod``) against the goal -- the
wrong part when ``iMod`` succeeds and the fifth ``done`` is what failed (session 4, issues
30 and 32).  :func:`split_compound` names the head and how the tail applies to the goals
the head makes, and :func:`branch_command` is the sentence that runs one tail tactic on
one of those goals, so the server can replay the parts speculatively and say which failed.

Only the shapes whose meaning is unambiguous are taken apart: ``t; [t1|…|tn]``,
``t; first tac`` / ``t; last tac`` (ssreflect: the first / last goal), and ``t; tac``
(every goal).  A tail that cannot fail (``try``), a leading goal selector or ``by``, and a
dispatch followed by more ``;`` are left whole.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from pcp.rocq.lexer import skip_comment, skip_string

TailKind = Literal["dispatch", "first", "last", "each"]


@dataclass(frozen=True)
class Compound:
    head: str
    kind: TailKind
    #: The tail's tactics: one per goal for ``dispatch`` (``""`` leaves that goal alone),
    #: else the one tactic.
    branches: tuple[str, ...]
    tail: str


def _top_level(code: str, sep: str) -> list[int]:
    """Offsets of ``sep`` outside brackets, comments and strings."""
    out: list[int] = []
    depth, i, n = 0, 0, len(code)
    while i < n:
        ch = code[i]
        if code.startswith("(*", i):
            i = skip_comment(code, i)
            continue
        if ch == '"':
            i = skip_string(code, i)
            continue
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and ch == sep and not (sep == "|" and code.startswith("||", i)):
            out.append(i)
        i += 1
    return out


def _split(code: str, sep: str) -> list[str]:
    cuts = _top_level(code, sep)
    bounds = [-1, *cuts, len(code)]
    return [code[a + 1:b] for a, b in zip(bounds, bounds[1:], strict=False)]


def _matching_bracket(code: str) -> int | None:
    """Where the ``[`` at offset 0 closes."""
    depth, i, n = 0, 0, len(code)
    while i < n:
        if code.startswith("(*", i):
            i = skip_comment(code, i)
            continue
        if code[i] == '"':
            i = skip_string(code, i)
            continue
        if code[i] in "([{":
            depth += 1
        elif code[i] in ")]}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return None


def split_compound(sentence: str) -> Compound | None:
    """``sentence`` as head and tail when it is ``head; tail`` in one of the shapes above."""
    code = " ".join(sentence.strip().split())
    if code.endswith("."):
        code = code[:-1].rstrip()
    cuts = _top_level(code, ";")
    if not cuts:
        return None
    head, tail = code[: cuts[0]].strip(), code[cuts[0] + 1:].strip()
    first = head.split(" ", 1)[0]
    if not head or not tail or first == "by" or first.endswith(":") or head.startswith(("-", "+", "*", "{", "}")):
        return None
    word = tail.split(" ", 1)[0]
    if tail.startswith("["):
        close = _matching_bracket(tail)
        if close != len(tail) - 1:
            return None  # `[…]; more`, or unbalanced: not one dispatch
        branches = tuple(b.strip() for b in _split(tail[1:-1], "|"))
        return Compound(head + ".", "dispatch", branches, tail)
    if word in ("try", "idtac") or tail.startswith("first ["):
        return None if word in ("try", "idtac") else Compound(head + ".", "each", (tail,), tail)
    if word in ("first", "last") and " " in tail:
        rest = tail.split(" ", 1)[1].strip()
        if _top_level(rest, ";") or rest in ("first", "last"):
            return None  # `first t1; t2` binds as ssreflect decides; `last first` rotates
        return Compound(head + ".", word, (rest,), tail)  # type: ignore[arg-type]
    return Compound(head + ".", "each", (tail,), tail)


def branch_command(goal: int, tactic: str) -> str:
    """The sentence that runs ``tactic`` on goal ``goal`` (1-based) of the focused goals."""
    return f"{goal}: ({tactic})."
