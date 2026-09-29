"""Why one ``proof_try`` candidate failed where a near-identical one survived (session 3, issue 22).

Two candidates that differ by a ``/=`` or a ``"[H]"`` usually fail and survive for one
reason, and the failing row's error (a whole ``iExact`` mismatch) does not say it.  The
difference is read off the two sentences' tokens, and the differences with a known
meaning get a line saying what the survivor's version does.
"""

from __future__ import annotations

import difflib
import re
from typing import Any

#: A quoted name, a ssreflect switch, an identifier-ish run (``/AU_sc``, ``Z.of_nat``), or one character.
_TOKEN = re.compile(r'"(?:[^"]|"")*"|/=|//=|//|\$!|[\w\'./]+|\S')
#: Beyond this many changed tokens the two are different attempts, not variants.
MAX_CHANGED = 6

_SIMPLIFY = frozenset({"/=", "//=", "simpl", "cbn", "cbv", "lazy"})


def _tokens(tactic: str) -> list[str]:
    return _TOKEN.findall(tactic)


def _notes(removed: list[str], added: list[str]) -> list[str]:
    out: list[str] = []
    if any(t in _SIMPLIFY for t in added) and not any(t in _SIMPLIFY for t in removed):
        out.append("the survivor simplifies first: the goal and the hypothesis agree only up to `simpl` "
                   "(a telescope, `-∗?`/`∀..` sugar or a β-redex that `/=` normalizes)")
    if ("//" in added or "//=" in added) and "//" not in removed:
        out.append("the survivor's `//` closes the trivial side goals the other leaves open")
    if "$!" in added and "$!" not in removed:
        out.append("the survivor instantiates the quantifiers explicitly (`$!`): unification could not guess them")
    for old in removed:
        name = old.strip('"')
        if old.startswith('"') and name and f'"[{name}]"' in added:
            out.append(f'the survivor\'s "[{name}]" gives {old} to the premise\'s proof (a spec pattern), where '
                       f"{old} alone must *be* that premise")
    return out


def compare(failed: str, survivor: str) -> dict[str, Any] | None:
    """How ``failed`` differs from ``survivor``, when they are variants of one tactic; else ``None``."""
    a, b = _tokens(failed), _tokens(survivor)
    removed: list[str] = []
    added: list[str] = []
    changes: list[str] = []
    kept = 0
    for op, i1, i2, j1, j2 in difflib.SequenceMatcher(a=a, b=b, autojunk=False).get_opcodes():
        if op == "equal":
            kept += sum(1 for t in a[i1:i2] if t != ".")
            continue
        old, new = a[i1:i2], b[j1:j2]
        removed += old
        added += new
        if old and new:
            changes.append(f"`{' '.join(old)}` → `{' '.join(new)}`")
        elif new:
            changes.append(f"adds `{' '.join(new)}`")
        else:
            changes.append(f"drops `{' '.join(old)}`")
    size = len(removed) + len(added)
    # Variants share more than they change: `lia.` is not a variant of `rewrite foo.`.
    if not size or size > MAX_CHANGED or kept < 2 or 2 * kept < size:
        return None
    out: dict[str, Any] = {"survivor": survivor, "differs": "; ".join(changes), "changed_tokens": size}
    notes = _notes(removed, added)
    if notes:
        out["why"] = notes
    return out


def closest_survivor(failed: str, survivors: list[str]) -> dict[str, Any] | None:
    """:func:`compare` against the survivor with the fewest changed tokens."""
    found = [c for c in (compare(failed, s) for s in survivors) if c is not None]
    return min(found, key=lambda c: c["changed_tokens"]) if found else None
