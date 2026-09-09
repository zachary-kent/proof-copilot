"""Reading ``Print Assumptions`` (PLAN.md 8.7 item 4).

The gate appends, for every name it proved::

    Locate M.name.
    Print Assumptions M.name.

``Locate`` prints ``Constant <library>.M.name`` on a line of its own; that line is the
**marker** the block after it belongs to.  ``Check`` was the marker once, but it
prints the term through the printer, and an abbreviation ``Notation TT := name`` made
it print ``TT``, so a correct proof came back "unverified".  Blocks are matched to
names from the *end* of the output backwards, because nothing a proof prints can
come after the trailer -- so whatever a proof emits (``idtac "Axioms:"`` included)
can neither shift nor forge a block.

Entries are parsed by grammar, not by position: an entry starts at column 0 with a
name followed by `` :`` (a wrapped type continues on indented lines), by `` is
assumed to be guarded/positive`` (``Unset Guard/Positivity Checking``) or by
`` relies on an unsafe hierarchy`` (``Unset Universe Checking``).  Any other line at
column 0 inside an ``Axioms:`` block is an assumption too -- one this parser does not
know -- and is reported as such, never skipped: silently dropping the universe line
certified a ``Type : Type`` development as clean (review finding).
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

_AXIOMS = "Axioms:"
_CLOSED = "Closed under the global context"
_ENTRY = re.compile(
    r"^(?P<name>[^\s:]+)\s*(?::|\s+is\s+assumed\s+to\s+be\s+(?P<kind>[a-z]+)|\s+relies\s+on\s+(?P<relies>.+?)\.?\s*$)"
)
_LOCATED = "Constant "


@dataclass(frozen=True)
class Assumption:
    name: str
    #: ``axiom`` for ordinary entries; ``guarded``/``positive``/``universe`` ... for the
    #: colon-less ones.
    kind: str = "axiom"

    @property
    def bare(self) -> str:
        return self.name.rsplit(".", 1)[-1]

    def render(self) -> str:
        return self.name if self.kind == "axiom" else f"{self.name} (assumed {self.kind})"


@dataclass
class AssumptionReport:
    """Per proved name, its assumptions.  ``failed`` names the ones that could not be read."""

    by_name: dict[str, list[Assumption]] = field(default_factory=dict)
    failed: list[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not self.failed

    def to_json(self) -> dict[str, list[str]]:
        return {name: [a.render() for a in axioms] for name, axioms in self.by_name.items()}


def trailer(names: list[str]) -> str:
    """The vernacular the gate appends for ``names`` (already module-qualified)."""
    return "\n".join(f"Locate {n}.\nPrint Assumptions {n}." for n in names)


def _marker_matches(line: str, name: str) -> bool:
    line = line.strip()
    if line.startswith(_LOCATED):
        line = line[len(_LOCATED) :].strip()
    return line == name or name.endswith("." + line) or line.endswith("." + name)


def _parse_block(lines: list[str], start: int, stop: int) -> list[Assumption] | None:
    """The block that begins at ``start`` (an ``Axioms:``/``Closed`` line), up to ``stop``."""
    head = lines[start].strip()
    if head.startswith(_CLOSED):
        return []
    if not head.startswith(_AXIOMS):
        return None
    out: list[Assumption] = []
    for line in lines[start + 1 : stop]:
        if not line.strip():
            continue
        if line[0].isspace():
            continue  # a wrapped type
        if line.startswith(_AXIOMS) or line.startswith(_CLOSED):
            break  # the next block's head: this block is complete
        m = _ENTRY.match(line)
        if not m:
            # Fail closed: an entry shape this parser does not know is still an entry.
            out.append(Assumption(line.strip(), "unrecognised"))
            continue
        kind = m.group("kind") or ("unsafe " + m.group("relies").strip() if m.group("relies") else "axiom")
        out.append(Assumption(m.group("name"), kind))
    return out


def parse_assumptions(output: str, names: list[str]) -> AssumptionReport:
    """Match the trailer's output to ``names`` (module-qualified, in trailer order)."""
    report = AssumptionReport()
    lines = output.splitlines()
    upper = len(lines)
    for name in reversed(names):
        marker = None
        for i in range(upper - 1, -1, -1):
            if _marker_matches(lines[i], name):
                marker = i
                break
        if marker is None:
            report.failed.append(name)
            continue
        block = None
        for j in range(marker + 1, upper):
            s = lines[j].strip()
            if s.startswith(_AXIOMS) or s.startswith(_CLOSED):
                block = j
                break
        parsed = _parse_block(lines, block, upper) if block is not None else None
        if parsed is None:
            report.failed.append(name)
        else:
            report.by_name[name] = parsed
        upper = marker
    report.failed.reverse()
    report.by_name = {n: report.by_name[n] for n in names if n in report.by_name}
    return report


def _suffix_match(printed: str, known: str) -> bool:
    """Component-wise: the shorter path must be a suffix of the longer.

    Rocq prints the shortest unambiguous name, so ``classic`` and
    ``Stdlib.Logic.Classical_Prop.classic`` both match ``Classical_Prop.classic`` --
    but ``Evil.classic`` does not.  Comparing bare last components let a module's own
    ``Axiom classic : False`` pass the whitelist (review finding).
    """
    a, b = printed.split("."), known.split(".")
    n = min(len(a), len(b))
    return n > 0 and a[-n:] == b[-n:]


def classify_assumptions(
    axioms: list[Assumption], *, whitelist: set[str], stubs: set[str]
) -> tuple[list[Assumption], list[Assumption], list[Assumption]]:
    """Split into (whitelisted, resting-on-stubs, offending).

    Names are compared by their last component: Rocq prints the shortest unambiguous
    name, which may be qualified (``M.child``) or not (``classic``) depending on scope.
    Colon-less entries (``assumed to be guarded``) are never whitelisted.
    """
    allowed: list[Assumption] = []
    leaning: list[Assumption] = []
    bad: list[Assumption] = []
    for a in axioms:
        if a.kind != "axiom":
            bad.append(a)
        elif any(_suffix_match(a.name, s) for s in stubs):
            leaning.append(a)
        elif any(_suffix_match(a.name, w) for w in whitelist):
            allowed.append(a)
        else:
            bad.append(a)
    return allowed, leaning, bad
