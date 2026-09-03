"""Statement sentinels: deterministic checks at freeze time (PLAN.md 8.4).

Deterministic before model.  Every check here is a program, and a model is the last
resort -- audits are *event-driven*, and one of the events is a sentinel hit.

The free ones run always.  The ones that cost a Rocq compile (vacuity) are opt-in,
because in the daily loop the human is the audit ladder and the loop must not slow
down for machinery the human is already faster than.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from pcp.orch.hashing import normalize_statement, statement_hash


@dataclass
class SentinelHit:
    sentinel: str
    node: str
    detail: str
    #: Blocking hits stop a freeze; advisory ones are recorded and reported.
    blocking: bool = False

    def render(self) -> str:
        mark = "BLOCK" if self.blocking else "note "
        return f"  [{mark}] {self.node}: {self.sentinel} -- {self.detail}"


@dataclass
class SentinelReport:
    hits: list[SentinelHit] = field(default_factory=list)

    @property
    def blocking(self) -> list[SentinelHit]:
        return [h for h in self.hits if h.blocking]

    @property
    def ok(self) -> bool:
        return not self.blocking

    def render(self) -> str:
        if not self.hits:
            return "sentinels: clean"
        return "sentinels:\n" + "\n".join(h.render() for h in self.hits)


# ------------------------------------------------------------------ free sentinels

def duplicate_statements(statements: dict[str, str]) -> list[SentinelHit]:
    """Agents love restating existing lemmas.  Catch it by hash, before proving."""
    by_hash: dict[str, list[str]] = {}
    for name, text in statements.items():
        by_hash.setdefault(statement_hash(_body_of(text)), []).append(name)
    hits = []
    for names in by_hash.values():
        if len(names) > 1:
            for name in names[1:]:
                hits.append(
                    SentinelHit(
                        "duplicate statement",
                        name,
                        f"same statement as {names[0]}",
                        blocking=True,
                    )
                )
    return hits


_WP = re.compile(r"\bWP\b|\bwp\b")
_TWP = re.compile(r"\btwp\b|\bWP.*?\[\{")


def partial_correctness(name: str, statement: str) -> list[SentinelHit]:
    """Iris `WP` is partial: divergence satisfies every spec (PLAN.md 8.4).

    Termination-relevant statements need total weakest preconditions or an explicit
    side condition.  The sentinel does not decide -- it makes the auditor decide
    deliberately rather than by default.
    """
    if _WP.search(statement) and not _TWP.search(statement):
        return [
            SentinelHit(
                "partial-correctness flag",
                name,
                "uses partial `WP`: divergence satisfies this spec. Use `twp` / `[{ }]` "
                "or carry an explicit termination side condition if that is not intended",
            )
        ]
    return []


def reduction_sentinel(requester_goal: str, requested: str, name: str = "<request>") -> list[SentinelHit]:
    """No lateral moves (PLAN.md 8.4).

    A requested lemma whose statement equals the requester's own goal is not
    progress, it is restatement.  Rejecting it mechanically is what keeps the
    "bridge proof" anti-pattern -- shuffling difficulty sideways instead of
    discharging it -- out of the graph entirely.
    """
    if statement_hash(_body_of(requested)) == statement_hash(_body_of(requester_goal)):
        return [
            SentinelHit(
                "reduction sentinel",
                name,
                "the requested lemma is the requester's own goal restated; that is not progress",
                blocking=True,
            )
        ]
    return []


def converging_failures(stuck_statements: dict[str, str], requested: str, name: str = "<request>") -> list[SentinelHit]:
    """A request duplicating an already-`stuck` node is a design signal, not work.

    Independent reductions converging on one hard obligation mean the statement, or
    the invariant above it, is wrong -- and the fix is a re-plan, not another worker.
    """
    h = statement_hash(_body_of(requested))
    for node, text in stuck_statements.items():
        if statement_hash(_body_of(text)) == h:
            return [
                SentinelHit(
                    "converging failure",
                    name,
                    f"duplicates `{node}`, which is already stuck; route this to its decomposer as a re-plan",
                    blocking=True,
                )
            ]
    return []


_HYP_BINDER = re.compile(r"\(\s*(H[\w']*)\s*:")


def hygiene_sentinel(parent_statement: str, child_statement: str, name: str) -> list[SentinelHit]:
    """Compare a child's hypothesis load against its parent's (PLAN.md 8.2).

    Depth drifts in cost and idiom: each level states children in terms of "what I
    happen to have", accumulating incidental hypotheses.  This flags accumulation
    early; the gate's unused-premise report catches it post-hoc.
    """
    parent = len(_HYP_BINDER.findall(parent_statement))
    child = len(_HYP_BINDER.findall(child_statement))
    if child > parent + 2:
        return [
            SentinelHit(
                "hygiene sentinel",
                name,
                f"carries {child} named hypotheses against the parent's {parent}; "
                "check for incidental accumulation",
            )
        ]
    return []


def run_free_sentinels(
    statements: dict[str, str],
    *,
    parent_statements: dict[str, str] | None = None,
) -> SentinelReport:
    """Everything that costs nothing.  Always run, at every freeze."""
    report = SentinelReport()
    report.hits.extend(duplicate_statements(statements))
    for name, text in statements.items():
        report.hits.extend(partial_correctness(name, text))
        parent = (parent_statements or {}).get(name)
        if parent:
            report.hits.extend(hygiene_sentinel(parent, text, name))
    return report


# ----------------------------------------------------------------- costed sentinels

VACUITY_SCRIPT = "iIntros; iExFalso; done."


def vacuity_probe(gate, target: str, siblings, *, timeout_body: str = VACUITY_SCRIPT) -> SentinelHit | None:
    """A budgeted attempt to derive `False` from the statement's hypotheses.

    In Iris this catches real cases, because contradictions are derivable in-logic:
    `l ↦ v ∗ l ↦ w ⊢ False`.  A statement whose hypotheses are contradictory is
    provable and worthless, and finding that out here costs one compile instead of a
    worker's whole budget plus an amendment cycle.

    Costs a Rocq compile, so it is opt-in.
    """
    result = gate.run(target, list(siblings), target_body=timeout_body, check_assumptions=False)
    if result.ok:
        return SentinelHit(
            "vacuity probe",
            target,
            "the hypotheses are contradictory: `False` is derivable from them, so this "
            "statement is vacuously provable and says nothing",
            blocking=True,
        )
    return None


def _body_of(statement: str) -> str:
    """The proposition, without the `Lemma name` prefix -- so a rename is not a new lemma."""
    text = normalize_statement(statement)
    m = re.match(r"^\s*(?:#\[[^\]]*\]\s*)?(?:Local\s+|Global\s+|Program\s+)*[A-Z][A-Za-z]*\s+[\w']+\s*(.*)$", text)
    return m.group(1) if m else text
