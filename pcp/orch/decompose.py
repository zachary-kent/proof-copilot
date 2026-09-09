"""The recursive control flow's *policy* (PLAN.md 8.2), feature-flagged off.

Everything the orchestrator does is one procedure::

    prove(stmt frozen@e, budget B):
        if estimate_simple(stmt):
            r ← dispatch(stmt, small b ⊂ B)      # optimistic probe
            if r = qed: return
        plan ← decompose(stmt)                    # children + GLUE PROOF
        freeze children  (sentinels always; audit only if triggered)
        for c in plan.children, in parallel: prove(c, share of B)

The daily loop is depth-1 with a human (or one decomposer) at the root; depth > 1
is Phase 7 material and stays behind ``config.flag("recursive_decomposition")``:
every function here that would *decide* to recurse says no while the flag is off,
so nothing speculative can reach the canary's critical path (ARCHITECTURE.md §3
rule 8).  What is built: the difficulty heuristic (to pick a probe budget, never to
gate on), the depth cap, the budget split, and the no-gap check.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from pcp.orch.model import Budget, Node
from pcp.rocq.lexer import identifiers, strip_comments

FLAG = "recursive_decomposition"
DEFAULT_DEPTH_CAP = 2

_MODALITY_MARKS = ("▷", "□", "|==>", "|={", "◇", "<pers>")
_INVARIANT_WORDS = frozenset({"inv", "na_inv", "cinv", "inv_alloc"})


def flagged(config: Any | None) -> bool:
    """Whether recursive decomposition is switched on at all."""
    return bool(config is not None and getattr(config, "flag", lambda *_: False)(FLAG))


@dataclass(frozen=True)
class Difficulty:
    """A cheap heuristic, deliberately: it picks a probe budget, it does not decide.
    The decision is probe-then-decompose, which is cheap to be wrong about."""

    size: int
    quantifiers: int
    modalities: int
    invariants: int

    @property
    def score(self) -> float:
        return self.size / 200.0 + 0.5 * self.quantifiers + 0.7 * self.modalities + 1.2 * self.invariants

    def simple(self, threshold: float = 2.5) -> bool:
        return self.score < threshold

    def to_json(self) -> dict[str, Any]:
        return {"size": self.size, "quantifiers": self.quantifiers, "modalities": self.modalities,
                "invariants": self.invariants, "score": self.score}


def estimate_difficulty(statement: str) -> Difficulty:
    code = strip_comments(statement)
    words = identifiers(code)
    return Difficulty(
        size=len(code),
        quantifiers=code.count("∀") + code.count("∃") + sum(1 for w in words if w in ("forall", "exists")),
        modalities=sum(code.count(m) for m in _MODALITY_MARKS),
        invariants=sum(1 for w in words if w in _INVARIANT_WORDS),
    )


@dataclass(frozen=True)
class DecompositionPolicy:
    depth_cap: int = DEFAULT_DEPTH_CAP
    #: Relaxed no-gap is the default: children freeze and dispatch immediately and
    #: the glue is a concurrent node (PLAN.md 8.2).
    strict_no_gap: bool = False
    probe_first: bool = True
    probe_share: float = 0.15


def may_decompose(node: Node, policy: DecompositionPolicy, config: Any | None = None) -> tuple[bool, str]:
    """At the cap a decomposer may not decompose: dispatch or return ``stuck``.  Off
    the flag, the answer is always no -- the daily loop is depth-1."""
    if not flagged(config):
        return False, f"recursive decomposition is off (config flag `{FLAG}`); the daily loop is depth-1"
    if node.depth >= policy.depth_cap:
        return False, (
            f"depth cap {policy.depth_cap} reached; re-plan one level up rather than adding "
            "another layer -- depth usually signals a missing abstraction"
        )
    if node.budget.exhausted():
        return False, "budget exhausted; this propagates upward as stuck"
    return True, ""


def probe_budget(node: Node, policy: DecompositionPolicy) -> Budget:
    return node.budget.split(1, share=policy.probe_share)


def child_budgets(node: Node, n_children: int) -> Budget:
    """Geometric split: depth is bounded and the cheap direction is width."""
    return node.budget.split(max(1, n_children))


def no_gap_check(children: list[str], glue: str) -> list[str]:
    """Strong no-gap (PLAN.md 8.8): the demand edge is the glue referencing the child.
    Returns the children the glue never mentions -- nodes nothing demands."""
    used = set(identifiers(strip_comments(glue)))
    return [name for name in children if name not in used]


def accept_plan(
    node: Node,
    children: list[str],
    glue: str,
    policy: DecompositionPolicy,
    *,
    config: Any | None = None,
    glue_gated: bool | None = None,
) -> tuple[bool, str]:
    allowed, why = may_decompose(node, policy, config)
    if not allowed:
        return False, why
    unused = no_gap_check(children, glue)
    if unused:
        return False, (
            "pull-only node creation: the glue never references " + ", ".join(unused)
            + " -- a node nothing demands cannot enter the graph"
        )
    if policy.strict_no_gap and not glue_gated:
        return False, "strict no-gap: the glue proof must Qed against the admitted children first"
    return True, ""


def intent_brief(root_goal: str, parent_rationale: str) -> str:
    """Two lines, carried in every context packet, so deep nodes are stated in the
    root's idiom rather than the local one (PLAN.md 8.2, "Depth is a smell")."""
    return (
        f"root goal: {' '.join(root_goal.split())[:200]}\n"
        f"why this node: {' '.join(parent_rationale.split())[:200]}"
    )


__all__ = [
    "DEFAULT_DEPTH_CAP",
    "FLAG",
    "DecompositionPolicy",
    "Difficulty",
    "accept_plan",
    "child_budgets",
    "estimate_difficulty",
    "flagged",
    "intent_brief",
    "may_decompose",
    "no_gap_check",
    "probe_budget",
]
