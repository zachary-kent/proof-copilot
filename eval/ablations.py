"""The ablation ladder (PLAN.md 13).

    no tools (baseline) → raw goal dump → +ledger → +retrieval → +speculative

Each rung adds exactly one capability, so the delta is attributable.  The rule that
makes this worth running: **a tool that does not survive its ablation gets deleted**.
Tool-surface bloat is a named risk, and the hard cap on tool count is only meaningful
if something occasionally fails to earn its place.

The number that decides whether the orchestration thesis pays is the *cheap-model*
solve rate, not the frontier one -- a frontier model that solves everything unaided
tells you nothing about a pipeline built on cheap parallel workers.
"""

from __future__ import annotations

from pathlib import Path

from eval.harness import Ablation

SKILLS = Path(__file__).resolve().parents[1] / "skills"


def _skill(name: str) -> list[str]:
    path = SKILLS / name
    return [path.read_text(encoding="utf-8")] if path.exists() else []


LADDER: dict[str, Ablation] = {
    # No tools at all: the statement and the file, nothing else.
    "baseline": Ablation(name="baseline"),
    # The worker can look at goals, but has no structured view of them.
    "goal-dump": Ablation(name="goal-dump", tools=["proof_open", "proof_step", "proof_state"]),
    # + the resource ledger: where_did_it_go / blame / leftovers.  This is the rung
    # that tests Claim 2 -- that Iris failures are resource-accounting failures.
    "ledger": Ablation(
        name="ledger",
        skills=_skill("prover.md"),
        tools=["proof_open", "proof_step", "proof_state", "proof_ledger", "proof_destruct"],
    ),
    # + retrieval: premise search and notation resolution (failure modes #5, #6).
    "retrieval": Ablation(
        name="retrieval",
        skills=_skill("prover.md"),
        tools=[
            "proof_open", "proof_step", "proof_state", "proof_ledger",
            "proof_destruct", "premise_search", "notation_resolve",
        ],
    ),
    # + speculative fan-out.  Near-free on a flat-rate window, expensive on a metered
    # API -- so this rung is also a test of the economics, not only the tooling.
    "speculative": Ablation(
        name="speculative",
        skills=_skill("prover.md"),
        tools=[
            "proof_open", "proof_step", "proof_state", "proof_ledger", "proof_destruct",
            "premise_search", "notation_resolve", "proof_try",
        ],
    ),
}

ORDER = ["baseline", "goal-dump", "ledger", "retrieval", "speculative"]


def deltas(results: list[dict]) -> list[str]:
    """Attribute the change in solve rate to the capability each rung added."""
    lines = []
    previous = None
    by_name = {r["ablation"]: r for r in results}
    for name in ORDER:
        r = by_name.get(name)
        if r is None:
            continue
        rate = 100 * r["solve_rate"]
        if previous is None:
            lines.append(f"{name:<14} {rate:5.1f}%")
        else:
            delta = rate - 100 * previous["solve_rate"]
            verdict = "earns its context" if delta > 2 else "DOES NOT EARN ITS CONTEXT -- delete it"
            lines.append(f"{name:<14} {rate:5.1f}%  ({delta:+.1f} pt)  {verdict}")
        previous = r
    return lines
