"""The ablation ladder (PLAN.md 13).

    no tools (baseline) -> raw goal dump -> +ledger -> +retrieval -> +speculative

Each rung is a strict superset of the previous one, so the change in solve rate
between neighbours is attributable to what the rung added.  The rule that makes this
worth running: **a tool that does not survive its ablation gets deleted**.  The tool
surface is hard-capped (``pcp.mcp.names.MAX_TOOLS``), and the cap is only meaningful if
something occasionally fails to earn its place.

An arm is a *value* (tools + skill) and nothing else.  The runner for an arm is built
from that value by ``eval/harness.py`` -- one runner per arm, never one runner for the
whole ladder -- which is what makes the legacy "control arm launched with every other
arm's MCP tools" bug impossible rather than fixed (bugs-dash-eval: harness.py:349).

The number that decides whether the orchestration thesis pays is the *cheap-model*
solve rate, not the frontier one -- a frontier model that solves everything unaided
tells you nothing about a pipeline built on cheap parallel workers.
"""

from __future__ import annotations

import sys
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pcp.mcp.names import STATE_TOOLS  # noqa: E402
from pcp.util.io import read_text  # noqa: E402
from pcp.util.paths import repo_root  # noqa: E402

#: A rung must move the solve rate by more than this to keep its context.
EARNS_THRESHOLD_PT = 2.0
PROVER_SKILL = "prover.md"


@dataclass(frozen=True)
class Ablation:
    """One rung: the state tools granted and the skill file (under ``skills/``) shown.

    ``skill`` is a file *name*, not its text, so the value is comparable and printable;
    :meth:`skill_texts` reads it when a packet is built.
    """

    name: str
    tools: tuple[str, ...] = ()
    skill: str = ""

    def __post_init__(self) -> None:
        unknown = [t for t in self.tools if t not in STATE_TOOLS]
        if unknown:
            raise ValueError(f"{self.name}: unknown state tool(s) {', '.join(unknown)}")

    def skill_texts(self, root: Path | None = None) -> list[str]:
        """The skill's text, for ``ProveConfig.skills``; ``[]`` when none or absent."""
        if not self.skill:
            return []
        path = (root or repo_root()) / "skills" / self.skill
        return [read_text(path)] if path.exists() else []

    def adds(self, previous: Ablation | None) -> str:
        """What this rung grants beyond ``previous`` -- the thing its delta measures."""
        if previous is None:
            return "no tools"
        tools = [t for t in self.tools if t not in previous.tools]
        parts = [f"+{t}" for t in tools]
        if self.skill and self.skill != previous.skill:
            parts.append(f"+skill {self.skill}")
        return " ".join(parts) or "nothing"

    def to_json(self) -> dict[str, Any]:
        return {"name": self.name, "tools": list(self.tools), "skill": self.skill}


_GOAL_DUMP = ("proof_open", "proof_step", "proof_state")
_LEDGER = (*_GOAL_DUMP, "proof_ledger", "proof_destruct")
_RETRIEVAL = (*_LEDGER, "premise_search", "notation_resolve")
_SPECULATIVE = (*_RETRIEVAL, "proof_try")

LADDER: dict[str, Ablation] = {
    # No tools at all: the statement and the file, nothing else.
    "baseline": Ablation("baseline"),
    # The worker can look at goals, but has no structured view of them.
    "goal-dump": Ablation("goal-dump", _GOAL_DUMP),
    # + the resource ledger: where_did_it_go / blame / leftovers, and the prover skill
    # that says how to use it.  This is the rung that tests Claim 2 -- that Iris
    # failures are resource-accounting failures.
    "ledger": Ablation("ledger", _LEDGER, PROVER_SKILL),
    # + retrieval: premise search and notation resolution (failure modes #5, #6).
    "retrieval": Ablation("retrieval", _RETRIEVAL, PROVER_SKILL),
    # + speculative fan-out.  Near-free on a flat-rate window, expensive on a metered
    # API -- so this rung is also a test of the economics, not only the tooling.
    "speculative": Ablation("speculative", _SPECULATIVE, PROVER_SKILL),
}

ORDER: tuple[str, ...] = ("baseline", "goal-dump", "ledger", "retrieval", "speculative")


def _check_supersets() -> None:
    previous: Ablation | None = None
    for name in ORDER:
        arm = LADDER[name]
        if previous is not None:
            assert set(previous.tools) <= set(arm.tools), f"{name} drops a tool {previous.name} had"
            assert not previous.skill or arm.skill == previous.skill, f"{name} drops {previous.name}'s skill"
        previous = arm


_check_supersets()


def describe() -> str:
    """The ladder, one rung per line, with what each rung adds."""
    lines = ["ablation ladder (each rung is a strict superset of the one before):"]
    previous: Ablation | None = None
    for name in ORDER:
        arm = LADDER[name]
        lines.append(f"  {name:<12} {arm.adds(previous)}")
        previous = arm
    return "\n".join(lines)


def _row(m: Any) -> Mapping[str, Any]:
    return m.to_json() if hasattr(m, "to_json") else m


def deltas(metrics: Sequence[Any]) -> str:
    """Attribute the change in solve rate to the capability each rung added.

    Takes ``Metrics`` objects or their ``to_json()`` rows.  Solve rates are over the
    tasks that were *measured*: an arm whose every task errored (a missing binary, a
    revoked login) has no rate and no verdict, because "0 % because claude was not on
    PATH" printed ``DOES NOT EARN ITS CONTEXT`` in the legacy harness.
    """
    by_name = {str(_row(m)["ablation"]): _row(m) for m in metrics}
    lines: list[str] = []
    previous: Mapping[str, Any] | None = None
    for name in ORDER:
        r = by_name.get(name)
        if r is None:
            continue
        measured = int(r.get("measured", r.get("n", 0)))
        if measured == 0:
            lines.append(f"{name:<14}   n/a   (no measurement: every task errored)")
            continue
        rate = 100 * float(r["solve_rate"])
        if previous is None:
            lines.append(f"{name:<14} {rate:5.1f}%")
        else:
            delta = rate - 100 * float(previous["solve_rate"])
            verdict = "earns its context" if delta > EARNS_THRESHOLD_PT else "DOES NOT EARN ITS CONTEXT -- delete it"
            lines.append(f"{name:<14} {rate:5.1f}%  ({delta:+.1f} pt)  {verdict}")
        previous = r
    return "\n".join(lines)


__all__ = ["EARNS_THRESHOLD_PT", "LADDER", "ORDER", "PROVER_SKILL", "Ablation", "deltas", "describe"]
