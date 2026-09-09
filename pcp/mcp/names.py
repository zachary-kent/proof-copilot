"""The tool surface, by name (PLAN.md 7).  Hard-capped, and listed in one place.

Every tool is a place the model can get lost, so the count is capped at
:data:`MAX_TOOLS` and asserted at import.  The blurbs are what the worker packet says
about a granted tool: a granted tool the worker is never told about is an ungranted
tool.
"""

from __future__ import annotations

MCP_SERVER_NAME = "pcp"
MAX_TOOLS = 12

#: The ten tools, in the order the server registers them.
TOOLS: tuple[str, ...] = (
    "proof_open",
    "proof_step",
    "proof_state",
    "proof_trace",
    "proof_ledger",
    "proof_try",
    "proof_destruct",
    "premise_search",
    "notation_resolve",
    "verify_node",
)
assert len(TOOLS) <= MAX_TOOLS, "the tool surface is capped (PLAN.md 7)"

#: What ``--state-tools`` may grant (same set, same order).
STATE_TOOLS: tuple[str, ...] = TOOLS

BLURBS: dict[str, str] = {
    "proof_open": "open this lemma and get its Iris proof state, per hypothesis",
    "proof_step": "run one tactic from the current state and see exactly what changed — no file edit, no recompile",
    "proof_state": "render the current goal under a token budget; says what it elided",
    "proof_ledger": "where did a hypothesis go? what consumed it? what is still live?",
    "proof_try": "run up to 20 candidate tactics from one state and report which survive",
    "proof_destruct": "compile an iDestruct/iIntros pattern from the hypothesis' structure, or find out exactly where your pattern and the prop diverge",
    "premise_search": "search for a lemma *at this goal*, instead of guessing a name",
    "notation_resolve": "what a notation means, what it unfolds to, which tactics apply",
    "proof_trace": "replay a script and get the resource-ledger event log",
    "verify_node": "run the deterministic gate on a proof body",
}


def mcp_tool_name(tool: str) -> str:
    """``proof_ledger`` -> ``mcp__pcp__proof_ledger``, the name the CLI allowlists."""
    return tool if tool.startswith("mcp__") else f"mcp__{MCP_SERVER_NAME}__{tool}"


def describe_tools(names: list[str]) -> list[tuple[str, str]]:
    """``(allowlist name, blurb)`` for each granted tool, in ``TOOLS`` order."""
    granted = set(names)
    return [(mcp_tool_name(t), BLURBS[t]) for t in TOOLS if t in granted]


def parse_state_tools(value: str | None) -> list[str]:
    """``--state-tools`` argument -> tool names.  ``None``/``all``/``""`` mean all."""
    from pcp.errors import UsageError

    if value is None or value.strip() in ("", "all"):
        return list(STATE_TOOLS)
    wanted = [t.strip() for t in value.split(",") if t.strip()]
    unknown = [t for t in wanted if t not in STATE_TOOLS]
    if unknown:
        raise UsageError(f"unknown state tool(s): {', '.join(unknown)}. Choose from: {', '.join(STATE_TOOLS)}")
    return [t for t in STATE_TOOLS if t in wanted]
