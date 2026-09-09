"""Feature flags.  Speculative machinery is off by default and may not break the canary."""

from __future__ import annotations

DEFAULT_FLAGS: dict[str, bool] = {
    "recursive_decomposition": False,  # depth > 1 (PLAN.md 8.2)
    "or_nodes": False,                 # alternative plans raced under split budgets
    "strict_no_gap": False,            # glue must Qed before children dispatch
    "amendment_lattice": False,        # beyond refute + human edit
    "vacuity_probes": False,           # costs a Rocq compile per statement
    "sketch_compiler": False,          # CSL mode (PLAN.md 9)
    "state_layer": False,              # wire pcp-state into worker packets (see --state-tools)
    "epsilon_spot_check": False,       # defaults to zero in the daily loop
}

FLAG_DOCS: dict[str, str] = {
    "recursive_decomposition": "depth > 1 decomposition (PLAN 8.2)",
    "or_nodes": "alternative plans raced under split budgets",
    "strict_no_gap": "glue must Qed before children dispatch",
    "amendment_lattice": "amendment classes beyond refute + human edit",
    "vacuity_probes": "one Rocq compile per statement to detect contradictory hypotheses",
    "sketch_compiler": "CSL mode (PLAN 9)",
    "state_layer": "wire pcp-state into worker packets (superseded by --state-tools)",
    "epsilon_spot_check": "random re-audit of successes; zero in the daily loop",
}
