"""Feature flags.  Speculative machinery is off by default and may not break the canary."""

from __future__ import annotations

DEFAULT_FLAGS: dict[str, bool] = {
    "recursive_decomposition": False,  # depth > 1 (PLAN.md 8.2); read by pcp.orch.decompose
    "amendment_lattice": False,        # beyond refute + human edit; read by pcp.orch.amend
}

#: Flags removed since an older config may still set them; :func:`pcp.config.schema.Config.validate`
#: warns once and drops them instead of refusing the whole config.
RETIRED_FLAGS: frozenset[str] = frozenset({
    "vacuity_probes", "sketch_compiler", "state_layer", "epsilon_spot_check", "or_nodes", "strict_no_gap",
})
