"""proof-copilot: structured Iris proof state + an obligation-graph orchestrator.

Two separable products live here, and they stay separable:

``pcp.core`` / ``pcp.mcp``   -- **pcp-state**: an Iris-aware, diffable, per-hypothesis
                               proof-state layer over Rocq (petanque).
``pcp.orch``                 -- **pcp-orch**: the recursive freeze->prove pipeline over a
                               durable SQLite obligation graph.

The daily loop (PLAN.md 8.11) has **no pcp-state dependency, by design**: day-one
workers ride plain ``coqc`` feedback, and the state layer is a measured upgrade to
their solve rate rather than a gate on the loop.  Concretely, importing
``pcp.orch.prove`` must not pull in petanque or the Iris state model -- ``pcp prove``
has to work on a machine where the only Rocq binary is ``coqc``.
``tests/test_layering.py`` enforces that.  (``pcp.orch`` does use ``pcp.core.vernac``,
which is a source lexer with no toolchain dependency at all.)
"""

__version__ = "0.1.0"
