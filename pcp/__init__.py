"""proof-copilot: structured Iris proof state + an obligation-graph orchestrator.

Two separable products live here and stay separable (docs/ARCHITECTURE.md):

``pcp.rocq`` / ``pcp.state`` / ``pcp.mcp``  -- **pcp-state**: an Iris-aware, diffable,
                                              per-hypothesis proof-state layer over Rocq.
``pcp.orch``                                -- **pcp-orch**: the freeze -> prove pipeline
                                              over a durable SQLite obligation graph.

The daily loop (``pcp prove``) must run on a machine where the only Rocq binary is
``coqc``: ``pcp.orch`` never imports ``pcp.state`` or petanque.  ``tests/test_layering.py``
enforces that.
"""

__version__ = "0.3.1"
