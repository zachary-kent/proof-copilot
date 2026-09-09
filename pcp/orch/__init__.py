"""pcp-orch: the freeze -> prove pipeline over a durable SQLite obligation graph (PLAN.md 8).

Never imports ``pcp.state``, ``pcp.mcp`` or petanque: the daily loop runs where the only
Rocq binary is ``coqc``.
"""
