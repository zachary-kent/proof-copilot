"""``pcp mcp``: the state-layer tool surface on stdio (contract 1.11)."""

from __future__ import annotations

import argparse

from pcp.cli.common import absolute


def cmd_mcp(args: argparse.Namespace) -> int:
    from pcp.mcp.server import run_stdio

    workspace = absolute(args.workspace)
    assert workspace is not None
    return run_stdio(workspace)
