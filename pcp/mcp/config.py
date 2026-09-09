"""The ``.mcp.json`` a worker's CLI reads to find its ``pcp mcp`` server."""

from __future__ import annotations

from pathlib import Path

from pcp.mcp.names import MCP_SERVER_NAME
from pcp.util.io import json_dump

MCP_CONFIG_FILE = ".mcp.json"


def write_mcp_config(workdir: Path, *, workspace: Path | None = None, pcp: str = "pcp") -> Path:
    """Point the worker's CLI at a ``pcp mcp`` server rooted in its own workdir.

    Rooted per node, so a worker's proof sessions cannot reach another node's scratch
    even though they share a binary.
    """
    target = Path(workdir) / MCP_CONFIG_FILE
    return json_dump(
        target,
        {
            "mcpServers": {
                MCP_SERVER_NAME: {
                    "command": pcp,
                    "args": ["mcp", "--workspace", str(workspace or workdir)],
                }
            }
        },
    )
