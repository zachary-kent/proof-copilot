"""Every spelling of the ``pcp mcp`` server entry, built from one function.

A worker's CLI reads a per-node ``.mcp.json`` (:func:`write_mcp_config`); an operator's
Claude Code or Codex reads the same entry as JSON, a ``claude mcp add`` line or a
``[mcp_servers.pcp]`` TOML table (``pcp integrate``, docs/INTEGRATIONS.md).  All of them
go through :func:`server_entry`, so the server name (:data:`MCP_SERVER_NAME`) and its
argv exist exactly once, and the Claude Code plugin's static ``.mcp.json`` is held to it
by tests/test_integrations.py.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from pcp.mcp.names import MCP_SERVER_NAME
from pcp.util.io import json_dump

MCP_CONFIG_FILE = ".mcp.json"

#: Codex's defaults are 10 s to start and 60 s per tool call; ``proof_open`` on a cold
#: pool and ``verify_node`` both compile, so both would be reported as failures.
CODEX_STARTUP_TIMEOUT_SEC = 30
CODEX_TOOL_TIMEOUT_SEC = 600


def server_entry(*, pcp: str = "pcp", workspace: Path | str | None = None) -> dict[str, Any]:
    """``{"command", "args"}`` for ``pcp mcp``.

    ``workspace=None`` omits ``--workspace``: the server then roots itself in the
    directory the client starts it in, which is what a user-level entry shared by every
    project needs.  A string is passed through verbatim, so a client placeholder such as
    ``${CLAUDE_PROJECT_DIR}`` survives.
    """
    args = ["mcp"]
    if workspace is not None:
        args += ["--workspace", str(workspace)]
    return {"command": pcp, "args": args}


def claude_mcp_json(*, pcp: str = "pcp", workspace: Path | str | None = None) -> dict[str, Any]:
    """The ``.mcp.json`` document (Claude Code, and the plugin's bundled copy)."""
    return {"mcpServers": {MCP_SERVER_NAME: server_entry(pcp=pcp, workspace=workspace)}}


def claude_add_argv(*, pcp: str = "pcp", workspace: Path | str | None = None, scope: str = "user") -> list[str]:
    """``claude mcp add`` for the same entry (``scope``: local | user | project)."""
    entry = server_entry(pcp=pcp, workspace=workspace)
    return ["claude", "mcp", "add", "--scope", scope, MCP_SERVER_NAME, "--", entry["command"], *entry["args"]]


def codex_add_argv(*, pcp: str = "pcp", workspace: Path | str | None = None) -> list[str]:
    """``codex mcp add`` for the same entry (it cannot set the timeouts; the TOML can)."""
    entry = server_entry(pcp=pcp, workspace=workspace)
    return ["codex", "mcp", "add", MCP_SERVER_NAME, "--", entry["command"], *entry["args"]]


def _toml_str(value: str) -> str:
    # A JSON string is a valid TOML basic string for everything json.dumps emits.
    return json.dumps(value, ensure_ascii=False)


def codex_toml(*, pcp: str = "pcp", workspace: Path | str | None = None) -> str:
    """The ``[mcp_servers.pcp]`` table for ``~/.codex/config.toml`` or ``.codex/config.toml``."""
    entry = server_entry(pcp=pcp, workspace=workspace)
    args = ", ".join(_toml_str(a) for a in entry["args"])
    return (
        f"[mcp_servers.{MCP_SERVER_NAME}]\n"
        f"command = {_toml_str(entry['command'])}\n"
        f"args = [{args}]\n"
        f"startup_timeout_sec = {CODEX_STARTUP_TIMEOUT_SEC}\n"
        f"tool_timeout_sec = {CODEX_TOOL_TIMEOUT_SEC}\n"
    )


def write_mcp_config(workdir: Path, *, workspace: Path | None = None, pcp: str = "pcp") -> Path:
    """Point the worker's CLI at a ``pcp mcp`` server rooted in its own workdir.

    Rooted per node, so a worker's proof sessions cannot reach another node's scratch
    even though they share a binary.
    """
    target = Path(workdir) / MCP_CONFIG_FILE
    return json_dump(target, claude_mcp_json(pcp=pcp, workspace=workspace or workdir))
