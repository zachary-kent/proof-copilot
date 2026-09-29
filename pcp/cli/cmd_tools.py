"""``pcp tools``: the MCP proof tools from a shell, through a per-workspace daemon.

``call`` starts the daemon on first use (detached; it outlives this command, so a
``proof_open`` session is still there for the next ``proof_step``) and prints the tool's
JSON result.  See :mod:`pcp.mcp.daemon` for the daemon's lifecycle.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any

from pcp.cli.common import absolute, err, note
from pcp.errors import UsageError

#: Arguments that name a file: a path relative to *this* shell's directory is made
#: absolute, since the daemon resolves relative paths against the workspace.
_PATH_ARGS = ("file", "plan")


def workspace_of(args: argparse.Namespace) -> Path:
    """The project ``--workspace`` (else cwd) names, as the MCP server picks it (:func:`workspace_for`)."""
    if getattr(args, "workspace", None) is not None:
        ws = absolute(args.workspace)
        assert ws is not None
        if not ws.is_dir():
            raise UsageError(f"--workspace {args.workspace}: no such directory")
    else:
        ws = Path(os.getcwd())
    from pcp.config.toolchain import workspace_for

    return workspace_for(ws)


def parse_call_args(raw_json: str | None, pairs: list[str] | None) -> dict[str, Any]:
    """The JSON object argument merged with ``--arg k=v`` pairs (a value is JSON if it parses)."""
    out: dict[str, Any] = {}
    if raw_json:
        text = sys.stdin.read() if raw_json == "-" else raw_json
        try:
            parsed = json.loads(text)
        except ValueError as exc:
            raise UsageError(f"the arguments are not valid JSON: {exc}") from exc
        if not isinstance(parsed, dict):
            raise UsageError('the arguments must be a JSON object, e.g. \'{"session": "s1", "tactic": "iIntros."}\'')
        out.update(parsed)
    for pair in pairs or []:
        key, sep, value = pair.partition("=")
        if not sep or not key:
            raise UsageError(f"--arg {pair!r}: expected KEY=VALUE")
        try:
            out[key] = json.loads(value)
        except ValueError:
            out[key] = value
    return out


def _absolutize(args: dict[str, Any], workspace: Path) -> dict[str, Any]:
    cwd = Path(os.getcwd())
    if cwd == workspace:
        return args
    for key in _PATH_ARGS:
        value = args.get(key)
        if isinstance(value, str) and value and not Path(value).is_absolute() and (cwd / value).exists():
            args[key] = str((cwd / value).resolve())
    return args


def _print(obj: Any, *, compact: bool) -> None:
    print(json.dumps(obj, ensure_ascii=False, indent=None if compact else 2, default=str))


def cmd_tools(args: argparse.Namespace) -> int:
    from pcp.mcp import daemon

    action = args.tools_action
    if action is None:
        raise UsageError("pcp tools: expected one of call | list | status | stop | serve")
    if action == "list":
        return _list(args)
    paths = daemon.paths_for(workspace_of(args))
    if action == "serve":
        return _serve(args, paths)
    if action == "status":
        status = daemon.ping(paths)
        if status is None:
            note(f"no pcp tools daemon for {paths.workspace}")
            return 1
        _print(status, compact=False)
        return 0
    if action == "stop":
        stopped = daemon.stop_daemon(paths)
        note(f"pcp tools: {'stopped the daemon' if stopped else 'no daemon was running'} for {paths.workspace}")
        return 0
    # call
    call_args = _absolutize(parse_call_args(args.args_json, args.arg), paths.workspace)
    if args.no_start:
        if daemon.ping(paths) is None:
            raise UsageError(f"no pcp tools daemon for {paths.workspace} (drop --no-start to start one)")
    else:
        daemon.ensure_daemon(paths, idle_s=args.idle_timeout, factory=args.factory)
    reply = daemon.request(paths, {"op": "call", "tool": args.tool, "args": call_args}, timeout=args.timeout)
    if not reply.get("ok"):
        err(f"pcp tools call {args.tool}: {reply.get('error')}")
        return 1
    _print(reply.get("result"), compact=args.compact)
    return 0


def _serve(args: argparse.Namespace, paths: Any) -> int:
    import logging

    from pcp.mcp import daemon

    logging.basicConfig(stream=sys.stderr, level=logging.INFO, format="%(asctime)s %(message)s")
    factory = daemon.load_factory(args.factory or daemon.DEFAULT_FACTORY)
    server = daemon.ToolDaemon(paths, daemon.ToolSet({}), idle_s=args.idle_timeout)
    try:
        server.acquire()  # the lock first: a second daemon must not build a PcpServer at all
    except daemon.DaemonRunning as exc:
        note(str(exc))
        return 0
    server.install_signal_handlers()
    try:
        server.toolset = factory(paths.workspace)
    except BaseException:
        server.close()
        raise
    server.serve()
    return 0


def _list(args: argparse.Namespace) -> int:
    from pcp.mcp import daemon

    if args.factory:
        tools = daemon.load_factory(args.factory)(Path(os.getcwd())).tools
    else:
        from pcp.mcp.server import tool_functions

        # The functions only touch the server when called, so a stand-in suffices to
        # read their signatures and descriptions without spawning anything.
        tools = tool_functions(None)  # type: ignore[arg-type]
    for entry in daemon.tool_signatures(tools):
        print(f"{entry['signature']}\n    {entry['summary']}")
    return 0
