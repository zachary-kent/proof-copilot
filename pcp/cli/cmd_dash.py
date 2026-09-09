"""``pcp serve`` and ``pcp report``."""

from __future__ import annotations

import argparse

from pcp.cli.common import absolute
from pcp.errors import UsageError


def cmd_serve(args: argparse.Namespace) -> int:
    from pcp.dash.serve import serve

    graph = absolute(args.graph)
    assert graph is not None
    return serve(graph, host=args.host, port=args.port)


def cmd_report(args: argparse.Namespace) -> int:
    from pcp.dash.report import write_report
    from pcp.orch.graph import Graph

    graph_path = absolute(args.graph)
    assert graph_path is not None
    if not graph_path.exists():
        raise UsageError(f"no graph at {graph_path}")
    out = absolute(args.out)
    assert out is not None
    graph = Graph.open_readonly(graph_path)
    try:
        write_report(graph, out)
    finally:
        graph.close()
    print(f"wrote {out}")
    return 0
