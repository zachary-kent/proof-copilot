"""`pcp serve` -- a read-only localhost dashboard over the graph (PLAN.md 10).

A browser is a strictly better graph renderer than curses at a fraction of the build
cost.  No framework, no build step, no client dependencies: one HTML page and an SSE
endpoint over the SQLite event table.

The cockpit is *not* this page.  Interaction lives in whatever harness you are
already sitting in -- steering is a sentence to the orchestrator session, not a
keybinding here.  This is the watching half, and it is deliberately read-only.
"""

from __future__ import annotations

import json
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any

from pcp.orch.graph import Graph

PAGE = Path(__file__).parent / "dashboard.html"


def snapshot(graph: Graph) -> dict[str, Any]:
    nodes = graph.nodes()
    return {
        "summary": graph.summary(),
        "nodes": [
            {
                "id": n.id,
                "name": n.name,
                "rank": n.rank,
                "parent": n.parent,
                "depth": n.depth,
                "epoch": n.epoch,
                "statement": n.statement,
                "statement_status": n.statement_status,
                "proof_status": n.proof_status,
                "attempts": n.attempts,
                "evidence": n.evidence[:600],
                "stale": bool(graph.stale_edges(n.id)),
            }
            for n in nodes
        ],
        "edges": [
            {"src": src, "dst": dst, "kind": kind}
            for n in nodes
            for dst, _epoch, kind in graph.deps(n.id)
            for src in (n.id,)
        ],
        # Progress = live admits discharged.  Fifty attic lemmas measure as zero
        # (PLAN.md 8.8) -- the burndown is not something a worker can inflate.
        "burndown": burndown(graph),
        "ts": time.time(),
    }


def burndown(graph: Graph) -> dict[str, int]:
    nodes = [n for n in graph.nodes() if n.proof_status != "attic"]
    done = sum(1 for n in nodes if n.done)
    return {
        "live": len(nodes),
        "discharged": done,
        "remaining": len(nodes) - done,
        "attic": sum(1 for n in graph.nodes() if n.proof_status == "attic"),
    }


class Handler(BaseHTTPRequestHandler):
    graph_path: Path

    def log_message(self, fmt: str, *args: Any) -> None:  # quiet by default
        pass

    def _graph(self) -> Graph:
        return Graph(self.graph_path)

    def do_GET(self) -> None:  # noqa: N802 -- BaseHTTPRequestHandler's spelling
        if self.path.startswith("/events"):
            return self._events()
        if self.path.startswith("/api/graph"):
            return self._json(snapshot(self._graph()))
        return self._page()

    def _page(self) -> None:
        body = PAGE.read_text(encoding="utf-8").encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _json(self, payload: dict[str, Any]) -> None:
        body = json.dumps(payload, default=str).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _events(self) -> None:
        """Server-sent events straight off the graph's own event table."""
        self.send_response(200)
        self.send_header("Content-Type", "text/event-stream")
        self.send_header("Cache-Control", "no-cache")
        self.send_header("Connection", "keep-alive")
        self.end_headers()
        graph = self._graph()
        last = 0
        try:
            while True:
                events = graph.events_since(last)
                for event in events:
                    last = max(last, event["id"])
                    self.wfile.write(f"event: graph\ndata: {json.dumps(event, default=str)}\n\n".encode())
                if events:
                    self.wfile.write(
                        f"event: snapshot\ndata: {json.dumps(snapshot(graph), default=str)}\n\n".encode()
                    )
                self.wfile.write(b": keepalive\n\n")
                self.wfile.flush()
                time.sleep(1.0)
        except (BrokenPipeError, ConnectionResetError):
            return
        finally:
            graph.close()


def serve(graph_path: Path, *, host: str = "127.0.0.1", port: int = 8765) -> int:
    if not Path(graph_path).exists():
        print(f"no graph at {graph_path}")
        return 2
    handler = type("BoundHandler", (Handler,), {"graph_path": Path(graph_path)})
    server = ThreadingHTTPServer((host, port), handler)
    print(f"pcp serve → http://{host}:{port}  (read-only; Ctrl-C to stop)")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
    return 0
