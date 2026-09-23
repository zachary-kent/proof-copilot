"""``pcp serve`` -- a read-only localhost dashboard over the graph (PLAN.md 10).

One HTML page and an SSE endpoint over the SQLite event table.  Read-only means
read-only: the graph is opened with ``mode=ro`` and nothing here ever writes, so a
dashboard cannot take a write lock from a running ``pcp prove`` or resurrect a graph
that is not there.

SSE resumes: every event carries an ``id:`` line and a reconnecting browser sends
``Last-Event-ID``, so a blip replays only what was missed.  A snapshot is pushed
whenever the graph's node table changes, whether or not an event accompanied it.
"""

from __future__ import annotations

import json
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any

from pcp.errors import UsageError
from pcp.orch.graph import Graph
from pcp.util.hashing import stable_json_hash

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
                "evidence": (n.evidence or "")[:600],
                "stale": bool(graph.stale_edges(n.id)),
            }
            for n in nodes
        ],
        "edges": [
            {"src": n.id, "dst": dst, "kind": kind} for n in nodes for dst, _epoch, kind in graph.deps(n.id)
        ],
        "burndown": burndown(graph),
        "ts": time.time(),
    }


def burndown(graph: Graph) -> dict[str, int]:
    """Progress = live admits discharged; attic lemmas count as zero (PLAN.md 8.8)."""
    all_nodes = graph.nodes()
    nodes = [n for n in all_nodes if n.proof_status != "attic"]
    done = sum(1 for n in nodes if n.proof_status in ("gated", "integrated"))
    return {
        "live": len(nodes),
        "discharged": done,
        "remaining": len(nodes) - done,
        "attic": sum(1 for n in all_nodes if n.proof_status == "attic"),
    }


def _snapshot_key(snap: dict[str, Any]) -> str:
    return stable_json_hash({k: v for k, v in snap.items() if k != "ts"})


class Handler(BaseHTTPRequestHandler):
    graph_path: Path

    def log_message(self, fmt: str, *args: Any) -> None:  # quiet by default
        pass

    def _graph(self) -> Graph:
        return Graph.open_readonly(self.graph_path)

    def do_GET(self) -> None:  # noqa: N802 -- BaseHTTPRequestHandler's spelling
        if self.path.startswith("/events"):
            self._events()
        elif self.path.startswith("/api/graph"):
            graph = self._graph()
            try:
                self._json(snapshot(graph))
            finally:
                graph.close()
        elif self.path.split("?", 1)[0] in ("/", "/index.html"):
            self._page()
        else:
            # A typo used to get the page with 200 and a silent JSON parse failure.
            self.send_error(404, "no such endpoint")

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
        self.send_response(200)
        self.send_header("Content-Type", "text/event-stream")
        self.send_header("Cache-Control", "no-cache")
        self.send_header("Connection", "keep-alive")
        self.end_headers()
        graph = self._graph()
        try:
            last = int(self.headers.get("Last-Event-ID") or 0)
        except ValueError:
            last = 0
        last_key = ""
        try:
            while True:
                for event in graph.events_since(last):
                    last = max(last, int(event["id"]))
                    self.wfile.write(
                        f"id: {event['id']}\nevent: graph\ndata: {json.dumps(event, default=str)}\n\n".encode()
                    )
                snap = snapshot(graph)
                key = _snapshot_key(snap)
                if key != last_key:
                    last_key = key
                    self.wfile.write(f"event: snapshot\ndata: {json.dumps(snap, default=str)}\n\n".encode())
                self.wfile.write(b": keepalive\n\n")
                self.wfile.flush()
                time.sleep(1.0)
        except (BrokenPipeError, ConnectionResetError):
            return
        finally:
            graph.close()


def banner(text: str) -> None:
    """Print the startup line; a non-UTF-8 stdout (LANG=C under systemd) must not
    kill the server after the port is bound."""
    try:
        print(text, flush=True)
    except UnicodeEncodeError:
        print(text.encode("ascii", "replace").decode("ascii"), flush=True)


def serve(graph_path: Path, *, host: str = "127.0.0.1", port: int = 8765) -> int:
    if not Path(graph_path).exists():
        raise UsageError(f"no graph at {graph_path}")
    if not PAGE.exists():
        raise UsageError(f"the dashboard page is missing at {PAGE} (package data not installed)")
    handler = type("BoundHandler", (Handler,), {"graph_path": Path(graph_path)})
    server = ThreadingHTTPServer((host, port), handler)
    banner(f"pcp serve → http://{host}:{port}  (read-only; Ctrl-C to stop)")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
    return 0
