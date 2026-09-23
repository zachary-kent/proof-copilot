"""pcp.dash: ``pcp serve``'s read-only HTTP surface and ``pcp report``, neither of which
ever creates a graph."""

from __future__ import annotations

import contextlib
import http.client
import io
import json
import subprocess
import sys
import threading
import urllib.request
from http.server import ThreadingHTTPServer
from pathlib import Path

import pytest

from pcp.dash import serve as serve_mod
from pcp.errors import UsageError
from pcp.orch.graph import Graph
from pcp.orch.model import Node, node_id
from tests._orch_fixtures import build_plain_graph


@pytest.fixture
def server(tmp_path):
    with Graph(tmp_path / "g.db") as g:
        g.add_node(Node(id=node_id("a"), name="a", statement='Lemma a : "q" = "q".', statement_status="frozen"))
    handler = type("BoundHandler", (serve_mod.Handler,), {"graph_path": tmp_path / "g.db"})
    srv = ThreadingHTTPServer(("127.0.0.1", 0), handler)
    t = threading.Thread(target=srv.serve_forever, daemon=True)
    t.start()
    yield f"http://127.0.0.1:{srv.server_address[1]}"
    srv.shutdown()
    srv.server_close()


def _get(url: str) -> tuple[int, bytes]:
    try:
        with urllib.request.urlopen(url, timeout=5) as resp:
            return resp.status, resp.read()
    except urllib.error.HTTPError as exc:
        return exc.code, exc.read()


def test_unknown_paths_are_404_and_known_ones_answer(server):
    assert _get(f"{server}/favicon.ico")[0] == 404
    assert _get(f"{server}/api/graphXYZ")[0] == 200  # prefix route, as documented
    status, body = _get(f"{server}/api/graph")
    assert status == 200 and json.loads(body)["nodes"][0]["name"] == "a"
    status, body = _get(f"{server}/")
    assert status == 200 and b"EventSource" in body and b"&quot;" in body


def test_banner_survives_an_ascii_stdout(tmp_path):
    out = io.TextIOWrapper(io.BytesIO(), encoding="ascii")
    with contextlib.redirect_stdout(out):
        serve_mod.banner("pcp serve → http://x")
    out.flush()
    assert b"pcp serve ? http://x" in out.buffer.getvalue()
    with pytest.raises(UsageError, match="no graph"):
        serve_mod.serve(tmp_path / "missing.db")


def _pcp(*args: str, cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, "-m", "pcp.cli.main", *args], cwd=str(cwd), capture_output=True, text=True, check=False)


def test_report_and_serve_read_the_graph_and_never_create_one(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    graph.set_proof_status(node_id("c1"), "claimed")
    graph.set_proof_status(node_id("c1"), "stuck", evidence="e")
    n_events = len(graph.events_since())
    graph.close()
    out = _pcp("report", "--graph", str(tmp_path / "graph.db"), "-o", str(tmp_path / "r.html"), cwd=tmp_path)
    assert out.returncode == 0 and (tmp_path / "r.html").exists()
    missing = _pcp("report", "--graph", str(tmp_path / "nope.db"), "-o", str(tmp_path / "r2.html"), cwd=tmp_path)
    assert missing.returncode == 2 and not (tmp_path / "nope.db").exists() and not (tmp_path / "r2.html").exists()
    assert _pcp("serve", "--graph", str(tmp_path / "nope.db"), cwd=tmp_path).returncode == 2

    handler = type("BoundHandler", (serve_mod.Handler,), {"graph_path": tmp_path / "graph.db"})
    server = ThreadingHTTPServer(("127.0.0.1", 0), handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        port = server.server_address[1]
        conn = http.client.HTTPConnection("127.0.0.1", port, timeout=10)
        conn.request("GET", "/api/graph")
        resp = conn.getresponse()
        data = json.loads(resp.read())
        assert resp.status == 200 and data["summary"] == {"open": 1, "stuck": 1} and len(data["nodes"]) == 2
        conn.close()
        events = http.client.HTTPConnection("127.0.0.1", port, timeout=10)
        events.request("GET", "/events", headers={"Last-Event-ID": str(n_events - 2)})
        resp = events.getresponse()
        assert resp.status == 200 and resp.getheader("Content-Type") == "text/event-stream"
        chunk = b""
        while b"event: snapshot" not in chunk:
            chunk += resp.fp.read1(65536)
        ids = [int(line.split(b":")[1]) for line in chunk.splitlines() if line.startswith(b"id:")]
        assert ids and all(i > n_events - 2 for i in ids) and len(ids) == 2, "only what was missed is replayed"
        events.close()
    finally:
        server.shutdown()
        server.server_close()
