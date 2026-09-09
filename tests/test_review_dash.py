"""Wave-3 review: the read-only dashboard's HTTP surface and startup."""

from __future__ import annotations

import contextlib
import io
import json
import threading
import urllib.request
from http.server import ThreadingHTTPServer

import pytest

from pcp.dash import serve as serve_mod
from pcp.errors import UsageError
from pcp.orch.graph import Graph
from pcp.orch.model import Node, node_id


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
