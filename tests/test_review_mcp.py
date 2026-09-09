"""Wave-3 review of the MCP server, driven through the installed SDK's own client.

The offline tests in ``test_mcp.py`` call the tool functions directly; here the
server is registered on the installed ``mcp`` SDK and every call travels the real
JSON-RPC path over in-memory streams -- schema generation, argument validation,
result framing -- so what the model's harness sees is what is asserted.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

pytest.importorskip("pytanque")
pytest.importorskip("mcp")

from pcp.mcp.names import TOOLS  # noqa: E402
from pcp.mcp.server import PcpServer, build_server, make_mcp  # noqa: E402

BAD_INPUT = {
    "proof_open": {"file": "nope.v", "lemma": "x"},
    "proof_trace": {"file": "nope.v", "lemma": "x"},
    "verify_node": {"file": "nope.v", "lemma": "x", "body": "idtac."},
    "proof_step": {"session": "s9", "tactic": "idtac."},
    "proof_state": {"session": "s9"},
    "proof_ledger": {"session": "s9", "query": "events"},
    "proof_try": {"session": "s9", "tactics": ["idtac."]},
    "proof_destruct": {"session": "s9", "hyp": "H", "spec": {"names": ["a"]}},
    "premise_search": {"session": "s9"},
    "notation_resolve": {"session": "s9", "token": "+"},
}


def _sdk_v2() -> bool:
    return hasattr(make_mcp("probe"), "_lowlevel_server")


@pytest.mark.skipif(not _sdk_v2(), reason="needs the mcp 2.x SDK (in-process lowlevel server)")
def test_the_server_survives_every_bad_call_through_the_sdk_client(tmp_path: Path, monkeypatch) -> None:
    import anyio
    from mcp.client.session import ClientSession
    from mcp.shared.memory import create_client_server_memory_streams

    seen: dict[str, object] = {}

    async def scenario() -> None:
        server, mcp = build_server(tmp_path)
        low = mcp._lowlevel_server
        try:
            async with (
                create_client_server_memory_streams() as (client_streams, server_streams),
                anyio.create_task_group() as tg,
            ):
                tg.start_soon(low.run, server_streams[0], server_streams[1], low.create_initialization_options())
                async with ClientSession(client_streams[0], client_streams[1]) as session:
                    await session.initialize()
                    listed = await session.list_tools()
                    seen["names"] = [t.name for t in listed.tools]
                    seen["schemas"] = {t.name: sorted((t.input_schema or {}).get("properties", {})) for t in listed.tools}

                    async def call(name: str, args: dict) -> tuple[bool, str]:
                        res = await session.call_tool(name, args)
                        return bool(res.is_error), (res.content[0].text if res.content else "")

                    seen["bad_input"] = {name: await call(name, args) for name, args in BAD_INPUT.items()}
                    # A fault *inside* a guarded tool is a JSON error object, not a protocol error.
                    monkeypatch.setattr(PcpServer, "_pool_for", lambda self, *, reflect: (_ for _ in ()).throw(RuntimeError("kaboom")))
                    (tmp_path / "x.v").write_text("Lemma x : True.\nProof. exact I. Qed.\n", encoding="utf-8")
                    seen["raise"] = await call("proof_open", {"file": "x.v", "lemma": "x"})
                    seen["after"] = await call("proof_state", {"session": "s9"})
                    seen["bad_types"] = await call("proof_step", {"session": 12, "tactic": ["a"]})
                    seen["missing"] = await call("proof_step", {"tactic": "x"})
                    seen["unknown"] = await call("nonexistent", {})
                    seen["still_alive"] = await call("proof_ledger", {"session": "s9", "query": "events"})
                tg.cancel_scope.cancel()
        finally:
            server.close()

    anyio.run(scenario)
    assert seen["names"] == list(TOOLS)
    assert seen["schemas"]["proof_destruct"] == ["apply", "hyp", "session", "spec"]
    assert seen["schemas"]["proof_state"] == ["budget", "diff_only", "mode", "relevance", "select", "session", "step"]
    for name, (is_error, text) in seen["bad_input"].items():
        assert not is_error, name
        assert "error" in json.loads(text), name
    is_error, text = seen["raise"]
    assert not is_error and json.loads(text) == {"error": "RuntimeError: kaboom"}
    assert json.loads(seen["after"][1]) == {"error": "no session 's9'; call proof_open first"}
    assert seen["bad_types"][0] and seen["missing"][0] and seen["unknown"][0], "the SDK refuses these itself"
    assert json.loads(seen["still_alive"][1]) == {"error": "no session 's9'; call proof_open first"}
