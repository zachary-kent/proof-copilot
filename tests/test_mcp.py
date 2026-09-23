"""The MCP tool surface: offline shape guarantees, then the live server on a scratch copy.

One ``PcpServer`` is shared by the live tests (a pet with Iris loaded costs 1-2 GB); the
kill test runs last because it takes a process down.  The scratch corpus is copied to a
temp workspace: ``fast`` opens write a ``__pcpfast.v`` twin beside the file and the
fixtures must stay untouched.
"""

from __future__ import annotations

import io
import json
import shutil
import threading
from pathlib import Path
from types import SimpleNamespace

import pytest
from conftest import SCRATCH, needs_petanque, needs_rocq, petanque_available

from pcp import __version__
from pcp.errors import StateError, ToolchainError, UsageError
from pcp.mcp.names import MAX_TOOLS, TOOLS, mcp_tool_name
from pcp.mcp.server import (
    LOST_ACTION,
    ParentWatch,
    PcpServer,
    SessionRecord,
    build_server,
    default_blame_step,
    make_mcp,
    run_stdio,
    served_tool_names,
    tool_functions,
)
from pcp.state.ipm.model import Hyp, IrisGoal, Step
from pcp.state.trace import Trace
from pcp.util.proc import kill_tree

pytest.importorskip("pytanque")


def _has_mcp() -> bool:
    try:
        make_mcp("probe")
    except ToolchainError:
        return False
    return True


# ------------------------------------------------------------------- offline


def test_the_tool_surface_is_exactly_ten_and_namespaced(tmp_path: Path) -> None:
    assert len(TOOLS) == 10 <= MAX_TOOLS and len(set(TOOLS)) == 10
    assert "prove_this_lemma" not in TOOLS and "fix_this_proof" not in TOOLS
    fns = tool_functions(PcpServer(tmp_path))
    assert tuple(fns) == TOOLS
    assert all(fn.__doc__ for fn in fns.values()), "every served tool needs a description"
    assert [mcp_tool_name(t) for t in TOOLS] == [f"mcp__pcp__{t}" for t in TOOLS]


def test_pcp_server_refuses_a_workspace_that_does_not_exist(tmp_path: Path) -> None:
    missing = tmp_path / "nope"
    with pytest.raises(UsageError, match="nope"):
        PcpServer(missing)


def test_pcp_server_names_an_unexpanded_placeholder(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.chdir(tmp_path)
    with pytest.raises(UsageError, match=r"\$\{CLAUDE_PROJECT_DIR\}") as exc_info:
        PcpServer("${CLAUDE_PROJECT_DIR}")
    assert "unexpanded" in str(exc_info.value)


@pytest.mark.skipif(not _has_mcp(), reason="no mcp SDK installed")
def test_make_mcp_sets_serverinfo_version_to_pcps_own(tmp_path: Path) -> None:
    mcp = make_mcp("probe")
    assert getattr(mcp, "version", None) == __version__


@pytest.mark.skipif(not _has_mcp(), reason="no mcp SDK installed")
def test_make_mcp_works_with_the_installed_sdk_and_serves_exactly_the_tools(tmp_path: Path) -> None:
    assert hasattr(make_mcp("probe"), "tool")
    server, mcp = build_server(tmp_path)
    try:
        assert served_tool_names(mcp) == list(TOOLS)
    finally:
        server.close()


def test_every_tool_answers_json_on_bad_input(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    fns = tool_functions(server)
    calls = {
        "proof_open": ("nope.v", "x"),
        "proof_trace": ("nope.v", "x"),
        "verify_node": ("nope.v", "x", "idtac."),
        "proof_step": ("s9", "idtac."),
        "proof_state": ("s9",),
        "proof_ledger": ("s9", "events"),
        "proof_try": ("s9", ["idtac."]),
        "proof_destruct": ("s9", "H"),
        "premise_search": ("s9",),
        "notation_resolve": ("s9", "+"),
    }
    for name, args in calls.items():
        out = json.loads(fns[name](*args))
        assert "error" in out, name
        if args[0] == "s9":
            assert out == {"error": "no session 's9'; call proof_open first"}, name
        else:
            assert "nope.v" in out["error"], name
    server.close()


def _fake_record(sid: str, goal: IrisGoal, *, step_raises: Exception | None = None) -> SessionRecord:
    trace = Trace(file="x.v", thm="t")
    trace.steps.append(Step(step=0, state_id=1, tactic="<start>", goals=[goal]))

    def step(tactic: str, **_: object) -> Step:
        if step_raises is not None:
            raise step_raises
        raise AssertionError("unexpected step")

    tracer = SimpleNamespace(trace=trace, step=step)
    return SessionRecord(sid, session=SimpleNamespace(), tracer=tracer)  # type: ignore[arg-type]


def test_destruct_spec_unknown_key_is_an_error_object_not_a_traceback(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    goal = IrisGoal(goal_id="g0", spatial=[Hyp(id="H", prop="P ∗ Q")], goal="Q ∗ P")
    server._sessions["s1"] = _fake_record("s1", goal)
    bad = server.proof_destruct("s1", "H", spec={"pattern": "[A B]"})
    assert set(bad) == {"error"} and "unknown destruct spec key" in bad["error"] and "pattern" in bad["error"]
    assert "error" in server.proof_destruct("s1", "H", spec="[A B]")  # type: ignore[arg-type]
    auto = server.proof_destruct("s1", "H")
    assert auto["tactic"] == 'iDestruct "H" as "[H1 H2]".' and auto["binders"] == []
    named = server.proof_destruct("s1", "H", spec={"names": ["HP", "HQ"]})
    assert named["tactic"] == 'iDestruct "H" as "[HP HQ]".'
    missing = server.proof_destruct("s1", "nope")
    assert missing["error"] == 'no hypothesis named "nope"' and missing["available"] == ["H"]
    assert json.loads(tool_functions(server)["proof_destruct"]("s1", "H", {"zzz": 1}))["error"]


def test_a_lost_session_is_never_reported_as_a_tactic_failure(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    goal = IrisGoal(goal_id="g0", spatial=[Hyp(id="H", prop="P")], goal="P")
    server._sessions["s1"] = _fake_record(
        "s1", goal, step_raises=StateError("session t was lost when petanque restarted; call proof_open again")
    )
    out = server.proof_step("s1", "iFrame.")
    assert out == {"ok": False, "error": "session t was lost when petanque restarted; call proof_open again",
                   "lost": True, "action": LOST_ACTION}
    assert "diagnosis" not in out
    server._sessions["s2"] = _fake_record("s2", goal, step_raises=RuntimeError("boom"))
    assert server.proof_step("s2", "iFrame.") == {"error": "RuntimeError: boom"}
    assert server.proof_state("s1", step=7) == {"error": "no step 7"}
    assert server.proof_ledger("s1", "blame") == {"error": "hyp is required"}
    assert "unknown query" in server.proof_ledger("s1", "what")["error"]


def test_default_blame_step_is_the_failed_step_else_the_next_one() -> None:
    trace = Trace(file="x.v", thm="t")
    assert default_blame_step(trace) == 0
    trace.steps.append(Step(step=0, state_id=1, tactic="<start>"))
    trace.steps.append(Step(step=1, state_id=2, tactic="iFrame."))
    assert default_blame_step(trace) == 2
    trace.steps.append(Step(step=2, state_id=-1, tactic="done.", ok=False, error="x"))
    trace.failed_at = 2
    assert default_blame_step(trace) == 2


def test_run_stdio_exits_zero_at_once_when_already_orphaned(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr("pcp.mcp.server.os.getppid", lambda: 1)
    monkeypatch.setattr("pcp.mcp.server.build_server", lambda *a, **k: (_ for _ in ()).throw(AssertionError("built")))
    assert run_stdio(tmp_path) == 0


def test_run_stdio_reports_a_missing_sdk_on_stderr_with_exit_2(tmp_path: Path, monkeypatch) -> None:
    def no_sdk(name: str = "pcp") -> None:
        raise ToolchainError("no usable MCP server API found. Install it with pip install 'proof-copilot[mcp]'")

    monkeypatch.setattr("pcp.mcp.server.make_mcp", no_sdk)
    err = io.StringIO()
    monkeypatch.setattr("pcp.mcp.server.sys.stderr", err)
    assert run_stdio(tmp_path) == 2
    assert "no usable MCP server API" in err.getvalue()


def test_parent_watch_fires_when_the_parent_changes(monkeypatch) -> None:
    ppids = iter([4242, 4242, 4242, 99])
    monkeypatch.setattr("pcp.mcp.server.os.getppid", lambda: next(ppids, 99))
    fired = threading.Event()
    watch = ParentWatch(fired.set, interval_s=0.01)
    assert watch.original == 4242 and watch.daemon
    watch.start()
    assert fired.wait(5.0) and watch.fired
    assert ParentWatch.orphaned(99) is False
    monkeypatch.setattr("pcp.mcp.server.os.getppid", lambda: 1)
    assert ParentWatch.orphaned(1) is True and ParentWatch.orphaned(4242) is True


def test_pcp_mcp_hands_run_stdio_an_absolute_workspace(monkeypatch, tmp_path: Path) -> None:
    from pcp.cli.main import main

    seen: list[Path] = []
    monkeypatch.setattr("pcp.mcp.server.run_stdio", lambda ws: seen.append(ws) or 0)
    assert main(["mcp", "--workspace", "."]) == 0
    assert seen == [tmp_path.resolve()]


# The same bad calls, registered on the installed SDK and sent through its own client:
# every call travels the real JSON-RPC path over in-memory streams -- schema
# generation, argument validation, result framing -- so what the model's harness sees
# is what is asserted.
SDK_BAD_INPUT = {
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
    return _has_mcp() and hasattr(make_mcp("probe"), "_lowlevel_server")


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

                    seen["bad_input"] = {name: await call(name, args) for name, args in SDK_BAD_INPUT.items()}
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


# ---------------------------------------------------------------------- live


@pytest.fixture(scope="module")
def ws(tmp_path_factory) -> Path:
    root = tmp_path_factory.mktemp("ws")
    for name in ("Basic.v", "Blame.v", "_CoqProject"):
        shutil.copy(SCRATCH / name, root / name)
    return root


@pytest.fixture(scope="module")
def server(ws: Path, tmp_path_factory):
    if not petanque_available():
        pytest.skip("no petanque binary")
    s = PcpServer(ws, coq_root=tmp_path_factory.mktemp("coq"))
    yield s
    s.close()


def _open(server: PcpServer, file: str, lemma: str, **kw) -> str:
    out = server.proof_open(file, lemma, **kw)
    assert "session" in out, out
    assert out["goal"] and "goal g0" in out["goal"][0] and isinstance(out["state_id"], int)
    return out["session"]


@needs_petanque
class TestLive:
    def test_a_wrong_pattern_fails_with_a_diagnosis_by_construction(self, server: PcpServer) -> None:
        sid = _open(server, "Blame.v", "premature_consumption")
        out = server.proof_step(sid, 'iIntros "[HP HQ HR]".')
        assert out["ok"] is False and out["error"] and "lost" not in out
        assert "pattern" in out["diagnosis"].lower(), out["diagnosis"]
        # A failed step costs a step number but does not move the session.
        state = server.proof_state(sid, step=1)
        assert state["ok"] is False and state["error"] == out["error"] and state["step"] == 1
        good = server.proof_step(sid, 'iIntros "[[HP HQ] HR]"')  # no period: the server adds it
        assert good["ok"] is True and good["loop_of"] is None and good["proof_finished"] is False
        assert {e["kind"] for e in good["ledger"]} == {"Intro"} and {e["hyp"] for e in good["ledger"]} == {"HP", "HQ", "HR"}
        assert "spatial ∗" in good["goal"][0] and '"HR" : R' in good["goal"][0]
        # Speculative: no move, `loop_of` on a no-op names the *trace* step (the failed
        # step 1 counts in the trace, not in the session's history), no diagnosis on success.
        spec = server.proof_step(sid, "idtac.", mode="speculative")
        assert spec == {"ok": True, "error": None, "loop_of": 2, "diagnosis": ""}
        assert server.proof_step(sid, "idtac.")["loop_of"] == 2
        assert server.proof_step(sid, "reflexivity.", mode="speculative")["diagnosis"]

    def test_proof_try_lists_the_survivors(self, server: PcpServer) -> None:
        sid = _open(server, "Basic.v", "sep_comm")
        assert server.proof_step(sid, 'iIntros "[HP HQ]".')["ok"]
        out = server.proof_try(sid, ["iFrame.", "reflexivity.", 'iSplitL "HP".', "done."])
        assert "iFrame." in out["survivors"] and 'iSplitL "HP".' in out["survivors"]
        assert "reflexivity." not in out["survivors"]
        by_tactic = {r["tactic"]: r for r in out["results"]}
        assert by_tactic["iFrame."]["proof_finished"] is True and by_tactic["reflexivity."]["error"]
        assert len(by_tactic["reflexivity."]["error"]) <= 300
        # Nothing moved: the session still has two spatial resources.
        assert server.proof_ledger(sid, "leftovers")["count"] == 2

    def test_select_shows_an_unchanged_hypothesis_under_diff_only(self, server: PcpServer) -> None:
        sid = _open(server, "Blame.v", "leftover_spatial")
        assert server.proof_step(sid, 'iIntros "[HP HQ]".')["ok"]
        moved = server.proof_step(sid, "idtac.")
        assert moved["ok"] and moved["loop_of"] == 1
        assert "HP=unchanged" in moved["goal"][0] and '"HP" : P' not in moved["goal"][0]
        plain = server.proof_state(sid)
        assert plain["step"] == 2 and "HP=unchanged" in plain["goals"][0]
        selected = server.proof_state(sid, select="HP")
        assert '"HP" : P' in selected["goals"][0] and "HQ" in selected["goals"][0]  # HQ only in the manifest
        assert '"HQ" : Q' not in selected["goals"][0]
        full = server.proof_state(sid, diff_only=False)
        assert '"HP" : P' in full["goals"][0] and '"HQ" : Q' in full["goals"][0]
        assert "rendered 5/5 hypotheses" in full["goals"][0]  # the pure context counts too
        tiny = server.proof_state(sid, diff_only=False, budget=1)
        assert set(tiny["elided"]) >= {"HP", "HQ"} and "budget exhausted" in tiny["goals"][0]

    def test_the_ledger_answers_where_a_hypothesis_went(self, server: PcpServer) -> None:
        sid = _open(server, "Blame.v", "premature_consumption")
        assert server.proof_step(sid, 'iIntros "[[HP HQ] HR]".')["ok"]
        closed = server.proof_step(sid, "iFrame.")
        assert closed["ok"] and closed["proof_finished"] is True
        where = server.proof_ledger(sid, "where_did_it_go", hyp="HP")["answer"]
        assert "framed" in where and "step 2" in where
        blamed = server.proof_ledger(sid, "blame", hyp="HP")["answer"]
        assert "not available at step 3?" in blamed and "repair class: frame-later" in blamed
        assert server.proof_ledger(sid, "leftovers") == {"answer": "the spatial context is empty", "count": 0}
        assert server.proof_ledger(sid, "unused_at_qed") == {"answer": "every resource was consumed"}
        events = server.proof_ledger(sid, "events")["answer"]
        assert 'step 1 · Intro · "HP"' in events and "GoalClosed" in events
        assert server.proof_ledger(sid, "where_did_it_go") == {"error": "hyp is required"}

    def test_destruct_compiles_from_the_skeleton_and_applies(self, server: PcpServer) -> None:
        sid = _open(server, "Basic.v", "exists_pure")
        assert server.proof_step(sid, 'iIntros "H".')["ok"]
        auto = server.proof_destruct(sid, "H")
        assert auto["binders"] == ["n"] and auto["tactic"].startswith('iDestruct "H" as (n) "[%')
        assert auto["skeleton"].splitlines()[0].startswith("exists n")
        spec = server.proof_destruct(sid, "H", spec={"binders": ["m"], "names": ["Hm", "HΦ"], "pure": ["Hm"]})
        assert spec["tactic"] == 'iDestruct "H" as (m) "[%Hm HΦ]".'
        assert "unknown destruct spec key" in server.proof_destruct(sid, "H", spec={"pattern": "x"})["error"]
        applied = server.proof_destruct(sid, "H", apply=True)
        assert applied["ok"] is True and applied["error"] is None
        assert "Φ n" in applied["goal"][0] and '"H"' not in applied["goal"][0]
        assert server.proof_destruct(sid, "H")["available"]
        # A real Rocq failure on apply gets the real error diagnosed -- aligning the
        # compiled pattern with the skeleton it came from would always say it fits.
        sid2 = _open(server, "Basic.v", "exists_pure")
        assert server.proof_step(sid2, 'iIntros "H".')["ok"]
        failed = server.proof_destruct(
            sid2, "H", spec={"binders": ["n"], "names": ["Hn", "HΦ"], "intuit": ["HΦ"]}, apply=True
        )
        assert failed["tactic"] == 'iDestruct "H" as (n) "[Hn #HΦ]".' and failed["ok"] is False
        assert "not persistent" in failed["error"] and "not persistent" in failed["diagnosis"]
        assert "pattern aligns with the hypothesis' structure" not in failed["diagnosis"]
        assert server.record(sid2).trace.failed_at == 2 and server.proof_state(sid2)["ok"] is False

    def test_premise_search_and_notation_resolve(self, server: PcpServer) -> None:
        sid = _open(server, "Basic.v", "sep_comm")
        found = server.premise_search(sid, query="add_comm")
        assert found["count"] > 0 and "add_comm" in found["answer"]
        nothing = server.premise_search(sid)
        assert nothing["count"] == 0 and "no premises found" in nothing["answer"]
        assert "Notation" in server.notation_resolve(sid, "+")["answer"]

    @needs_rocq
    def test_verify_node_is_the_same_gate(self, server: PcpServer) -> None:
        ok = server.verify_node("Basic.v", "sep_comm", 'Proof. iIntros "[HP HQ]". iFrame. Qed.')
        assert ok["ok"] is True and ok["report"].startswith("gate: PASS") and "sep_comm" in ok["assumptions"]
        bad = server.verify_node("Basic.v", "sep_comm", "admit.")
        assert bad["ok"] is False and bad["report"].startswith("gate: FAIL")

    def test_two_sessions_step_concurrently_and_keep_their_own_goals(self, server: PcpServer) -> None:
        a = _open(server, "Basic.v", "sep_comm")
        b = _open(server, "Blame.v", "leftover_spatial")
        results: dict[str, dict] = {}
        barrier = threading.Barrier(2)

        def go(sid: str) -> None:
            barrier.wait()
            results[sid] = server.proof_step(sid, 'iIntros "[HP HQ]".')

        threads = [threading.Thread(target=go, args=(sid,)) for sid in (a, b)]
        for t in threads:
            t.start()
        for t in threads:
            t.join(timeout=120)
        assert results[a]["ok"] and results[b]["ok"], results
        assert "⊢ Q ∗ P" in results[a]["goal"][0] and "⊢ P\n" in results[b]["goal"][0] + "\n"
        assert "⊢ Q ∗ P" not in results[b]["goal"][0]

    @needs_rocq
    def test_reflect_opens_through_idump_without_touching_the_environment(self, server: PcpServer, monkeypatch) -> None:
        import os

        before = dict(os.environ)
        sid = _open(server, "Basic.v", "load_twice", reflect=True)
        assert dict(os.environ) == before
        step = server.proof_step(sid, 'iIntros "Hl".')
        assert step["ok"] and '"Hl" : l ↦ v' in step["goal"][0]
        rec = server.record(sid)
        assert rec.reflector is not None and rec.reflector.available is True
        state = rec.session.state(rec.trace.final.state_id)
        verbose = rec.reflector.dump_hyp("Hl", state=state, printing="Set Printing All.")
        assert verbose is not None and "pointsto" in verbose.body
        assert (server.coq_root / "pcp" / "IDump.vo").exists()

    def test_a_killed_petanque_is_reported_as_lost_and_proof_open_recovers(self, server: PcpServer) -> None:
        sid = _open(server, "Basic.v", "sep_comm")
        proc = server.record(sid).session.process
        assert proc is not None and proc in server.pool.processes and proc.pid
        kill_tree(proc.pid)
        out = server.proof_step(sid, 'iIntros "[HP HQ]".')
        assert out["ok"] is False and out["lost"] is True and out["action"] == LOST_ACTION
        assert "proof_open again" in out["error"] and "diagnosis" not in out
        again = server.proof_step(sid, "idtac.")
        assert again.get("lost") is True
        fresh = _open(server, "Basic.v", "sep_comm")
        assert server.proof_step(fresh, 'iIntros "[HP HQ]".')["ok"] is True
