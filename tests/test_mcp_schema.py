"""The one result schema (D3), goal lists (MF3), incremental replay (D5) and the server's
session/pool bookkeeping -- offline, with fakes.  The live side is test_mcp_live_schema.py.
"""

from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from pcp.mcp import server as server_mod
from pcp.mcp.names import TOOLS
from pcp.mcp.result import BLOCK_KEYS, conform, failure, one_line, result, where
from pcp.mcp.server import PcpServer, SectionContext, SessionRecord
from pcp.state.ipm.model import Hyp, IrisGoal, Modality, Step, WPInfo
from pcp.state.petanque import StateHandle
from pcp.state.render import describe_goal_list, goal_list, goal_shape
from pcp.state.trace import ReplayCache, ReplayEntry, Trace, Tracer, replay_key

pytest.importorskip("pytanque")


# ------------------------------------------------------------------- schema


def test_result_puts_the_fixed_block_first() -> None:
    out = result(True, "did it\nand more", where=where(step=3), goal=["g"], next=["a", ""], extra=1)
    assert list(out) == [*BLOCK_KEYS, "extra"]
    assert out["what"] == "did it" and out["next"] == ["a"]
    assert out["where"] == {"file": None, "line": None, "column": None, "sentence": None, "step": 3}
    assert where() is None
    bad = failure("nope", "Coq: boom")
    assert bad["ok"] is False and bad["error"] == "Coq: boom"


def test_conform_fills_a_bare_error_into_the_schema() -> None:
    out = conform({"error": "first line\nsecond", "lost": True})
    assert list(out)[:5] == list(BLOCK_KEYS) and out["ok"] is False and out["what"] == "first line"
    assert out["lost"] is True and out["next"] == [] and out["where"] is None
    assert conform({"answer": "x"})["ok"] is True
    assert conform({"ok": False, "what": "kept"})["what"] == "kept"


def test_one_line_collapses_and_cuts() -> None:
    assert one_line("\n\n  a   b \n c") == "a b"
    assert one_line("x" * 300, 10) == "x" * 9 + "…"


# ----------------------------------------------------------------- goal lists


def _g(goal: str, gid: str = "g0", *, hyps: tuple[str, ...] = (), ipm: bool = True, **mod: object) -> IrisGoal:
    return IrisGoal(goal_id=gid, spatial=[Hyp(id=h, prop=h) for h in hyps], goal=goal, is_ipm=ipm,
                    modality=Modality(**mod))  # type: ignore[arg-type]


def test_goal_shape_names_the_head_a_tactic_will_meet() -> None:
    wp = _g("WP ! #l {{ v, Φ v }}", wp=WPInfo(expr_hash="e", expr_summary="! #l"))
    assert goal_shape(wp) == "WP ! #l · WP ! #l {{ v, Φ v }}"
    assert goal_shape(_g("|={⊤}=> P", fupd=True, mask="⊤")).startswith("|={⊤}=> · ")
    assert goal_shape(_g("⌜x = 1⌝")).startswith("pure ⌜…⌝ · ")
    assert goal_shape(_g("Z.of_nat a = b", ipm=False)).startswith("Coq equality · ")
    assert goal_shape(_g("P ∗ Q")).startswith("∗ (sep) · ")
    assert goal_shape(_g("Q")) == "Q"  # an atom is its own shape
    assert len(goal_shape(_g("P ∗ " + "Q ∗ " * 100 + "R"))) == 100


def test_goal_list_marks_new_kept_focused_and_closed() -> None:
    parent, side = _g("P ∗ Q", "g0", hyps=("HP",)), _g("R", "g1")
    split = goal_list([parent, side], [_g("P", "g0"), _g("Q", "g1"), _g("R", "g2")])
    assert split is not None and (split["before"], split["after"]) == (2, 3)
    assert [(g["n"], g["status"], g["focused"]) for g in split["goals"]] == [
        (1, "new", True), (2, "new", False), (3, "kept", False)]
    assert describe_goal_list(split) == "2 goals → 3 (2 new)"
    closed = goal_list([parent, side], [_g("R", "g0")])
    assert closed is not None and closed["closed"] == ["∗ (sep) · P ∗ Q"] and closed["goals"][0]["status"] == "kept"
    assert describe_goal_list(closed).startswith("goal closed, 1 left; now focused: R")
    # One goal transformed in place is not a change of goals: the render shows it.
    assert goal_list([parent, side], [_g("Q ∗ P", "g0"), _g("R", "g1")]) is None
    assert describe_goal_list(goal_list([parent], [])) == "no goals left"


# -------------------------------------------------------------- replay cache


def _handle(st: int, *, proc: int = 7, gen: int = 0, finished: bool = False) -> StateHandle:
    return StateHandle(process=proc, generation=gen, st=st, proof_finished=finished, state_hash=1000 + st)


def _entry(tactics: list[str], *, gen: int = 0) -> ReplayEntry:
    steps = [Step(step=0, state_id=1, tactic="<start>", goals=[_g("P")])]
    steps += [Step(step=i, state_id=i + 1, tactic=t, goals=[_g(f"P{i}")], elapsed_ms=100) for i, t in enumerate(tactics, 1)]
    states = [_handle(s.state_id, gen=gen, finished=i == len(tactics)) for i, s in enumerate(steps)]
    events = [SimpleNamespace(step=i, to_json=lambda: {}) for i in range(1, len(tactics) + 1)]
    return ReplayEntry(process=7, generation=gen, steps=steps, states=states, events=events, start_ms=50)


def test_replay_entry_reuses_the_longest_common_prefix() -> None:
    entry = _entry(["a.", "b.", "c."])
    assert entry.common_prefix(["a.", " b.", "x.", "c."]) == 2
    assert entry.common_prefix(["z."]) == 0 and entry.common_prefix(["a.", "b.", "c.", "d."]) == 3
    assert entry.saved_ms(2) == 250


def test_replay_cache_is_a_bounded_lru() -> None:
    cache = ReplayCache(size=2)
    for k in ("a", "b"):
        cache.put((k,), _entry([k]))
    assert cache.get(("a",)) is not None  # a is now the most recent
    cache.put(("c",), _entry(["c"]))
    assert cache.get(("b",)) is None and len(cache) == 2
    cache.drop(("a",))
    assert cache.get(("a",)) is None and cache.get(None) is None


def test_replay_key_ignores_proof_bodies_but_not_statements(tmp_path: Path) -> None:
    f = tmp_path / "x.v"
    f.write_text("Lemma a : True.\nProof. exact I. Qed.\n\nLemma b : True.\nProof. exact I. Qed.\n", encoding="utf-8")
    key = replay_key(f, "b", stub_prefix=True)
    f.write_text("Lemma a : True.\nProof. idtac. exact I. Qed.\n\nLemma b : True.\nProof. auto. Qed.\n", encoding="utf-8")
    assert replay_key(f, "b", stub_prefix=True) == key  # both proofs edited: same root state
    assert replay_key(f, "b", stub_prefix=False) != key
    f.write_text("Lemma a : 1 = 1.\nProof. exact I. Qed.\n\nLemma b : True.\nProof. auto. Qed.\n", encoding="utf-8")
    assert replay_key(f, "b", stub_prefix=True) != key
    assert replay_key(f, "missing", stub_prefix=True) is None


class _FakeSession:
    def __init__(self, proc: object) -> None:
        self.process = proc
        self.source_file = self.file = "/p/x.v"
        self.thm = "t"
        self.resumed: tuple | None = None

    def resume(self, root: StateHandle, history: list) -> None:
        self.resumed = (root, history)


def test_tracer_resume_adopts_the_prefix_only_on_the_same_process_generation() -> None:
    entry = _entry(["a.", "b.", "c."])
    stale = Tracer(_FakeSession(SimpleNamespace(id=7, generation=1)))  # type: ignore[arg-type]
    assert stale.resume(entry, ["a."]) is None and stale.session.resumed is None
    other = Tracer(_FakeSession(SimpleNamespace(id=8, generation=0)))  # type: ignore[arg-type]
    assert other.resume(entry, ["a."]) is None
    tracer = Tracer(_FakeSession(SimpleNamespace(id=7, generation=0)))  # type: ignore[arg-type]
    assert tracer.resume(entry, ["a.", "b.", "x."]) == 2
    root, history = tracer.session.resumed
    assert root.st == 1 and [(t, s.st) for t, s in history] == [("a.", 2), ("b.", 3)]
    assert [s.step for s in tracer.trace.steps] == [0, 1, 2] and tracer.trace.tactics == ["a.", "b."]
    assert [e.step for e in tracer.trace.events] == [1, 2] and not tracer.trace.finished
    assert tracer.prev_goals[0].goal == "P2"
    whole = Tracer(_FakeSession(SimpleNamespace(id=7, generation=0)))  # type: ignore[arg-type]
    assert whole.resume(entry, ["a.", "b.", "c."]) == 3 and whole.trace.finished


# ---------------------------------------------------------- sessions and pools


class _Closable(SimpleNamespace):
    closed = 0

    def close(self) -> None:
        self.closed += 1


def _record(server: PcpServer, sid: str) -> SessionRecord:
    trace = Trace(file="x.v", thm="t")
    trace.steps.append(Step(step=0, state_id=1, tactic="<start>", goals=[_g("P")]))
    session = _Closable(source_file=str(server.workspace / "x.v"), thm="t", pool=None)
    rec = SessionRecord(sid, session=session, tracer=SimpleNamespace(trace=trace))  # type: ignore[arg-type]
    server._sessions[sid] = rec
    return rec


def test_proof_close_closes_the_session_and_forgets_it(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    rec = _record(server, "s1")
    out = server.proof_close("s1")
    assert out["ok"] is True and out["closed"] == "s1" and rec.session.closed == 1 and server.sessions == []
    again = server.proof_close("s1")
    assert again["ok"] is False and "no session 's1'" in again["error"]
    other = _record(server, "s2")
    server.close()
    assert other.session.closed == 1 and server.sessions == []


def test_registering_past_the_cap_closes_the_oldest(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(server_mod, "MAX_SESSIONS", 2)
    server = PcpServer(tmp_path)
    sessions = [_Closable() for _ in range(3)]
    ids = [server._register(s, SimpleNamespace(), None).id for s in sessions]  # type: ignore[arg-type]
    assert server.sessions == ids[1:] and [s.closed for s in sessions] == [1, 0, 0]


def test_a_file_in_another_project_gets_a_pool_rooted_there(tmp_path: Path) -> None:
    """Issue 6 on the MCP path: the workspace is a directory without a project file."""
    (tmp_path / "_CoqProject").write_text("-Q . smr\n", encoding="utf-8")
    sub = tmp_path / "theories" / "hazptr"
    sub.mkdir(parents=True)
    (sub / "x.v").write_text("Lemma t : True. Proof. exact I. Qed.\n", encoding="utf-8")
    elsewhere = tmp_path.parent / f"{tmp_path.name}-ws"
    elsewhere.mkdir()
    server = PcpServer(elsewhere)
    pool = server._pool_for(reflect=False, file=sub / "x.v")
    assert pool.workspace == tmp_path.resolve() and pool is not server.pool and pool.cfg["start_timeout"]
    assert server._pool_for(reflect=False, file=sub / "x.v") is pool  # one pool per root, lazily
    assert pool in server._pools() and not pool.processes  # nothing spawned yet
    plain = tmp_path.parent / f"{tmp_path.name}-plain"
    plain.mkdir()
    (plain / "y.v").write_text("Lemma u : True. Proof. exact I. Qed.\n", encoding="utf-8")
    alone = PcpServer(plain)
    assert alone._pool_for(reflect=False, file=plain / "y.v") is alone.pool  # no project: the workspace
    rooted = PcpServer(tmp_path)
    assert rooted._pool_for(reflect=False, file=sub / "x.v") is rooted.pool  # the workspace is the project
    inside = PcpServer(sub)  # launched below the project: the workspace is the project (session 3)
    assert inside.workspace == tmp_path.resolve() and inside._pool_for(reflect=False, file=sub / "x.v") is inside.pool
    for s in (server, alone, rooted, inside):
        s.close()


def test_a_result_section_is_added_but_never_breaks_a_result(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    rec = _record(server, "s1")
    seen: list[SectionContext] = []

    def fine(ctx: SectionContext) -> list[str]:
        seen.append(ctx)
        return ["hello"]

    server.sections = {"extra": fine, "empty": lambda ctx: [], "broken": lambda ctx: 1 / 0, "goal": lambda ctx: "x"}
    ctx = SectionContext("proof_step", rec, "t.", [], None, None, False)
    out = server._sections({"ok": True, "goal": None}, ctx)
    assert out == {"ok": True, "goal": None, "extra": ["hello"]} and seen == [ctx]


def test_pcp_tools_list_prints_every_tool_without_a_server(capsys) -> None:
    from pcp.cli.main import main

    assert main(["tools", "list"]) == 0
    printed = capsys.readouterr().out
    for name in TOOLS:
        assert f"{name}(" in printed, name
    assert "incremental" in printed


def test_every_tool_description_is_json_safe_through_the_wrappers(tmp_path: Path) -> None:
    from pcp.mcp.server import tool_functions

    fns = tool_functions(PcpServer(tmp_path))
    out = json.loads(fns["proof_close"]("nope"))
    assert list(out)[:5] == list(BLOCK_KEYS)
