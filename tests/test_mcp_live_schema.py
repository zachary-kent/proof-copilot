"""The unified result schema against real petanque: failures, goal lists, incremental
replay, timeouts, project-rooted pools, and the tools added with them (D3-D5, MF3, MF5, MF6).

Everything runs on temp copies: the corpus and the fixtures stay untouched, and every
test that edits a file edits its own copy.
"""

from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest
from conftest import SCRATCH, needs_petanque, needs_rocq

from pcp.mcp.result import BLOCK_KEYS
from pcp.mcp.server import PcpServer
from pcp.state.petanque import PetProcess

pytest.importorskip("pytanque")

INV_FIXTURE = Path(__file__).parent / "fixtures" / "iris_inv"

LOAD_TWICE = ['iIntros "Hl".', "wp_load.", "wp_seq.", "wp_load.", "iFrame."]


@pytest.fixture(scope="module")
def ws(tmp_path_factory) -> Path:
    root = tmp_path_factory.mktemp("schema")
    for name in ("Basic.v", "Blame.v", "_CoqProject"):
        shutil.copy(SCRATCH / name, root / name)
    return root


@pytest.fixture(scope="module")
def server(ws: Path):
    s = PcpServer(ws, pool_size=1)
    yield s
    s.close()


def _schema(out: dict) -> dict:
    assert list(out)[:5] == list(BLOCK_KEYS), out
    assert isinstance(out["what"], str) and out["what"] and "\n" not in out["what"]
    assert isinstance(out["next"], list)
    return out


def _open(server: PcpServer, file: str, lemma: str) -> str:
    out = _schema(server.proof_open(file, lemma))
    assert out["ok"] is True, out
    assert out["where"]["file"] == file and out["where"]["step"] == 0 and out["where"]["line"]
    return out["session"]


@needs_petanque
def test_step_results_carry_where_goal_and_the_goal_list(server: PcpServer) -> None:
    sid = _open(server, "Basic.v", "sep_comm")
    intro = _schema(server.proof_step(sid, 'iIntros "[HP HQ]".'))
    assert intro["ok"] and intro["where"]["step"] == 1 and intro["where"]["sentence"] == 'iIntros "[HP HQ]".'
    assert "goal_list" not in intro and intro["warnings"] == [] and isinstance(intro["effects"], list)
    split = _schema(server.proof_step(sid, 'iSplitL "HQ".'))
    assert split["what"].endswith("1 goal → 2 (2 new)")
    rows = split["goal_list"]["goals"]
    assert [(r["n"], r["shape"], r["status"], r["focused"]) for r in rows] == [
        (1, "Q", "new", True), (2, "P", "new", False)]
    assert any("bullet" in n for n in split["next"])
    # A failure: the step, the tactic, the goal it met, the error and a diagnosis.
    bad = _schema(server.proof_step(sid, "reflexivity."))
    assert bad["ok"] is False and bad["where"]["step"] == 3 and bad["where"]["sentence"] == "reflexivity."
    assert bad["error"] and "reflexive" in bad["error"] and bad["timed_out"] is False
    assert bad["goal"] and "⊢ Q" in bad["goal"][0] and bad["goal_shapes"] == ["Q", "P"]
    assert bad["diagnosis"] and bad["diagnosis_class"] and bad["diagnosis_confidence"] in ("high", "low")
    closed = _schema(server.proof_step(sid, 'iExact "HQ".'))
    assert closed["goal_list"]["closed"] == ["Q"] and closed["what"].endswith("goal closed, 1 left; now focused: P")
    done = _schema(server.proof_step(sid, 'iExact "HP".'))
    assert done["proof_finished"] and done["goal_list"]["after"] == 0
    assert done["next"][0].startswith('verify_node("Basic.v", "sep_comm", "iIntros')
    try_out = _schema(server.proof_try(_open(server, "Basic.v", "sep_comm"), ['iIntros "[HP HQ]".', "done."]))
    assert try_out["ok"] and try_out["survivors"] == ['iIntros "[HP HQ]".']
    assert try_out["results"][0]["goals"] == 1 and try_out["results"][0]["shape"] == "∗ (sep) · Q ∗ P"


@needs_petanque
def test_proof_trace_failure_is_placed_and_carries_the_goal(ws: Path, server: PcpServer) -> None:
    f = ws / "Trace1.v"
    f.write_text((ws / "Basic.v").read_text(encoding="utf-8").replace(
        "iIntros \"Hl\". wp_load. wp_seq. wp_load. iFrame. done.", "iIntros \"Hl\". wp_load. wp_seq. wp_load. iFrame. reflexivity."),
        encoding="utf-8")
    out = _schema(server.proof_trace("Trace1.v", "load_twice"))
    w = out["where"]
    assert out["ok"] is False and (w["file"], w["sentence"], w["step"]) == ("Trace1.v", "reflexivity.", 6)
    assert w["line"] == 30 and w["column"] and out["failure"]["line"] == w["line"]
    assert out["goal"] and "⌜v = v⌝" in out["goal"][0] and out["failure"]["diagnosis"]
    assert "edit Trace1.v:30" in out["next"][1] and out["replayed_from"] == 0
    assert server.proof_close(out["session"])["ok"]


@needs_petanque
def test_retrace_after_an_edit_reruns_only_the_tail(ws: Path, server: PcpServer, monkeypatch) -> None:
    """D5: the unchanged prefix is adopted from the last trace; count the sentences petanque runs."""
    f = ws / "Replay.v"
    source = (ws / "Basic.v").read_text(encoding="utf-8")
    f.write_text(source, encoding="utf-8")
    ran: list[str] = []
    real_run = PetProcess.run

    def counting(self, state, cmd, **kw):
        if any(s in cmd for s in (*LOAD_TWICE, "done.", "by iFrame.")):
            ran.append(cmd)
        return real_run(self, state, cmd, **kw)

    monkeypatch.setattr(PetProcess, "run", counting)
    first = _schema(server.proof_trace("Replay.v", "load_twice"))
    assert first["ok"] and first["finished"] and first["replayed_from"] == 0 and len(ran) == 6
    # Edit the last sentence in the file: the prefix key (statements only) is unchanged.
    f.write_text(source.replace("wp_load. iFrame. done.", "wp_load. by iFrame."), encoding="utf-8")
    ran.clear()
    second = _schema(server.proof_trace("Replay.v", "load_twice"))
    assert second["ok"] and second["finished"], second
    assert (second["replayed_from"], second["reused_steps"]) == (5, 4) and len(ran) == 1, ran
    assert second["saved_ms"] > 0 and "reused 4 steps" in second["what"]
    assert second["steps"] == 5 and [s.step for s in server.record(second["session"]).trace.steps] == list(range(6))
    # The session it returns is a normal one: its history is the whole script.
    rec = server.record(second["session"])
    assert [t for t, _ in rec.session.history][-1] == "by iFrame." and len(rec.session.history) == 5
    # A changed statement before the lemma changes the key: a full run.
    f.write_text(source.replace("Lemma sep_comm (P Q : iProp Σ) : P ∗ Q -∗ Q ∗ P.",
                                "Lemma sep_comm (P Q : iProp Σ) : Q ∗ P -∗ P ∗ Q."), encoding="utf-8")
    ran.clear()
    third = _schema(server.proof_trace("Replay.v", "load_twice"))
    assert third["replayed_from"] == 0 and len(ran) == 6
    # incremental=False forces a full run even when the cache would serve it.
    ran.clear()
    assert server.proof_trace("Replay.v", "load_twice", incremental=False)["replayed_from"] == 0 and len(ran) == 6


@needs_petanque
def test_a_restarted_process_falls_back_to_a_full_replay(ws: Path, server: PcpServer) -> None:
    script = [*LOAD_TWICE, "done."]
    assert server.proof_trace("Basic.v", "load_twice", script)["ok"]
    proc = server.pool.processes[0]
    proc.restart("test restart")
    again = _schema(server.proof_trace("Basic.v", "load_twice", script))
    assert again["ok"] and again["finished"] and again["replayed_from"] == 0


@needs_petanque
def test_a_step_timeout_is_a_result_and_never_wedges_the_pool(server: PcpServer) -> None:
    """D4: a tactic that loops is `timed_out`, the session stays usable, other sessions too."""
    old = server.pool.cfg.get("step_timeout")
    server.pool.cfg["step_timeout"] = 2
    try:
        sid = _open(server, "Basic.v", "sep_comm")
    finally:
        if old is None:
            server.pool.cfg.pop("step_timeout")
        else:
            server.pool.cfg["step_timeout"] = old
    out = _schema(server.proof_step(sid, "do 1000000000 idtac."))
    assert out["ok"] is False and out["timed_out"] is True and "lost" not in out, out
    assert "timed out" in out["what"] and out["where"]["sentence"] == "do 1000000000 idtac." and out["goal"]
    assert server.proof_step(sid, 'iIntros "[HP HQ]".')["ok"]  # the same session goes on
    other = _open(server, "Blame.v", "leftover_spatial")
    assert server.proof_step(other, 'iIntros "[HP HQ]".')["ok"]


@needs_petanque
@needs_rocq
def test_start_failure_is_placed_in_the_schema(ws: Path, server: PcpServer) -> None:
    (ws / "Broken.v").write_text("Lemma ok : True.\nProof. exact I. Qed.\n\nLemma bad : nat_is_not_a_thing.\nProof. Admitted.\n",
                                 encoding="utf-8")
    out = _schema(server.proof_open("Broken.v", "bad"))
    assert out["ok"] is False and out["timed_out"] is False and out["error"]
    assert out["where"]["file"] == "Broken.v" and out["where"]["line"] == 4 and out["next"]
    assert out["what"].startswith("the statement of bad does not elaborate")


@needs_petanque
@needs_rocq
def test_a_workspace_without_a_project_file_roots_the_pool_at_the_files_project(tmp_path: Path) -> None:
    """Issue 6 on the MCP path: `--workspace theories/sub` must still see `-Q . proj`."""
    from pcp.config.env import coqc_binary

    (tmp_path / "_CoqProject").write_text("-Q . proj\n", encoding="utf-8")
    sub = tmp_path / "sub"
    sub.mkdir()
    (tmp_path / "A.v").write_text("Definition answer := 42.\n", encoding="utf-8")
    built = subprocess.run([str(coqc_binary(tmp_path)), "-Q", ".", "proj", "A.v"], cwd=tmp_path, capture_output=True,
                           text=True, timeout=120, check=False)
    assert built.returncode == 0, built.stderr
    (sub / "B.v").write_text("From proj Require Import A.\n\nLemma b : answer = 42.\nProof. reflexivity. Qed.\n",
                             encoding="utf-8")
    server = PcpServer(sub, pool_size=1)
    try:
        out = _schema(server.proof_trace("B.v", "b"))
        assert out["ok"] and out["finished"], out
        assert server.record(out["session"]).session.pool.workspace == tmp_path.resolve()
    finally:
        server.close()


# ------------------------------------------------------- shape and invariants


@pytest.fixture(scope="module")
def inv_server(tmp_path_factory):
    root = tmp_path_factory.mktemp("iris_inv")
    for f in INV_FIXTURE.iterdir():
        shutil.copy(f, root / f.name)
    s = PcpServer(root, pool_size=1)
    yield s
    s.close()


@needs_rocq
@needs_petanque
def test_proof_expect_reports_the_minimal_difference_and_never_moves(inv_server: PcpServer) -> None:
    sid = _open(inv_server, "Inv.v", "offset_goal")
    assert inv_server.proof_step(sid, 'iIntros "#Hinv".')["ok"]
    wrong = _schema(inv_server.proof_expect(sid, "WP ! #(l +ₗ 1) ;; ! #l {{ v, True }}"))
    assert wrong["ok"] is False and "convertible" in wrong["what"].lower() or "NOT" in wrong["what"]
    assert [(d["expected"], d["actual"]) for d in wrong["parts"][0]["diffs"]] == [("1", "(0 + 1)")]
    assert any("strict=false" in n for n in wrong["next"])
    right = _schema(inv_server.proof_expect(sid, "WP ! #(?x +ₗ (0 + 1)) ;; ! #?x {{ _, True }}"))
    assert right["ok"] is True and right["parts"][0]["bindings"] == {"x": "l"}
    hyps = _schema(inv_server.proof_expect(sid, "", hyps={"Hinv": "inv _ (cnt_inv ?k l)"}))
    assert hyps["ok"] is True
    assert inv_server.proof_state(sid)["step"] == 1  # nothing moved


@needs_rocq
@needs_petanque
def test_proof_inv_generates_checks_and_applies_the_opening(inv_server: PcpServer) -> None:
    sid = _open(inv_server, "Inv.v", "load_goal")
    assert inv_server.proof_step(sid, 'iIntros "#Hinv".')["ok"]
    gen = _schema(inv_server.proof_inv(sid, "cnt_inv"))
    tactic = 'iInv "Hinv" as (n m) "(>Hl & >Hk & >%Hn & H & >%Hm)" "Hclose".'
    assert gen["ok"] and gen["tactic"] == tactic and gen["verified"] is True and "apply" in gen["next"][1]
    assert inv_server.proof_state(sid)["step"] == 1
    applied = _schema(inv_server.proof_inv(sid, "Hinv", apply=True))
    assert applied["ok"] and applied["applied"] is True and applied["where"]["step"] == 2
    assert applied["goal"] and '"Hl"' in applied["goal"][0]
    again = _schema(inv_server.proof_inv(sid, "Hinv"))  # ↑N is no longer in the mask
    assert again["ok"] is False and again["side_goals"] and again["error"]
