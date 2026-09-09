"""pcp.orch.prove.resume: crash resume, salvage, and which file a resumed run proves."""

from __future__ import annotations

import asyncio

from pcp.orch.model import node_id
from pcp.orch.prove.resume import DESIGNED_FILE_META, reopen_incomplete, resume_development
from pcp.orch.runners.mock import MockRunner
from pcp.orch.schedule import Scheduler
from tests._orch_fixtures import ANSWERS, FakeGate, build_plain_graph, plain_cfg


def test_claimed_and_stuck_with_attempts_reopen_contested_stays(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("claimed", "stuck", "spent", "contested", "gated"))
    for name in ("claimed", "stuck", "spent", "contested", "gated"):
        graph.set_proof_status(node_id(name), "claimed")
    graph.set_proof_status(node_id("stuck"), "stuck", evidence="e")
    graph.set_proof_status(node_id("contested"), "contested", evidence="wrong")
    graph.record_proof(node_id("gated"), "exact I.")
    for _ in range(2):
        a = graph.start_attempt(node_id("spent"), runner="mock")
        graph.finish_attempt(a, status="stuck", evidence="x")
    graph.set_proof_status(node_id("spent"), "stuck", evidence="x")
    reopened = reopen_incomplete(graph, max_attempts=2)
    assert set(reopened) == {"claimed", "stuck"}
    assert graph.by_name("spent").proof_status == "stuck", "no attempts left this epoch"
    assert graph.by_name("contested").proof_status == "contested"
    assert graph.by_name("gated").proof_status == "gated"
    assert graph.by_name("stuck").evidence == "e", "the evidence carries into the next run's first attempt"
    graph.close()


def test_a_gate_passing_attempt_is_salvaged_instead_of_redispatched(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    graph.set_proof_status(node_id("c1"), "claimed")
    a = graph.start_attempt(node_id("c1"), runner="mock")
    graph.finish_attempt(a, status="qed", body="intros H. exact H.", gate={"ok": True, "checks": []})
    # ... and the process died here, before set_proof_status("gated").
    assert reopen_incomplete(graph, max_attempts=2) == []
    c1 = graph.by_name("c1")
    assert c1.proof_status == "gated" and c1.body == "intros H. exact H."
    assert any(e["kind"] == "proof.salvaged" for e in graph.events_since())
    graph.close()


def test_a_crash_mid_attempt_is_resumed_and_only_that_node_is_redispatched(tmp_path):
    class Crash(BaseException):
        pass

    graph, root, dev = build_plain_graph(tmp_path)

    def boom(p):
        if p.name == "root":
            raise Crash()

    first = MockRunner(dict(ANSWERS), on_dispatch=boom)
    try:
        asyncio.run(Scheduler(graph, dev, first, anchor="root", gate=FakeGate(), workroot=tmp_path / "w", node_seconds=5).run())
    except Crash:
        pass
    assert graph.by_name("root").proof_status == "claimed"
    assert reopen_incomplete(graph, max_attempts=2) == ["root"]
    dispatched: list[str] = []
    second = MockRunner(dict(ANSWERS), on_dispatch=lambda p: dispatched.append(p.name))
    report = asyncio.run(Scheduler(graph, dev, second, anchor="root", gate=FakeGate(), workroot=tmp_path / "w", node_seconds=5).run())
    assert dispatched == ["root"] and [o.status for o in report.outcomes] == ["qed"]
    assert graph.summary() == {"gated": 3}
    graph.close()


def test_the_designed_file_is_honoured_on_resume(tmp_path):
    cfg = plain_cfg(tmp_path)
    graph, root, dev = build_plain_graph(tmp_path / "g")
    assert resume_development(cfg, graph).path == cfg.file
    designed = tmp_path / "work" / "root.designed" / "Plain.v"
    designed.parent.mkdir(parents=True)
    designed.write_text(dev.source.replace("Admitted.", "Admitted. (* designed *)"), encoding="utf-8")
    graph.set_meta(DESIGNED_FILE_META, str(designed))
    assert resume_development(cfg, graph).path == designed
    designed.unlink()
    assert resume_development(cfg, graph).path == cfg.file, "a vanished design falls back to the source"
    graph.close()


def test_spec_only_resume_stages_the_development(tmp_path):
    cfg = plain_cfg(tmp_path, brief="spec-only")
    (cfg.file.parent / "DESIGN.md").write_text("# secret brief", encoding="utf-8")
    graph, root, dev = build_plain_graph(tmp_path / "g")
    staged = resume_development(cfg, graph)
    assert staged.path.parent == cfg.workroot / "root.staged"
    assert not (staged.path.parent / "DESIGN.md").exists()
    graph.close()
