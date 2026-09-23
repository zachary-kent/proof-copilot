"""pcp.orch.prove.resume: crash resume, salvage, and which file a resumed run proves."""

from __future__ import annotations

import asyncio
import subprocess
import sys
from pathlib import Path

import pytest

from pcp.errors import LockedError
from pcp.orch.graph import Graph
from pcp.orch.model import node_id
from pcp.orch.protocol import NodePayload
from pcp.orch.prove import prove, workroot_lock_path
from pcp.orch.prove.design import design_rounds_used
from pcp.orch.prove.resume import DESIGNED_FILE_META, reopen_incomplete, resume_development
from pcp.orch.runners.mock import MockRunner
from pcp.orch.schedule import Scheduler
from pcp.util.locks import RunLock
from tests._orch_fixtures import ANSWERS, FakeGate, build_plain_graph, plain_cfg
from tests.conftest import needs_rocq

ROOT = Path(__file__).resolve().parents[1]
DRIVER = Path(__file__).with_name("_crash_driver.py")


def _events(graph: Graph) -> list[str]:
    return [e["kind"] for e in graph.events_since()]


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


def test_resume_never_salvages_a_body_gated_for_an_earlier_epoch(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    c1 = node_id("c1")
    graph.set_proof_status(c1, "claimed")
    a = graph.start_attempt(c1, runner="mock")
    graph.finish_attempt(a, status="qed", body="OLD EPOCH BODY", gate={"ok": True, "checks": []})
    graph.record_proof(c1, "OLD EPOCH BODY")
    graph.update(c1, proof_status="open", role="human")  # a revision invalidated it: epoch 1
    graph.set_proof_status(c1, "claimed")
    graph.start_attempt(c1, runner="mock")  # ... and the resumed run died mid-attempt
    assert reopen_incomplete(graph, max_attempts=3) == ["c1"]
    n = graph.by_name("c1")
    assert n.proof_status == "open" and n.body is None and n.epoch == 1
    assert "proof.salvaged" not in _events(graph)
    # The same row at the current epoch is salvaged.
    graph.set_proof_status(c1, "claimed")
    b = graph.start_attempt(c1, runner="mock")
    graph.finish_attempt(b, status="qed", body="NEW", gate={"ok": True, "checks": []})
    assert reopen_incomplete(graph, max_attempts=3) == []
    assert graph.by_name("c1").proof_status == "gated" and graph.by_name("c1").body == "NEW"
    graph.close()


def test_a_node_reopened_after_a_crash_carries_its_evidence_and_partial(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    c1 = node_id("c1")
    graph.set_proof_status(c1, "claimed")
    a = graph.start_attempt(c1, runner="mock")
    graph.finish_attempt(a, status="stuck", evidence="Error: iFrame failed: spatial context is not empty", body="iIntros. (* half *)")
    # ... the process died between finish_attempt and set_proof_status.
    assert reopen_incomplete(graph, max_attempts=2) == ["c1"]
    assert "spatial context" in graph.by_name("c1").evidence
    seen: list[NodePayload] = []
    runner = MockRunner(dict(ANSWERS), on_dispatch=seen.append)
    asyncio.run(Scheduler(graph, dev, runner, anchor="root", gate=FakeGate(), workroot=tmp_path / "work", node_seconds=5).run())
    p = next(x for x in seen if x.name == "c1")
    assert p.attempt == 2 and "spatial context" in p.evidence
    task = (p.workdir / "TASK.md").read_text(encoding="utf-8")
    assert "## Your previous attempt's proof (partial)" in task and "iIntros. (* half *)" in task
    graph.close()


@pytest.mark.parametrize("phase", ["after_start", "after_finish", "mid_design"])
@needs_rocq
def test_resume_after_a_real_process_death(tmp_path, canary_dir, phase):
    """The process is killed with ``os._exit`` -- no finally blocks, no WAL checkpoint."""
    sys.path.insert(0, str(ROOT / "tests"))
    from _crash_driver import ANSWERS as CANARY_ANSWERS
    from _crash_driver import EXIT_CODE, config

    proc = subprocess.run(
        [sys.executable, str(DRIVER), phase, str(tmp_path), str(canary_dir)],
        capture_output=True, text=True, timeout=600, check=False,
    )
    assert proc.returncode == EXIT_CODE, proc.stdout + proc.stderr
    graph = Graph(tmp_path / "graph.db")
    before = {n.name: n.proof_status for n in graph.nodes()}
    graph.close()
    RunLock(workroot_lock_path(tmp_path / "work")).acquire().release()
    RunLock((tmp_path / "graph.db").with_name("graph.db.lock")).acquire().release()  # the kernel released the locks
    dispatched: list[tuple[str, int, str]] = []
    runner = MockRunner(answers=dict(CANARY_ANSWERS), on_dispatch=lambda p: dispatched.append((p.name, p.attempt, p.file)))
    result = asyncio.run(prove(config(phase, tmp_path, canary_dir), runner))
    assert result.integrated, result.render()
    kinds = _events(result.graph)
    names = [n for n, _, _ in dispatched]
    if phase == "after_start":
        assert before["canary_main"] == "claimed"
        assert "run.resumed" in kinds and ("canary_main", 2, str(canary_dir / "Canary.v")) in dispatched
    elif phase == "after_finish":
        assert before["canary_main"] == "claimed"
        assert "proof.salvaged" in kinds and "canary_main" not in names, "a gated body is salvaged, not re-proved"
    else:
        designed = Path(str(result.graph.get_meta("designed_file")))
        assert designed.exists() and {f for _, _, f in dispatched} == {str(designed)}, "the designed file is honoured"
        assert design_rounds_used(result.graph, result.root) == 2, "the crashed round counts"
    assert result.graph.summary() == {"integrated": 3}
    assert len(result.render().splitlines()) <= 24
    result.close()


def test_two_runs_sharing_a_workroot_are_refused_by_the_workroot_lock(tmp_path):
    """Attempt ids are per graph, so two graphs on one workroot hand two live workers
    the same ``<node>/a1`` directory; the lock beside the workroot forbids it."""
    cfg = plain_cfg(tmp_path, run_lock=True, graph_path=tmp_path / "a.db")
    other = RunLock(workroot_lock_path(cfg.workroot)).acquire()
    try:
        with pytest.raises(LockedError, match="work.lock"):
            asyncio.run(prove(cfg, MockRunner({})))
        from pcp.cli.cmd_prove import fresh_start

        with pytest.raises(LockedError):
            fresh_start(tmp_path / "b.db", cfg.workroot)
    finally:
        other.release()
    assert workroot_lock_path(Path("/x/.pcp/work")) == Path("/x/.pcp/work.lock")
