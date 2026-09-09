"""Wave-3 review of the prove pipeline: liveness, crash-resume and the decomposer protocol.

Every test here reproduces a defect found by attacking the rewritten pipeline (or
pins an invariant the attack could not break).  Names say the scenario.
"""

from __future__ import annotations

import asyncio
import copy
import dataclasses
import http.client
import json
import shutil
import subprocess
import sys
import threading
import time
from http.server import ThreadingHTTPServer
from pathlib import Path

import pytest

from pcp.errors import LockedError, UsageError
from pcp.orch.contract import DesignContract
from pcp.orch.decomposer import (
    ChildStatement,
    Decomposer,
    PlanProposal,
    json_in_stream,
    parse_proposal,
    validate_proposal,
)
from pcp.orch.graph import Graph
from pcp.orch.model import Node, node_id
from pcp.orch.protocol import NodePayload, NodeResult
from pcp.orch.prove import (
    OrchestrationRequired,
    ProveConfig,
    ProveResult,
    freeze_target,
    prove,
    workroot_lock_path,
)
from pcp.orch.prove.design import (
    DesignDriver,
    DesignError,
    DesignViolatesContract,
    apply_design,
    design_rounds_used,
    stage_spec_only,
)
from pcp.orch.prove.integrate import integrate
from pcp.orch.prove.resume import reopen_incomplete
from pcp.orch.record import Recorder
from pcp.orch.runners.cli import CLIRunner, run_cli
from pcp.orch.runners.mock import WRONG_PROOF, MockRunner
from pcp.orch.schedule import NodeOutcome, RunReport, Scheduler, repin_edges
from pcp.orch.sentinels import SentinelReport
from pcp.rocq.assemble import Development, NodeSpec
from pcp.util.locks import RunLock
from tests._orch_fixtures import ANSWERS, PLAN_SOURCE, FakeGate, build_plain_graph, plain_cfg, write_plain
from tests.conftest import needs_rocq

ROOT = Path(__file__).resolve().parents[1]
DRIVER = Path(__file__).with_name("_crash_driver.py")


def _sched(graph, dev, runner, tmp_path, **kw) -> Scheduler:
    kw.setdefault("gate", FakeGate())
    kw.setdefault("workroot", tmp_path / "work")
    kw.setdefault("node_seconds", 5)
    return Scheduler(graph, dev, runner, anchor="root", **kw)


def _events(graph: Graph) -> list[str]:
    return [e["kind"] for e in graph.events_since()]


# ------------------------------------------------------------------ scheduler liveness


class HangingRunner:
    """Never returns and never honours ``budget_seconds``: a broken runner."""

    name = "hang"

    def __init__(self, write_answer: dict | None = None) -> None:
        self.write_answer = write_answer

    def available(self) -> bool:
        return True

    async def run_node(self, node: NodePayload) -> NodeResult:
        if self.write_answer is not None:
            (Path(node.workdir) / "answer.json").write_text(json.dumps(self.write_answer), encoding="utf-8")
        await asyncio.sleep(3600)
        return NodeResult(status="stuck")


def test_a_runner_that_never_returns_is_cut_off_at_the_deadline(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    s = _sched(graph, dev, HangingRunner(), tmp_path, node_seconds=0.3, deadline_grace_s=0.2, max_attempts=2)
    started = time.perf_counter()
    report = asyncio.run(asyncio.wait_for(s.run(), timeout=20))
    assert time.perf_counter() - started < 10, "the run wedged"
    assert {o.status for o in report.outcomes} == {"stuck"}
    assert all(o.attempts == 2 for o in report.outcomes), "a deadline is retried once, with evidence"
    assert all("did not stop it" in o.evidence for o in report.outcomes)
    assert graph.summary() == {"stuck": 2}, "nothing stays claimed"
    rows = graph.attempts_for(node_id("c1"))
    assert len(rows) == 2 and all(r["finished"] is not None and r["status"] == "stuck" for r in rows)
    graph.close()


def test_a_hung_runner_that_wrote_its_answer_first_is_honoured(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    runner = HangingRunner({"status": "qed", "proof": "intros H. exact H."})
    report = asyncio.run(asyncio.wait_for(_sched(graph, dev, runner, tmp_path, node_seconds=0.2, deadline_grace_s=0.1).run(), timeout=20))
    assert {o.status for o in report.outcomes} == {"qed"}
    assert graph.by_name("c1").proof_status == "gated" and graph.by_name("c1").body == "intros H. exact H."
    graph.close()


class BadRecorder:
    run_id = "r"
    root = Path("/nonexistent")

    def write(self, *a, **k):
        raise OSError(28, "No space left on device")


def test_a_recorder_failure_does_not_lose_a_gated_proof(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    report = asyncio.run(_sched(graph, dev, MockRunner(dict(ANSWERS)), tmp_path, recorder=BadRecorder()).run())
    assert {o.status for o in report.outcomes} == {"qed"}
    assert graph.summary() == {"gated": 2}
    assert "record.failed" in _events(graph)
    graph.close()


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


# ------------------------------------------------------------------ crash-resume invariants


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
    asyncio.run(_sched(graph, dev, MockRunner(dict(ANSWERS), on_dispatch=seen.append), tmp_path).run())
    p = next(x for x in seen if x.name == "c1")
    assert p.attempt == 2 and "spatial context" in p.evidence
    task = (p.workdir / "TASK.md").read_text(encoding="utf-8")
    assert "## Your previous attempt's proof (partial)" in task and "iIntros. (* half *)" in task
    graph.close()


class ScriptedDecomposerRunner:
    name = "scripted-decomposer"

    def __init__(self, answers: list[str]):
        self.answers, self.calls = list(answers), 0

    def available(self) -> bool:
        return True

    async def run_node(self, node):
        text = self.answers[min(self.calls, len(self.answers) - 1)]
        self.calls += 1
        return NodeResult(status="qed", raw=text, trace={"final_text": text, "model": "scripted"})


def test_design_rounds_are_bounded_across_resumes(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=())
    for rnd in (1, 2):
        a = graph.start_attempt(root.id, runner="d", role="decomposer", round=rnd)
        graph.finish_attempt(a, status="stuck", evidence="rejected")
    assert design_rounds_used(graph, root) == 2
    plan = '{"children": [{"name": "c1", "statement": "Lemma c1 : True."}]}'
    runner = ScriptedDecomposerRunner([plan])
    cfg = plain_cfg(tmp_path, decomposer_runner=runner, max_design_rounds=2, decomposer_seconds=5)
    with pytest.raises(OrchestrationRequired, match="design budget is spent"):
        asyncio.run(DesignDriver(cfg, graph, root, contract=DesignContract.everything_frozen()).initial(dev))
    assert runner.calls == 0, "the budget is checked before the decomposer is spent"
    cfg.max_design_rounds = 3
    asyncio.run(DesignDriver(cfg, graph, root, contract=DesignContract.everything_frozen()).initial(dev))
    rows = [r for r in graph.attempts_for(root.id) if r["role"] == "decomposer"]
    assert runner.calls == 1 and rows[-1]["round"] == 3 and graph.by_name("c1") is not None
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


# ------------------------------------------------------------------ stale demand edges (PLAN.md 8.1)


def test_integration_refuses_a_stale_demand_edge_and_a_regated_proof_repins_it(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    c1 = node_id("c1")
    for n in (c1, root.id):
        graph.set_proof_status(n, "claimed")
        graph.record_proof(n, "exact I.")
    # c1 is restated (epoch 1): the root's proof was of c1@0.
    graph.update(c1, statement="Lemma c1 (P : Prop) : P -> P -> P.", epoch=1, proof_status="open", body=None, role="human")
    graph.set_proof_status(c1, "claimed")
    graph.record_proof(c1, "intros H _. exact H.")
    assert graph.stale_edges(root.id) == [(c1, 0, 1)]
    ok, detail = integrate(graph, dev, FakeGate(), root)
    assert not ok and "stale" in detail and "c1" in detail
    assert graph.by_name("root").proof_status == "gated", "nothing was half-integrated"
    repin_edges(graph, root.id)  # what recording a re-checked proof does
    assert graph.stale_edges(root.id) == []
    ok, detail = integrate(graph, dev, FakeGate(), root)
    assert ok, detail
    assert graph.summary() == {"integrated": 2}
    graph.close()


def test_a_restated_plan_child_makes_the_run_recheck_the_roots_proof(tmp_path, monkeypatch):
    """End to end with a scripted gate: the root was proved against c1@0; the user
    restates c1; the next run replays the root's proof and re-pins (or reopens it)."""
    monkeypatch.setattr("pcp.orch.prove.Gate", lambda d, **kw: FakeGate())
    cfg = plain_cfg(tmp_path)
    first = asyncio.run(prove(cfg, MockRunner(dict(ANSWERS))))
    assert first.integrated and first.graph.stale_edges(node_id("root")) == []
    first.close()
    cfg.plan.write_text(PLAN_SOURCE.replace("Lemma c1 (P : Prop) : P -> P.", "Lemma c1 (P : Prop) : P -> P -> P."), encoding="utf-8")
    dispatched: list[str] = []
    second = asyncio.run(prove(cfg, MockRunner(dict(ANSWERS), on_dispatch=lambda p: dispatched.append(p.name))))
    assert second.integrated, second.render()
    replayed = next(e for e in second.graph.events_since() if e["kind"] == "edges.revalidated")
    assert replayed["payload"] == {"kept": ["root"], "reopened": []}
    assert dispatched == ["c1"], "the root's proof still held on replay: not re-dispatched"
    assert second.graph.stale_edges(node_id("root")) == []
    second.close()
    # And when the replay fails, the root is reopened and re-dispatched.
    cfg3 = plain_cfg(tmp_path / "b")
    asyncio.run(prove(cfg3, MockRunner(dict(ANSWERS)))).close()
    cfg3.plan.write_text(PLAN_SOURCE.replace("Lemma c2 (Q : Prop) : Q -> Q.", "Lemma c2 (Q : Prop) : Q -> Q -> Q."), encoding="utf-8")
    monkeypatch.setattr("pcp.orch.prove.Gate", lambda d, **kw: FakeGate(reject=("intros H _.",)))  # the root's body
    dispatched.clear()
    third = asyncio.run(prove(cfg3, MockRunner(dict(ANSWERS), on_dispatch=lambda p: dispatched.append(p.name))))
    assert not third.integrated and set(dispatched) == {"c2", "root"}
    replayed = next(e for e in third.graph.events_since() if e["kind"] == "edges.revalidated")
    assert replayed["payload"]["reopened"] == ["root"]
    third.close()


# ------------------------------------------------------------------ the target is frozen


def test_the_run_target_is_frozen_whatever_the_contract_says(tmp_path):
    loose = DesignContract(results=frozenset({"helper"}), mutable_lemmas=True, allow_additions=True)
    frozen = freeze_target(loose, "root")
    assert frozen.results == {"helper", "root"} and freeze_target(frozen, "root") is frozen
    assert freeze_target(object(), "root") is not None  # a contract without results is left alone
    graph, root, dev = build_plain_graph(tmp_path, names=())
    rewrite = json.dumps({
        "definitions": [{"name": "root", "text": "Definition root : Prop."}],
        "children": [{"name": "c", "statement": "Lemma c : True."}],
    })
    cfg = plain_cfg(
        tmp_path, plan_source=None, decomposer_runner=ScriptedDecomposerRunner([rewrite]),
        max_design_rounds=1, decomposer_seconds=5, contract=loose,
    )
    graph.close()
    with pytest.raises(OrchestrationRequired) as exc:
        asyncio.run(prove(cfg, MockRunner({})))
    assert "root: changed" in str(exc.value) and "result to be proved" in str(exc.value)
    graph = Graph(cfg.graph_path)
    assert graph.get_meta("designed_file") is None
    graph.close()


# ------------------------------------------------------------------ decomposer protocol


def test_a_child_statement_with_a_trailing_sentence_is_refused(tmp_path):
    for trailer in ("Unset Guard Checking.", "Set Nested Proofs Allowed.", "Set Printing All."):
        p = parse_proposal(json.dumps({"children": [{"name": "foo", "statement": f"Lemma foo : True. {trailer}"}]}))
        problems = validate_proposal(p)
        assert any("exactly one sentence" in x for x in problems), (trailer, problems)
    graph, root, dev = build_plain_graph(tmp_path, names=())
    cfg = plain_cfg(tmp_path)
    smuggled = PlanProposal(children=(ChildStatement("foo", "Lemma foo : True. Unset Guard Checking."),))
    with pytest.raises(DesignViolatesContract, match="Guard Checking"):
        apply_design(cfg, graph, dev, root, smuggled, contract=DesignContract(allow_additions=True), round_no=1, workroot=tmp_path / "w")
    harmless = PlanProposal(children=(ChildStatement("foo", "Lemma foo : True. Set Printing All."),))
    with pytest.raises(DesignViolatesContract, match="single statement sentence"):
        apply_design(cfg, graph, dev, root, harmless, contract=DesignContract(allow_additions=True), round_no=1, workroot=tmp_path / "w")
    graph.close()


def _stream(*turns: str, tool_result: str = "") -> str:
    lines = []
    for text in turns:
        lines.append(json.dumps({"type": "assistant", "message": {"content": [{"type": "text", "text": text}]}}))
        if tool_result:
            lines.append(json.dumps({"type": "user", "message": {"content": [{"type": "tool_result", "content": tool_result}]}}))
    lines.append(json.dumps({"type": "result", "result": turns[-1]}))
    return "\n".join(lines)


def test_a_plan_stated_in_an_earlier_turn_is_found(tmp_path):
    plan = '{"children": [{"name": "c9", "statement": "Lemma c9 : True."}]}'
    template = '{"children": [{"name": "helper_lemma_name", "statement": "Lemma helper_lemma_name : True."}]}'
    raw = _stream("Here is the plan:\n```json\n" + plan + "\n```", "Done.", tool_result="TASK.md says: " + template)
    assert json_in_stream(raw)["children"][0]["name"] == "c9", "assistant text only, never a tool result"
    assert json_in_stream("not a stream") is None

    class Runner:
        name = "stream"

        def available(self):
            return True

        async def run_node(self, node):
            return NodeResult(status="qed", raw=raw, trace={"final_text": "Done.", "model": "m"})

    graph, root, dev = build_plain_graph(tmp_path, names=())
    out = asyncio.run(Decomposer(Runner(), graph, dev, tmp_path / "w").propose(root, None, budget_seconds=5))
    assert out.ok and out.proposal.names() == ["c9"], out.render()
    graph.close()


def test_decomposer_records_keep_the_stream_and_a_recorder_failure_does_not_end_the_run(tmp_path):
    plan = '{"children": [{"name": "c9", "statement": "Lemma c9 : True."}]}'
    raw = _stream(plan)

    class Runner:
        name = "stream"

        def available(self):
            return True

        async def run_node(self, node):
            return NodeResult(status="qed", raw=raw, trace={"final_text": plan, "model": "m"})

    graph, root, dev = build_plain_graph(tmp_path, names=())
    rec = Recorder(tmp_path / "rec", run_id="run")
    out = asyncio.run(Decomposer(Runner(), graph, dev, tmp_path / "w", rec).propose(root, None, budget_seconds=5))
    assert out.ok
    transcript = (tmp_path / "rec" / "run" / f"root.{out.attempt_id}.decompose" / "transcript.txt").read_text(encoding="utf-8")
    assert '"type": "assistant"' in transcript, "the full event stream, not the final text"
    out2 = asyncio.run(Decomposer(Runner(), graph, dev, tmp_path / "w", BadRecorder()).propose(root, None, budget_seconds=5))
    assert out2.ok and "record.failed" in _events(graph)
    graph.close()


def test_a_decomposer_runner_that_never_returns_is_a_deadline_and_protocol_slips_are_stuck_rows(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=())
    d = Decomposer(HangingRunner(), graph, dev, tmp_path / "w", deadline_grace_s=0.1)
    out = asyncio.run(asyncio.wait_for(d.propose(root, None, budget_seconds=0.2), timeout=20))
    assert out.deadline and not out.infrastructure and not out.ok
    rows = graph.attempts_for(root.id)
    assert rows[-1]["status"] == "stuck" and rows[-1]["finished"] is not None
    violation = ScriptedDecomposerRunner(['{"children": [{"name": "c", "statement": "Lemma c : True. Proof. exact I. Qed."}]}'])
    out2 = asyncio.run(Decomposer(violation, graph, dev, tmp_path / "w").propose(root, None, budget_seconds=5))
    assert out2.violation and graph.attempts_for(root.id)[-1]["status"] == "stuck"

    class Broken:
        name = "broken"

        def available(self):
            return True

        async def run_node(self, node):
            return NodeResult(status="error", evidence="`claude` is not on PATH")

    out3 = asyncio.run(Decomposer(Broken(), graph, dev, tmp_path / "w").propose(root, None, budget_seconds=5))
    assert out3.infrastructure and graph.attempts_for(root.id)[-1]["status"] == "error"
    graph.close()


ADVERSARIAL_REPLIES = {
    "json_with_braces_in_strings": ('{"rationale": "the triple {{{ P }}} e {{{ Q }}} is }", "children": [{"name": "c9", "statement": "Lemma c9 : True."}]}', "ok"),
    "unset_guard_checking_definition": ('{"definitions": ["Unset Guard Checking."], "children": [{"name": "c9", "statement": "Lemma c9 : True."}]}', "apply"),
    "nested_proofs_definition": ('{"definitions": ["Set Nested Proofs Allowed."], "children": [{"name": "c9", "statement": "Lemma c9 : True."}]}', "apply"),
    "axiom_definition": ('{"definitions": ["Axiom magic : False."], "children": [{"name": "c9", "statement": "Lemma c9 : True."}]}', "apply"),
    "lemma_with_proof_as_definition": ('{"definitions": [{"name": "h", "text": "Lemma h : True. Proof. exact I. Qed."}], "children": [{"name": "c9", "statement": "Lemma c9 : True."}]}', "refused"),
    "child_restating_the_root": ('{"children": [{"name": "again", "statement": "Lemma again (P Q : Prop) : P -> Q -> P."}]}', "refused"),
    "child_restating_an_existing_lemma": ('{"children": [{"name": "helper", "statement": "Lemma helper (P Q : Prop) : P -> Q -> Q."}]}', "refused"),
    "child_without_trailing_period": ('{"children": [{"name": "c9", "statement": "Lemma c9 : True"}]}', "ok"),
    "definitions_only": ('{"definitions": ["Definition v : nat := 0."], "children": []}', "refused"),
    "duplicate_names": ('{"children": [{"name": "c9", "statement": "Lemma c9 : True."}, {"name": "c9", "statement": "Lemma c9 : False."}]}', "refused"),
    "import_that_is_not_a_require": ('{"imports": ["Import foo."], "children": [{"name": "c9", "statement": "Lemma c9 : True."}]}', "refused"),
    "child_with_a_trailing_escape_hatch": ('{"children": [{"name": "c9", "statement": "Lemma c9 : True. Unset Guard Checking."}]}', "refused"),
    "children_not_a_list": ('{"children": "Lemma c9 : True."}', "refused"),
    "no_json_at_all": ("I would rather discuss the design in prose.", "refused"),
}


@pytest.mark.parametrize("name", sorted(ADVERSARIAL_REPLIES))
def test_every_adversarial_reply_is_refused_with_a_reaskable_problem(tmp_path, name):
    reply, expectation = ADVERSARIAL_REPLIES[name]
    graph, root, dev = build_plain_graph(tmp_path, names=())
    cfg = plain_cfg(tmp_path)
    out = asyncio.run(Decomposer(ScriptedDecomposerRunner([reply]), graph, dev, tmp_path / "w").propose(root, None, budget_seconds=5))
    assert out.render().strip(), "every verdict is text the decomposer can be re-asked with"
    assert not out.infrastructure
    if expectation == "refused":
        assert not out.ok, out.render()
        assert "Traceback" not in out.render()
        return
    assert out.ok, out.render()
    contract = DesignContract(allow_additions=True)
    if expectation == "apply":
        with pytest.raises(DesignError) as exc:
            apply_design(cfg, graph, dev, root, out.proposal, contract=contract, round_no=1, workroot=tmp_path / "w")
        assert "Traceback" not in str(exc.value)
        assert graph.get_meta("designed_file") is None and not list((tmp_path / "w").glob("*.designed*"))
    else:
        assert out.proposal.children[0].statement.endswith(".")
    graph.close()


# ------------------------------------------------------------------ report shape


def test_the_report_stays_one_screen_with_a_dozen_children_and_revisions(tmp_path):
    from pcp.orch.decomposer import DecompositionResult

    names = [f"child_{i}" for i in range(12)]
    plan = parse_proposal(json.dumps({"children": [{"name": n, "statement": f"Lemma {n} : True."} for n in names]}))
    rejected = DecompositionResult(problems=[f"problem {i}" for i in range(8)], round=3)
    report = RunReport(outcomes=[NodeOutcome(n, n, "stuck", evidence="x" * 300) for n in names] + [NodeOutcome("root", "root", "stuck", evidence="y")])
    graph, root, dev = build_plain_graph(tmp_path, names=())
    result = ProveResult(
        report=report, sentinels=SentinelReport(), graph=graph, root=root,
        decomposition=DecompositionResult(proposal=plan, model="m"),
        design_rounds=[DecompositionResult(proposal=plan, model="m", round=2), rejected],
        integration_detail="13 open", record_dir=tmp_path,
    )
    lines = result.render().splitlines()
    assert len(lines) <= 24, "\n".join(lines)
    assert lines[0] == "decomposer: m -- plan: 12 obligation(s)"
    assert lines[1] == "design revision 2: plan: 12 obligation(s)"
    assert lines[2].startswith("design revision 3: decomposition rejected:") and "(+5 more)" in lines[2]
    assert max(len(x) for x in lines if not x.startswith(("records:", "solution:"))) <= 140
    graph.close()


# ------------------------------------------------------------------ adversarial CLI workers (real processes)

SCRIPTS = {
    "hang": "sleep 30",
    "proof_then_fail": "printf 'intros H. exact H.' > proof.v; echo oops >&2; exit 1",
    "malformed": "echo '{not json' > answer.json",
    "binary_junk": "printf '\\xff\\xfe{\"status\":\"qed\"}' > answer.json",
    "exit_no_answer": "echo 'Failed to authenticate' >&2; exit 1",
    "contested": "echo '{\"status\":\"contested\",\"evidence\":\"the statement is false\"}' > answer.json",
    "list_proof": "echo '{\"status\":\"qed\",\"proof\":[\"exact I.\"]}' > answer.json",
    "wrapped": "echo '{\"status\":\"qed\",\"proof\":\"Proof. intros H. exact H. Qed.\"}' > answer.json",
    "edited_scratch": "sed -i 's/^admit\\.$/intros H. (* half *)/' Plain.v; sleep 30",
    "gate_fail_twice": f"echo '{{\"status\":\"qed\",\"proof\":\"{WRONG_PROOF}\"}}' > answer.json",
}


class ScriptRunner(CLIRunner):
    """A real ``bash`` worker per node, chosen by node name."""

    def __init__(self) -> None:
        super().__init__(argv=["bash", "-c", "true"], name="script", binary="bash", stream="text")

    async def run_node(self, node: NodePayload) -> NodeResult:
        clone = copy.copy(self)
        clone.argv = ["bash", "-c", SCRIPTS.get(node.name, "true")]
        return await run_cli(clone, node)


def test_adversarial_cli_workers_all_terminate_in_the_four_shapes(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=tuple(SCRIPTS))
    rec = Recorder(tmp_path / "rec", run_id="run")
    s = _sched(graph, dev, ScriptRunner(), tmp_path, node_seconds=1.0, max_attempts=2, recorder=rec, concurrency=16)
    started = time.perf_counter()
    report = asyncio.run(asyncio.wait_for(s.run(), timeout=60))
    assert time.perf_counter() - started < 20
    by = {o.name: o for o in report.outcomes}
    assert {o.status for o in report.outcomes} <= {"qed", "stuck", "contested", "error"}
    assert not [n.name for n in graph.nodes() if n.proof_status == "claimed"]
    assert all(r["finished"] is not None for n in graph.nodes() for r in graph.attempts_for(n.id))
    assert by["hang"].status == "stuck" and by["hang"].attempts == 2 and "deadline" in by["hang"].evidence
    assert by["proof_then_fail"].status == "qed" and graph.by_name("proof_then_fail").body == "intros H. exact H."
    assert by["wrapped"].status == "qed"
    assert by["malformed"].status == "stuck" and "malformed answer.json" in by["malformed"].evidence
    assert by["binary_junk"].status == "stuck" and by["list_proof"].status == "stuck"
    assert by["exit_no_answer"].status == "error" and by["exit_no_answer"].attempts == 1
    assert by["contested"].status == "contested" and graph.by_name("contested").proof_status == "contested"
    assert by["edited_scratch"].status == "stuck" and "recovered a 1-line partial proof" in by["edited_scratch"].evidence
    assert by["gate_fail_twice"].status == "stuck" and by["gate_fail_twice"].attempts == 2
    dirs = [p for p in (tmp_path / "work").rglob("a*") if p.is_dir()]
    assert len(dirs) == report.dispatched == len(list((tmp_path / "rec" / "run").iterdir()))
    assert len(report.render().splitlines()) <= 24
    graph.close()


@needs_rocq
def test_the_real_gate_rejects_a_body_that_aborts_and_declares(tmp_path):
    from pcp.orch.gate import Gate

    dev_path, _ = write_plain(tmp_path, plan=None)
    dev = Development(dev_path)
    spec = NodeSpec("c1", "Lemma c1 (P : Prop) : P -> P.", "intros H. Abort. Lemma evil : False. admit. Qed.")
    result = Gate(dev).run("root", [spec], target="c1", truncate=True, stub_prefix=True)
    assert not result.ok and any(not c.ok and not c.advisory for c in result.checks)
    assert all(c.name != "compiles (coqc)" or c.detail.startswith("skipped") for c in result.checks), "refused before any compile"


# ------------------------------------------------------------------ pcp check / report / serve


def _pcp(*args: str, cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, "-m", "pcp.cli.main", *args], cwd=str(cwd), capture_output=True, text=True, check=False)


def test_pcp_check_reports_a_missing_body_or_development_without_a_traceback(tmp_path):
    dev_path, _ = write_plain(tmp_path, plan=None)
    packet = tmp_path / "packet"
    packet.mkdir()
    meta = {"target": "root", "anchor": "root", "file": str(dev_path), "statement": "Lemma root (P Q : Prop) : P -> Q -> P.", "siblings": [], "scratch": "Plain.v"}
    (packet / "pcp-node.json").write_text(json.dumps(meta), encoding="utf-8")
    missing = _pcp("check", "--body", str(tmp_path / "nope.v"), cwd=packet)
    assert missing.returncode == 2 and "no such body file" in missing.stderr and "Traceback" not in missing.stderr
    meta["file"] = str(tmp_path / "gone" / "Plain.v")
    (packet / "pcp-node.json").write_text(json.dumps(meta), encoding="utf-8")
    gone = _pcp("check", "--body", str(dev_path), cwd=packet)
    assert gone.returncode == 2 and "is gone" in gone.stderr and "Traceback" not in gone.stderr


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

    from pcp.dash.serve import Handler

    handler = type("BoundHandler", (Handler,), {"graph_path": tmp_path / "graph.db"})
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


# ------------------------------------------------------------------ rwcas_design: contract, staging, sandbox


@needs_rocq
def test_rwcas_design_contract_import_and_frozen_result(tmp_path, bench_dir):
    corpus = tmp_path / "rwcas_design"
    shutil.copytree(bench_dir / "rwcas_design", corpus)
    contract = freeze_target(DesignContract.from_corpus(corpus), "write_spec")
    assert {"is_rwcas", "rwcasG", "value"} == set(contract.mutable) and "write_spec" in contract.results
    dev = Development(corpus / "Rwcas.v")
    graph = Graph(tmp_path / "g.db")
    root = graph.add_node(Node(id=node_id("write_spec"), name="write_spec", statement=dev.require_block("write_spec").statement, rank="root", statement_status="frozen"))
    cfg = ProveConfig(file=corpus / "Rwcas.v", target="write_spec", graph_path=tmp_path / "g.db", workroot=tmp_path / "w", run_lock=False)
    design = parse_proposal(json.dumps({
        "imports": ["From iris.base_logic.lib Require Import ghost_var."],
        "definitions": [
            {"name": "rwcasG", "text": "Class rwcasG Σ := {\n  rwcas_heapGS :: heapGS Σ;\n  rwcas_ghost_varG :: ghost_varG Σ Z;\n}."},
            {"name": "value", "text": "Definition value (γ : gname) (n : Z) : iProp Σ := ghost_var γ (1/2) n."},
            {"name": "rwcas_inv", "text": "Definition rwcas_inv (γ : gname) (l : loc) : iProp Σ := (∃ n : Z, l ↦ #n ∗ ghost_var γ (1/2) n)%I."},
            {"name": "is_rwcas", "text": "Definition is_rwcas (γ : gname) (v : val) : iProp Σ := (∃ l : loc, ⌜v = #l⌝ ∗ inv rwcasN (rwcas_inv γ l))%I."},
        ],
        "children": [{"name": "rwcas_value_agree", "statement": "Lemma rwcas_value_agree (γ : gname) (n m : Z) : value γ n -∗ value γ m -∗ ⌜n = m⌝."}],
    }))
    designed = apply_design(cfg, graph, dev, root, design, contract=contract, round_no=1, workroot=tmp_path / "w")
    text = designed.source
    assert "ghost_var." in "\n".join(text.splitlines()[:5]) and text.index("Definition rwcas_inv") < text.index("Definition is_rwcas")
    assert graph.get_meta("designed_file") == str(designed.path)
    for name, bad_text in (("rwcasN", 'Definition rwcasN : namespace := N .@ "other".'), ("write_spec", "Definition write_spec : Prop.")):
        bad = parse_proposal(json.dumps({"definitions": [{"name": name, "text": bad_text}], "children": [{"name": "c", "statement": "Lemma c : True."}]}))
        with pytest.raises(DesignViolatesContract, match=f"{name}: changed"):
            apply_design(cfg, graph, dev, root, bad, contract=contract, round_no=2, workroot=tmp_path / "w")
    graph.close()


def test_spec_only_staging_binds_only_the_staged_directory_into_the_sandbox(tmp_path, bench_dir):
    corpus = tmp_path / "rwcas_design"
    shutil.copytree(bench_dir / "rwcas_design", corpus)
    cfg = ProveConfig(file=corpus / "Rwcas.v", target="write_spec", graph_path=tmp_path / "g.db", workroot=tmp_path / "w", brief="spec-only", run_lock=False)
    staged = stage_spec_only(cfg, node_id("write_spec"), contract=DesignContract.from_corpus(corpus))
    assert sorted(p.name for p in staged.path.parent.iterdir()) == ["Rwcas.v", "_CoqProject", "design.json"]
    assert set(json.loads((staged.path.parent / "design.json").read_text())) == {"mutable", "results", "mutable_lemmas", "allow_additions", "allow_imports", "frozen_names"}
    from pcp.orch.runners import sandbox as sb

    if not sb.available():
        pytest.skip("no bubblewrap")
    box = sb.Sandbox.for_benchmark(ROOT, reference=tmp_path / "ref", corpus_dir=staged.path.parent, provider="anthropic", root=tmp_path / "stage")
    box = dataclasses.replace(box, refresh_credentials=False, clearenv=True)
    argv = box.wrap(["claude", "-p"], workdir=tmp_path / "w" / "n" / "a1", node_file_dir=staged.path.parent)
    joined = " ".join(argv)
    assert str(corpus) not in joined and str(bench_dir) not in joined and str(staged.path.parent) in joined
    binds = [argv[i + 1] for i, a in enumerate(argv) if a in ("--ro-bind", "--bind")]
    assert not [b for b in binds if (Path(b) / "DESIGN.md").exists() or Path(b).name == "DESIGN.md"]
    masked = [argv[i + 1] for i, a in enumerate(argv) if a == "--tmpfs"]
    assert str(ROOT / "eval") in masked and str(ROOT / ".pcp") in masked


def test_usage_errors_from_the_body_argument_are_usage_errors():
    from pcp.cli.common import read_body_arg

    with pytest.raises(UsageError, match="no such body file"):
        read_body_arg(Path("/nonexistent/body.v"))
