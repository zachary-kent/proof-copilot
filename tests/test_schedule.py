"""pcp.orch.schedule: whole-frontier dispatch, isolation, retry, attempt budgets."""

from __future__ import annotations

import asyncio
import json
import time
from pathlib import Path

import pytest

from pcp.orch.model import Node, node_id
from pcp.orch.protocol import NodePayload, NodeResult
from pcp.orch.runners.mock import WRONG_PROOF, MockRunner
from pcp.orch.schedule import NodeOutcome, RunReport, Scheduler, attempts_spent, failure_evidence, siblings_of
from tests._orch_fixtures import ANSWERS, FakeGate, build_plain_graph


def scheduler(graph, dev, runner, tmp_path, **kw) -> Scheduler:
    kw.setdefault("gate", FakeGate())
    kw.setdefault("workroot", tmp_path / "work")
    kw.setdefault("node_seconds", 60)
    return Scheduler(graph, dev, runner, anchor="root", **kw)


class SlowRunner(MockRunner):
    """Records when each node starts, so parallelism is observable."""

    def __init__(self, *a, **kw):
        super().__init__(*a, **kw)
        self.starts: dict[str, float] = {}
        self.ends: dict[str, float] = {}

    async def run_node(self, node: NodePayload) -> NodeResult:
        self.starts[node.name] = time.perf_counter()
        result = await super().run_node(node)
        self.ends[node.name] = time.perf_counter()
        return result


def test_the_whole_frontier_dispatches_at_once(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path)
    runner = SlowRunner(dict(ANSWERS), delay_s=0.3)
    report = asyncio.run(scheduler(graph, dev, runner, tmp_path).run())
    assert {o.status for o in report.outcomes} == {"qed"} and len(report.outcomes) == 3
    assert max(runner.starts.values()) - min(runner.starts.values()) < 0.25, "the three nodes did not start together"
    assert report.dispatched == 3 and report.gate_failures == 0
    assert graph.summary() == {"gated": 3}
    graph.close()


def test_a_raising_runner_isolates_one_node_and_the_others_finish(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path)
    runner = MockRunner(dict(ANSWERS), raise_for={"c1"})
    report = asyncio.run(scheduler(graph, dev, runner, tmp_path).run())
    by_name = {o.name: o for o in report.outcomes}
    assert by_name["c1"].status == "error" and "scripted crash" in by_name["c1"].evidence
    assert "Traceback" in by_name["c1"].evidence
    assert by_name["c2"].status == "qed" and by_name["root"].status == "qed"
    assert graph.by_name("c1").proof_status == "stuck", "no node is left claimed"
    rows = graph.attempts_for(node_id("c1"))
    assert rows and rows[-1]["status"] == "error" and rows[-1]["finished"] is not None
    graph.close()


class ErrorRunner:
    name = "erroring"

    def __init__(self):
        self.calls = 0

    def available(self):
        return True

    async def run_node(self, node):
        self.calls += 1
        return NodeResult(status="error", evidence="claude is not on PATH or could not be started")


def test_error_results_are_not_retried(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    runner = ErrorRunner()
    report = asyncio.run(scheduler(graph, dev, runner, tmp_path, max_attempts=3).run())
    assert runner.calls == 2, "one attempt per node, no retry for an infrastructure error"
    assert all(o.status == "error" and o.attempts == 1 for o in report.outcomes)
    assert graph.by_name("c1").proof_status == "stuck"
    assert "not on PATH" in graph.by_name("c1").evidence
    assert "error" in report.render()
    graph.close()


def test_a_gate_failed_qed_retries_with_the_previous_body_in_the_packet(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    seen: list[NodePayload] = []
    runner = MockRunner(dict(ANSWERS), fail_first={"c1"}, on_dispatch=seen.append)
    gate = FakeGate()
    report = asyncio.run(scheduler(graph, dev, runner, tmp_path, gate=gate).run())
    c1 = next(o for o in report.outcomes if o.name == "c1")
    assert c1.status == "qed" and c1.attempts == 2
    assert report.dispatched == 3 and report.gate_failures == 1
    attempts = [p for p in seen if p.name == "c1"]
    assert [p.attempt for p in attempts] == [1, 2]
    assert not attempts[0].evidence and "gate: FAIL" in attempts[1].evidence
    retry = attempts[1].workdir
    assert retry != attempts[0].workdir, "every attempt gets a fresh directory"
    task = (retry / "TASK.md").read_text()
    assert "## Your previous attempt's proof (partial)" in task and WRONG_PROOF in task
    assert WRONG_PROOF in (retry / dev.path.name).read_text()
    assert json.loads((retry / "pcp-node.json").read_text())["attempt"] == 2
    graph.close()


def test_the_attempt_budget_is_bounded_across_runs(tmp_path):
    from pcp.orch.prove.resume import reopen_incomplete

    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    runner = MockRunner({})  # never answers: every attempt is stuck
    first = asyncio.run(scheduler(graph, dev, runner, tmp_path, max_attempts=2).run())
    assert {o.attempts for o in first.outcomes} == {2}
    assert attempts_spent(graph, graph.by_name("c1")) == 2
    # A re-run with the same budget buys nothing: the node is not even reopened.
    assert reopen_incomplete(graph, max_attempts=2) == []
    second = asyncio.run(scheduler(graph, dev, runner, tmp_path, max_attempts=2).run())
    assert second.outcomes == [] and second.dispatched == 0
    # A raised budget buys exactly the difference.
    assert set(reopen_incomplete(graph, max_attempts=3)) == {"c1", "root"}
    third = asyncio.run(scheduler(graph, dev, runner, tmp_path, max_attempts=3).run())
    assert {o.attempts for o in third.outcomes} == {1} and third.dispatched == 2
    assert attempts_spent(graph, graph.by_name("c1")) == 3
    graph.close()


def test_a_node_with_no_attempts_left_is_reported_stuck_without_dispatch(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    c1 = graph.by_name("c1")
    for _ in range(2):
        graph.set_proof_status(c1.id, "claimed")
        a = graph.start_attempt(c1.id, runner="mock")
        graph.finish_attempt(a, status="stuck", evidence="x")
        graph.set_proof_status(c1.id, "open")
    dispatched: list[str] = []
    runner = MockRunner(dict(ANSWERS), on_dispatch=lambda p: dispatched.append(p.name))
    report = asyncio.run(scheduler(graph, dev, runner, tmp_path, max_attempts=2).run())
    out = next(o for o in report.outcomes if o.name == "c1")
    assert out.status == "stuck" and "attempt budget spent (2)" in out.evidence and "--attempts" in out.evidence
    assert "c1" not in dispatched and "root" in dispatched
    assert graph.by_name("c1").proof_status == "stuck"
    graph.close()


def test_node_seconds_reaches_the_payload_not_the_run_budget(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    seen: list[NodePayload] = []
    runner = MockRunner(dict(ANSWERS), on_dispatch=seen.append)
    asyncio.run(scheduler(graph, dev, runner, tmp_path, node_seconds=123).run())
    assert {p.budget_seconds for p in seen} == {123.0}
    graph.close()


def test_non_mockable_nodes_run_serially_first(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1", "c2", "c3"))
    graph.update(node_id("c1"), mockable=False)
    runner = SlowRunner(dict(ANSWERS) | {"c3": "intros H. exact H."}, delay_s=0.2)
    report = asyncio.run(scheduler(graph, dev, runner, tmp_path).run())
    assert {o.status for o in report.outcomes} == {"qed"}
    assert runner.ends["c1"] <= min(runner.starts[n] for n in ("c2", "c3", "root"))
    graph.close()


def test_an_unproved_non_mockable_node_blocks_its_dependents_rather_than_crashing(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1", "c2"))
    graph.update(node_id("c1"), mockable=False)
    runner = MockRunner({"c2": ANSWERS["c2"], "root": ANSWERS["root"]})  # c1 never answers
    report = asyncio.run(scheduler(graph, dev, runner, tmp_path).run())
    by_name = {o.name: o for o in report.outcomes}
    assert by_name["c1"].status == "stuck"
    assert by_name["c2"].status == "stuck" and "blocked: non-mockable" in by_name["c2"].evidence
    assert by_name["c2"].attempts == 0
    graph.close()


def test_a_gate_that_cannot_run_is_not_charged_and_leaves_the_node_open(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    runner = MockRunner(dict(ANSWERS))
    report = asyncio.run(scheduler(graph, dev, runner, tmp_path, gate=FakeGate(infrastructure=True)).run())
    out = next(o for o in report.outcomes if o.name == "c1")
    assert out.status == "error" and "not charged" in out.evidence
    assert graph.by_name("c1").proof_status == "open"
    assert attempts_spent(graph, graph.by_name("c1")) == 0
    assert graph.attempts_for(node_id("c1"))[-1]["status"] == "error"
    graph.close()


class EmptyQed:
    name = "empty"

    def available(self):
        return True

    async def run_node(self, node):
        return NodeResult(status="qed", proof="")


def test_a_qed_with_an_empty_proof_is_a_stuck_attempt(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    gate = FakeGate()
    report = asyncio.run(scheduler(graph, dev, EmptyQed(), tmp_path, gate=gate, max_attempts=1).run())
    assert all(o.status == "stuck" for o in report.outcomes)
    assert gate.calls == [], "nothing to gate"
    assert {r["status"] for r in graph.attempts_for(node_id("c1"))} == {"stuck"}
    assert "empty proof body" in graph.by_name("c1").evidence
    graph.close()


def test_contested_is_terminal(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    runner = MockRunner(dict(ANSWERS), statuses={"c1": "contested"})
    report = asyncio.run(scheduler(graph, dev, runner, tmp_path, max_attempts=3).run())
    out = next(o for o in report.outcomes if o.name == "c1")
    assert out.status == "contested" and out.attempts == 1
    assert graph.by_name("c1").proof_status == "contested"
    graph.close()


def test_siblings_never_carry_a_body_while_unproved(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path)
    graph.set_proof_status(node_id("c1"), "claimed")
    graph.record_proof(node_id("c1"), "exact I.")
    specs = {s.name: s for s in siblings_of(graph, dev)}
    assert specs["c1"].body == "exact I." and specs["c2"].body is None
    assert "root" not in specs and "helper" not in specs, "the root and in-file lemmas are not injected"
    graph.update(node_id("c1"), proof_status="open")
    assert siblings_of(graph, dev)[0].body is None, "reopening clears the body"
    graph.close()


def test_the_plan_preamble_reaches_the_packet_and_the_gate(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    seen: list[NodePayload] = []
    runner = MockRunner(dict(ANSWERS), on_dispatch=seen.append)
    gate = FakeGate()
    asyncio.run(scheduler(graph, dev, runner, tmp_path, gate=gate, preamble="Require Import Stdlib.Lists.List.").run())
    scratch = next(p for p in seen if p.name == "c1").workdir / dev.path.name
    assert "Require Import Stdlib.Lists.List." in scratch.read_text()
    meta = json.loads((scratch.parent / "pcp-node.json").read_text())
    assert meta["preamble"] == "Require Import Stdlib.Lists.List."
    assert all(c["extra_preamble"] == "Require Import Stdlib.Lists.List." for c in gate.calls)
    graph.close()


def test_failure_evidence_keeps_the_gates_words_after_a_long_complaint():
    result = NodeResult(status="stuck", evidence="x" * 5000)
    from pcp.orch.gate import CHECK_COMPILES, Check, GateResult

    gate = GateResult(ok=False, checks=[Check(CHECK_COMPILES, False, "Error: boom")])
    text = failure_evidence(result, gate)
    assert "gate: FAIL" in text[:4000] and len(text) <= 6000


def test_run_report_render_and_json_shapes():
    report = RunReport(
        outcomes=[
            NodeOutcome("a", "a", "qed", attempts=1, elapsed_s=2.0),
            NodeOutcome("b", "b", "stuck", evidence="it broke " * 30),
            NodeOutcome("c", "c", "contested", evidence="wrong"),
        ],
        elapsed_s=23.4, dispatched=4,
    )
    lines = report.render().splitlines()
    assert lines[0] == "1 qed · 1 stuck · 1 contested   (23s, 4 dispatches)"
    assert lines[1].startswith("  qed       a  (2s, 1 attempt(s))")
    assert lines[2].startswith("  stuck     b  ") and len(lines[2]) <= 120
    assert lines[3].startswith("  contested c  wrong")
    assert set(report.to_json()["outcomes"][0]) == {"node", "name", "status", "attempts", "elapsed_s", "evidence", "requests", "amendments", "review"}
    merged = RunReport.combined([report, RunReport(outcomes=[NodeOutcome("b", "b", "qed", attempts=1)], dispatched=1)])
    assert {o.name: o.status for o in merged.outcomes} == {"a": "qed", "b": "qed", "c": "contested"}
    assert merged.dispatched == 5


class Crash(BaseException):
    """A simulated process death (not an Exception: isolation must let it through)."""


def test_a_base_exception_aborts_the_run_like_a_crash(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))

    def boom(p: NodePayload) -> None:
        if p.name == "root":
            raise Crash()

    runner = MockRunner(dict(ANSWERS), on_dispatch=boom)
    with pytest.raises(Crash):
        asyncio.run(scheduler(graph, dev, runner, tmp_path).run())
    assert graph.by_name("root").proof_status == "claimed", "a crash leaves the in-flight node claimed; resume handles it"
    graph.close()


def test_scheduler_rejects_nothing_it_is_given(tmp_path):
    """Every documented knob has exactly one consumer: the constructor stores them all."""
    graph, root, dev = build_plain_graph(tmp_path)
    s = scheduler(graph, dev, MockRunner({}), tmp_path, concurrency=7, max_attempts=4, skills=["s"], state_tools=["proof_open"],
                  library=[Path("/x")], check_command="pcp check", corpus="lbl", design_brief="brief", round=2)
    assert s.concurrency == 7 and s.max_attempts == 4 and s.round == 2 and s.context.design == "brief"
    graph.close()


def test_node_ids_are_slugs_and_collision_free():
    assert node_id("foo") == "foo"
    assert node_id("foo.bar") != node_id("foo_bar")
    Node(id=node_id("x"), name="x", statement="Lemma x : True.")


def test_a_node_is_parked_for_review_after_n_failed_attempts_with_budget_left(tmp_path):
    from pcp.orch.prove.resume import reopen_incomplete

    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    runner = MockRunner({})  # every attempt is stuck
    report = asyncio.run(scheduler(graph, dev, runner, tmp_path, max_attempts=4, review_after=2).run())
    c1 = next(o for o in report.outcomes if o.name == "c1")
    assert c1.status == "stuck" and c1.review and c1.attempts == 2
    assert attempts_spent(graph, graph.by_name("c1")) == 2 and graph.by_name("c1").proof_status == "stuck"
    assert [e["kind"] for e in graph.events_since(0, limit=5000)].count("node.for_review") >= 1
    assert "[for review]" in c1.one_line() and c1.to_json()["review"] is True
    # Reopened without a verdict (a crash, a run without an approver): parked again at
    # once, no attempt spent -- the budget waits for the review.
    assert "c1" in reopen_incomplete(graph, max_attempts=4)
    again = asyncio.run(scheduler(graph, dev, runner, tmp_path, max_attempts=4, review_after=2).run())
    c1_again = next(o for o in again.outcomes if o.name == "c1")
    assert c1_again.review and c1_again.attempts == 0 and attempts_spent(graph, graph.by_name("c1")) == 2
    # Once the epoch has had its verdict, the remaining budget is spent normally.
    reopen_incomplete(graph, max_attempts=4)
    spent = asyncio.run(scheduler(graph, dev, runner, tmp_path, max_attempts=4, review_after=2, reviewed=lambda n: True).run())
    c1_spent = next(o for o in spent.outcomes if o.name == "c1")
    assert not c1_spent.review and c1_spent.attempts == 2 and attempts_spent(graph, graph.by_name("c1")) == 4
    graph.close()


def test_review_after_zero_is_the_old_behaviour(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    report = asyncio.run(scheduler(graph, dev, MockRunner({}), tmp_path, max_attempts=3, review_after=0).run())
    c1 = next(o for o in report.outcomes if o.name == "c1")
    assert not c1.review and c1.attempts == 3
    graph.close()


def test_review_is_reached_at_the_default_budget(tmp_path):
    """Review finding: with --attempts 2 --review-after 2 (both defaults) the check only
    ran before an attempt, so the second failure ended the loop unreviewed."""
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    report = asyncio.run(scheduler(graph, dev, MockRunner({}), tmp_path, max_attempts=2, review_after=2).run())
    c1 = next(o for o in report.outcomes if o.name == "c1")
    assert c1.review and c1.attempts == 2 and attempts_spent(graph, graph.by_name("c1")) == 2
    # a resumed node whose budget is already spent is offered for review too, not just parked
    from pcp.orch.prove.resume import reopen_incomplete
    assert reopen_incomplete(graph, max_attempts=2) == []
    graph.set_proof_status(node_id("c1"), "open")
    again = asyncio.run(scheduler(graph, dev, MockRunner({}), tmp_path, max_attempts=2, review_after=2).run())
    c1_again = next(o for o in again.outcomes if o.name == "c1")
    assert c1_again.review and c1_again.attempts == 0
    graph.close()


def test_a_node_reopened_by_an_amendment_retries_before_any_review(tmp_path):
    from pcp.orch.protocol import AMENDED_MARKER

    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    asyncio.run(scheduler(graph, dev, MockRunner({}), tmp_path, max_attempts=4, review_after=2).run())  # 2 failures, parked for review
    graph.set_proof_status(node_id("c1"), "open", evidence=f"{AMENDED_MARKER} helper now carries ⌜n = 0⌝")
    again = asyncio.run(scheduler(graph, dev, MockRunner({}), tmp_path, max_attempts=4, review_after=2).run())
    c1 = next(o for o in again.outcomes if o.name == "c1")
    assert c1.attempts == 1 and c1.review, "one retry against the amended design, then the review reads that failure"
    graph.close()
