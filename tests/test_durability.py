"""Durability of the run (wave 5): outage pause, in-flight recovery, supervision,
ladder resume.

Each test names the scenario it pins.  Sleeps and the clock inside
:mod:`pcp.orch.outage` are replaced by a fake so a 12-hour pause takes milliseconds;
the supervisor tests run real processes because a real ``os._exit`` is the thing
being survived.
"""

from __future__ import annotations

import asyncio
import json
import os
import shlex
import signal
import subprocess
import sys
import time
from pathlib import Path

import pytest

from pcp.cli.main import main as pcp_main
from pcp.errors import LockedError
from pcp.orch import outage
from pcp.orch.contract import DesignContract
from pcp.orch.decomposer import Decomposer
from pcp.orch.graph import Graph
from pcp.orch.model import Budget, node_id
from pcp.orch.outage import (
    BACKOFF_S,
    Outage,
    PausePolicy,
    ProviderPause,
    detect_outage,
    parse_reset_time,
    provider_probe,
    wait_for_provider,
)
from pcp.orch.packet import build_packet
from pcp.orch.protocol import NodePayload, NodeResult
from pcp.orch.prove import ProveConfig, lock_path, prove
from pcp.orch.prove.design import DesignDriver, design_rounds_used
from pcp.orch.prove.resume import INTERRUPTED_NOTE, RESUMED_NOTE, reopen_incomplete, resume_incomplete
from pcp.orch.record import Recorder
from pcp.orch.runners.cli import CLIRunner
from pcp.orch.runners.mock import MockRunner
from pcp.orch.schedule import MAX_OUTAGE_RETRIES, Scheduler, attempts_spent, last_partial, siblings_of
from pcp.orch.supervise import OUTCOME_FILE, PID_FILE, Supervisor, read_outcome, strip_flags
from pcp.util.locks import RunLock
from tests._orch_fixtures import ANSWERS, FakeGate, build_plain_graph, plain_cfg, write_plain
from tests.conftest import needs_rocq

ROOT = Path(__file__).resolve().parents[1]

SESSION_LIMIT = "You've hit your session limit · resets 9:50pm (America/New_York)"
REVOKED = "401 OAuth access token has been revoked"
FAILED_AUTH = "Failed to authenticate"
CEILING = "Claude's response exceeded the 64000 output token maximum"


# ------------------------------------------------------------------ fixtures


class FakeClock:
    """Sleeps advance a fake clock instead of waiting."""

    def __init__(self, start: float = 1_700_000_000.0) -> None:
        self.now = start
        self.sleeps: list[float] = []

    async def sleep(self, seconds: float) -> None:
        self.sleeps.append(seconds)
        self.now += seconds
        await asyncio.sleep(0)  # yield, as a real sleep would

    def time(self) -> float:
        return self.now


@pytest.fixture
def clock(monkeypatch) -> FakeClock:
    c = FakeClock()
    monkeypatch.setattr(outage, "_sleep", c.sleep)
    monkeypatch.setattr(outage, "_now", c.time)
    return c


def scripted_probe(*answers: bool | None):
    """A probe answering from a list (the last answer repeats), counting its calls."""
    calls: list[int] = []

    async def probe() -> bool | None:
        calls.append(1)
        return answers[min(len(calls) - 1, len(answers) - 1)]

    probe.calls = calls  # type: ignore[attr-defined]
    return probe


class OutageRunner(MockRunner):
    """Answers like the mock, after ``outages`` calls that fail underneath the worker."""

    def __init__(self, *a, outages: int = 0, detail: str = FAILED_AUTH, **kw) -> None:
        super().__init__(*a, **kw)
        self.outages = outages
        self.detail = detail
        self.calls = 0

    async def run_node(self, node: NodePayload) -> NodeResult:
        self.calls += 1
        if self.outages > 0:
            self.outages -= 1
            return NodeResult(status="error", evidence=f"claude exited with status 1 and wrote no answer: {self.detail}", exit_code=1)
        return await super().run_node(node)


def _sched(graph, dev, runner, tmp_path, **kw) -> Scheduler:
    kw.setdefault("gate", FakeGate())
    kw.setdefault("workroot", tmp_path / "work")
    kw.setdefault("node_seconds", 60)
    return Scheduler(graph, dev, runner, anchor="root", **kw)


def _kinds(graph: Graph) -> list[str]:
    return [e["kind"] for e in graph.events_since()]


def _error(evidence: str, **kw) -> NodeResult:
    return NodeResult(status="error", evidence=evidence, exit_code=kw.pop("exit_code", 1), **kw)


# ------------------------------------------------------------------ detect_outage


@pytest.mark.parametrize(
    ("evidence", "kind", "retryable"),
    [
        (SESSION_LIMIT, "rate_limited", True),
        (REVOKED, "unauthenticated", True),
        (FAILED_AUTH, "unauthenticated", True),
        ("claude exited with status 1 and wrote no answer: Please run /login", "unauthenticated", True),
        ("the runner ended with error_during_execution: API Error: 429 rate limit exceeded", "rate_limited", True),
        ("API Error: 529 overloaded", "provider_unreachable", True),
        ("fetch failed: getaddrinfo ENOTFOUND api.anthropic.com", "provider_unreachable", True),
        ("the runner ended with error: connection refused", "provider_unreachable", True),
        ("HTTP 503 Service Unavailable", "provider_unreachable", True),
        ("claude is not on PATH or could not be started (claude: [Errno 2] No such file or directory); install it", "cli_missing", False),
    ],
)
def test_detect_outage_recognises_each_kind(evidence, kind, retryable):
    found = detect_outage(_error(evidence))
    assert found is not None, evidence
    assert found.kind == kind and found.retryable is retryable
    assert found.detail and kind in found.describe()


def test_detect_outage_the_output_ceiling_is_not_an_outage():
    assert detect_outage(_error(f"the runner ended with error_during_execution: {CEILING}")) is None


@pytest.mark.parametrize(
    "result",
    [
        NodeResult(status="stuck", evidence="Error: Unable to unify a with b"),
        _error('File "Plain.v", line 401, characters 3-10: Error: Unable to unify a with b'),
        NodeResult(status="stuck", evidence="the worker produced no answer.json, no proof.v and no fenced proof block"),
        NodeResult(status="stuck", evidence=FAILED_AUTH),  # a worker cannot claim an outage
        NodeResult(status="contested", evidence="401 OAuth access token has been revoked, says the statement"),
        _error("mock: scripted error for c1"),
        _error("the orchestrator failed while running this node: ValueError: boom"),
    ],
)
def test_detect_outage_negatives(result):
    assert detect_outage(result) is None


def test_detect_outage_reads_the_trace_and_the_exit_code():
    from_stderr = _error("claude exited with status 1 and wrote no answer: see below", trace={"stderr_lines": ["", FAILED_AUTH]})
    assert detect_outage(from_stderr).kind == "unauthenticated"
    from_detail = _error("the runner ended with error_during_execution", trace={"result_error": "error_during_execution", "result_detail": SESSION_LIMIT})
    found = detect_outage(from_detail)
    assert found.kind == "rate_limited" and found.resume_at is not None
    assert detect_outage(_error("bash: claude: command not found", exit_code=127)).kind == "cli_missing"
    assert detect_outage(_error("something odd happened", exit_code=127)).kind == "cli_missing"


def test_parse_reset_time_today_or_tomorrow_in_local_time():
    morning = time.mktime((2026, 9, 5, 8, 0, 0, 0, 0, -1))
    evening = time.mktime((2026, 9, 5, 22, 0, 0, 0, 0, -1))
    today = parse_reset_time(SESSION_LIMIT, now=morning)
    assert today is not None and time.localtime(today)[:5] == (2026, 9, 5, 21, 50)
    tomorrow = parse_reset_time(SESSION_LIMIT, now=evening)
    assert tomorrow is not None and time.localtime(tomorrow)[:5] == (2026, 9, 6, 21, 50)
    assert parse_reset_time("resets 12am", now=morning) is not None
    assert time.localtime(parse_reset_time("resets 12:30pm", now=morning))[3:5] == (12, 30)
    assert parse_reset_time("resets in 2h 15m", now=morning) == morning + 2 * 3600 + 15 * 60
    assert parse_reset_time("Error: Unable to unify", now=morning) is None
    found = detect_outage(_error(SESSION_LIMIT), now=morning)
    assert found is not None and found.resume_at == today
    assert Outage.from_json(found.to_json()) == found


# ------------------------------------------------------------------ wait_for_provider


def test_wait_for_provider_backs_off_30_60_120_300_until_the_probe_says_yes(clock):
    probe = scripted_probe(False, False, False, False, False, True)
    said: list[str] = []
    ok = asyncio.run(wait_for_provider(probe, outage=Outage("unauthenticated", REVOKED), max_wait_s=12 * 3600, on_wait=said.append))
    assert ok is True
    assert clock.sleeps == [*BACKOFF_S, 300.0], "the cap holds"
    assert len(probe.calls) == 6
    assert said[0].startswith("paused: unauthenticated -- run `claude` `/login`") and "probing again in 30 s" in said[0]
    assert "(waited 0 s of 12 h)" in said[0] and "probing again in 300 s" in said[-1]


def test_wait_for_provider_gives_up_when_max_wait_is_spent(clock):
    probe = scripted_probe(False)
    said: list[str] = []
    ok = asyncio.run(wait_for_provider(probe, outage=Outage("provider_unreachable", "connection refused"), max_wait_s=200, on_wait=said.append))
    assert ok is False
    assert sum(clock.sleeps) == 200 and clock.sleeps == [30, 60, 110], "the last sleep is clipped to what is left"
    assert said[-1].startswith("gave up waiting for the provider after 3 min")


def test_wait_for_provider_treats_an_unknown_probe_as_back_after_one_backoff(clock):
    probe = scripted_probe(None)
    ok = asyncio.run(wait_for_provider(probe, outage=Outage("unauthenticated", "x"), max_wait_s=3600, on_wait=lambda _: None))
    assert ok is True and clock.sleeps == [30.0] and len(probe.calls) == 2


def test_wait_for_provider_sleeps_until_the_window_resets_first(clock):
    resume_at = clock.now + 1000
    probe = scripted_probe(True)
    said: list[str] = []
    ok = asyncio.run(wait_for_provider(probe, outage=Outage("rate_limited", SESSION_LIMIT, resume_at=resume_at), max_wait_s=7200, on_wait=said.append))
    assert ok and clock.sleeps == [1000 + outage.RESET_GRACE_S] and len(probe.calls) == 1
    assert "sleeping 18 min until the window resets" in said[0] and "window resets at" in said[0]
    # A reset beyond the budget sleeps what is left, probes once, and gives up.
    clock.sleeps.clear()
    ok = asyncio.run(wait_for_provider(scripted_probe(False), outage=Outage("rate_limited", "x", resume_at=clock.now + 9000), max_wait_s=100, on_wait=said.append))
    assert ok is False and clock.sleeps == [100]


def test_wait_for_provider_a_raising_probe_is_an_unknown(clock):
    async def broken() -> bool | None:
        raise RuntimeError("probe exploded")

    said: list[str] = []
    ok = asyncio.run(wait_for_provider(broken, outage=Outage("unauthenticated", "x"), max_wait_s=3600, on_wait=said.append))
    assert ok is True and clock.sleeps == [30.0]
    assert any("probe exploded" in s for s in said)


def test_provider_probe_prefers_the_auth_check_then_claude_then_unknown(monkeypatch):
    codex = CLIRunner(argv=["codex", "exec"], name="codex", binary="codex", auth_check=("codex", "login", "status"))

    async def yes() -> bool | None:
        return True

    monkeypatch.setattr(codex, "authenticated", yes)
    assert asyncio.run(provider_probe(codex)()) is True

    claude = CLIRunner(argv=["claude", "-p"], name="claude:default", binary="claude", stream="claude")
    seen: list[dict] = []

    async def fake_claude_probe(**kw) -> bool | None:
        seen.append(kw)
        return False

    monkeypatch.setattr(outage, "claude_probe", fake_claude_probe)
    assert asyncio.run(provider_probe(claude)()) is False and seen[0]["binary"] == "claude"
    from pcp.orch.runners.sandbox import Sandbox, SandboxedRunner

    boxed = SandboxedRunner(claude, Sandbox(refresh_credentials=False))
    assert asyncio.run(provider_probe(boxed)()) is False, "a sandboxed runner probes through its inner runner, on the host"
    assert asyncio.run(provider_probe(MockRunner({}))()) is None


# ------------------------------------------------------------------ the scheduler pause


def test_scheduler_pauses_on_an_outage_and_redispatches_uncharged(tmp_path, clock, capsys):
    graph, root, dev = build_plain_graph(tmp_path)
    runner = OutageRunner(dict(ANSWERS), outages=2)
    probe = scripted_probe(False, True)
    rec = Recorder(tmp_path / "rec", run_id="run")
    s = _sched(graph, dev, runner, tmp_path, pause=PausePolicy(max_wait_s=12 * 3600), probe=probe, recorder=rec)
    report = asyncio.run(asyncio.wait_for(s.run(), timeout=30))
    assert {o.status for o in report.outcomes} == {"qed"} and len(report.outcomes) == 3
    assert "error" not in report.render()
    assert graph.summary() == {"gated": 3}
    assert all(attempts_spent(graph, n) == 1 for n in graph.nodes()), "outage rows are never charged"
    errors = [r for n in graph.nodes() for r in graph.attempts_for(n.id) if r["status"] == "error"]
    assert len(errors) == 2 and all(r["finished"] is not None for r in errors)
    assert runner.calls == 5, "two outages, then every node once"
    kinds = _kinds(graph)
    assert kinds.count("run.paused") == 1 and kinds.count("run.resumed") == 1
    assert kinds.count("run.pause_joined") == 1, "the second outage joined the pause"
    paused = next(e for e in graph.events_since() if e["kind"] == "run.paused")
    assert paused["payload"]["kind"] == "unauthenticated" and FAILED_AUTH in paused["payload"]["detail"]
    assert clock.sleeps == [30.0] and len(probe.calls) == 2
    log = (rec.root / "run.log").read_text(encoding="utf-8")
    assert "paused: unauthenticated" in log and "resumed after" in log
    assert "paused: unauthenticated" in capsys.readouterr().err
    graph.close()


def test_an_exhausted_pause_parks_the_nodes_stuck_with_the_outage_and_the_run_ends(tmp_path, clock):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    runner = OutageRunner(dict(ANSWERS), outages=99, detail=REVOKED)
    s = _sched(graph, dev, runner, tmp_path, pause=PausePolicy(max_wait_s=600), probe=scripted_probe(False))
    started = time.perf_counter()
    report = asyncio.run(asyncio.wait_for(s.run(), timeout=30))
    assert time.perf_counter() - started < 10, "the run wedged"
    assert {o.status for o in report.outcomes} == {"error"}
    assert all(o.evidence.startswith("provider outage: ") and "(waited 10 min)" in o.evidence for o in report.outcomes)
    assert all(REVOKED in o.evidence for o in report.outcomes)
    assert graph.summary() == {"stuck": 2}, "parked, never claimed"
    assert "error" in report.render()
    kinds = _kinds(graph)
    assert kinds.count("run.paused") == 1 and "run.pause_exhausted" in kinds and "run.resumed" not in kinds
    assert sum(clock.sleeps) == 600
    # Uncharged: a later run gets both nodes back with their full budget.
    assert set(reopen_incomplete(graph, max_attempts=2)) == {"c1", "root"}
    assert all(attempts_spent(graph, n) == 0 for n in graph.nodes())
    graph.close()


def test_pause_hours_zero_is_the_old_behaviour(tmp_path, clock):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    runner = OutageRunner(dict(ANSWERS), outages=99)
    s = _sched(graph, dev, runner, tmp_path, pause=PausePolicy.from_hours(0), probe=scripted_probe(True))
    report = asyncio.run(s.run())
    assert {o.status for o in report.outcomes} == {"error"} and runner.calls == 2
    assert graph.by_name("c1").proof_status == "stuck" and FAILED_AUTH in graph.by_name("c1").evidence
    assert "run.paused" not in _kinds(graph) and clock.sleeps == []
    assert s.pause is None and not PausePolicy.from_hours(0).active and PausePolicy.from_hours(12).max_wait_s == 12 * 3600
    graph.close()


def test_a_missing_cli_is_not_retryable_and_parks_as_before(tmp_path, clock):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    runner = OutageRunner(dict(ANSWERS), outages=99, detail="claude is not on PATH or could not be started")
    s = _sched(graph, dev, runner, tmp_path, pause=PausePolicy(), probe=scripted_probe(True))
    report = asyncio.run(s.run())
    assert {o.status for o in report.outcomes} == {"error"} and runner.calls == 2
    assert "run.paused" not in _kinds(graph)
    graph.close()


def test_a_flapping_provider_is_bounded_per_node(tmp_path, clock):
    """The probe says yes and the next attempt fails again: bounded, never a hot loop."""
    graph, root, dev = build_plain_graph(tmp_path, names=())
    runner = OutageRunner(dict(ANSWERS), outages=99)
    s = _sched(graph, dev, runner, tmp_path, pause=PausePolicy(max_wait_s=3600), probe=scripted_probe(True))
    report = asyncio.run(asyncio.wait_for(s.run(), timeout=30))
    assert [o.status for o in report.outcomes] == ["error"]
    assert runner.calls == MAX_OUTAGE_RETRIES + 1
    assert "consecutive attempts failed with a provider outage" in report.outcomes[0].evidence
    assert _kinds(graph).count("run.paused") == MAX_OUTAGE_RETRIES
    assert clock.sleeps == [30.0] * (MAX_OUTAGE_RETRIES - 1), "a second outage right after a resume backs off before probing"
    assert graph.by_name("root").proof_status == "stuck"
    graph.close()


def test_in_flight_attempts_continue_while_the_run_is_paused_and_new_dispatch_waits(tmp_path, clock):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1", "c2"))
    order: list[str] = []

    class Mixed(MockRunner):
        c1_calls = 0

        async def run_node(self, node: NodePayload) -> NodeResult:
            order.append(f"start:{node.name}:{node.attempt}")
            if node.name == "c1":
                self.c1_calls += 1
                if self.c1_calls == 1:
                    await asyncio.sleep(0.05)  # the outage lands while everyone else is in flight
                    return NodeResult(status="error", evidence=FAILED_AUTH, exit_code=1)
            await asyncio.sleep(0.3 if node.name == "c2" else 0.1)
            result = await super().run_node(node)
            order.append(f"end:{node.name}:{node.attempt}")
            return result

    async def slow_probe() -> bool | None:
        await asyncio.sleep(0.15)  # the provider takes a moment to come back
        return True

    pause = ProviderPause(PausePolicy(max_wait_s=3600), slow_probe, on_event=lambda k, p: order.append(k))
    runner = Mixed(dict(ANSWERS), fail_first={"root"})
    report = asyncio.run(asyncio.wait_for(_sched(graph, dev, runner, tmp_path, pause=pause).run(), timeout=30))
    assert {o.status for o in report.outcomes} == {"qed"}
    assert order.index("end:c2:1") > order.index("run.paused"), "the in-flight attempt ran on through the pause"
    # The root's gate-failed retry became due during the pause and waited for the resume.
    assert order.index("end:root:1") > order.index("run.paused")
    assert order.index("start:root:2") > order.index("run.resumed")
    assert [k for k in order if k.startswith("run.")] == ["run.paused", "run.resumed"]
    assert clock.sleeps == [], "the probe answered on its first call: no backoff"
    assert order.count("start:c1:1") == 2, "the re-dispatch is attempt 1 again: the outage was never charged"
    graph.close()


@needs_rocq
def test_canary_integrates_through_an_outage_pause(tmp_path, canary_dir, clock):
    from tests.test_canary import CANARY_ANSWERS

    cfg = ProveConfig(
        file=canary_dir / "Canary.v", target="canary_main", plan=canary_dir / "plan.v",
        graph_path=tmp_path / "graph.db", workroot=tmp_path / "work", node_seconds=180,
        budget=Budget(requests=50, seconds=1800), pause_hours=30, run_lock=False, record_root=tmp_path / "rec",
    )
    runner = OutageRunner(dict(CANARY_ANSWERS), outages=2, detail=SESSION_LIMIT)
    result = asyncio.run(prove(cfg, runner))
    assert result.integrated, result.render()
    paused = next(e for e in result.graph.events_since() if e["kind"] == "run.paused")
    assert paused["payload"]["kind"] == "rate_limited" and paused["payload"]["resume_at"] is not None
    assert clock.sleeps[0] >= outage.RESET_GRACE_S, "slept until the window reset before probing"
    assert "error" not in result.report.render()
    assert result.graph.summary() == {"integrated": 3}
    assert all(attempts_spent(result.graph, n) == 1 for n in result.graph.nodes())
    kinds = _kinds(result.graph)
    assert "run.paused" in kinds and "run.resumed" in kinds
    assert clock.sleeps, "a mock runner cannot be probed: one backoff step, then resume"
    log = (Path(result.record_dir) / "run.log").read_text(encoding="utf-8")
    assert "run.paused" in log and "run.resumed" in log
    result.close()


# ------------------------------------------------------------------ the decomposer pause


class OutageThenPlanRunner:
    name = "scripted-decomposer"

    def __init__(self, plan: str, outages: int = 1) -> None:
        self.plan, self.outages, self.calls = plan, outages, 0

    def available(self) -> bool:
        return True

    async def run_node(self, node):
        self.calls += 1
        if self.outages > 0:
            self.outages -= 1
            return NodeResult(status="error", evidence=REVOKED, exit_code=1)
        return NodeResult(status="qed", raw=self.plan, trace={"final_text": self.plan, "model": "scripted"})


PLAN = '{"children": [{"name": "c1", "statement": "Lemma c1 : True."}]}'


def test_decomposer_outage_pauses_and_retries_the_round_once_without_counting_it_twice(tmp_path, clock):
    graph, root, dev = build_plain_graph(tmp_path, names=())
    runner = OutageThenPlanRunner(PLAN)
    pause = ProviderPause(PausePolicy(max_wait_s=3600), scripted_probe(False, True), on_event=lambda k, p: graph.emit(k, root.id, **p))
    cfg = plain_cfg(tmp_path, decomposer_runner=runner, max_design_rounds=2, decomposer_seconds=5)
    driver = DesignDriver(cfg, graph, root, contract=DesignContract.everything_frozen(), pause=pause)
    asyncio.run(driver.initial(dev))
    assert runner.calls == 2 and driver.rounds_used == 1
    assert design_rounds_used(graph, root) == 1, "the retried round is the same round"
    rows = [r for r in graph.attempts_for(root.id) if r["role"] == "decomposer"]
    assert [r["status"] for r in rows] == ["error", "qed"] and {r["round"] for r in rows} == {1}
    assert all(r["finished"] is not None for r in rows)
    kinds = _kinds(graph)
    assert "decomposer.outage" in kinds and "run.paused" in kinds and "run.resumed" in kinds
    assert graph.by_name("c1") is not None
    graph.close()


def test_decomposer_outage_without_a_pause_is_infrastructure_as_before(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=())
    runner = OutageThenPlanRunner(PLAN)
    out = asyncio.run(Decomposer(runner, graph, dev, tmp_path / "w").propose(root, None, budget_seconds=5))
    assert out.infrastructure and runner.calls == 1
    assert graph.attempts_for(root.id)[-1]["status"] == "error"
    exhausted = ProviderPause(PausePolicy(max_wait_s=1), scripted_probe(False))
    exhausted.exhausted = Outage("unauthenticated", "earlier")
    out2 = asyncio.run(Decomposer(OutageThenPlanRunner(PLAN), graph, dev, tmp_path / "w", pause=exhausted).propose(root, None, budget_seconds=5))
    assert out2.infrastructure, "after an exhausted pause an outage is filed, not waited for"
    graph.close()


# ------------------------------------------------------------------ in-flight recovery on resume

PARTIAL = "intros H.\n(* half way *)\nidtac."


def _interrupted_attempt(graph: Graph, dev, workroot: Path, name: str = "c1") -> int:
    """A node claimed, its attempt row open, its packet written, its scratch file edited
    -- and then the process died."""
    node = graph.by_name(name)
    if node.proof_status == "stuck":
        graph.set_proof_status(node.id, "open")
    graph.set_proof_status(node.id, "claimed")
    attempt_id = graph.start_attempt(node.id, runner="mock")
    packet = build_packet(graph, node, dev, siblings_of(graph, dev), anchor="root", root=workroot, attempt_id=attempt_id)
    scratch = packet.scratch.read_text(encoding="utf-8")
    assert "admit." in scratch
    packet.scratch.write_text(scratch.replace("admit.", PARTIAL, 1), encoding="utf-8")
    return attempt_id


def test_resume_recovers_the_partial_from_the_interrupted_attempt_directory(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    work = tmp_path / "work"
    attempt_id = _interrupted_attempt(graph, dev, work)
    report = resume_incomplete(graph, max_attempts=2, workroot=work)
    assert report.reopened == ["c1"] and report.recovered_partials == ["c1"] and report.interrupted == [attempt_id]
    row = graph.attempt(attempt_id)
    assert row["status"] == "stuck" and row["finished"] is not None
    assert row["evidence"] == INTERRUPTED_NOTE and row["body"] == PARTIAL
    c1 = graph.by_name("c1")
    assert c1.proof_status == "open" and c1.evidence.startswith(RESUMED_NOTE)
    assert last_partial(graph, c1) == PARTIAL
    assert "proof.recovered" in _kinds(graph)
    # The next packet carries it, exactly as an in-run retry would.
    seen: list[NodePayload] = []
    runner = MockRunner(dict(ANSWERS), on_dispatch=seen.append)
    result = asyncio.run(_sched(graph, dev, runner, tmp_path, workroot=work).run())
    assert {o.status for o in result.outcomes} == {"qed"}
    p = next(x for x in seen if x.name == "c1")
    assert p.attempt == 2 and RESUMED_NOTE in p.evidence
    task = (p.workdir / "TASK.md").read_text(encoding="utf-8")
    assert "## Your previous attempt's proof (partial)" in task and PARTIAL in task
    assert PARTIAL in (p.workdir / dev.path.name).read_text(encoding="utf-8")
    graph.close()


def test_resume_closes_a_claimed_row_that_left_no_directory(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    c1 = node_id("c1")
    graph.set_proof_status(c1, "claimed")
    a = graph.start_attempt(c1, runner="mock")
    graph.finish_attempt(a, status="stuck", evidence="Error: iFrame failed: spatial context is not empty")
    graph.set_proof_status(c1, "open")
    graph.set_proof_status(c1, "claimed")
    b = graph.start_attempt(c1, runner="mock")  # died before the packet was written
    report = resume_incomplete(graph, max_attempts=3, workroot=tmp_path / "work")
    assert report.reopened == ["c1"] and report.recovered_partials == [] and report.interrupted == [b]
    row = graph.attempt(b)
    assert row["status"] == "stuck" and row["body"] is None and row["evidence"] == INTERRUPTED_NOTE
    assert "spatial context" in graph.by_name("c1").evidence, "the earlier attempt's evidence still informs the retry"
    assert RESUMED_NOTE not in graph.by_name("c1").evidence
    assert attempts_spent(graph, graph.by_name("c1")) == 2, "the interrupted attempt is charged: the worker ran"
    assert not [r for r in graph.attempts_for(c1) if r["status"] == "claimed"]
    graph.close()


def test_resume_closes_an_interrupted_decomposer_round_and_the_round_still_counts(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=())
    a = graph.start_attempt(root.id, runner="d", role="decomposer", round=2)
    b = graph.start_attempt(root.id, runner="a", role="approver", round=1)
    report = resume_incomplete(graph, max_attempts=2, workroot=tmp_path / "work")
    assert sorted(report.interrupted) == sorted([a, b]) and report.reopened == []
    assert {graph.attempt(x)["status"] for x in (a, b)} == {"stuck"}
    assert graph.attempt(a)["evidence"] == INTERRUPTED_NOTE
    assert design_rounds_used(graph, root) == 2
    graph.close()


def test_last_partial_falls_back_to_the_attempt_directory(tmp_path):
    graph, root, dev = build_plain_graph(tmp_path, names=("c1",))
    work = tmp_path / "work"
    attempt_id = _interrupted_attempt(graph, dev, work)
    graph.finish_attempt(attempt_id, status="stuck", evidence="killed")  # a row without a body
    c1 = graph.by_name("c1")
    assert last_partial(graph, c1) == ""
    assert last_partial(graph, c1, workroot=work) == PARTIAL
    assert last_partial(graph, c1, workroot=tmp_path / "elsewhere") == ""
    graph.close()


def test_the_run_resumed_event_carries_the_recovered_partials(tmp_path, monkeypatch):
    monkeypatch.setattr("pcp.orch.prove.Gate", lambda d, **kw: FakeGate())
    cfg = plain_cfg(tmp_path, pause_hours=0, max_attempts=1)
    first = asyncio.run(prove(cfg, MockRunner(dict(ANSWERS), statuses={"c1": "stuck"})))
    assert not first.integrated
    first.close()
    graph = Graph(cfg.graph_path)
    from pcp.rocq.assemble import Development

    _interrupted_attempt(graph, Development(cfg.file), cfg.workroot)
    graph.close()
    cfg.max_attempts = 3  # the stuck attempt and the interrupted one are both charged
    result = asyncio.run(prove(cfg, MockRunner(dict(ANSWERS))))
    assert result.integrated, result.render()
    resumed = next(e for e in result.graph.events_since() if e["kind"] == "run.resumed")
    assert resumed["payload"]["recovered_partials"] == ["c1"] and resumed["payload"]["reopened"] == ["c1"]
    assert len(resumed["payload"]["interrupted"]) == 1
    result.close()


# ------------------------------------------------------------------ supervision

CRASH_ONCE_CHILD = r"""
import os, sys
sys.path.insert(0, sys.argv[4])
from pathlib import Path
from pcp.orch.graph import Graph
from pcp.orch.supervise import write_outcome
graph, marker, outcome = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
g = Graph(graph)
if not marker.exists():
    marker.write_text("crashed once")
    g.emit("attempt.started", None, note="about to die")
    print("dying mid-run", flush=True)
    os._exit(3)
g.emit("run.finished", None, integrated=True)
g.close()
print("second run finished", flush=True)
write_outcome(outcome, integrated=True, exit_code=0)
sys.exit(0)
"""

ALWAYS_CRASH_CHILD = "import os, sys; print('boom', flush=True); os._exit(3)"

RETURNED_ERROR_CHILD = r"""
import sys
sys.path.insert(0, sys.argv[2])
from pcp.orch.supervise import write_outcome
write_outcome(sys.argv[1], integrated=False, exit_code=2, error="usage: no such plan")
sys.exit(2)
"""

LOCK_HOLDING_CHILD = r"""
import sys, time
sys.path.insert(0, sys.argv[3])
from pathlib import Path
from pcp.util.locks import RunLock
lock = RunLock(sys.argv[1]).acquire()
Path(sys.argv[2]).write_text("held")
time.sleep(120)
"""


def test_the_supervisor_restarts_a_crashed_child_and_exits_with_the_childs_outcome(tmp_path):
    state = tmp_path / "state"
    graph = tmp_path / "graph.db"
    marker = tmp_path / "crashed"
    argv = [sys.executable, "-c", CRASH_ONCE_CHILD, str(graph), str(marker), str(state / OUTCOME_FILE), str(ROOT)]
    sup = Supervisor(argv=argv, state=state, graph=graph, max_restarts=3, backoff_s=(0.05,))
    assert sup.run() == 0
    g = Graph(graph)
    kinds = _kinds(g)
    assert kinds.count("run.restarted") == 1 and "run.finished" in kinds
    restarted = next(e for e in g.events_since() if e["kind"] == "run.restarted")
    assert restarted["payload"]["n"] == 1 and "exited with status 3" in restarted["payload"]["reason"]
    g.close()
    log = sup.log.read_text(encoding="utf-8")
    assert "dying mid-run" in log and "second run finished" in log
    assert "restart 1/3" in log and "finished: exit 0" in log
    assert read_outcome(sup.outcome)["integrated"] is True
    assert not sup.pid_file.exists(), "the pid file goes with the supervisor"


def test_the_supervisor_gives_up_after_max_restarts(tmp_path):
    state = tmp_path / "state"
    sup = Supervisor(argv=[sys.executable, "-c", ALWAYS_CRASH_CHILD], state=state, max_restarts=2, backoff_s=(0.01,))
    assert sup.run() == 1
    log = sup.log.read_text(encoding="utf-8")
    assert log.splitlines().count("boom") == 3 and "restart budget (2) is spent" in log


def test_a_child_that_returned_an_error_is_finished_not_restarted(tmp_path):
    state = tmp_path / "state"
    argv = [sys.executable, "-c", RETURNED_ERROR_CHILD, str(state / OUTCOME_FILE), str(ROOT)]
    sup = Supervisor(argv=argv, state=state, max_restarts=5, backoff_s=(0.01,))
    assert sup.run() == 2
    assert "restart" not in sup.log.read_text(encoding="utf-8")
    missing = Supervisor(argv=["/nonexistent/python", "-c", "pass"], state=tmp_path / "s2", max_restarts=5)
    assert missing.run() == 2


def _wait_for(predicate, timeout: float = 20.0) -> None:
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if predicate():
            return
        time.sleep(0.05)
    raise AssertionError("timed out waiting")


def _alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    try:
        # A zombie is not alive for our purposes.
        return "Z" not in Path(f"/proc/{pid}/stat").read_text().split(")")[-1].split()[0]
    except OSError:
        return False


def test_sigterm_to_the_supervisor_kills_the_child_group_and_leaves_the_lock_acquirable(tmp_path):
    state = tmp_path / "state"
    lock = tmp_path / "graph.db.lock"
    held = tmp_path / "held"
    child = [sys.executable, "-c", LOCK_HOLDING_CHILD, str(lock), str(held), str(ROOT)]
    driver = (
        "import sys; sys.path.insert(0, sys.argv[1]); from pathlib import Path; from pcp.orch.supervise import Supervisor; "
        "sys.exit(Supervisor(argv=sys.argv[3:], state=Path(sys.argv[2]), max_restarts=3, backoff_s=(0.1,)).run())"
    )
    sup = subprocess.Popen([sys.executable, "-c", driver, str(ROOT), str(state), *child], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    try:
        _wait_for(held.exists)
        with pytest.raises(LockedError):
            RunLock(lock).acquire()
        pid_file = json.loads((state / PID_FILE).read_text(encoding="utf-8"))
        assert pid_file["pid"] == sup.pid and pid_file["child_pid"]
        child_pid = int(pid_file["child_pid"])
        assert _alive(child_pid)
        os.kill(sup.pid, signal.SIGTERM)
        assert sup.wait(timeout=30) == 143
        _wait_for(lambda: not _alive(child_pid))
        RunLock(lock).acquire().release()  # the kernel released the dead holder's flock
        log = (state / "supervisor.log").read_text(encoding="utf-8")
        assert "received SIGTERM" in log and "the graph is resumable" in log
        assert not (state / PID_FILE).exists()
    finally:
        if sup.poll() is None:
            sup.kill()
            sup.wait()


def test_a_killed_lock_holders_lock_is_acquirable(tmp_path):
    lock = tmp_path / "g.db.lock"
    held = tmp_path / "held"
    proc = subprocess.Popen([sys.executable, "-c", LOCK_HOLDING_CHILD, str(lock), str(held), str(ROOT)])
    try:
        _wait_for(held.exists)
        with pytest.raises(LockedError, match=str(proc.pid)):
            RunLock(lock).acquire()
    finally:
        proc.kill()
        proc.wait()
    RunLock(lock).acquire().release()


def test_strip_flags_and_the_re_exec_command_lines(tmp_path):
    from pcp.cli.cmd_prove import child_argv, supervisor_argv

    raw = ["prove", "Foo.v", "foo", "--supervise", "--fresh", "--max-restarts", "7", "--record=.pcp/runs", "--attempts=3", "--plan", "plan.v"]
    assert strip_flags(raw, flags=("--supervise", "--fresh"), valued=("--max-restarts",)) == ["prove", "Foo.v", "foo", "--record=.pcp/runs", "--attempts=3", "--plan", "plan.v"]
    assert strip_flags(["--max-restarts=7", "x"], valued=("--max-restarts",)) == ["x"]
    sup = supervisor_argv(raw, state=tmp_path / "s", run_id="20260905-010203", max_restarts=7)
    assert sup[:3] == [sys.executable, "-m", "pcp.cli.main"] and "--supervise" not in sup and "--fresh" not in sup
    assert sup[sup.index("--supervised-child") + 1] == str(tmp_path / "s") and sup[sup.index("--max-restarts") + 1] == "7"
    assert sup[sup.index("--record-run-id") + 1] == "20260905-010203"
    child = child_argv(sup[3:], outcome=tmp_path / "s" / OUTCOME_FILE)
    assert "--supervised-child" not in child and "--max-restarts" not in child and "--fresh" not in child
    assert child[child.index("--outcome-file") + 1] == str(tmp_path / "s" / OUTCOME_FILE)
    assert child[child.index("--record-run-id") + 1] == "20260905-010203", "every try records into the same run directory"
    assert child.count("--plan") == 1


def test_pcp_prove_supervise_launches_detached_and_prints_the_pid(tmp_path, monkeypatch, capsys):
    dev, plan = write_plain(tmp_path)
    spawned: list[dict] = []

    def fake_spawn(argv, *, log, cwd=None, env=None):
        spawned.append({"argv": [str(a) for a in argv], "log": Path(log), "cwd": cwd})
        return 4242

    monkeypatch.setattr("pcp.util.proc.spawn_detached", fake_spawn)
    graph, work, record = tmp_path / "g.db", tmp_path / "work", tmp_path / "rec"
    argv = ["prove", str(dev), "root", "--plan", str(plan), "--runner", "mock", "--graph", str(graph), "--workroot", str(work),
            "--record", str(record), "--supervise", "--fresh", "--max-restarts", "3", "--pause-hours", "0"]
    assert pcp_main(argv) == 0
    out = capsys.readouterr().out
    assert out.startswith("supervising pid 4242; follow with: pcp status --graph") and "tail -f" in out
    assert len(spawned) == 1
    child = spawned[0]["argv"]
    assert child[:4] == [sys.executable, "-m", "pcp.cli.main", "prove"]
    assert "--supervise" not in child and "--fresh" not in child and "--supervised-child" in child
    run_id = child[child.index("--record-run-id") + 1]
    state = record / run_id
    assert spawned[0]["log"] == state / "supervisor.log" and Path(child[child.index("--supervised-child") + 1]) == state
    assert state.is_dir(), "the record run directory is claimed up front so every try shares it"
    # Without --record the supervisor lives in the workroot.
    spawned.clear()
    assert pcp_main([a for a in argv if a not in ("--record", str(record))]) == 0
    assert Path(spawned[0]["argv"][spawned[0]["argv"].index("--supervised-child") + 1]) == work
    assert "--record-run-id" not in spawned[0]["argv"]


def test_pcp_prove_writes_its_outcome_on_a_normal_return_and_on_a_returned_error(tmp_path, capsys):
    dev, plan = write_plain(tmp_path)
    outcome = tmp_path / "outcome.json"
    argv = ["prove", str(dev), "root", "--plan", str(plan), "--runner", "mock", "--graph", str(tmp_path / "g.db"),
            "--workroot", str(tmp_path / "work"), "--pause-hours", "0", "--outcome-file", str(outcome)]
    assert pcp_main(argv) == 1  # the bare mock answers nothing: ran, did not integrate
    data = read_outcome(outcome)
    assert data is not None and data["exit_code"] == 1 and data["integrated"] is False
    assert any(words in data["detail"] for words in ("still open", "not proved"))
    outcome.unlink()
    holder = RunLock(lock_path(tmp_path / "g.db")).acquire()
    try:
        assert pcp_main(argv) == 2
    finally:
        holder.release()
    data = read_outcome(outcome)
    assert data and data["exit_code"] == 2 and "another pcp run holds" in data["error"]
    assert read_outcome(tmp_path / "nope.json") is None
    assert "supervising" not in capsys.readouterr().out


# ------------------------------------------------------------------ ladder resume


def _ladder_paths(tmp_path: Path, bench_dir: Path):
    import shutil

    from eval.ladder import Paths

    paths = Paths(tmp_path / "repo")
    for name in ("rwcas_design", "seqlock_design", "seqlock_wf_design"):
        shutil.copytree(bench_dir / name, paths.corpus / name)
    return paths


def test_ladder_resume_reuses_the_stamps_paths_drops_fresh_and_skips_finished_rungs(tmp_path, bench_dir, capsys):
    from eval.ladder import LADDER, main, rung_argv, tag_for

    paths = _ladder_paths(tmp_path, bench_dir)
    rung = LADDER[0]
    assert "--fresh" in rung_argv(rung, paths, stamp="t") and "--fresh" not in rung_argv(rung, paths, stamp="t", fresh=False)
    done = {"outage": "", "rung": "rwcas_design", "root": "write_spec", "exit": 0, "timed_out": False, "elapsed_s": 5.0,
            "record": str(paths.record(tag_for("t", "rwcas_design"))), "log": "x", "published": None, "tail": "", "brief": "spec-only"}
    failed = dict(done, rung="seqlock_design", root="x34_spec", exit=1)
    paths.runs.mkdir(parents=True)
    paths.summary("t").write_text(json.dumps([done, failed]), encoding="utf-8")
    launcher = [sys.executable, "-c", "import sys; print(sys.argv); sys.exit(0)"]
    code = main(["--resume", "t", "--skip-preflight", "--brief", "spec-only", "--stamp", "ignored"], paths=paths, launcher=launcher)
    out = capsys.readouterr().out
    assert code == 0
    assert "resuming ladder t: keeping rwcas_design; running seqlock_design, seqlock_wf_design" in out
    rows = json.loads(paths.summary("t").read_text(encoding="utf-8"))
    assert [r["rung"] for r in rows] == ["rwcas_design", "seqlock_design", "seqlock_wf_design"]
    assert rows[0] == done, "a finished rung's row is kept as it was"
    assert all(r["exit"] == 0 for r in rows)
    for name in ("seqlock_design", "seqlock_wf_design"):
        tag = tag_for("t", name)
        text = paths.log(tag).read_text(encoding="utf-8")
        argv = shlex.split(text.splitlines()[0].lstrip("# "))
        assert "--fresh" not in argv and argv[argv.index("--graph") + 1] == str(paths.graph(tag))
        assert argv[argv.index("--record") + 1] == str(paths.record(tag))
    assert not paths.log(tag_for("t", "rwcas_design")).exists(), "the finished rung was not run"


def test_ladder_resume_dry_run_lists_only_the_unfinished_rungs(tmp_path, bench_dir, capsys):
    from eval.ladder import main

    paths = _ladder_paths(tmp_path, bench_dir)
    paths.runs.mkdir(parents=True)
    paths.summary("s").write_text(json.dumps([{"rung": "rwcas_design", "exit": 0}, {"rung": "seqlock_wf_design", "exit": 0}]), encoding="utf-8")
    assert main(["--resume", "s", "--dry-run", "--brief", "spec-only"], paths=paths) == 0
    lines = capsys.readouterr().out.strip().splitlines()
    assert len(lines) == 1
    argv = shlex.split(lines[0])
    assert argv[argv.index("--corpus") + 1] == "seqlock_design" and "--fresh" not in argv
    assert "ladder_s_seqlock_design" in argv[argv.index("--graph") + 1]
    # No summary yet: everything runs, still without --fresh.
    assert main(["--resume", "fresh-stamp", "--dry-run", "--brief", "spec-only"], paths=paths) == 0
    assert len(capsys.readouterr().out.strip().splitlines()) == 3


def test_recorder_log_appends_timestamped_lines(tmp_path):
    rec = Recorder(tmp_path / "rec", run_id="r")
    rec.log("paused: unauthenticated")
    rec.log("resumed")
    lines = (rec.root / "run.log").read_text(encoding="utf-8").splitlines()
    assert len(lines) == 2 and lines[0].endswith("paused: unauthenticated") and lines[1].endswith("resumed")
    assert Recorder(tmp_path / "rec", run_id="r").root == rec.root, "a run id is reusable: every restart records into one directory"
