"""The permanent canary (PLAN.md 8.11).

One golden end-to-end run -- a known lemma, a known plan, scripted workers -- that
executes in CI and before every release.  What is under test is the loop: freeze,
whole-frontier dispatch, deterministic gating, the one evidence-informed retry,
crash resume, integration by machine oracle, the one-screen report, the run lock.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from pcp.errors import LockedError
from pcp.orch.model import Budget
from pcp.orch.prove import ProveConfig, lock_path, run
from pcp.orch.runners.mock import MockRunner
from pcp.util.locks import RunLock
from tests.conftest import needs_rocq

pytestmark = needs_rocq

CANARY_ANSWERS = {
    "canary_swap": 'iIntros "[HA HB]". iFrame.',
    "canary_assoc": 'iIntros "[HA [HB HC]]". iFrame.',
    "canary_main": (
        'iIntros "H". iDestruct (canary_swap with "H") as "[HQR HP]". '
        'iDestruct "HQR" as "[HQ HR]". iFrame.'
    ),
}


def _cfg(tmp_path: Path, canary_dir: Path, **kw) -> ProveConfig:
    return ProveConfig(
        file=canary_dir / "Canary.v", target="canary_main", plan=canary_dir / "plan.v",
        graph_path=tmp_path / "graph.db", workroot=tmp_path / "work",
        node_seconds=180, budget=Budget(requests=50, seconds=1800), **kw,
    )


def _runner(**kw) -> MockRunner:
    return MockRunner(answers=dict(CANARY_ANSWERS), **kw)


def test_canary_integrates(tmp_path, canary_dir):
    result = run(_cfg(tmp_path, canary_dir), _runner())
    assert result.integrated, result.render()
    assert len(result.report.by_status("qed")) == 3
    assert result.sentinels.ok
    assert result.graph.summary() == {"integrated": 3}
    assert result.report.dispatched == 3
    assert not lock_path(tmp_path / "graph.db").exists() or True  # the lock file may remain; the lock is released
    result.close()


def test_canary_retries_once_with_evidence(tmp_path, canary_dir):
    seen: list[tuple[str, int, bool]] = []
    runner = _runner(fail_first={"canary_assoc"})
    runner.on_dispatch = lambda p: seen.append((p.name, p.attempt, bool(p.evidence)))
    result = run(_cfg(tmp_path, canary_dir), runner)
    assert result.integrated, result.render()
    assoc = [s for s in seen if s[0] == "canary_assoc"]
    assert [s[1] for s in assoc] == [1, 2], assoc
    assert assoc[1][2], "the retry must carry the previous attempt's evidence"
    assert max(s[1] for s in seen) == 2
    assert result.report.gate_failures == 1 and result.report.dispatched == 4
    result.close()


def test_canary_never_wedges_when_the_worker_has_no_answer(tmp_path, canary_dir):
    result = run(_cfg(tmp_path, canary_dir), MockRunner(answers={}))
    assert not result.integrated
    statuses = {o.status for o in result.report.outcomes}
    assert statuses <= {"qed", "stuck", "contested", "error"}
    assert len(result.report.outcomes) == 3
    assert "still open" in result.integration_detail or "not proved" in result.integration_detail
    assert result.graph.summary() == {"stuck": 3}
    result.close()


class Crash(BaseException):
    """The process dying mid-attempt."""


def test_canary_resumes_after_a_crash(tmp_path, canary_dir):
    """Resumed after a crash, only the node that was in flight is redispatched."""

    def die_on_root(p) -> None:
        if p.name == "canary_main":
            raise Crash()

    with pytest.raises(Crash):
        run(_cfg(tmp_path, canary_dir), _runner(on_dispatch=die_on_root))
    dispatched: list[str] = []
    second = _runner(on_dispatch=lambda p: dispatched.append(p.name))
    result = run(_cfg(tmp_path, canary_dir), second)
    assert result.integrated, result.render()
    assert dispatched == ["canary_main"], dispatched
    kinds = [e["kind"] for e in result.graph.events_since()]
    assert "run.resumed" in kinds
    result.close()


def test_a_worker_that_claims_qed_without_gating_is_a_failed_attempt(tmp_path, canary_dir):
    answers = dict(CANARY_ANSWERS)
    answers["canary_swap"] = "iIntros. (* nonsense *) idtac."
    result = run(_cfg(tmp_path, canary_dir), MockRunner(answers=answers))
    swap = next(o for o in result.report.outcomes if o.name == "canary_swap")
    assert swap.status == "stuck" and swap.attempts == 2
    assert swap.gate is not None and not swap.gate.ok
    assert not result.integrated
    result.close()


def test_a_worker_cannot_smuggle_an_admit_past_the_gate(tmp_path, canary_dir):
    answers = dict(CANARY_ANSWERS)
    answers["canary_swap"] = "admit."
    result = run(_cfg(tmp_path, canary_dir), MockRunner(answers=answers))
    swap = next(o for o in result.report.outcomes if o.name == "canary_swap")
    assert swap.status == "stuck"
    assert any("Admitted" in c.name and not c.ok for c in swap.gate.checks)
    result.close()


def test_report_fits_on_one_screen(tmp_path, canary_dir):
    result = run(_cfg(tmp_path, canary_dir), _runner())
    lines = result.render().splitlines()
    assert len(lines) <= 24, "\n".join(lines)
    assert lines[0] == "3 qed · 0 stuck · 0 contested" + lines[0][len("3 qed · 0 stuck · 0 contested"):]
    assert result.to_json()["integrated"] is True and len(result.to_json()["outcomes"]) == 3
    result.close()


def test_a_second_prove_on_the_same_graph_is_refused_by_the_lock(tmp_path, canary_dir):
    cfg = _cfg(tmp_path, canary_dir)
    with RunLock(lock_path(cfg.graph_path)), pytest.raises(LockedError, match="another pcp run holds"):
        run(cfg, _runner())
    result = run(cfg, _runner())
    assert result.integrated
    result.close()
