"""The permanent canary (PLAN.md 8.11).

One golden end-to-end run -- a known lemma, a known plan, scripted workers -- that
executes in CI and before every release.  The daily loop is the product, and this is
the test that says so: speculative features are feature-flagged off by default and
are **not allowed to break this**.

What is under test is the loop, not Iris: freeze, parallel dispatch of the whole
frontier, deterministic gating, the one evidence-informed retry, crash-resume, and
integration by machine oracle (`Qed` + clean `Print Assumptions`).
"""

from __future__ import annotations

from pathlib import Path

from tests.conftest import needs_rocq

CANARY_ANSWERS = {
    "canary_swap": 'iIntros "[HA HB]". iFrame.',
    "canary_assoc": 'iIntros "[HA [HB HC]]". iFrame.',
    "canary_main": (
        'iIntros "H". iDestruct (canary_swap with "H") as "[HQR HP]". '
        'iDestruct "HQR" as "[HQ HR]". iFrame.'
    ),
}


def _cfg(tmp_path: Path, canary_dir: Path, **kw):
    from pcp.orch.graph import Budget
    from pcp.orch.prove import ProveConfig

    return ProveConfig(
        file=canary_dir / "Canary.v",
        target="canary_main",
        plan=canary_dir / "plan.v",
        graph_path=tmp_path / "graph.db",
        workroot=tmp_path / "work",
        node_seconds=180,
        budget=Budget(requests=50, seconds=1800),
        **kw,
    )


def _runner(**kw):
    from pcp.orch.runners.mock import MockRunner

    return MockRunner(answers=dict(CANARY_ANSWERS), **kw)


@needs_rocq
def test_canary_integrates(tmp_path: Path, canary_dir: Path) -> None:
    from pcp.orch.prove import run

    result = run(_cfg(tmp_path, canary_dir), _runner())
    assert result.integrated, result.render()
    assert len(result.report.by_status("qed")) == 3
    assert result.sentinels.ok
    # Completion has a machine oracle; nothing here is a model's opinion.
    assert result.graph.summary() == {"integrated": 3}


@needs_rocq
def test_canary_retries_once_with_evidence(tmp_path: Path, canary_dir: Path) -> None:
    """A failed first attempt must be retried exactly once, with evidence attached."""
    from pcp.orch.prove import run

    seen: list[tuple[str, int, bool]] = []
    runner = _runner(fail_first={"canary_assoc"})
    runner.on_dispatch = lambda p: seen.append((p.name, p.attempt, bool(p.evidence)))

    result = run(_cfg(tmp_path, canary_dir), runner)
    assert result.integrated, result.render()
    assoc = [s for s in seen if s[0] == "canary_assoc"]
    assert [s[1] for s in assoc] == [1, 2], assoc
    assert assoc[1][2], "the retry must carry the previous attempt's evidence"
    # And no node is attempted a third time: one retry, then escalate.
    assert max(s[1] for s in seen) == 2


@needs_rocq
def test_canary_never_wedges_when_the_worker_has_no_answer(tmp_path: Path, canary_dir: Path) -> None:
    """Every node terminates in one of three shapes within its budget."""
    from pcp.orch.prove import run
    from pcp.orch.runners.mock import MockRunner

    result = run(_cfg(tmp_path, canary_dir), MockRunner(answers={}))
    assert not result.integrated
    statuses = {o.status for o in result.report.outcomes}
    assert statuses <= {"qed", "stuck", "contested", "error"}
    assert len(result.report.outcomes) == 3
    assert "still open" in result.integration_detail or "not proved" in result.integration_detail


@needs_rocq
def test_canary_resumes_after_a_crash(tmp_path: Path, canary_dir: Path) -> None:
    """`pcp prove` resumed after a crash picks up from the SQLite graph."""
    from pcp.orch.prove import run

    partial = _runner()
    partial.answers.pop("canary_main")
    first = run(_cfg(tmp_path, canary_dir), partial)
    assert not first.integrated
    assert len(first.report.by_status("qed")) == 2
    first.graph.close()

    # Same graph path: the two proved children must not be re-dispatched.
    dispatched: list[str] = []
    second = _runner()
    second.on_dispatch = lambda p: dispatched.append(p.name)
    result = run(_cfg(tmp_path, canary_dir), second)
    assert result.integrated, result.render()
    assert dispatched == ["canary_main"], dispatched


@needs_rocq
def test_a_worker_that_claims_qed_without_gating_is_a_failed_attempt(tmp_path: Path, canary_dir: Path) -> None:
    """No model argues with the gate: a `qed` that does not compile is `stuck`."""
    from pcp.orch.prove import run
    from pcp.orch.runners.mock import MockRunner

    answers = dict(CANARY_ANSWERS)
    answers["canary_swap"] = "iIntros. (* nonsense *) idtac."
    result = run(_cfg(tmp_path, canary_dir), MockRunner(answers=answers))
    swap = next(o for o in result.report.outcomes if o.name == "canary_swap")
    assert swap.status == "stuck"
    assert swap.gate is not None and not swap.gate.ok
    assert not result.integrated


@needs_rocq
def test_a_worker_cannot_smuggle_an_admit_past_the_gate(tmp_path: Path, canary_dir: Path) -> None:
    from pcp.orch.prove import run
    from pcp.orch.runners.mock import MockRunner

    answers = dict(CANARY_ANSWERS)
    answers["canary_swap"] = "admit."
    result = run(_cfg(tmp_path, canary_dir), MockRunner(answers=answers))
    swap = next(o for o in result.report.outcomes if o.name == "canary_swap")
    assert swap.status == "stuck"
    assert any("Admitted" in c.name and not c.ok for c in swap.gate.checks)  # type: ignore[union-attr]


@needs_rocq
def test_report_fits_on_one_screen(tmp_path: Path, canary_dir: Path) -> None:
    """Short reports are part of the engineering contract, not a nicety."""
    from pcp.orch.prove import run

    result = run(_cfg(tmp_path, canary_dir), _runner())
    lines = result.render().splitlines()
    assert len(lines) <= 24, "\n".join(lines)
