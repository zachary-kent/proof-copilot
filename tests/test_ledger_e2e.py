"""The ledger on real Iris proofs (eval/corpus/scratch/Blame.v), through the shared pool."""

from __future__ import annotations

import _ipm_standin  # noqa: F401
import pytest
from conftest import needs_petanque

from pcp.state.ledger.query import blame, leftovers, unused_at_qed, where_did_it_go

pytestmark = needs_petanque


def _trace(pool, scratch_dir, lemma: str, tactics: list[str]):
    pytest.importorskip("pcp.state.trace")
    from pcp.state.explain import open_session
    from pcp.state.ledger.diff import attach
    from pcp.state.trace import Tracer

    session = open_session(pool, scratch_dir / "Blame.v", lemma)
    tracer = attach(Tracer(session))
    for t in tactics:
        step = tracer.step(t)
        assert step.ok, step.error
    return tracer.trace


def test_premature_consumption(pool, scratch_dir) -> None:
    trace = _trace(pool, scratch_dir, "premature_consumption", ['iIntros "[[HP HQ] HR]".', "iFrame."])
    assert trace.finished
    kinds = [(e.step, e.kind, e.hyp) for e in trace.events]
    assert (1, "Intro", "HP") in kinds and (1, "Intro", "HQ") in kinds and (1, "Intro", "HR") in kinds
    assert (2, "GoalClosed", None) in kinds
    assert (2, "Frame", "HP") in kinds
    assert not [e for e in trace.events if e.kind in ("MaskChange", "LaterIntro")]
    p = where_did_it_go(trace, "HP")
    assert p.fate == "framed"
    b = blame(trace, 3, "HP")
    assert b.repair == "frame-later" and '"HP" was framed at step 2 by `iFrame.`' in b.render()
    assert unused_at_qed(trace) == []


def test_persistent_is_not_consumed(pool, scratch_dir) -> None:
    trace = _trace(pool, scratch_dir, "persistent_is_not_consumed", ['iIntros "[#HP HQ]".', 'iFrame "HP".', "iFrame."])
    assert trace.finished
    hp = [e for e in trace.events if e.hyp == "HP"]
    assert hp and all(e.kind != "Consume" for e in hp), [e.render() for e in hp]
    assert any(e.kind == "Frame" and e.klass == "intuitionistic" for e in hp)
    p = where_did_it_go(trace, "HP")
    assert p.fate != "consumed"
    assert blame(trace, 4, "HP").repair in ("restate", "duplicate-it-is-persistent")


def test_leftover_spatial(pool, scratch_dir) -> None:
    trace = _trace(pool, scratch_dir, "leftover_spatial", ['iIntros "[HP HQ]".'])
    assert [h.id for h in leftovers(trace)] == ["HP", "HQ"]
    assert [h.id for h in leftovers(trace, 1)] == ["HP", "HQ"]
    assert where_did_it_go(trace, "HQ").fate == "live"
