"""The diagnosis feedback log (pcp.state.diagnosis_log, D2): append-only, never raises on
the hot path, and turns agent verdicts into per-class hit/miss counts."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from pcp.state.diagnose import diagnose_structured
from pcp.state.diagnosis_log import (
    class_stats,
    log_path,
    misclassified,
    read_log,
    record_diagnosis,
    record_feedback,
)
from pcp.state.ipm.model import Hyp, IrisGoal

FOCUS = "Expected a single focused goal but 2 goals are focused."


def _frame_dx():
    goal = IrisGoal(goal="† b … (length vs) ∗ R", spatial=[Hyp("†Hb", "† b … n")])
    return diagnose_structured('iFrame "†Hb".', "iFrame: cannot frame († b … n)", goal)


def test_record_and_feedback_are_append_only_jsonl(tmp_path: Path) -> None:
    did = record_diagnosis(tmp_path, _frame_dx(), goal_hash="g:1")
    assert len(did) == 12
    (rec,) = read_log(tmp_path)
    assert rec["rec"] == "diagnosis" and rec["id"] == did and rec["family"] == "frame"
    assert rec["repair"] == "rewrite-before-frame" and rec["confidence"] == "high" and rec["tactic_head"] == "iFrame"
    assert rec["error_hash"].startswith("e:") and "cannot frame" in rec["error_excerpt"] and rec["goal_hash"] == "g:1"
    assert record_feedback(tmp_path, did, correct=False, note="needed iSplitL", actual="split-goal") == {"ok": True, "id": did}
    lines = log_path(tmp_path).read_text(encoding="utf-8").splitlines()
    assert len(lines) == 2 and json.loads(lines[0]) == rec  # the diagnosis line is never rewritten
    assert json.loads(lines[1])["rec"] == "feedback"


def test_class_stats_count_hits_misses_and_unrated_with_the_latest_verdict(tmp_path: Path) -> None:
    a = record_diagnosis(tmp_path, _frame_dx())
    b = record_diagnosis(tmp_path, _frame_dx())
    c = record_diagnosis(tmp_path, diagnose_structured("rewrite H.", FOCUS, None))
    record_diagnosis(tmp_path, diagnose_structured("rewrite H.", FOCUS, None))
    record_feedback(tmp_path, a, correct=False)
    record_feedback(tmp_path, a, correct=True)  # revised: the latest verdict counts
    record_feedback(tmp_path, b, correct=False, note="wrong occurrence")
    record_feedback(tmp_path, c, correct=True)
    stats = class_stats(tmp_path)
    assert stats["rewrite-before-frame"] == {"diagnosed": 2, "confirmed": 1, "wrong": 1, "unrated": 0}
    assert stats["bullet"] == {"diagnosed": 2, "confirmed": 1, "wrong": 0, "unrated": 1}
    assert class_stats(tmp_path, by="family")["focus"]["diagnosed"] == 2
    (wrong,) = misclassified(tmp_path)
    assert wrong["id"] == b and wrong["note"] == "wrong occurrence"


def test_unknown_ids_are_reported_not_raised(tmp_path: Path) -> None:
    assert record_feedback(tmp_path, "nope")["ok"] is False
    assert record_feedback(tmp_path, "")["ok"] is False


def test_logging_never_breaks_the_step(tmp_path: Path) -> None:
    blocked = tmp_path / "ws"
    blocked.write_text("a file where the workspace directory should be")
    assert record_diagnosis(blocked, _frame_dx()) == ""
    assert record_diagnosis(None, _frame_dx()) == ""
    (tmp_path / ".pcp").mkdir()
    log_path(tmp_path).write_text("not json\n{\"rec\": \"diagnosis\", \"id\": \"x\", \"repair\": \"bullet\"}\n")
    assert class_stats(tmp_path)["bullet"]["diagnosed"] == 1


def test_pcp_diagnoses_cli_prints_the_counts(tmp_path: Path) -> None:
    did = record_diagnosis(tmp_path, diagnose_structured("rewrite H.", FOCUS, None))
    record_feedback(tmp_path, did, correct=False, note="it was a bullet after all?")
    out = subprocess.run([sys.executable, "-m", "pcp.cli.main", "diagnoses", "--workspace", str(tmp_path)],
                         capture_output=True, text=True, check=True).stdout
    assert "bullet" in out and "wrong" in out
    wrong = subprocess.run([sys.executable, "-m", "pcp.cli.main", "diagnoses", "--workspace", str(tmp_path), "--wrong"],
                           capture_output=True, text=True, check=True).stdout
    assert did in wrong and "it was a bullet after all?" in wrong
