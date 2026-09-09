"""pcp.orch.record: durable attempt records keyed by attempt id."""

from __future__ import annotations

import json

import pytest

from pcp.errors import UsageError
from pcp.orch.failures import classify_record
from pcp.orch.record import RECORD_FILE, AttemptRecord, Recorder, load_records


def _record(**kw) -> AttemptRecord:
    base = dict(run_id="r", node="n", lemma="lemma", attempt=1, runner="mock", status="stuck", solved=False,
                evidence="Error: Unable to unify a with b", attempt_id=7)
    base.update(kw)
    return AttemptRecord(**base)


def test_write_persists_every_file(tmp_path):
    rec = Recorder(tmp_path, run_id="run1")
    workdir = tmp_path / "work"
    workdir.mkdir()
    (workdir / "TASK.md").write_text("task")
    (workdir / "answer.json").write_text("{}")
    out = rec.write(_record(proof="exact I.\n", gate_report="gate: FAIL", trace={"turns": 1}), workdir=workdir, transcript="x" * 10)
    assert out == tmp_path / "run1" / "lemma.7"
    assert {p.name for p in out.iterdir()} == {RECORD_FILE, "proof.v", "gate.txt", "trace.json", "transcript.txt", "TASK.md", "answer.json"}
    data = json.loads((out / RECORD_FILE).read_text())
    assert data["primary_failure"] == "unification-failure" and data["proof_lines"] == 1 and data["attempt_id"] == 7
    assert data["transcript_tail"] == "x" * 10 and data["started_at"] > 0


def test_records_are_never_overwritten(tmp_path):
    rec = Recorder(tmp_path, run_id="run1")
    rec.write(_record(attempt_id=1, round=1))
    with pytest.raises(UsageError):
        rec.write(_record(attempt_id=1, round=2))
    rec.write(_record(attempt_id=2, round=2))
    assert sorted(p.name for p in (tmp_path / "run1").iterdir()) == ["lemma.1", "lemma.2"]


def test_dir_for_uses_attempt_id_and_suffix(tmp_path):
    rec = Recorder(tmp_path, run_id="run1")
    assert rec.dir_for("root", 3, "decompose").name == "root.3.decompose"
    assert rec.dir_for("a/b c", 4).name == "a_b_c.4"


def test_transcript_keeps_head_and_tail(tmp_path):
    rec = Recorder(tmp_path, run_id="run1")
    transcript = "H" * 30_000 + "M" * 300_000 + "T" * 250_000
    out = rec.write(_record(), transcript=transcript)
    saved = (out / "transcript.txt").read_text()
    assert saved.startswith("H" * 20_000) and saved.endswith("T" * 200_000) and "chars elided" in saved


def test_load_records_backfills_and_reports_unreadable(tmp_path):
    rec = Recorder(tmp_path, run_id="run1")
    out = rec.write(_record(), transcript="tail text")
    data = json.loads((out / RECORD_FILE).read_text())
    data["transcript_tail"] = ""
    (out / RECORD_FILE).write_text(json.dumps(data))
    bad = tmp_path / "run1" / "lemma.9"
    bad.mkdir()
    (bad / RECORD_FILE).write_text("{truncated")
    records = list(load_records(tmp_path))
    assert len(records) == 2
    assert records[0]["transcript_tail"] == "tail text"
    assert records[1]["unreadable"] and records[1]["status"] == "error"


def test_stored_classification_matches_the_report(tmp_path):
    rec = Recorder(tmp_path, run_id="run1")
    rec.write(_record(evidence="Error: iNext: missing later", transcript_tail="mask mask"))
    stored = next(load_records(tmp_path))
    assert stored["primary_failure"] == classify_record(stored).primary == "later-modality"
    summary = rec.summary()
    assert summary["total"] == 1 and summary["primary"] == {"later-modality": 1}


def test_solved_records_carry_friction_but_no_failure(tmp_path):
    rec = Recorder(tmp_path, run_id="run1")
    r = _record(status="qed", solved=True, trace={"errors": ["Error: iFrame: cannot frame; spatial context is not empty"]})
    rec.write(r)
    assert r.primary_failure == "" and r.friction_classes == ["leftover-spatial"]
    assert AttemptRecord.from_json(r.to_json()) == r
