"""pcp.orch.record: durable attempt records keyed by attempt id."""

from __future__ import annotations

import json
import os

import pytest

from pcp.errors import UsageError
from pcp.orch.failures import classify_record
from pcp.orch.record import RECORD_FILE, AttemptRecord, Recorder, load_records
from tests._orch_fixtures import bounded


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


def test_recorder_skips_special_and_oversized_worker_files(tmp_path):
    work = tmp_path / "work"
    work.mkdir()
    os.mkfifo(work / "answer.json")
    (work / "TASK.md").mkdir()
    os.symlink("/dev/zero", work / "pcp-node.json")
    rec = AttemptRecord(run_id="r", node="t", lemma="t", attempt=1, runner="x", status="stuck", solved=False, attempt_id=1)
    out = bounded(lambda: Recorder(tmp_path / "rec", "run").write(rec, workdir=work))
    assert (out / "record.json").exists() and not (out / "answer.json").exists() and not (out / "TASK.md").exists()


def test_an_unreadable_record_is_reported_not_raised(tmp_path):
    if os.geteuid() == 0:
        pytest.skip("root reads everything")
    d = tmp_path / "run" / "a.1"
    d.mkdir(parents=True)
    (d / "record.json").write_text("{}")
    os.chmod(d / "record.json", 0)
    try:
        records = list(load_records(tmp_path / "run"))
    finally:
        os.chmod(d / "record.json", 0o644)
    assert len(records) == 1 and records[0]["unreadable"] and "PermissionError" in records[0]["evidence"]


def test_two_recorders_started_in_the_same_second_get_distinct_directories(tmp_path, monkeypatch):
    import pcp.orch.record as record_mod

    monkeypatch.setattr(record_mod.time, "strftime", lambda fmt: "20260904-120000")
    a = Recorder(tmp_path)
    b = Recorder(tmp_path)
    assert a.run_id == "20260904-120000" and b.run_id == "20260904-120000-1" and a.root != b.root
    assert Recorder(tmp_path, "explicit").run_id == "explicit"
