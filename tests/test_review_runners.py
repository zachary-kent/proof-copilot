"""Wave-3 review: what a worker can put in its directory must never wedge or crash the reader."""

from __future__ import annotations

import os
import threading

import pytest

from pcp.orch.failures import classify
from pcp.orch.protocol import MAX_WORKER_FILE_BYTES, read_answer_file, read_edited_body, read_result
from pcp.orch.record import AttemptRecord, Recorder, load_records
from pcp.orch.runners.stream import parse_output

DEEP = "[" * 100_000 + "]" * 100_000


def _bounded(fn, seconds: float = 5.0):
    """Run ``fn`` in a thread; a reader that blocks on a FIFO would hang the test."""
    box: dict = {}

    def run() -> None:
        try:
            box["result"] = fn()
        except BaseException as exc:  # noqa: BLE001
            box["error"] = exc
    t = threading.Thread(target=run, daemon=True)
    t.start()
    t.join(seconds)
    assert not t.is_alive(), "the reader blocked"
    if "error" in box:
        raise box["error"]
    return box["result"]


@pytest.mark.parametrize("name", ["answer.json", "proof.v", "Dev.v", "extra.v"])
def test_a_fifo_or_device_named_like_a_worker_file_never_blocks_the_reader(tmp_path, name):
    os.mkfifo(tmp_path / name)
    r = _bounded(lambda: read_result(tmp_path, "", target="t", scratch_file="Dev.v"))
    assert r.status == "stuck" and r.proof == ""
    os.unlink(tmp_path / name)
    os.symlink("/dev/zero", tmp_path / name)
    r = _bounded(lambda: read_result(tmp_path, "", target="t", scratch_file="Dev.v"))
    assert r.status == "stuck"
    if name == "answer.json":
        assert "symlink" in r.evidence


def test_a_directory_named_like_a_worker_file_does_not_raise(tmp_path):
    for name in ("answer.json", "proof.v", "x.v"):
        (tmp_path / name).mkdir()
    r = read_result(tmp_path, "", target="t", scratch_file="Dev.v")
    assert r.status == "stuck" and "not a regular file" in r.evidence


def test_oversized_and_deeply_nested_answers_are_malformed_not_read(tmp_path):
    big = tmp_path / "answer.json"
    big.write_bytes(b'{"status":"qed","proof":"' + b"x" * (MAX_WORKER_FILE_BYTES + 1) + b'"}')
    r = read_answer_file(big)
    assert r.status == "stuck" and "limit" in r.evidence
    big.write_text('{"status":"qed","proof":' + DEEP + "}")
    assert read_answer_file(big).status == "stuck"
    trace = parse_output('{"type":"assistant","message":{"content":' + DEEP + "}}\n", "claude")
    assert trace.events == 0 and len(trace.stderr_lines) == 1
    (tmp_path / "Dev.v").write_text("Lemma t : True.\nProof.\n  exact I.\nQed.\n")
    assert read_edited_body(tmp_path, "t", scratch_file="Dev.v") == "exact I."


def test_recorder_skips_special_and_oversized_worker_files(tmp_path):
    work = tmp_path / "work"
    work.mkdir()
    os.mkfifo(work / "answer.json")
    (work / "TASK.md").mkdir()
    os.symlink("/dev/zero", work / "pcp-node.json")
    rec = AttemptRecord(run_id="r", node="t", lemma="t", attempt=1, runner="x", status="stuck", solved=False, attempt_id=1)
    out = _bounded(lambda: Recorder(tmp_path / "rec", "run").write(rec, workdir=work))
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


def test_a_protocol_violation_recorded_with_status_error_stays_a_protocol_violation():
    c = classify("the decomposer produced no JSON object to read", status="error")
    assert c.classes[:2] == ["protocol-violation", "runner-error"]
    c = classify("each definition must be an object", status="error")
    assert c.primary == "protocol-violation"
    c = classify("claude exited with status 1 and wrote no answer: 401 OAuth access token has been revoked", status="error", exit_code=1)
    assert c.primary == "runner-error"
    assert classify("worker exceeded its 1800s deadline and was killed", status="error").primary == "runner-error"


async def test_the_mock_returns_a_scripted_error_directly_without_an_answer_file(tmp_path):
    from pcp.orch.protocol import ANSWER_FILE, NodePayload
    from pcp.orch.runners.mock import MockRunner

    runner = MockRunner({"x": "exact I."}, statuses={"x": "error"})
    node = NodePayload(node_id="x", name="x", statement="Lemma x : True.", file="", workdir=tmp_path / "a1")
    result = await runner.run_node(node)
    assert result.status == "error" and "scripted error" in result.evidence and result.exit_code == 1
    assert not (tmp_path / "a1" / ANSWER_FILE).exists()
    assert result.cost["requests"] == 1 and result.trace["model"] == "mock"
    ok = await MockRunner({"x": "exact I."}).run_node(node)
    assert ok.status == "qed" and ok.exit_code == 0 and (tmp_path / "a1" / ANSWER_FILE).exists()
