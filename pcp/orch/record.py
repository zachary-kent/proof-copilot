"""Durable per-attempt records, for failure analysis (PLAN.md 13; contract §5.3).

Every attempt -- successful or not -- leaves behind the exact packet the worker saw,
what it sent back, what the gate said, the *full* event stream (head and tail), and
a classification of how it failed.  Plain files on purpose: they outlive this tool,
they diff, and a human can read one without a viewer.

Record directories are keyed by the graph's global attempt id, which is unique by
construction, so a design round or a decomposer re-ask can never overwrite an
earlier record (ARCHITECTURE.md §8).  Writing twice to the same directory is refused.
"""

from __future__ import annotations

import time
from collections.abc import Iterator
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

from pcp.errors import UsageError
from pcp.orch.failures import classify_record, friction_classes
from pcp.orch.protocol import ANSWER_FILE, NODE_FILE, TASK_FILE
from pcp.util.io import atomic_write_text, copy_if_exists, ensure_dir, json_dump, json_load, read_text
from pcp.util.text import head_tail, one_line

RECORD_FILE = "record.json"
RUN_LOG = "run.log"
TRANSCRIPT_HEAD = 20_000
TRANSCRIPT_TAIL = 200_000
TRANSCRIPT_TAIL_CLASSIFIED = 4000
COMPILE_OUTPUT_KEPT = 8000
#: Worker files bigger than this are not copied into the record.
COPIED_FILE_LIMIT = 32 << 20


@dataclass
class AttemptRecord:
    """Everything about one attempt that is worth keeping (fields = contract §5.3 + ids)."""

    run_id: str
    node: str
    lemma: str
    attempt: int
    runner: str
    status: str
    solved: bool
    elapsed_s: float = 0.0
    cost: dict[str, Any] = field(default_factory=dict)
    evidence: str = ""
    gate_report: str = ""
    compile_output: str = ""
    gate_checks: list[dict[str, Any]] = field(default_factory=list)
    proof: str = ""
    proof_lines: int = 0
    requests: list[dict[str, str]] = field(default_factory=list)
    primary_failure: str = ""
    failure_classes: list[str] = field(default_factory=list)
    failure_evidence: str = ""
    transcript_tail: str = ""
    corpus: str = ""
    trace: dict[str, Any] = field(default_factory=dict)
    friction_classes: list[str] = field(default_factory=list)
    #: When the attempt started; filled from ``finished - elapsed`` if unset at write.
    started_at: float = 0.0
    #: The graph's attempt id (record directory key) and the design round.
    attempt_id: int = 0
    round: int = 1
    #: The runner process's exit code -- a first-class classifier input.
    exit_code: int | None = None

    def classify(self) -> AttemptRecord:
        """Classify with exactly the inputs ``pcp failures`` will use again later."""
        rec = self.to_json()
        self.friction_classes = sorted({klass for klass, _ in friction_classes(rec)})
        if self.solved:
            self.primary_failure, self.failure_classes, self.failure_evidence = "", [], ""
            return self
        c = classify_record(rec)
        self.primary_failure = c.primary
        self.failure_classes = c.classes
        self.failure_evidence = c.evidence
        return self

    def to_json(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_json(cls, data: dict[str, Any]) -> AttemptRecord:
        known = set(cls.__dataclass_fields__)
        return cls(**{k: v for k, v in data.items() if k in known})


class Recorder:
    """Writes attempt records under one run directory ``<root>/<run_id>/``."""

    def __init__(self, root: str | Path, run_id: str | None = None) -> None:
        base = Path(root)
        self.run_id = run_id or _unique_run_id(base, time.strftime("%Y%m%d-%H%M%S"))
        self.root = ensure_dir(base / self.run_id)

    def dir_for(self, lemma: str, attempt_id: int, suffix: str = "") -> Path:
        """``<run>/<lemma>.<attempt_id>[.<suffix>]`` -- unique because attempt ids are."""
        name = f"{_safe(lemma)}.{int(attempt_id)}" + (f".{_safe(suffix)}" if suffix else "")
        return self.root / name

    def write(self, record: AttemptRecord, *, workdir: str | Path | None = None, transcript: str = "", suffix: str = "") -> Path:
        out = self.dir_for(record.lemma, record.attempt_id or record.attempt, suffix)
        if (out / RECORD_FILE).exists():
            raise UsageError(f"refusing to overwrite the record at {out}")
        ensure_dir(out)
        if transcript and not record.transcript_tail:
            record.transcript_tail = transcript[-TRANSCRIPT_TAIL_CLASSIFIED:]
        record.compile_output = record.compile_output[-COMPILE_OUTPUT_KEPT:]
        if not record.started_at:
            record.started_at = time.time() - record.elapsed_s
        record.classify()
        record.proof_lines = len(record.proof.strip().splitlines()) if record.proof else 0
        json_dump(out / RECORD_FILE, record.to_json())
        if record.proof:
            atomic_write_text(out / "proof.v", record.proof)
        if record.gate_report:
            atomic_write_text(out / "gate.txt", record.gate_report)
        if record.trace:
            json_dump(out / "trace.json", record.trace)
        if transcript:
            atomic_write_text(out / "transcript.txt", head_tail(transcript, head=TRANSCRIPT_HEAD, tail=TRANSCRIPT_TAIL))
        if workdir is not None:
            for name in (TASK_FILE, NODE_FILE, ANSWER_FILE):
                copy_if_exists(Path(workdir) / name, out / name, max_bytes=COPIED_FILE_LIMIT)
        return out

    def log(self, line: str) -> Path:
        """Append one timestamped line to ``<run>/run.log``: the run's own narrative
        (a pause, a resume, a restart) next to the attempts it explains.  Plain
        ``open(..., "a")``: one writer per run, and a line lost to a crash is a line
        about the crash."""
        path = self.root / RUN_LOG
        with open(path, "a", encoding="utf-8") as fh:
            fh.write(f"{time.strftime('%Y-%m-%d %H:%M:%S')} {one_line(line, 400)}\n")
        return path

    def summary(self) -> dict[str, Any]:
        from pcp.orch.failures import summarize

        report = summarize(load_records(self.root))
        return {
            "run_id": self.run_id,
            "root": str(self.root),
            "total": report.total,
            "solved": report.solved,
            "primary": dict(report.primary),
        }


def load_records(root: str | Path) -> Iterator[dict[str, Any]]:
    """Every attempt record under ``root``, in a stable order.

    Records written before ``transcript_tail`` existed are backfilled from the
    ``transcript.txt`` next to them.  An unreadable ``record.json`` (a run killed
    mid-write, before atomic writes) is yielded as a failed, ``unreadable`` record
    rather than silently dropped from the totals.
    """
    for path in sorted(Path(root).rglob(RECORD_FILE)):
        try:
            record = json_load(path)
        except (ValueError, OSError, RecursionError) as exc:
            yield {
                "lemma": path.parent.name, "status": "error", "solved": False, "unreadable": True,
                "evidence": f"unreadable {RECORD_FILE}: {type(exc).__name__}: {exc}",
            }
            continue
        if not isinstance(record, dict):
            continue
        if not record.get("transcript_tail"):
            transcript = path.parent / "transcript.txt"
            if transcript.exists():
                record["transcript_tail"] = read_text(transcript)[-TRANSCRIPT_TAIL_CLASSIFIED:]
        yield record


def _safe(name: str) -> str:
    return "".join(c if c.isalnum() or c in "_-." else "_" for c in name)[:80]


def _unique_run_id(base: Path, stamp: str) -> str:
    """``stamp``, or ``stamp-N`` when that directory already exists.

    The run id has one-second resolution, so two runs started in the same second
    would otherwise share a record directory.  ``mkdir``
    is the claim, so two processes cannot both win the same name.
    """
    base.mkdir(parents=True, exist_ok=True)
    for n in range(1000):
        candidate = stamp if n == 0 else f"{stamp}-{n}"
        try:
            (base / candidate).mkdir()
        except FileExistsError:
            continue
        return candidate
    raise UsageError(f"{base}: could not find a free run directory for {stamp}")
