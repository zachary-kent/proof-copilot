"""Durable per-attempt records, for failure analysis (PLAN.md 13).

"Every real session writes to `.pcp/traces/`. That is your regression corpus, your
debugging record, and -- later -- training data."

A solve rate tells you whether the tooling helped.  It does not tell you *what to
build next*, and that is the question a benchmark run is actually being asked.  So
every attempt -- successful or not -- leaves behind the exact packet the worker saw,
what it sent back, what the gate said, and a classification of how it failed.

The records are plain files on purpose.  They outlive this tool, they diff, and a
human can read one without a viewer.
"""

from __future__ import annotations

import json
import shutil
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Iterator

from pcp.orch.failures import classify

RECORD_FILE = "record.json"


@dataclass
class AttemptRecord:
    """Everything about one worker attempt that is worth keeping."""

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
    #: Tail of the worker's transcript.  Classified alongside the evidence, because
    #: an infrastructure failure shows up here and nowhere else.
    transcript_tail: str = ""
    corpus: str = ""
    #: The worker's own trace: turns, tool calls, tokens, friction.
    trace: dict[str, Any] = field(default_factory=dict)
    #: Failure classes the worker hit *and recovered from* on its way to a solve.
    friction_classes: list[str] = field(default_factory=list)
    started_at: float = field(default_factory=time.time)

    def classify(self) -> "AttemptRecord":
        # Errors a worker recovered from are classified whether or not it solved.
        # A lemma proved after six turns of mask arithmetic is the strongest signal
        # there is about what to build next, and scoring it only as "solved" throws
        # that away.
        self.friction_classes = sorted({
            klass
            for err in (self.trace or {}).get("errors", [])
            for klass in classify(err).classes
        })
        if self.solved:
            self.primary_failure = ""
            self.failure_classes = []
            return self
        c = classify(
            self.evidence, self.gate_report, self.compile_output,
            context=self.transcript_tail,
            status=self.status,
        )
        self.primary_failure = c.primary
        self.failure_classes = c.classes
        self.failure_evidence = c.findings[0].evidence if c.findings else ""
        return self

    def to_json(self) -> dict[str, Any]:
        return asdict(self)


class Recorder:
    """Writes attempt records under one run directory."""

    def __init__(self, root: Path, run_id: str | None = None) -> None:
        self.run_id = run_id or time.strftime("%Y%m%d-%H%M%S")
        self.root = Path(root) / self.run_id
        self.root.mkdir(parents=True, exist_ok=True)

    def dir_for(self, lemma: str, attempt: int) -> Path:
        path = self.root / f"{_safe(lemma)}.{attempt}"
        path.mkdir(parents=True, exist_ok=True)
        return path

    def write(
        self,
        record: AttemptRecord,
        *,
        workdir: Path | None = None,
        transcript: str = "",
    ) -> Path:
        if transcript and not record.transcript_tail:
            record.transcript_tail = transcript[-4000:]
        record.classify()
        record.proof_lines = len(record.proof.strip().splitlines()) if record.proof else 0
        out = self.dir_for(record.lemma, record.attempt)
        (out / RECORD_FILE).write_text(json.dumps(record.to_json(), indent=2, default=str), encoding="utf-8")
        if record.proof:
            (out / "proof.v").write_text(record.proof, encoding="utf-8")
        if record.gate_report:
            (out / "gate.txt").write_text(record.gate_report, encoding="utf-8")
        if record.trace:
            (out / "trace.json").write_text(
                json.dumps(record.trace, indent=2, default=str), encoding="utf-8"
            )
        if transcript:
            # Keep the head as well as the tail: the CLI reports MCP server status in
            # its very first event, and a tail-only transcript hid a server that was
            # failing to start on every run.
            (out / "transcript.txt").write_text(_clip(transcript), encoding="utf-8")
        if workdir is not None:
            # The packet is the worker's whole world; keeping it is what makes a
            # failure reproducible six weeks later.
            for name in ("TASK.md", "pcp-node.json", "answer.json"):
                src = Path(workdir) / name
                if src.exists():
                    shutil.copy2(src, out / name)
        return out

    def summary(self) -> dict[str, Any]:
        records = list(load_records(self.root))
        from pcp.orch.failures import summarize

        report = summarize(records)
        return {
            "run_id": self.run_id,
            "root": str(self.root),
            "total": report.total,
            "solved": report.solved,
            "primary": dict(report.primary),
        }


def load_records(root: Path) -> Iterator[dict[str, Any]]:
    """Every attempt record under ``root``, in a stable order.

    Records written before ``transcript_tail`` existed are backfilled from the
    ``transcript.txt`` next to them, so an old run reclassifies under new rules
    instead of being stuck with the verdict it got on the day.
    """
    for path in sorted(Path(root).rglob(RECORD_FILE)):
        try:
            record = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            continue
        if not record.get("transcript_tail"):
            transcript = path.parent / "transcript.txt"
            if transcript.exists():
                record["transcript_tail"] = transcript.read_text(encoding="utf-8")[-4000:]
        yield record


def _clip(text: str, head: int = 20_000, tail: int = 200_000) -> str:
    if len(text) <= head + tail:
        return text
    return text[:head] + f"\n\n… [{len(text) - head - tail} chars elided] …\n\n" + text[-tail:]


def _safe(name: str) -> str:
    return "".join(c if c.isalnum() or c in "_-." else "_" for c in name)[:80]
