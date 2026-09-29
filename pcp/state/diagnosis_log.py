"""The diagnosis log: every diagnosis, and the agent's verdict on it (D2).

The prose diagnoses are heuristics; the only way to tune them is to know when they
named the wrong repair.  So each one is appended to ``<workspace>/.pcp/diagnoses.jsonl``
with its error family, tactic, repair class and a hash/excerpt of the error, under a
short id the tool result carries.  An agent that finds the class wrong says so with
:func:`record_feedback` (exposed as the ``diagnosis_feedback`` tool), and
:func:`class_stats` turns the log into per-class hit/miss counts.

The log is written on the hot path of every failing step, so writing is one
``open(..., "a")`` of one line and **never raises**: a full disk or a read-only
workspace costs the record, not the step.  Records are append-only; feedback is its
own record that refers to a diagnosis by id, so no line is ever rewritten.
"""

from __future__ import annotations

import json
import time
import uuid
from collections import defaultdict
from pathlib import Path
from typing import Any

from pcp.config.load import state_dir
from pcp.state.diagnose import Diagnosis
from pcp.util.hashing import content_hash

LOG_NAME = Path(".pcp") / "diagnoses.jsonl"
_EXCERPT = 300
_TACTIC = 300


def log_path(workspace: Path | str) -> Path:
    return Path(workspace) / LOG_NAME


def _append(workspace: Path | str, record: dict[str, Any]) -> bool:
    try:
        path = state_dir(workspace) / LOG_NAME.name
        with path.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(record, ensure_ascii=False) + "\n")
        return True
    except Exception:  # noqa: BLE001 -- logging must never break the step it records
        return False


def record_diagnosis(workspace: Path | str | None, dx: Diagnosis, *, goal_hash: str = "") -> str:
    """Append ``dx``; return its id, or ``""`` when nothing was written."""
    if workspace is None:
        return ""
    try:
        did = uuid.uuid4().hex[:12]
        error = " ".join((dx.error or "").split())
        head = dx.tactic.split()[0] if dx.tactic.split() else ""
        record = {
            "rec": "diagnosis", "id": did, "ts": round(time.time(), 3),
            "family": dx.family, "repair": dx.repair, "confidence": dx.confidence,
            "tactic_head": head, "tactic": dx.tactic[:_TACTIC],
            "error_hash": content_hash(error, prefix="e:") if error else "",
            "error_excerpt": error[:_EXCERPT], "goal_hash": goal_hash, "evidence": list(dx.evidence)[:8],
        }
    except Exception:  # noqa: BLE001 -- same contract as _append
        return ""
    return did if _append(workspace, record) else ""


def record_feedback(workspace: Path | str, diagnosis_id: str, *, correct: bool = False, note: str = "",
                    actual: str | None = None) -> dict[str, Any]:
    """The agent's verdict on a diagnosis: was its repair class the right one?

    ``actual`` is the repair class that did work, when the agent knows it.  Returns
    ``{"ok": True, "id": ...}`` or ``{"ok": False, "error": ...}`` (an unknown id is
    reported, not raised: the tool call must not fail on a stale id).
    """
    did = str(diagnosis_id or "").strip()
    if not did:
        return {"ok": False, "error": "diagnosis id is required"}
    if not any(r.get("rec") == "diagnosis" and r.get("id") == did for r in read_log(workspace)):
        return {"ok": False, "error": f"no diagnosis {did!r} in {log_path(workspace)}"}
    record = {"rec": "feedback", "id": did, "ts": round(time.time(), 3), "correct": bool(correct),
              "note": str(note or "")[:1000], "actual": actual or None}
    if not _append(workspace, record):
        return {"ok": False, "error": f"could not write {log_path(workspace)}"}
    return {"ok": True, "id": did}


def read_log(workspace: Path | str) -> list[dict[str, Any]]:
    """Every record, oldest first; unreadable lines are skipped."""
    path = log_path(workspace)
    out: list[dict[str, Any]] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return out
    for line in lines:
        try:
            rec = json.loads(line)
        except ValueError:
            continue
        if isinstance(rec, dict):
            out.append(rec)
    return out


def _joined(workspace: Path | str) -> list[tuple[dict[str, Any], dict[str, Any] | None]]:
    """Each diagnosis with its *latest* feedback (an agent may revise its verdict)."""
    diags: dict[str, dict[str, Any]] = {}
    feedback: dict[str, dict[str, Any]] = {}
    for rec in read_log(workspace):
        if rec.get("rec") == "diagnosis" and rec.get("id"):
            diags[rec["id"]] = rec
        elif rec.get("rec") == "feedback" and rec.get("id"):
            feedback[rec["id"]] = rec
    return [(d, feedback.get(i)) for i, d in diags.items()]


def class_stats(workspace: Path | str, *, by: str = "repair") -> dict[str, dict[str, int]]:
    """Per-class counts: ``{class: {"diagnosed", "confirmed", "wrong", "unrated"}}``.

    ``by`` groups by any diagnosis field (``repair``, ``family``, ``tactic_head``,
    ``confidence``).  ``wrong`` counts feedback with ``correct=False``: the misfires
    the heuristics should be tuned against.
    """
    stats: dict[str, dict[str, int]] = defaultdict(lambda: {"diagnosed": 0, "confirmed": 0, "wrong": 0, "unrated": 0})
    for d, fb in _joined(workspace):
        row = stats[str(d.get(by) or "")]
        row["diagnosed"] += 1
        if fb is None:
            row["unrated"] += 1
        elif fb.get("correct"):
            row["confirmed"] += 1
        else:
            row["wrong"] += 1
    return dict(stats)


def misclassified(workspace: Path | str) -> list[dict[str, Any]]:
    """The diagnoses an agent marked wrong, with its note and the class that worked."""
    out = []
    for d, fb in _joined(workspace):
        if fb is not None and not fb.get("correct"):
            out.append({**d, "note": fb.get("note", ""), "actual": fb.get("actual")})
    return out


def render_stats(stats: dict[str, dict[str, int]]) -> str:
    if not stats:
        return "no diagnoses recorded"
    width = max(len(k) for k in stats) if stats else 0
    lines = [f"{'class':<{width}}  diagnosed  confirmed  wrong  unrated"]
    for key, row in sorted(stats.items(), key=lambda kv: -kv[1]["diagnosed"]):
        lines.append(f"{key or '-':<{width}}  {row['diagnosed']:>9}  {row['confirmed']:>9}  {row['wrong']:>5}  {row['unrated']:>7}")
    return "\n".join(lines)
