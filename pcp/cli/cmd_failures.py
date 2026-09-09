"""``pcp failures RUN_DIR`` (contract §1.12): a solve rate is a number, a failure
taxonomy is a work queue."""

from __future__ import annotations

import argparse

from pcp.cli.common import absolute, err
from pcp.orch.failures import TAXONOMY, summarize
from pcp.orch.record import load_records
from pcp.util.io import json_dumps


def cmd_failures(args: argparse.Namespace) -> int:
    root = absolute(args.run)
    assert root is not None
    records = list(load_records(root)) if root.exists() else []
    if not records:
        err(f"no records under {root}")
        return 2
    klass = getattr(args, "klass", None)
    if klass:
        if klass not in TAXONOMY:
            err(f"unknown class {klass!r}; one of: {', '.join(TAXONOMY)}")
            return 2
        shown = 0
        for rec in records:
            if rec.get("solved") or klass not in (rec.get("failure_classes") or []):
                continue
            shown += 1
            print(f"--- {rec.get('lemma', '?')} attempt {rec.get('attempt', '?')} ({rec.get('status', '?')})")
            print(f"    {str(rec.get('failure_evidence', ''))[:300]}")
            if rec.get("evidence"):
                print("    evidence: " + " ".join(str(rec["evidence"]).split())[:300])
        print(f"\n{shown} record(s) in class {klass}")
        return 0
    report = summarize(records)
    if args.json:
        print(json_dumps({
            "total": report.total, "solved": report.solved,
            "primary": dict(report.primary), "all_classes": dict(report.all_classes),
        }))
        return 0
    print(report.render(limit=args.examples))
    return 0
