"""``pcp diagnoses``: how often each step-diagnosis class was right, from the feedback log.

The counts come from ``<workspace>/.pcp/diagnoses.jsonl`` (``pcp.state.diagnosis_log``):
every failing ``proof_step`` appends its diagnosis, and ``diagnosis_feedback`` appends
the agent's verdict.  ``--wrong`` lists the misfires, the input for tuning a heuristic.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from pcp.cli.common import absolute


def cmd_diagnoses(args: argparse.Namespace) -> int:
    from pcp.config.toolchain import project_root
    from pcp.state.diagnosis_log import class_stats, log_path, misclassified, render_stats

    ws = absolute(args.workspace) if args.workspace is not None else (project_root(Path.cwd()) or Path.cwd())
    assert ws is not None
    if args.wrong:
        rows = misclassified(ws)
        if args.json:
            print(json.dumps(rows, ensure_ascii=False, indent=2))
        elif not rows:
            print(f"no diagnosis marked wrong in {log_path(ws)}")
        for r in rows if not args.json else []:
            actual = f" (worked: {r['actual']})" if r.get("actual") else ""
            print(f"{r['id']}  {r.get('repair', '?')}{actual}  `{r.get('tactic', '')}`")
            print(f"    error: {r.get('error_excerpt', '')[:160]}")
            if r.get("note"):
                print(f"    note: {r['note']}")
        return 0
    stats = class_stats(ws, by=args.by)
    print(json.dumps(stats, indent=2) if args.json else render_stats(stats))
    return 0
