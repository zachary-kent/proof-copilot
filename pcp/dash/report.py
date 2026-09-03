"""`pcp report` -- a static HTML snapshot (PLAN.md 10).

The dashboard is optional; the summary is not.  This is the summary in a form you
can attach to something: one self-contained file, no server, no JavaScript.
"""

from __future__ import annotations

import html
import time
from pathlib import Path

from pcp.dash.serve import burndown, snapshot
from pcp.orch.graph import Graph


def write_report(graph: Graph, out: Path) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_report(graph), encoding="utf-8")
    return out


def render_report(graph: Graph) -> str:
    snap = snapshot(graph)
    b = burndown(graph)
    rows = []
    for n in snap["nodes"]:
        evidence = (
            f'<div class="ev">{html.escape(n["evidence"])}</div>' if n["evidence"] else ""
        )
        rows.append(
            f'<tr><td class="n">{html.escape(n["name"])}</td>'
            f'<td class="{html.escape(n["proof_status"])}">{html.escape(n["proof_status"])}</td>'
            f'<td>{html.escape(n["statement_status"])}@{n["epoch"]}</td>'
            f'<td>{n["attempts"]}</td></tr>'
            f'<tr><td colspan="4" class="s">{html.escape(n["statement"])}{evidence}</td></tr>'
        )
    summary = " · ".join(f"{v} {k}" for k, v in snap["summary"].items()) or "empty graph"
    return _TEMPLATE.format(
        summary=html.escape(summary),
        when=time.strftime("%Y-%m-%d %H:%M:%S"),
        discharged=b["discharged"],
        live=b["live"],
        attic=b["attic"],
        rows="\n".join(rows),
    )


_TEMPLATE = """<!doctype html>
<meta charset="utf-8"><title>pcp report</title>
<style>
 :root {{ color-scheme: light dark; }}
 body {{ font:13px/1.55 ui-monospace,Menlo,monospace; margin:2rem auto; max-width:70rem; padding:0 1rem; }}
 h1 {{ font-size:15px; }}
 table {{ border-collapse:collapse; width:100%; }}
 td {{ padding:2px 8px 2px 0; vertical-align:top; }}
 .n {{ font-weight:600; }}
 .s {{ color:#666; white-space:pre-wrap; border-bottom:1px solid #ddd; padding-bottom:6px; }}
 .ev {{ color:#b42318; white-space:pre-wrap; margin-top:4px; }}
 .integrated,.gated {{ color:#1a7f37; }}
 .stuck {{ color:#b42318; }} .contested {{ color:#b54708; }} .open {{ color:#888; }}
</style>
<h1>proof-copilot — {summary}</h1>
<p>{discharged}/{live} obligations discharged · {attic} in the attic (counts as zero progress) · {when}</p>
<table>
{rows}
</table>
"""
