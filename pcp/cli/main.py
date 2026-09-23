"""The ``pcp`` command: parser and dispatch only.  Each subcommand lives in its own module.

Modules are imported lazily per subcommand so that ``pcp prove`` never loads the state
layer and ``pcp trace`` never loads the orchestrator (docs/ARCHITECTURE.md 1).
"""

from __future__ import annotations

import argparse
import importlib
import sys
from pathlib import Path

from pcp import __version__
from pcp.cli.common import run_command
from pcp.config.schema import EFFORT_LEVELS

DEFAULT_GRAPH = Path(".pcp/graph.db")
DEFAULT_WORKROOT = Path(".pcp/work")


def _dispatch(module: str, func: str):
    def run(args: argparse.Namespace) -> int:
        mod = importlib.import_module(f"pcp.cli.{module}")
        return getattr(mod, func)(args)

    return run


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="pcp", description="proof-copilot: Iris proof state and orchestration")
    p.add_argument("--version", action="version", version=f"pcp {__version__}")
    sub = p.add_subparsers(dest="command")

    # ---------------------------------------------------------------- orchestrator
    prove = sub.add_parser("prove", help="prove a lemma from a plan (the daily loop)")
    prove.add_argument("file", type=Path)
    prove.add_argument("lemma")
    prove.add_argument("--plan", type=Path, help=".v file of child statements")
    prove.add_argument("--runner", default="auto", help="auto | codex | claude | claude-code | direct | mock")
    prove.add_argument("--model", default=None, help="alias for --prover-model")
    prove.add_argument("--prover-model", default=None, metavar="MODEL",
                       help="model for the prover role (default: the provider's prover tier)")
    prove.add_argument("--decomposer", default=None, metavar="MODEL",
                       help="model for the decomposer role (Read/Glob/Grep only; it cannot prove)")
    prove.add_argument("--decomposer-effort", default=None, choices=EFFORT_LEVELS,
                       help="default: xhigh — a bad plan is the most expensive error there is")
    prove.add_argument("--approver-effort", default=None, choices=EFFORT_LEVELS,
                       help="effort for the approver that adjudicates amendment requests and contests "
                            "(default: medium — a yes/no on one conjunct, not a design)")
    prove.add_argument("--prover-effort", default=None, choices=EFFORT_LEVELS,
                       help="default: medium — the bulk tier buys attempts, not thinking")
    prove.add_argument("--concurrency", type=int, default=None)
    prove.add_argument("--node-seconds", type=float, default=900.0, help="per-attempt wall clock for a worker")
    prove.add_argument("--decomposer-seconds", type=float, default=None,
                       help="deadline for a design round (default 1800)")
    prove.add_argument("--attempts", type=int, default=2, help="attempts per node (1 dispatch + retries)")
    prove.add_argument("--design-rounds", type=int, default=3, metavar="N",
                       help="how many times the design may be revised after failed proofs (default 3)")
    prove.add_argument("--amendments", type=int, default=6, metavar="N",
                       help="definition amendments provers may have applied per run -- a strengthening that "
                            "compiles is applied and replayed without a design round; 0 disables (default 6)")
    prove.add_argument("--review-after", type=int, default=2, metavar="N",
                       help="after N failed attempts at a statement, hand the node to the approver instead of "
                            "retrying (0: never; needs an approver and --amendments > 0); a verdict costs "
                            "seconds where an attempt costs the node's clock")
    prove.add_argument("--approver-seconds", type=float, default=600.0, metavar="S",
                       help="deadline for one approver verdict on an amendment or a contest (default 600)")
    prove.add_argument("--state-tools", nargs="?", const="all", default=None,
                       help="grant provers the `pcp mcp` proof-state tools: bare flag for all, or a comma list")
    prove.add_argument("--library", action="append", default=None, metavar="DIR",
                       help="a directory bound read-only into every worker sandbox and named in the packet (repeatable)")
    prove.add_argument("--graph", type=Path, default=DEFAULT_GRAPH)
    prove.add_argument("--workroot", type=Path, default=DEFAULT_WORKROOT)
    prove.add_argument("--fresh", action="store_true", help="discard any existing graph and workroot first")
    prove.add_argument("--intent", default="", help="two-line intent brief carried to every worker")
    prove.add_argument("--sandbox", action="store_true",
                       help="run every worker inside bubblewrap (masked $HOME, read-only repo, answer key hidden)")
    prove.add_argument("--reference", type=Path, default=Path(".pcp/reference"),
                       help="answer-key directory to hide from sandboxed workers")
    prove.add_argument("--record", type=Path, default=None, metavar="DIR",
                       help="record every attempt under DIR/<run-id>/ (see `pcp failures`)")
    prove.add_argument("--corpus", default="", help="corpus label recorded with each attempt")
    prove.add_argument("--brief", default="full", choices=["full", "spec-only"],
                       help="what the design brief tells workers: `spec-only` hides role notes and hints")
    prove.add_argument("--no-orchestration", action="store_true",
                       help="allow a single prover to take the whole goal (default: orchestration required)")
    prove.add_argument("--pause-hours", type=float, default=12.0, metavar="H",
                       help="on a provider outage (revoked login, usage window, unreachable API) pause the run and "
                            "probe until it is back, for up to H hours; 0 parks the affected nodes instead (default 12)")
    prove.add_argument("--supervise", action="store_true",
                       help="run detached under a supervisor that restarts the run after a crash and prints the "
                            "pid and log to follow")
    prove.add_argument("--max-restarts", type=int, default=20, metavar="N",
                       help="with --supervise: restarts before giving up (default 20)")
    prove.add_argument("--record-run-id", default=None, metavar="ID",
                       help="with --record: reuse DIR/ID instead of a fresh timestamped run directory")
    prove.add_argument("--supervised-child", type=Path, default=None, metavar="DIR", help=argparse.SUPPRESS)
    prove.add_argument("--outcome-file", type=Path, default=None, metavar="FILE", help=argparse.SUPPRESS)
    prove.add_argument("--config", type=Path, default=None, help="config file (default .pcp/config.toml)")
    prove.add_argument("--json", action="store_true")
    prove.set_defaults(func=_dispatch("cmd_prove", "cmd_prove"))

    check = sub.add_parser("check", help="run the deterministic gate on a proof body (workers use this)")
    check.add_argument("body_positional", nargs="?", default=None, metavar="BODY",
                       help="file with the proof body ('-' for stdin); same as --body")
    check.add_argument("--dir", type=Path, default=Path("."))
    check.add_argument("--body", type=Path, default=None, help="file with the proof body ('-' for stdin)")
    check.add_argument("--json", action="store_true")
    check.add_argument("--unused-premises", action="store_true", help="also run the removal probe (slow)")
    check.add_argument("--design", action="store_true",
                       help="check the whole edited file against the design contract instead of one body")
    check.add_argument("--full", action="store_true", help="compile every other proof in the file too (slow)")
    check.add_argument("--diagnose", dest="diagnose", action="store_true", default=None,
                       help="on a compile failure, replay through petanque and report the goal at the failing tactic")
    check.add_argument("--no-diagnose", dest="diagnose", action="store_false", help="never replay")
    check.set_defaults(func=_dispatch("cmd_check", "cmd_check"))

    status = sub.add_parser("status", help="one-screen summary of the graph")
    status.add_argument("--graph", type=Path, default=DEFAULT_GRAPH)
    status.add_argument("--json", action="store_true")
    status.set_defaults(func=_dispatch("cmd_status", "cmd_status"))

    handoff = sub.add_parser("handoff", help="emit a .v for a stuck node, with evidence as comments")
    handoff.add_argument("node")
    handoff.add_argument("--graph", type=Path, default=DEFAULT_GRAPH)
    handoff.add_argument("-o", "--out", type=Path, default=None)
    handoff.set_defaults(func=_dispatch("cmd_status", "cmd_handoff"))

    serve = sub.add_parser("serve", help="localhost dashboard over the graph (SSE)")
    serve.add_argument("--graph", type=Path, default=DEFAULT_GRAPH)
    serve.add_argument("--port", type=int, default=8765)
    serve.add_argument("--host", default="127.0.0.1")
    serve.set_defaults(func=_dispatch("cmd_dash", "cmd_serve"))

    report = sub.add_parser("report", help="static HTML snapshot of the graph")
    report.add_argument("--graph", type=Path, default=DEFAULT_GRAPH)
    report.add_argument("-o", "--out", type=Path, default=Path(".pcp/report.html"))
    report.set_defaults(func=_dispatch("cmd_dash", "cmd_report"))

    sketch = sub.add_parser("sketch", help="compile a CSL proof sketch into frozen obligations")
    sketch.add_argument("file", type=Path)
    sketch.add_argument("--out", type=Path, default=Path("plan.v"))
    sketch.add_argument("--json", action="store_true")
    sketch.set_defaults(func=_dispatch("cmd_sketch", "cmd_sketch"))

    failures = sub.add_parser("failures", help="classify recorded attempts by failure mode")
    failures.add_argument("run", type=Path, help="a run directory written by --record")
    failures.add_argument("--json", action="store_true")
    failures.add_argument("--examples", type=int, default=3)
    failures.add_argument("--class", dest="klass", default=None,
                          help="show every record in one class instead of a summary")
    failures.set_defaults(func=_dispatch("cmd_failures", "cmd_failures"))

    models = sub.add_parser("models", help="show which model each role will use, and why")
    models.add_argument("--example", action="store_true", help="print a starting .pcp/config.toml and exit")
    models.add_argument("--config", type=Path, default=None)
    models.set_defaults(func=_dispatch("cmd_doctor", "cmd_models"))

    doctor = sub.add_parser("doctor", help="check the toolchain, its pins, packaged assets and provider logins")
    doctor.add_argument("--config", type=Path, default=None)
    doctor.set_defaults(func=_dispatch("cmd_doctor", "cmd_doctor"))

    setup = sub.add_parser("setup", help="build the pinned Rocq/Iris/coq-lsp opam switch (idempotent)")
    setup.add_argument("--dry-run", action="store_true", help="print the opam commands that would run, change nothing")
    setup.add_argument("--switch", default=None, metavar="NAME",
                       help="opam switch to build (default: $PCP_OPAM_SWITCH, else the pinned name `pcp`)")
    setup.add_argument("--jobs", type=int, default=None, metavar="N", help="parallel opam jobs (default: all cores)")
    setup.add_argument("--force", action="store_true", help="run the script even when every pin already matches")
    setup.set_defaults(func=_dispatch("cmd_setup", "cmd_setup"))

    envp = sub.add_parser("env", help='print shell exports for the pinned switch: eval "$(pcp env)"')
    envp.add_argument("--switch", default=None, metavar="NAME", help="default: $PCP_OPAM_SWITCH, else `pcp`")
    envp.set_defaults(func=_dispatch("cmd_setup", "cmd_env"))

    init = sub.add_parser("init", help="make a directory a pcp project: write .pcp/config.toml, git-ignore .pcp/")
    init.add_argument("dir", nargs="?", type=Path, default=None, help="project directory (default: .)")
    init.add_argument("--force", action="store_true", help="overwrite an existing .pcp/config.toml")
    init.set_defaults(func=_dispatch("cmd_init", "cmd_init"))

    integ = sub.add_parser("integrate", help="print (or --write) the pcp MCP server config for Claude Code / "
                                              "Codex, or an AGENTS.md block (docs/INTEGRATIONS.md)")
    integ.add_argument("target", choices=["claude", "codex", "agents-md"])
    integ.add_argument("--write", action="store_true",
                       help="merge into the config instead of printing: claude -> DIR/.mcp.json (needs --project); "
                            "codex -> ~/.codex/config.toml, or DIR/.codex/config.toml with --project; "
                            "agents-md -> DIR/AGENTS.md (default DIR: .)")
    integ.add_argument("--project", type=Path, default=None, metavar="DIR",
                       help="project-scoped config in DIR (committable: runs bare `pcp`, not this machine's path)")
    integ.add_argument("--pcp", default=None, metavar="CMD",
                       help="command the client runs (default: this pcp's absolute path; `pcp` with --project)")
    integ.add_argument("--force", action="store_true", help="replace an existing, different pcp entry")
    integ.set_defaults(func=_dispatch("cmd_integrate", "cmd_integrate"))

    skill = sub.add_parser("skill", help="print a packaged worker skill: the norms provers are given")
    skill.add_argument("action", choices=["list", "show"])
    skill.add_argument("name", nargs="?", default=None, help="prover | logatom | invariants | decomposer")
    skill.set_defaults(func=_dispatch("cmd_integrate", "cmd_skill"))

    # ------------------------------------------------------------------ state layer
    trace = sub.add_parser("trace", help="tactic-by-tactic Iris state dump (JSONL)")
    trace.add_argument("file", type=Path)
    trace.add_argument("lemma")
    trace.add_argument("--script", type=Path, default=None, help="file of tactics, one per line")
    trace.add_argument("-o", "--out", type=Path, default=None)
    trace.add_argument("--reflect", action="store_true", help="use the Ltac2 iDump path")
    trace.add_argument("--oracle", action="store_true", help="run the persistence oracle per step")
    trace.set_defaults(func=_dispatch("cmd_trace", "cmd_trace"))

    state = sub.add_parser("state", help="budgeted render of a traced state")
    state.add_argument("trace", type=Path)
    state.add_argument("--step", type=int, default=None)
    state.add_argument("--select", default=None)
    state.add_argument("--mode", default="full", choices=["full", "folded", "summary", "hash-only"])
    state.add_argument("--budget", type=int, default=4000)
    state.add_argument("--all", action="store_true", help="disable diff-only")
    state.set_defaults(func=_dispatch("cmd_trace", "cmd_state"))

    ledger = sub.add_parser("ledger", help="query the resource ledger of a trace")
    ledger.add_argument("trace", type=Path)
    ledger.add_argument("query", choices=["events", "where", "blame", "leftovers", "unused"])
    ledger.add_argument("--hyp", default=None)
    ledger.add_argument("--step", type=int, default=None)
    ledger.set_defaults(func=_dispatch("cmd_trace", "cmd_ledger"))

    destruct = sub.add_parser("destruct", help="compile an iDestruct pattern, or diagnose one")
    destruct.add_argument("prop")
    destruct.add_argument("--pattern", default=None, help="check this pattern instead of synthesising one")
    destruct.add_argument("--name", default="H")
    destruct.set_defaults(func=_dispatch("cmd_trace", "cmd_destruct"))

    mcp = sub.add_parser("mcp", help="run the MCP server on stdio")
    mcp.add_argument("--workspace", type=Path, default=Path("."))
    mcp.set_defaults(func=_dispatch("cmd_mcp", "cmd_mcp"))

    docs = sub.add_parser("docs", help="build a local, grep-able index of the installed Rocq libraries")
    docs.add_argument("-o", "--out", type=Path, default=Path(".pcp/docs/index.txt"))
    docs.add_argument("--libraries", nargs="+", default=["iris", "stdpp"])
    docs.set_defaults(func=_dispatch("cmd_doctor", "cmd_docs"))

    return p


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    raw = list(sys.argv[1:] if argv is None else argv)
    args = parser.parse_args(raw)
    # The command line as typed: ``pcp prove --supervise`` re-execs exactly this.
    args.raw_argv = raw
    if not getattr(args, "func", None):
        parser.print_help()
        return 1
    return run_command(args.func, args)


if __name__ == "__main__":
    sys.exit(main())
