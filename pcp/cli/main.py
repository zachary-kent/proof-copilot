"""The `pcp` command line.

Two products, one binary.  ``prove`` / ``status`` / ``handoff`` / ``check`` drive the
orchestrator; ``trace`` / ``state`` / ``ledger`` / ``destruct`` drive the state layer.
They share nothing but the executable, which is the point (PLAN.md 0).
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any

from pcp import __version__
from pcp.orch.providers import EFFORT_LEVELS as EFFORT_CHOICES


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if not getattr(args, "func", None):
        parser.print_help()
        return 1
    try:
        return int(args.func(args) or 0)
    except KeyboardInterrupt:
        print("interrupted", file=sys.stderr)
        return 130
    except SystemExit as exc:
        if exc.code in (0, None):
            return 0
        print(exc, file=sys.stderr)
        # `SystemExit("message")` is the normal way this codebase aborts with an
        # explanation; `int()` on it raised ValueError and buried the explanation
        # under a traceback.
        return exc.code if isinstance(exc.code, int) else 1


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
    prove.add_argument("--model", default=None)
    prove.add_argument("--concurrency", type=int, default=None)
    prove.add_argument("--node-seconds", type=float, default=900.0)
    prove.add_argument("--state-tools", nargs="?", const="all", default=None,
                       help="grant provers the `pcp mcp` proof-state tools "
                            "(default: off). `--state-tools` for all of them, or a "
                            "comma-separated subset. The off/on pair is the ablation.")
    prove.add_argument("--library", action="append", default=None, metavar="DIR",
                       help="a directory bound read-only into every worker sandbox: "
                            "prior rungs' own solutions, papers. Repeatable. Nothing "
                            "is given by default; a corpus reference must never go here.")
    prove.add_argument("--decomposer-seconds", type=float, default=None,
                       help="deadline for a design round (default: 1800 — the design "
                            "step is one-shot, and there is no partial credit)")
    prove.add_argument("--attempts", type=int, default=2, help="attempts per node (1 dispatch + retries)")
    prove.add_argument("--graph", type=Path, default=Path(".pcp/graph.db"))
    prove.add_argument("--workroot", type=Path, default=Path(".pcp/work"))
    prove.add_argument("--intent", default="", help="two-line intent brief carried to every worker")
    prove.add_argument("--fresh", action="store_true", help="discard any existing graph and start over")
    prove.add_argument(
        "--sandbox", action="store_true",
        help="run every worker inside bubblewrap: masked $HOME, read-only repo, the "
        "answer key hidden, code forges and search engines blackholed. Use this for "
        "benchmarks on public developments.",
    )
    prove.add_argument("--reference", type=Path, default=Path(".pcp/reference"),
                       help="answer-key directory to hide from sandboxed workers")
    prove.add_argument("--record", type=Path, default=None, metavar="DIR",
                       help="record every attempt for failure analysis (see `pcp failures`)")
    prove.add_argument("--corpus", default="", help="corpus label recorded with each attempt")
    prove.add_argument(
        "--decomposer", default=None, metavar="MODEL",
        help="model for the decomposer role. Granted Read/Glob/Grep only -- it cannot "
        "write, edit or execute, so it cannot do proof engineering. Defaults to the "
        "detected provider's decomposer tier.",
    )
    prove.add_argument(
        "--prover-model", default=None, metavar="MODEL",
        help="model for the prover role (default: the detected provider's prover tier)",
    )
    prove.add_argument(
        "--design-rounds", type=int, default=3, metavar="N",
        help="how many times the design may be revised in the light of a failure "
        "(default 3). A design that needs a fourth revision is a design problem.",
    )
    prove.add_argument("--decomposer-effort", default=None, choices=EFFORT_CHOICES,
                       help="default: xhigh — a bad plan is the most expensive error there is")
    prove.add_argument("--prover-effort", default=None, choices=EFFORT_CHOICES,
                       help="default: medium — the bulk tier buys attempts, not thinking")
    prove.add_argument(
        "--no-orchestration", action="store_true",
        help="allow a single prover to take the whole goal. Off by default: an "
        "unorchestrated run is not measuring the pipeline.",
    )
    prove.add_argument("--json", action="store_true")
    prove.set_defaults(func=cmd_prove)

    check = sub.add_parser("check", help="run the deterministic gate on a proof body (workers use this)")
    check.add_argument("body_positional", nargs="?", default=None, metavar="BODY",
                       help="file with the proof body ('-' for stdin); same as --body")
    check.add_argument("--dir", type=Path, default=Path("."))
    check.add_argument("--body", type=Path, default=None, help="file with the proof body ('-' for stdin)")
    check.add_argument("--json", action="store_true")
    check.add_argument("--unused-premises", action="store_true", help="also run the removal probe (slow)")
    check.add_argument(
        "--design", action="store_true",
        help="check the whole file rather than one proof body. For a design task, "
        "where filling in the invariant means editing definitions; the contract "
        "decides what may change.",
    )
    check.add_argument(
        "--full",
        action="store_true",
        help="compile every other proof in the file too (slow; the orchestrator does "
        "this at integration, not per node)",
    )
    # Tri-state on purpose. Left alone, the packet decides -- so the state layer
    # stays inside the arm that was granted it and an ablation keeps its meaning.
    check.add_argument(
        "--diagnose", dest="diagnose", action="store_true", default=None,
        help="on a compile failure, replay the proof through petanque and report the "
        "Iris goal as it stood at the failing tactic (default: on when the packet "
        "granted the state tools)",
    )
    check.add_argument(
        "--no-diagnose", dest="diagnose", action="store_false",
        help="never replay; report the compiler output alone",
    )
    check.set_defaults(func=cmd_check)

    status = sub.add_parser("status", help="one-screen summary of the graph")
    status.add_argument("--graph", type=Path, default=Path(".pcp/graph.db"))
    status.add_argument("--json", action="store_true")
    status.set_defaults(func=cmd_status)

    handoff = sub.add_parser("handoff", help="emit a .v for a stuck node, with evidence as comments")
    handoff.add_argument("node")
    handoff.add_argument("--graph", type=Path, default=Path(".pcp/graph.db"))
    handoff.add_argument("-o", "--out", type=Path, default=None)
    handoff.set_defaults(func=cmd_handoff)

    serve = sub.add_parser("serve", help="localhost dashboard over the graph (SSE)")
    serve.add_argument("--graph", type=Path, default=Path(".pcp/graph.db"))
    serve.add_argument("--port", type=int, default=8765)
    serve.add_argument("--host", default="127.0.0.1")
    serve.set_defaults(func=cmd_serve)

    report = sub.add_parser("report", help="static HTML snapshot of the graph")
    report.add_argument("--graph", type=Path, default=Path(".pcp/graph.db"))
    report.add_argument("-o", "--out", type=Path, default=Path(".pcp/report.html"))
    report.set_defaults(func=cmd_report)

    sketch = sub.add_parser("sketch", help="compile a CSL proof sketch into frozen obligations")
    sketch.add_argument("file", type=Path)
    sketch.add_argument("--out", type=Path, default=Path("plan.v"))
    sketch.add_argument("--json", action="store_true")
    sketch.set_defaults(func=cmd_sketch)

    # ------------------------------------------------------------------ state layer
    trace = sub.add_parser("trace", help="tactic-by-tactic Iris state dump (JSONL)")
    trace.add_argument("file", type=Path)
    trace.add_argument("lemma")
    trace.add_argument("--script", type=Path, default=None, help="file of tactics, one per line")
    trace.add_argument("-o", "--out", type=Path, default=None)
    trace.add_argument("--reflect", action="store_true", help="use the Ltac2 iDump path")
    trace.add_argument("--oracle", action="store_true", help="run the persistence oracle per step")
    trace.set_defaults(func=cmd_trace)

    state = sub.add_parser("state", help="budgeted render of a traced state")
    state.add_argument("trace", type=Path)
    state.add_argument("--step", type=int, default=None)
    state.add_argument("--select", default=None)
    state.add_argument("--mode", default="full", choices=["full", "folded", "summary", "hash-only"])
    state.add_argument("--budget", type=int, default=4000)
    state.add_argument("--all", action="store_true", help="disable diff-only")
    state.set_defaults(func=cmd_state)

    ledger = sub.add_parser("ledger", help="query the resource ledger of a trace")
    ledger.add_argument("trace", type=Path)
    ledger.add_argument("query", choices=["events", "where", "blame", "leftovers", "unused"])
    ledger.add_argument("--hyp", default=None)
    ledger.add_argument("--step", type=int, default=None)
    ledger.set_defaults(func=cmd_ledger)

    destruct = sub.add_parser("destruct", help="compile an iDestruct pattern, or diagnose one")
    destruct.add_argument("prop")
    destruct.add_argument("--pattern", default=None, help="check this pattern instead of synthesising one")
    destruct.add_argument("--name", default="H")
    destruct.set_defaults(func=cmd_destruct)

    mcp = sub.add_parser("mcp", help="run the MCP server on stdio")
    mcp.add_argument("--workspace", type=Path, default=Path("."))
    mcp.set_defaults(func=cmd_mcp)

    failures = sub.add_parser("failures", help="classify recorded attempts by failure mode")
    failures.add_argument("run", type=Path, help="a run directory written by --record")
    failures.add_argument("--json", action="store_true")
    failures.add_argument("--examples", type=int, default=3)
    failures.add_argument("--class", dest="klass", default=None,
                          help="show every record in one class instead of a summary")
    failures.set_defaults(func=cmd_failures)

    docs = sub.add_parser("docs", help="build a local, grep-able index of the installed Rocq libraries")
    docs.add_argument("-o", "--out", type=Path, default=Path(".pcp/docs/index.txt"))
    docs.add_argument("--libraries", nargs="+", default=["iris", "stdpp"])
    docs.set_defaults(func=cmd_docs)

    models = sub.add_parser("models", help="show which model each role will use, and why")
    models.add_argument("--example", action="store_true",
                        help="print a starting .pcp/config.toml and exit")
    models.set_defaults(func=cmd_models)

    doctor = sub.add_parser("doctor", help="check the toolchain and provider logins")
    doctor.set_defaults(func=cmd_doctor)

    return p


# ------------------------------------------------------------------------- prove

def _pick_runner(
    name: str,
    model: str | None,
    *,
    sandbox: bool = False,
    reference: Path | None = None,
    mcp_tools: list[str] | None = None,
    role: str = "prover",
    effort: str | None = None,
    corpus: Path | None = None,
    library: list[Path] | None = None,
):
    from pcp.orch.runners.claude_code import ClaudeCodeSubagentRunner
    from pcp.orch.runners.cli import claude_headless_runner, codex_cli_runner
    from pcp.orch.runners.direct import DirectAPIRunner
    from pcp.orch.runners.mock import MockRunner

    from pcp.orch.providers import resolve_effort

    provider_of = {"claude": "anthropic", "claude-code": "anthropic", "direct": "anthropic",
                   "codex": "codex", "mock": "mock"}
    effort = effort or resolve_effort(role)
    # Inside bubblewrap the sandbox *is* the containment: the worker has no network
    # to the forges, a read-only repo and one writable directory.  Leaving the CLI's
    # own permission prompts on top of that only costs turns -- a real run lost one
    # to `rm -f probe.v probe.vo …` being held for approval.
    permission_mode = "bypassPermissions" if sandbox else "acceptEdits"
    KNOWN = ("codex", "claude", "claude-code", "direct", "mock")
    notes: dict[str, str | None] = {}

    def build(candidate: str):
        # The tier is resolved per *candidate*, because which provider is in play is
        # exactly what `auto` decides.  Resolving it only for an explicit --runner
        # meant the common `auto` path silently ignored the configured tier and ran
        # on whatever the CLI defaults to -- so `pcp models` advertised one model and
        # the run recorded another, which makes two runs incomparable.
        pinned, note = _model_for(role, provider_of.get(candidate, "anthropic"))
        chosen = model or pinned
        notes[candidate] = None if model else note
        if candidate == "codex":
            return codex_cli_runner(chosen)
        if candidate == "claude":
            return claude_headless_runner(
                chosen, mcp_tools=mcp_tools, permission_mode=permission_mode, effort=effort
            )
        if candidate == "claude-code":
            return ClaudeCodeSubagentRunner(model=chosen)
        if candidate == "direct":
            return DirectAPIRunner(model=chosen or DirectAPIRunner.model)
        return MockRunner()

    def selected(runner, candidate: str):
        if notes.get(candidate):
            print(notes[candidate], file=sys.stderr)
        return _maybe_sandbox(runner, candidate, sandbox, reference, corpus, library)

    if name != "auto":
        if name not in KNOWN:
            raise SystemExit(f"unknown runner {name!r}; choose from {', '.join(KNOWN)}")
        return selected(build(name), name)
    # Priority order from PLAN.md 11: the flat-rate workhorse first, metered last.
    for candidate in ("codex", "claude", "claude-code", "direct"):
        runner = build(candidate)
        if runner.available():
            return selected(runner, candidate)
    raise SystemExit(
        "no runner is available. Install one of `codex` or `claude`, or set "
        "ANTHROPIC_API_KEY for --runner direct. `pcp doctor` shows what is missing."
    )


def _model_flag(value: str | None, flag: str, provider: str = "anthropic") -> str | None:
    """Accept a model flag in either the bare or the `provider/model` form.

    `pcp models` prints bindings as `anthropic/claude-opus-5`, and the config pins
    them the same way, so that is the form a user has in front of them when they
    reach for `--decomposer`. Passing it through verbatim reaches the CLI as
    `--model anthropic/claude-opus-5`, which it rejects -- and the run dies at the
    first decomposition with "no JSON object to read", which reads like a decomposer
    fault rather than a typo in a flag.
    """
    if not value:
        return value
    head, sep, tail = value.partition("/")
    if not sep:
        return value
    if head != provider:
        raise SystemExit(
            f"{flag} names provider {head!r}, but this run uses {provider!r}. "
            f"Pass a {provider} model, or change the runner."
        )
    return tail


#: Every tool `pcp mcp` exposes. Named here rather than discovered so that an
#: ablation is reproducible: what "tools on" meant is recorded in the source, not in
#: whatever the server happened to register that day.
STATE_TOOLS = (
    "proof_open", "proof_step", "proof_state", "proof_trace", "proof_ledger",
    "proof_try", "proof_destruct", "premise_search", "notation_resolve", "verify_node",
)


def _state_tools(value: str | None) -> list[str]:
    """Resolve `--state-tools` to the tool names granted to each prover."""
    if value is None:
        return []
    if value in ("all", ""):
        return list(STATE_TOOLS)
    chosen = [t.strip() for t in value.split(",") if t.strip()]
    unknown = [t for t in chosen if t not in STATE_TOOLS]
    if unknown:
        raise SystemExit(
            f"unknown state tool(s): {', '.join(unknown)}. "
            f"Choose from: {', '.join(STATE_TOOLS)}"
        )
    return chosen


def _library(values: list[str] | None) -> list[Path]:
    """Resolve `--library` to directories bound read-only into every sandbox.

    A ladder rung is allowed what a person doing the same ladder would have: their
    own earlier solutions, and published reading. Both are opt-in and named on the
    command line, because the default must stay "nothing" -- an accidental library
    is indistinguishable from a leak.
    """
    out: list[Path] = []
    for value in values or []:
        path = Path(value).expanduser().resolve()
        if not path.exists():
            raise SystemExit(f"--library {value}: no such path")
        out.append(path)
    return out


def _model_for(role: str, provider: str = "anthropic") -> tuple[str | None, str | None]:
    """The configured model for a role, and the line to report about it.

    A tier binding names a provider *and* a model. Applying the model without
    checking the provider would hand `--model luna` to the Claude CLI because the
    prover tier happens to be `codex/luna` -- a config-shaped way to break a run.

    The note is *returned* rather than printed. `auto` builds every candidate in
    priority order to find out which is installed, so printing from here announced
    a fallback for a provider the run then never used, and contradicted itself one
    line later with the truth. Only the selected candidate's note is worth saying.
    """
    from pcp.orch.providers import resolve

    binding = resolve(role)
    if binding is None:
        return None, None
    if binding.provider != provider:
        return None, (
            f"{role}: config binds {binding.spec}, but this run uses {provider}; "
            "falling back to the provider default"
        )
    # Say where the binding actually came from. `.pcp/config.toml` is optional, and
    # claiming a default came from a file that does not exist is the same class of
    # bug as a `--runner auto` that reports a tier it did not use.
    from pcp.orch.providers import DEFAULT_CONFIG

    source = (
        str(DEFAULT_CONFIG) if Path(DEFAULT_CONFIG).exists()
        else "built-in default for the providers detected on this machine"
    )
    return binding.model, f"{role}: {binding.spec} (from {source})"


def _maybe_sandbox(runner, provider: str, sandbox: bool, reference: Path | None,
                   corpus: Path | None = None, library: list[Path] | None = None):
    """Wrap a subprocess runner in bubblewrap when a benchmark asks for isolation."""
    if not sandbox:
        return runner
    from pcp.orch.runners.sandbox import Sandbox, SandboxedRunner, available

    if not hasattr(runner, "argv"):
        raise SystemExit(
            f"--sandbox needs a subprocess runner; {runner.name} runs in-process. "
            "Use --runner codex or --runner claude."
        )
    if not available():
        raise SystemExit("--sandbox needs bubblewrap (`bwrap`); install it or drop --sandbox")
    repo = Path(__file__).resolve().parents[2]
    ref = Path(reference).resolve() if reference else None
    return SandboxedRunner(
        inner=runner,
        sandbox_factory=lambda workdir: Sandbox.for_benchmark(
            workdir, repo=repo, reference=ref, provider=provider.split("-")[0],
            corpus=corpus, library=library,
        ),
    )


def cmd_prove(args: argparse.Namespace) -> int:
    import shutil

    from pcp.orch.prove import ProveConfig, run

    if args.fresh:
        for path in (args.graph, args.workroot):
            if path.exists():
                shutil.rmtree(path) if path.is_dir() else path.unlink()

    state_tools = _state_tools(args.state_tools)
    library = _library(getattr(args, "library", None))
    runner = _pick_runner(
        args.runner,
        _model_flag(args.prover_model or args.model, "--prover-model"),
        sandbox=args.sandbox, reference=args.reference, role="prover",
        effort=args.prover_effort, corpus=Path(args.file).resolve().parent,
        mcp_tools=state_tools or None, library=library,
    )
    if state_tools:
        print(f"state tools: {', '.join(state_tools)}", file=sys.stderr)
    decomposer = None
    if not args.no_orchestration and args.plan is None:
        from pcp.orch.decomposer import decomposer_runner

        factory = None
        if args.sandbox:
            from pcp.orch.runners.sandbox import Sandbox

            repo = Path(__file__).resolve().parents[2]
            ref = Path(args.reference).resolve() if args.reference else None
            corpus_dir = Path(args.file).resolve().parent
            factory = lambda w: Sandbox.for_benchmark(  # noqa: E731
                w, repo=repo, reference=ref, provider="claude", corpus=corpus_dir,
                library=library,
            )
        from pcp.orch.providers import resolve_effort

        pinned, note = _model_for("decomposer", "anthropic")
        chosen = _model_flag(args.decomposer, "--decomposer") or pinned
        if note and not args.decomposer:
            print(note, file=sys.stderr)
        effort = args.decomposer_effort or resolve_effort("decomposer")
        decomposer = decomposer_runner(chosen, sandbox_factory=factory, effort=effort)
        print(
            f"decomposer: {getattr(decomposer, 'name', '?')} (read-only)"
            + ("" if chosen else "  [no model pinned -- using the provider default]"),
            file=sys.stderr,
        )
    cfg = ProveConfig(
        file=args.file,
        target=args.lemma,
        plan=args.plan,
        graph_path=args.graph,
        workroot=args.workroot,
        concurrency=args.concurrency,
        node_seconds=args.node_seconds,
        **({"decomposer_seconds": args.decomposer_seconds}
           if args.decomposer_seconds else {}),
        max_attempts=args.attempts,
        intent=args.intent,
        skills=_load_skills(),
        state_tools=state_tools,
        library=library,
        record_root=args.record,
        corpus=args.corpus,
        require_orchestration=not args.no_orchestration,
        decomposer_runner=decomposer,
        max_design_rounds=args.design_rounds,
    )
    print(f"runner: {runner.name}", file=sys.stderr)
    result = run(cfg, runner)
    if args.json:
        print(json.dumps(_prove_json(result), indent=2, default=str))
    else:
        print(result.render())
    return 0 if result.integrated else 1


def _prove_json(result: Any) -> dict[str, Any]:
    return {
        "integrated": result.integrated,
        "detail": result.integration_detail,
        "elapsed_s": result.report.elapsed_s,
        "outcomes": [
            {
                "node": o.node_id,
                "name": o.name,
                "status": o.status,
                "attempts": o.attempts,
                "elapsed_s": o.elapsed_s,
                "evidence": o.evidence,
                "requests": o.requests,
            }
            for o in result.report.outcomes
        ],
        "sentinels": [
            {"sentinel": h.sentinel, "node": h.node, "detail": h.detail, "blocking": h.blocking}
            for h in result.sentinels.hits
        ],
    }


def _load_skills() -> list[str]:
    """Worker norms travel with the packet, not with the prompt template."""
    root = Path(__file__).resolve().parents[2] / "skills"
    out = []
    for name in ("prover.md",):
        path = root / name
        if path.exists():
            out.append(path.read_text(encoding="utf-8"))
    return out


# ------------------------------------------------------------------------- check

def cmd_check(args: argparse.Namespace) -> int:
    from pcp.orch.assemble import Development, NodeSpec
    from pcp.orch.gate import Gate
    from pcp.orch.packet import NODE_FILE

    workdir = args.dir.resolve()
    if args.body is None and args.body_positional is not None:
        args.body = Path(args.body_positional)
    meta_path = workdir / NODE_FILE
    if not meta_path.exists():
        print(
            f"no {NODE_FILE} in {workdir}.\n"
            "Run `pcp check` from inside your node's work directory (the one holding "
            "TASK.md), or pass --dir. With no arguments it checks the proof body as "
            "you left it in the .v file; `pcp check proof.v` checks a body from a file.",
            file=sys.stderr,
        )
        return 2
    meta = json.loads(meta_path.read_text(encoding="utf-8"))

    if args.body is not None:
        body = sys.stdin.read() if str(args.body) == "-" else Path(args.body).read_text(encoding="utf-8")
    else:
        body = _body_from_scratch(workdir, meta)
        if body is None:
            print(
                "could not find your proof body. Either edit the assembled .v in this "
                "directory, or pass --body proof.v",
                file=sys.stderr,
            )
            return 2

    dev = Development(meta["file"])
    gate = Gate(dev)

    if args.design:
        from pcp.orch.contract import DesignContract

        candidate = _candidate_file(workdir, dev)
        if candidate is None:
            print(f"no {dev.path.name} in {workdir} to check", file=sys.stderr)
            return 2
        contract = DesignContract.from_corpus(Path(meta.get("corpus") or dev.path.parent))
        result = gate.run_design(candidate, contract)
        diagnosis = _diagnose_failure(result, meta, workdir, args)
        if args.json:
            payload = result.to_json()
            if diagnosis:
                payload["diagnosis"] = diagnosis
            print(json.dumps(payload, indent=2))
        else:
            print(result.render())
            if diagnosis:
                print()
                print(diagnosis)
            print()
            print(f"contract: {contract.describe()}")
            if not result.ok:
                print(_check_advice(result))
        return 0 if result.ok else 1

    specs = [
        NodeSpec(name=s["name"], statement=s["statement"], body=None)
        for s in meta.get("siblings", [])
        if s["name"] != meta["target"]
    ]
    from pcp.orch.runners.base import strip_proof_wrapper

    body = strip_proof_wrapper(body)
    is_anchor = meta["target"] == meta["anchor"]
    if not is_anchor:
        specs.append(NodeSpec(name=meta["target"], statement=meta["statement"], body=body))
    result = gate.run(
        meta["anchor"],
        specs,
        target_body=body if is_anchor else None,
        target=meta["target"],
        unused_premise_report=args.unused_premises,
        stub_prefix=not args.full,
    )
    diagnosis = _diagnose_failure(result, meta, workdir, args)
    if args.json:
        payload = result.to_json()
        if diagnosis:
            payload["diagnosis"] = diagnosis
        print(json.dumps(payload, indent=2))
    else:
        print(result.render())
        if diagnosis:
            print()
            print(diagnosis)
        if not result.ok:
            print()
            print(_check_advice(result))
    return 0 if result.ok else 1


#: What a failing gate check means, in the worker's terms.  Without this a worker
#: goes and reads `pcp/orch/gate.py` to work out what the checker wants -- one real
#: run spent seven turns doing exactly that.
_CHECK_ADVICE = {
    "no new Admitted / admit / Axiom / Parameter":
        "Your body contains an admit. The gate rejects it before compiling anything. "
        "If you genuinely cannot finish, answer `stuck` with evidence instead.",
    "no escape hatches":
        "Your body disables a kernel check. Remove it; the proof has to hold with the "
        "checks on.",
    "ambient-state hygiene (no global Instance/Hint/Notation/Ltac)":
        "Global registrations change how *future* statements elaborate. Make it "
        "`Local` (Local Ltac / Local Instance / Local Hint).",
    "statement pinning by construction":
        "The frozen statement is not present verbatim. You changed the lemma line -- "
        "revert it; only the proof body is yours.",
    "`Proof using` discipline":
        "The assembled file lost its `Set Default Proof Using` directive.",
    "compiles (coqc)":
        "Rocq rejected the proof. The first error is above; the rest of the output is "
        "in the same report.",
    "design contract (only declared-mutable definitions changed)":
        "You changed something the contract does not let you change. The program and "
        "the specifications are the theorem; only the definitions named in the "
        "contract are yours. Imports may be added but not removed.",
    "axiom hygiene (Print Assumptions ⊆ whitelist + open stubs)":
        "The proof leans on an axiom that is not allowed. Sibling lemmas still stubbed "
        "with Admitted are fine; anything else is not.",
}


def _check_advice(result: Any) -> str:
    lines = ["what to do:"]
    for check in result.checks:
        if check.ok or check.advisory:
            continue
        advice = _CHECK_ADVICE.get(check.name)
        lines.append(f"  · {check.name}: {advice or check.detail or 'see the report above'}")
    if len(lines) == 1:
        lines.append("  · every named check passed; re-read the compiler output above")
    return "\n".join(lines)


def _diagnose_failure(result: Any, meta: dict, workdir: Path, args: argparse.Namespace) -> str:
    """Enrich a failing compile with the proof state at the failing tactic.

    The alternative considered was shadowing `coqc` itself with a wrapper. Rejected:
    the gate's whole authority rests on "it compiles" meaning what `coqc` means, and
    a `coqc` on PATH that is not `coqc` is the highest-stakes version of a knob that
    silently is not what it claims. `pcp check` is already ours, already the command
    the packet tells the worker to run, and still calls the real compiler underneath.

    Silent and non-fatal by construction: a worker whose box has no petanque, or
    whose replay falls over, sees exactly what it saw before.
    """
    if result.ok or not _wants_diagnosis(meta, args):
        return ""
    if not any(c.name.startswith("compiles") and not c.ok for c in result.checks):
        return ""  # a static check failed; there is no compiler error to explain
    if not getattr(result, "assembled", ""):
        return ""
    try:
        from pcp.mcp.explain import explain
    except Exception as exc:  # noqa: BLE001 -- pcp-state is an optional dependency
        return f"(diagnosis unavailable: {exc})" if args.diagnose else ""
    text = explain(
        result.assembled,
        workdir=workdir,
        compile_output=result.compile_output,
        prefer=meta.get("target"),
        stub_prefix=not args.full,
    )
    if not text and args.diagnose:
        return "(no diagnosis: petanque is not on PATH, or the failure is not inside a proof body)"
    return text


def _wants_diagnosis(meta: dict, args: argparse.Namespace) -> bool:
    """`--diagnose`/`--no-diagnose` win; otherwise the packet decides.

    Defaulting to the packet is what keeps an ablation honest. The replay *is* the
    state layer, so a control arm that was denied the state tools must not be handed
    them back through the checker.
    """
    if args.diagnose is not None:
        return bool(args.diagnose)
    return bool(meta.get("diagnose"))


#: Machine scratch, never a worker's file.  `_stubbed_copy` and the diagnosis replay
#: both write twins next to the source so the project's `-Q`/`-R` flags apply to
#: them; one left behind by a killed process must not become the proof under test.
SCRATCH_INFIX = "__pcp"


def _worker_files(workdir: Path) -> list[Path]:
    return sorted(p for p in workdir.glob("*.v") if SCRATCH_INFIX not in p.stem)


def _candidate_file(workdir: Path, dev) -> str | None:
    """The worker's edited copy of the development, if it has one."""
    local = workdir / dev.path.name
    if local.exists():
        return local.read_text(encoding="utf-8")
    for candidate in _worker_files(workdir):
        return candidate.read_text(encoding="utf-8")
    return None


def _body_from_scratch(workdir: Path, meta: dict) -> str | None:
    from pcp.core.vernac import find_block

    for candidate in _worker_files(workdir):
        block = find_block(candidate.read_text(encoding="utf-8"), meta["target"])
        if block is not None and block.has_proof:
            return block.body(candidate.read_text(encoding="utf-8"))
    for name in ("proof.v", "body.v"):
        path = workdir / name
        if path.exists():
            return path.read_text(encoding="utf-8")
    return None


# ------------------------------------------------------------------------ status

def cmd_status(args: argparse.Namespace) -> int:
    from pcp.orch.graph import Graph

    if not args.graph.exists():
        print(f"no graph at {args.graph}", file=sys.stderr)
        return 2
    graph = Graph(args.graph)
    nodes = graph.nodes()
    if args.json:
        print(json.dumps({"summary": graph.summary(), "nodes": [_node_json(n) for n in nodes]}, indent=2))
        return 0
    summary = graph.summary()
    order = ["integrated", "gated", "qed", "claimed", "open", "stuck", "contested", "attic"]
    print(" · ".join(f"{summary[k]} {k}" for k in order if k in summary) or "empty graph")
    print()
    for n in nodes:
        mark = {"integrated": "✓", "gated": "✓", "stuck": "✗", "contested": "?", "claimed": "…"}.get(n.proof_status, "·")
        line = f" {mark} {n.name:32} {n.proof_status:11} {n.statement_status:9} epoch {n.epoch} attempts {n.attempts}"
        print(line)
        if n.evidence and n.proof_status in ("stuck", "contested"):
            print(f"     {' '.join(n.evidence.split())[:150]}")
    return 0


def _node_json(n: Any) -> dict[str, Any]:
    return {
        "id": n.id,
        "name": n.name,
        "rank": n.rank,
        "epoch": n.epoch,
        "statement_status": n.statement_status,
        "proof_status": n.proof_status,
        "attempts": n.attempts,
        "evidence": n.evidence,
    }


# ----------------------------------------------------------------------- handoff

def cmd_handoff(args: argparse.Namespace) -> int:
    from pcp.orch.graph import Graph
    from pcp.orch.handoff import render_handoff

    graph = Graph(args.graph)
    node = graph.get(args.node) or graph.by_name(args.node)
    if node is None:
        print(f"no node {args.node!r} in {args.graph}", file=sys.stderr)
        return 2
    text = render_handoff(graph, node)
    out = args.out or Path(f"{node.name}_handoff.v")
    out.write_text(text, encoding="utf-8")
    print(f"wrote {out}")
    return 0


# ------------------------------------------------------------------- dash / report

def cmd_serve(args: argparse.Namespace) -> int:
    from pcp.dash.serve import serve

    return serve(args.graph, host=args.host, port=args.port)


def cmd_report(args: argparse.Namespace) -> int:
    from pcp.dash.report import write_report
    from pcp.orch.graph import Graph

    graph = Graph(args.graph)
    path = write_report(graph, args.out)
    print(f"wrote {path}")
    return 0


def cmd_sketch(args: argparse.Namespace) -> int:
    from pcp.orch.sketch import compile_sketch

    sketch = compile_sketch(args.file.read_text(encoding="utf-8"))
    if args.json:
        print(json.dumps(sketch.to_json(), indent=2))
        return 0
    args.out.write_text(sketch.render_plan(), encoding="utf-8")
    print(sketch.render_summary())
    print(f"\nwrote {args.out}")
    return 0


# ------------------------------------------------------------------- state layer

def _session(file: Path, lemma: str, *, reflect: bool = False):
    from pcp.core.session import ProofSession, SessionPool

    pool = SessionPool(file.resolve().parent, size=1)
    pre = None
    if reflect:
        from pcp.core.ipm.reflect import build_idump, coqpath_with

        root = Path(".pcp/coq").resolve()
        build_idump(root)
        os.environ["COQPATH"] = coqpath_with(root)
        os.environ["ROCQPATH"] = os.environ["COQPATH"]
        pre = "Require Import pcp.IDump."
    return pool, ProofSession(pool, file, lemma, pre_commands=pre)


def cmd_trace(args: argparse.Namespace) -> int:
    from pcp.core.trace import Tracer
    from pcp.core.vernac import find_block

    if args.script:
        tactics = [l.strip() for l in args.script.read_text(encoding="utf-8").splitlines() if l.strip()]
    else:
        block = find_block(args.file.read_text(encoding="utf-8"), args.lemma)
        if block is None or not block.has_proof:
            print(f"{args.file}: {args.lemma} has no proof to trace; pass --script", file=sys.stderr)
            return 2
        tactics = block.tactics()

    pool, session = _session(args.file, args.lemma, reflect=args.reflect)
    try:
        tracer = Tracer(session)
        tracer.start()
        trace = tracer.run_script(tactics)
        if args.oracle:
            from pcp.core.ipm.oracle import annotate

            for step in trace.steps:
                for goal in step.goals:
                    annotate(session, goal)
        out = args.out or Path(f".pcp/traces/{args.file.stem}.{args.lemma}.jsonl")
        trace.write(out)
        print(f"{len(trace.steps)} steps, {len(trace.events)} ledger events → {out}")
        if trace.error:
            print(f"stopped at step {trace.failed_at}: {trace.error}", file=sys.stderr)
        return 0
    finally:
        pool.close()


def cmd_state(args: argparse.Namespace) -> int:
    from pcp.core.render import RenderOptions, render_goal
    from pcp.core.trace import Trace

    trace = Trace.read(args.trace)
    step = trace.step_at(args.step) if args.step is not None else trace.final
    if step is None or not step.goals:
        print("no goals at that step", file=sys.stderr)
        return 2
    prev = None
    if not args.all and args.step:
        prev_step = trace.step_at(args.step - 1)
        prev = prev_step.goals[0] if prev_step and prev_step.goals else None
    opts = RenderOptions(select=args.select, mode=args.mode, budget=args.budget, diff_only=not args.all)
    for goal in step.goals:
        print(render_goal(goal, previous=prev, options=opts, store=trace.store).text)
        print()
    return 0


def cmd_ledger(args: argparse.Namespace) -> int:
    from pcp.core.ledger.query import LedgerQuery
    from pcp.core.trace import Trace

    trace = Trace.read(args.trace)
    q = LedgerQuery(trace)
    if args.query == "events":
        for e in trace.events:
            print(e.render())
    elif args.query == "where":
        if not args.hyp:
            print("--hyp is required", file=sys.stderr)
            return 2
        print(q.where_did_it_go(args.hyp).render())
    elif args.query == "blame":
        if not args.hyp:
            print("--hyp is required", file=sys.stderr)
            return 2
        print(q.blame(args.step if args.step is not None else len(trace.steps), args.hyp).render())
    elif args.query == "leftovers":
        hyps = q.leftovers(args.step)
        if not hyps:
            print("the spatial context is empty")
        for h in hyps:
            print(f'  "{h.id}" : {h.prop}')
    elif args.query == "unused":
        names = q.unused_at_qed()
        print(", ".join(names) if names else "every resource was consumed")
    return 0


def cmd_destruct(args: argparse.Namespace) -> int:
    from pcp.core.ipm.pattern import align, compile_auto
    from pcp.core.ipm.skeleton import parse_skeleton

    skel = parse_skeleton(args.prop)
    if args.pattern:
        report = align(args.pattern, skel, binders=None)
        print(report.render())
        return 0 if report.ok else 1
    d = compile_auto(skel, args.name)
    print(d.idestruct(args.name))
    print()
    print("prop skeleton:")
    print(skel.render(1))
    return 0


def cmd_failures(args: argparse.Namespace) -> int:
    from pcp.orch.failures import TAXONOMY, summarize
    from pcp.orch.record import load_records

    records = list(load_records(args.run))
    if not records:
        print(f"no records under {args.run}", file=sys.stderr)
        return 2

    if args.klass:
        if args.klass not in TAXONOMY:
            print(f"unknown class {args.klass!r}; one of: {', '.join(TAXONOMY)}", file=sys.stderr)
            return 2
        shown = 0
        for rec in records:
            if rec.get("solved") or args.klass not in (rec.get("failure_classes") or []):
                continue
            shown += 1
            print(f"--- {rec['lemma']} attempt {rec['attempt']} ({rec['status']})")
            print(f"    {rec.get('failure_evidence', '')[:300]}")
            if rec.get("evidence"):
                print("    evidence: " + " ".join(rec["evidence"].split())[:300])
        print(f"\n{shown} record(s) in class {args.klass}")
        return 0

    report = summarize(records)
    if args.json:
        print(json.dumps({
            "total": report.total, "solved": report.solved,
            "primary": dict(report.primary), "all_classes": dict(report.all_classes),
        }, indent=2))
        return 0
    print(report.render(limit=args.examples))
    return 0


def cmd_docs(args: argparse.Namespace) -> int:
    from pcp.core.search import build_local_index, library_roots

    roots = library_roots()
    if not roots:
        print("no Rocq library root found; set ROCQPATH", file=sys.stderr)
        return 2
    path, n = build_local_index(roots, args.out, libraries=tuple(args.libraries))
    print(f"{n} declarations from {', '.join(args.libraries)} → {path}")
    return 0


def cmd_mcp(args: argparse.Namespace) -> int:
    from pcp.mcp.server import run_stdio

    return run_stdio(args.workspace)


# ------------------------------------------------------------------------ doctor

def cmd_models(args: argparse.Namespace) -> int:
    from pcp.orch.providers import DEFAULT_CONFIG, EXAMPLE_CONFIG, describe_bindings

    if args.example:
        print(EXAMPLE_CONFIG)
        return 0
    print(describe_bindings())
    source = "detected defaults" if not Path(DEFAULT_CONFIG).exists() else str(DEFAULT_CONFIG)
    print(f"\nsource: {source}")
    print(
        "override per run with --decomposer / --prover-model, or pin them in "
        f"{DEFAULT_CONFIG} ([tiers] decomposer = \"anthropic/claude-fable-5\")."
    )
    return 0


def cmd_doctor(args: argparse.Namespace) -> int:
    from pcp.core.session import pet_binary, pet_server_binary, rocq_binary
    from pcp.orch.runners.claude_code import ClaudeCodeSubagentRunner
    from pcp.orch.runners.cli import claude_headless_runner, codex_cli_runner
    from pcp.orch.runners.direct import DirectAPIRunner

    ok = True
    print("toolchain")
    for label, value in (
        ("coqc / rocq", rocq_binary()),
        ("pet (stdio petanque)", pet_binary()),
        ("pet-server (socket)", pet_server_binary()),
    ):
        print(f"  {label:24} {value or '— missing'}")
        if label == "coqc / rocq" and not value:
            ok = False
    for var in ("COQPATH", "ROCQPATH"):
        print(f"  {var:24} {os.environ.get(var, '— unset')}")

    print("\nlibraries")
    import importlib.util

    if importlib.util.find_spec("pytanque") is not None:
        print("  pytanque                 ok")
    else:
        print("  pytanque                 — missing (pip install 'pytanque @ git+https://github.com/LLM4Rocq/pytanque')")
    # Probe the API this actually uses.  `import mcp` succeeds on both SDK
    # generations, so checking the package alone reported "ok" for a server that
    # could not start -- the failure surfaced only when a worker asked for a tool.
    try:
        from pcp.mcp.server import make_mcp

        make_mcp("probe")
        print("  mcp server API           ok")
    except Exception as exc:  # noqa: BLE001 -- report, do not crash the doctor
        print(f"  mcp server API           — unusable ({exc})")

    print("\nmodels by role")
    from pcp.orch.providers import describe_bindings

    for line in describe_bindings().splitlines():
        print("  " + line)

    print("\nrunners")
    for runner in (codex_cli_runner(), claude_headless_runner(), ClaudeCodeSubagentRunner(), DirectAPIRunner()):
        mark = "ok" if runner.available() else "— unavailable"
        print(f"  {runner.name:24} {mark}")
    print(
        "\nLogin is delegated: run `codex login` or Claude Code's `/login` yourself. "
        "Inside a Claude Code session, `! codex login` runs it without leaving the session."
    )
    if not ok:
        print("\nRun ./scripts/setup-toolchain.sh, then `. ./env.sh`.", file=sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
