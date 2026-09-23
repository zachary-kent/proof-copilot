"""``pcp prove`` (contract §1.1): validate everything, *then* touch the graph.

``--fresh`` deletes a resumable run, so it runs only after every flag has been
validated and the runners built -- a typo in ``--library`` used to destroy the
graph first and complain second.  Exit 0 iff the run integrated; 1 when it ran and
did not; 2 for usage errors (``OrchestrationRequired`` included).

Three processes can be running this command (:mod:`pcp.orch.supervise`):

* ``--supervise``: validate, ``--fresh`` if asked, then re-exec detached as the
  supervisor and exit 0 with the pid and log to follow;
* ``--supervised-child DIR`` (hidden): the detached supervisor loop, which runs the
  command below as a child once per try;
* ``--outcome-file FILE`` (hidden): an ordinary run that also writes its outcome on
  a normal return, so the supervisor can tell "finished" from "died".
"""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Any

from pcp.cli.common import absolute, note
from pcp.cli.runners import library_dirs, select_approver, select_decomposer, select_runner, state_tools_for
from pcp.config.load import load
from pcp.errors import PcpError, UsageError
from pcp.util.io import ensure_dir, json_dumps, rm_tree
from pcp.util.locks import RunLock

GRAPH_SIDECARS = ("-wal", "-shm")
#: Flags a re-exec never carries: the launcher's own, and ``--fresh`` (the launcher
#: already wiped the graph; a restart must resume it).
LAUNCH_FLAGS = ("--supervise", "--fresh")
LAUNCH_VALUED = ("--max-restarts", "--supervised-child", "--outcome-file", "--record-run-id")


def load_skills() -> list[str]:
    """Worker norms travel with the packet, not with the prompt template.  Packaged
    (:mod:`pcp.util.assets`), so a missing file is a broken install and fails the run
    instead of silently sending workers out without their norms."""
    from pcp.util.assets import PROVER_SKILL, skill_text

    return [skill_text(PROVER_SKILL)]


def fresh_start(graph: Path, workroot: Path) -> None:
    """Delete the graph, its WAL sidecars and the workroot, under both run locks so
    neither a live run's graph nor another graph's live workroot is pulled out from
    under it.  Leaving ``-wal`` behind let SQLite replay the old run into the "fresh"
    database; the lock files themselves stay (deleting one would let two runs each
    hold "the" lock)."""
    from pcp.orch.prove import lock_path, workroot_lock_path

    with RunLock(lock_path(graph)), RunLock(workroot_lock_path(workroot)):
        for path in (graph, *(graph.with_name(graph.name + s) for s in GRAPH_SIDECARS)):
            if path.exists():
                path.unlink()
        if workroot.exists():
            rm_tree(workroot)


def supervisor_argv(raw: list[str], *, state: Path, run_id: str | None, max_restarts: int) -> list[str]:
    """The detached supervisor's command line: the run as typed, minus the launcher's
    flags, plus where to keep its state."""
    from pcp.orch.supervise import strip_flags

    base = strip_flags(raw, flags=LAUNCH_FLAGS, valued=LAUNCH_VALUED)
    if run_id:
        base += ["--record-run-id", run_id]
    return [sys.executable, "-m", "pcp.cli.main", *base, "--supervised-child", str(state), "--max-restarts", str(int(max_restarts))]


def child_argv(raw: list[str], *, outcome: Path) -> list[str]:
    """One try of the run, as the supervisor starts it."""
    from pcp.orch.supervise import strip_flags

    base = strip_flags(raw, flags=LAUNCH_FLAGS, valued=("--max-restarts", "--supervised-child", "--outcome-file"))
    return [sys.executable, "-m", "pcp.cli.main", *base, "--outcome-file", str(outcome)]


def launch_supervisor(args: argparse.Namespace, *, graph: Path, workroot: Path, record_root: Path | None) -> int:
    """``--supervise``: re-exec detached and return at once (module docstring)."""
    from pcp.orch.supervise import LOG_FILE, state_dir
    from pcp.util.proc import spawn_detached

    raw = list(getattr(args, "raw_argv", None) or [])
    if not raw:
        raise UsageError("--supervise needs the command line as typed; run it through `pcp prove`")
    run_id = None
    if record_root is not None:
        from pcp.orch.record import Recorder

        run_id = Recorder(record_root).run_id
    state = ensure_dir(state_dir(record_root=record_root, run_id=run_id, workroot=workroot))
    argv = supervisor_argv(raw, state=state, run_id=run_id, max_restarts=int(args.max_restarts))
    pid = spawn_detached(argv, log=state / LOG_FILE, cwd=os.getcwd())
    print(f"supervising pid {pid}; follow with: pcp status --graph {graph} | tail -f {state / LOG_FILE}")
    return 0


def run_supervisor(args: argparse.Namespace) -> int:
    """``--supervised-child DIR``: the loop itself (the detached process)."""
    from pcp.orch.supervise import OUTCOME_FILE, Supervisor

    state = absolute(args.supervised_child)
    assert state is not None
    raw = list(getattr(args, "raw_argv", None) or [])
    supervisor = Supervisor(
        argv=child_argv(raw, outcome=state / OUTCOME_FILE), state=state, graph=absolute(args.graph),
        max_restarts=int(args.max_restarts), cwd=Path(os.getcwd()),
    )
    return supervisor.run()


def cmd_prove(args: argparse.Namespace) -> int:
    from pcp.orch.prove import ProveConfig, run

    if getattr(args, "supervised_child", None) is not None:
        return run_supervisor(args)
    cfg = load(absolute(args.config) if getattr(args, "config", None) else None)
    file = absolute(args.file)
    assert file is not None
    if not file.exists():
        raise UsageError(f"{args.file}: no such file")
    plan = absolute(args.plan) if args.plan is not None else None
    if plan is not None and not plan.exists():
        raise UsageError(f"{args.plan}: no such plan file")
    graph = absolute(args.graph)
    workroot = absolute(args.workroot)
    assert graph is not None and workroot is not None

    # Everything below validates before anything is deleted or opened.
    state_tools = state_tools_for(args)
    library = library_dirs(getattr(args, "library", None))
    corpus_dir = file.parent
    if args.brief == "spec-only":
        from pcp.orch.prove.design import staged_dir

        # Workers and the decomposer see the staged copy and only that: the
        # sandbox's corpus bind must not hand the original directory back.
        corpus_dir = staged_dir(ProveConfig(file=file, target=args.lemma, workroot=workroot))
    runner, notes = select_runner(args, cfg, role="prover", corpus_dir=corpus_dir, library=library)
    decomposer = None
    approver = None
    if not args.no_orchestration and plan is None:
        decomposer, more = select_decomposer(args, cfg, corpus_dir=corpus_dir, library=library)
        notes += more
    if decomposer is not None:
        # The approver is the decomposer's delegate (same model, lower effort); it
        # adjudicates `replace` amendments and contests.  A plan-based run has no
        # decomposer and so no approver: `add` strengthenings still apply (they are
        # machine-checked), a `replace` is refused as needing one.
        approver = select_approver(args, cfg, corpus_dir=corpus_dir, library=library)
        notes.append(f"approver: {approver.name}")

    # Before --fresh: a broken install must fail before it wipes the graph.
    skills = load_skills()
    if args.fresh:
        fresh_start(graph, workroot)
    record_root = absolute(args.record) if args.record is not None else None
    if getattr(args, "supervise", False):
        return launch_supervisor(args, graph=graph, workroot=workroot, record_root=record_root)

    kwargs: dict[str, Any] = {}
    if args.decomposer_seconds is not None:
        kwargs["decomposer_seconds"] = float(args.decomposer_seconds)
    prove_cfg = ProveConfig(
        file=file,
        target=args.lemma,
        plan=plan,
        graph_path=graph,
        workroot=workroot,
        concurrency=args.concurrency,
        node_seconds=float(args.node_seconds),
        max_attempts=int(args.attempts),
        intent=args.intent,
        skills=skills,
        state_tools=state_tools,
        library=library,
        record_root=record_root,
        record_run_id=getattr(args, "record_run_id", None),
        pause_hours=float(getattr(args, "pause_hours", 12.0) or 0.0),
        corpus=args.corpus,
        require_orchestration=not args.no_orchestration,
        decomposer_runner=decomposer,
        max_design_rounds=int(args.design_rounds),
        max_amendments=int(args.amendments),
        review_after=int(getattr(args, "review_after", 2)),
        approver_seconds=float(args.approver_seconds),
        approver_runner=approver,
        brief=args.brief,
        config=cfg,
        index_path=absolute(Path(".pcp/docs/index.txt")),
        **kwargs,
    )
    if state_tools:
        note(f"state tools: {', '.join(state_tools)}")
    for line in notes:
        note(line)
    note(f"runner: {runner.name}")
    outcome = absolute(args.outcome_file) if getattr(args, "outcome_file", None) is not None else None
    try:
        result = run(prove_cfg, runner)
    except PcpError as exc:
        # A usage error or a failed design is a *return*, not a crash: the supervisor
        # must not restart it.
        _write_outcome(outcome, integrated=False, exit_code=exc.exit_code, error=str(exc)[:400])
        raise
    try:
        if args.json:
            print(json_dumps(result.to_json()))
        else:
            print(result.render())
    finally:
        result.close()
    code = 0 if result.integrated else 1
    _write_outcome(outcome, integrated=result.integrated, exit_code=code, detail=result.integration_detail[:400])
    return code


def _write_outcome(path: Path | None, **fields: Any) -> None:
    if path is None:
        return
    from pcp.orch.supervise import write_outcome

    write_outcome(path, **fields)
