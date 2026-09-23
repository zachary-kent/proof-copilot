"""``pcp prove`` -- the daily loop (PLAN.md 8.11).

Everything else in the design will be tuned; this is the part that is not allowed to
be.  *"I have a lemma and high-level intuition for its proof; the orchestrator
manages parallel dispatch"* must work every time::

    pcp prove Foo.v foo_correct --plan plan.v

1. The user's lemma is the fixed root and the user is the root decomposer.
   Statements freeze immediately (:mod:`pcp.orch.prove.plan`), with only the free
   sentinels.  Without a plan, a read-only decomposer states the obligations
   (:mod:`pcp.orch.prove.design`).
2. The whole frontier dispatches at once (:mod:`pcp.orch.schedule`); the root is
   itself a node, dispatched concurrently.
3. Returns are gated deterministically; failures retry once with evidence.  What
   remains lands back with the user as ``qed`` / ``stuck`` / ``contested``, and the
   run *integrates* only when the root ``Qed``s with ``Print Assumptions ⊆ whitelist``
   (:mod:`pcp.orch.prove.integrate`).

A run always resumes from the graph (:mod:`pcp.orch.prove.resume`); ``--fresh`` is
what starts over.  A provider outage pauses the run rather than ending it
(:mod:`pcp.orch.outage`; ``--pause-hours``), and ``--supervise`` keeps the process
itself alive across crashes (:mod:`pcp.orch.supervise`): PLAN.md 11 says the window
is the scarce resource, and a run that dies at 2 a.m. wastes the rest of the night.  One ``pcp prove`` per graph *and* per workroot: the run holds
``<graph>.lock`` and ``<workroot>.lock`` -- attempt ids are per graph, so two graphs
sharing a workroot handed two live workers the same attempt directory (review
finding).  Every documented knob reaches exactly one consumer here
(``--node-seconds`` is the per-attempt clock, ``--concurrency`` and config
``concurrency`` the semaphore, config ``axiom_whitelist`` the gate, ``--brief
spec-only`` the staging).  Whatever the corpus contract says, the run's own target
is a frozen result: a ``design.json`` naming *other* results once let the target be
restated through ``definitions`` (``Definition root : Prop.``) and "integrated".
"""

from __future__ import annotations

import asyncio
import contextlib
import dataclasses
import sys
import time
from collections.abc import Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from pcp.errors import UsageError
from pcp.orch.gate import Gate
from pcp.orch.graph import Graph
from pcp.orch.model import ADJUDICATED_META, Budget, Node
from pcp.orch.protocol import Runner
from pcp.orch.schedule import RunReport, Scheduler, default_concurrency
from pcp.orch.sentinels import SentinelReport
from pcp.rocq.assemble import Development
from pcp.util.locks import RunLock

__all__ = [
    "DesignFailed",
    "OrchestrationRequired",
    "ProveConfig",
    "ProveResult",
    "freeze_target",
    "lock_path",
    "prove",
    "run",
    "workroot_lock_path",
]
#: A rejected design round keeps this many lines of its reason in the summary.
HEADLINE_LINES = 4


class OrchestrationRequired(UsageError):
    """The run would have been one prover doing everything."""


class DesignFailed(OrchestrationRequired):
    """The decomposer ran and no usable design came out of its rounds.

    A run outcome, not a usage error: it exits 1 like "ran but did not integrate",
    so a ladder does not mistake a rung that spent 30 minutes designing for one
    that could not start (review of the first spec-only ladder run).
    """

    exit_code = 1


@dataclass
class ProveConfig:
    file: Path
    target: str
    plan: Path | None = None
    graph_path: Path = Path(".pcp/graph.db")
    workroot: Path = Path(".pcp/work")
    concurrency: int | None = None
    #: The per-attempt wall clock.  Always the worker's deadline.
    node_seconds: float = 900.0
    #: Attempts per node *per statement epoch*, counted across runs.
    max_attempts: int = 2
    budget: Budget = field(default_factory=lambda: Budget(requests=200, seconds=7200))
    skills: Sequence[str] = ()
    state_tools: Sequence[str] = ()
    library: Sequence[Path] = ()
    intent: str = ""
    check_command: str = "pcp check"
    record_root: Path | None = None
    corpus: str = ""
    require_orchestration: bool = True
    decomposer_runner: Runner | None = None
    decomposer_seconds: float = 1800.0
    #: Decomposer *design* rounds in total: the initial proposal plus every revision.
    max_design_rounds: int = 3
    #: Definition amendments *applied* per run (PLAN.md 8.5; :mod:`pcp.orch.prove.amendments`).
    #: They never count against ``max_design_rounds``; ``0`` disables the path.
    max_amendments: int = 6
    #: Failed prover attempts at an epoch after which a node with budget left goes to
    #: the approver instead of being retried (0: never; effective only with an approver).
    review_after: int = 2
    #: The approver's clock for one verdict (an amendment or a contest).
    approver_seconds: float = 600.0
    #: The adjudicating runner (the decomposer's model at a lower effort); the
    #: decomposer runner stands in when unset.  ``object`` because it is a ``Runner``
    #: built by the CLI, and the config must not import the runner tree.
    approver_runner: object | None = None
    contract: Any | None = None
    #: ``full``: the corpus DESIGN.md reaches provers and the decomposer.
    #: ``spec-only``: the development is staged without it, and nothing can read it.
    brief: str = "full"
    config: Any | None = None
    #: Extra axioms the gate accepts, on top of the config's ``axiom_whitelist``.
    axiom_whitelist_extra: Sequence[str] = ()
    index_path: Path | None = None
    run_lock: bool = True
    #: How long a provider outage (revoked login, usage window, unreachable API) may
    #: pause the run before the affected nodes are parked; ``0`` disables the pause
    #: and an outage is an ``error`` outcome, as before.
    pause_hours: float = 12.0
    #: Reuse this record run id (``<record>/<id>/``) instead of a fresh timestamp: the
    #: supervisor gives every restart of one run the same directory.
    record_run_id: str | None = None

    def whitelist(self) -> tuple[str, ...]:
        extra = list(self.axiom_whitelist_extra)
        if self.config is not None:
            extra += list(getattr(self.config, "axiom_whitelist", []) or [])
        return tuple(dict.fromkeys(extra))

    def effective_concurrency(self) -> int:
        if self.concurrency:
            return int(self.concurrency)
        configured = getattr(self.config, "concurrency", None) if self.config is not None else None
        return int(configured) if configured else default_concurrency()


@dataclass
class ProveResult:
    report: RunReport
    sentinels: SentinelReport
    #: Left open so callers can inspect it; :meth:`close` when done (the CLI does).
    graph: Graph
    root: Node
    integrated: bool = False
    integration_detail: str = ""
    solution: Path | None = None
    record_dir: Path | None = None
    decomposition: Any | None = None
    design_rounds: list[Any] = field(default_factory=list)
    #: ``AmendmentOutcome`` per request the provers made (applied or refused).
    amendments: list[Any] = field(default_factory=list)
    elapsed_s: float = 0.0

    def close(self) -> None:
        self.graph.close()

    def render(self) -> str:
        """One screen (PLAN.md 8.11): a design round is one line here -- its children
        are the report's own lines -- and a rejected one keeps a few lines of why."""
        lines = [self.sentinels.render()] if self.sentinels.hits else []
        if self.decomposition is not None:
            model = getattr(self.decomposition, "model", "")
            lines.append(f"decomposer: {model or 'unknown model'} -- {_headline(self.decomposition)}")
        for revision in self.design_rounds:
            lines.append(f"design revision {getattr(revision, 'round', '?')}: {_headline(revision)}")
        lines.extend(a.render() for a in self.amendments)
        if self.decomposition is not None or self.design_rounds or self.amendments:
            lines.append("")
        lines.append(self.report.render())
        lines.append("")
        if self.integrated:
            lines.append(f"integrated: `{self.root.name}` Qeds and Print Assumptions is clean.")
            if self.solution is not None:
                lines.append(f"solution: {self.solution}")
        else:
            lines.append(f"not integrated: {self.integration_detail}")
        if self.record_dir is not None:
            lines.append(f"records: {self.record_dir}  (pcp failures {self.record_dir})")
        return "\n".join(lines)

    def to_json(self) -> dict[str, Any]:
        return {
            "integrated": self.integrated,
            "detail": self.integration_detail,
            "elapsed_s": self.elapsed_s,
            "outcomes": [o.to_json() for o in self.report.outcomes],
            "sentinels": [h.to_json() for h in self.sentinels.hits],
            "amendments": [a.to_json() for a in self.amendments],
        }


def _headline(result: Any) -> str:
    text = result.render().splitlines() or [""]
    if text[0].startswith("plan:"):
        return text[0]
    kept = text[:HEADLINE_LINES]
    more = len(text) - len(kept)
    return " ".join(line.strip() for line in kept) + (f" (+{more} more)" if more > 0 else "")


def lock_path(graph_path: str | Path) -> Path:
    p = Path(graph_path)
    return p.with_name(p.name + ".lock")


def workroot_lock_path(workroot: str | Path) -> Path:
    """Beside the workroot, not inside it: ``--fresh`` removes the directory and a
    lock file deleted from under its holder lets a second run hold "the" lock."""
    p = Path(workroot)
    return p.with_name(p.name + ".lock")


def freeze_target(contract: Any, target: str) -> Any:
    """The run's target is a result whatever the corpus contract says (module docstring)."""
    results = getattr(contract, "results", None)
    if results is None or target in results:
        return contract
    return dataclasses.replace(contract, results=frozenset(results) | {target})


async def prove(cfg: ProveConfig, runner: Runner) -> ProveResult:
    from pcp.orch.prove.plan import build_graph, plan_nodes

    started = time.perf_counter()
    plan = plan_nodes(cfg)
    locks: list[RunLock] = []
    try:
        if cfg.run_lock:
            locks.append(RunLock(lock_path(cfg.graph_path)).acquire())
            locks.append(RunLock(workroot_lock_path(cfg.workroot)).acquire())
        graph, root, sentinels = build_graph(cfg, plan, whitelist=cfg.whitelist())
        try:
            return await _prove(cfg, runner, plan, graph, root, sentinels, started)
        except BaseException:
            graph.close()
            raise
    finally:
        for lock in reversed(locks):
            lock.release()


async def _prove(cfg: ProveConfig, runner: Runner, plan: Any, graph: Graph, root: Node, sentinels: SentinelReport, started: float) -> ProveResult:
    from pcp.orch.contract import DesignContract
    from pcp.orch.outage import PausePolicy, ProviderPause, provider_probe
    from pcp.orch.prove.amendments import AmendmentRun, contested_nodes, parked_for_review, review_after
    from pcp.orch.prove.design import DesignDriver, read_design_brief, revalidate
    from pcp.orch.prove.integrate import export_solution, integrate
    from pcp.orch.prove.plan import has_children
    from pcp.orch.prove.resume import resume_development, resume_incomplete

    # Loaded ONCE from the original corpus and carried through every round; the
    # target is frozen in it whatever the corpus declared.
    contract = cfg.contract if cfg.contract is not None else DesignContract.from_corpus(Path(cfg.file).parent)
    contract = freeze_target(contract, cfg.target)
    dev = resume_development(cfg, graph, contract=contract)
    design_brief = read_design_brief(cfg)
    recorder = None
    if cfg.record_root is not None:
        from pcp.orch.record import Recorder

        recorder = Recorder(cfg.record_root, run_id=cfg.record_run_id)
    whitelist = cfg.whitelist()

    def gate_for(d: Development) -> Gate:
        return Gate(d, extra_whitelist=whitelist)

    def say(message: str) -> None:
        print(message, file=sys.stderr, flush=True)
        if recorder is not None:
            with contextlib.suppress(Exception):
                recorder.log(message)

    def pause_event(kind: str, payload: dict[str, Any]) -> None:
        graph.emit(kind, root.id, **payload)
        if recorder is not None:
            with contextlib.suppress(Exception):
                recorder.log(f"{kind}: {payload}")

    # One pause for the whole run, shared by the scheduler, the decomposer and the
    # approver (module docstring): the first outage holds it, the others join it.
    pause = ProviderPause(PausePolicy.from_hours(cfg.pause_hours), provider_probe(runner), on_wait=say, on_event=pause_event)
    driver = DesignDriver(
        cfg, graph, root, contract=contract, recorder=recorder, preamble=plan.preamble,
        design_brief=design_brief, gate_factory=gate_for, pause=pause,
    )
    if not sentinels.ok:
        # A blocked plan is the user's to fix; nothing is designed or dispatched.
        return ProveResult(
            report=RunReport(elapsed_s=time.perf_counter() - started), sentinels=sentinels, graph=graph, root=root,
            integration_detail="blocked by sentinels before any worker was dispatched",
            elapsed_s=time.perf_counter() - started,
        )
    if cfg.require_orchestration and not has_children(graph, root):
        if cfg.decomposer_runner is None:
            raise OrchestrationRequired(
                "orchestration is required and no obligations were stated.\n"
                "no plan was supplied and no decomposer runner is configured"
                "\n\nSupply a plan with --plan, or configure a decomposer. A single "
                "prover taking the whole goal is not an orchestrated run."
            )
        dev = await driver.initial(dev, elapsed_s=time.perf_counter() - started)

    async def dispatch(d: Development, round_no: int) -> RunReport:
        scheduler = Scheduler(
            graph, d, runner, anchor=cfg.target, gate=gate_for(d), workroot=cfg.workroot,
            concurrency=cfg.effective_concurrency(), node_seconds=cfg.node_seconds,
            max_attempts=cfg.max_attempts, skills=cfg.skills, state_tools=cfg.state_tools,
            library=cfg.library, check_command=cfg.check_command, recorder=recorder, corpus=cfg.corpus,
            design_brief=design_brief, index_path=cfg.index_path, round=round_no, preamble=plan.preamble,
            amendments=int(cfg.max_amendments) > 0, pause=pause,
            review_after=review_after(cfg),
            reviewed=lambda n: graph.get_meta(f"{ADJUDICATED_META}:{n.id}") == str(n.epoch),
        )
        return await scheduler.run()

    resumed = resume_incomplete(graph, max_attempts=cfg.max_attempts, workroot=cfg.workroot)
    if resumed.any:
        graph.emit("run.resumed", root.id, **resumed.to_json())
        if recorder is not None:
            with contextlib.suppress(Exception):
                recorder.log(f"run.resumed: {resumed.to_json()}")
    # A proof checked against an obligation that has since been restated (a stale
    # demand edge, PLAN.md 8.1) is replayed now: kept and re-pinned, or reopened.
    kept, stale = revalidate(graph, dev, gate_for(dev), root, preamble=plan.preamble, only_stale=True)
    if kept or stale:
        graph.emit("edges.revalidated", root.id, kept=kept, reopened=stale)
    # The incremental route back to the design (PLAN.md 8.5; amendments.py).  Contests
    # left by an earlier run are adjudicated first -- a `strategy` verdict reopens the
    # node for this dispatch, a one-definition fix is applied before anything is
    # dispatched against the design the approver just called wrong.  Then every
    # dispatch's amendment requests are applied and the frontier re-dispatched, before
    # (and usually instead of) a full design revision.
    amendments = AmendmentRun(driver)
    if amendments.enabled:
        parked = parked_for_review(graph, cfg)
        dev, _reopened, fixes = await amendments.adjudicate(
            dev, contested_nodes(graph) + parked, review={n.id for n in parked},
        )
        if fixes:
            dev, _ = await amendments.apply(dev, fixes, approved=True)
    report = await dispatch(dev, amendments.base_round + amendments.applied)
    dev, report = await amendments.loop(dev, report, dispatch)
    if driver.active:
        dev, report = await driver.revise(dev, report, dispatch, cheap_tier=amendments.loop if amendments.enabled else None)

    integrated, detail = integrate(graph, dev, gate_for(dev), root, preamble=plan.preamble)
    solution = export_solution(recorder, graph, dev, root, integrated=integrated, preamble=plan.preamble)
    if solution is not None:
        graph.emit("run.exported", root.id, path=str(solution))
    elapsed = time.perf_counter() - started
    report.elapsed_s = elapsed
    result = ProveResult(
        report=report, sentinels=sentinels, graph=graph, root=graph.require(root.id),
        integrated=integrated, integration_detail=detail, solution=solution,
        record_dir=recorder.root if recorder else None, decomposition=driver.decomposition,
        design_rounds=list(driver.rounds), amendments=list(amendments.outcomes), elapsed_s=elapsed,
    )
    graph.emit("run.finished", root.id, integrated=integrated, summary=report.render()[:1000])
    return result


def run(cfg: ProveConfig, runner: Runner) -> ProveResult:
    return asyncio.run(prove(cfg, runner))
