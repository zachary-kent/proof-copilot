"""`pcp prove` -- the daily loop (PLAN.md 8.11).

Everything else in the design will be tuned; this is the part that is not allowed to
be.  The common workflow -- *"I have a lemma and high-level intuition for its proof;
the orchestrator manages parallel dispatch"* -- must work every time.

    pcp prove Foo.v foo_correct --plan plan.v

1. The user's lemma is the fixed root and the user is the root decomposer: they state
   the children.  Statements freeze immediately, with only the free sentinels.
2. The whole frontier dispatches at once, in parallel, budgeted.  The glue -- the root
   from its admitted children -- is itself a node, dispatched concurrently.  The
   no-gap rule relaxes from gate to node here: a human-vouched plan is trusted enough
   to dispatch against, and a gap surfaces as an ordinary `stuck` on the glue node
   rather than as up-front ceremony.
3. Returns are gated deterministically.  Failures retry once with evidence attached.
   What remains lands back with the user as `qed` / `stuck` / `contested`, always with
   evidence, and the user adjudicates.

Non-dependencies, by design: quorums, OR-nodes, the sketch compiler, the difficulty
estimator, depth > 1 recursion, more than one provider -- and no pcp-state at all.
"""

from __future__ import annotations

import asyncio
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable, Sequence

from pcp.orch.assemble import Assembly, Development, NodeSpec, parse_plan, plan_preamble
from pcp.orch.gate import Gate, _first_error
from pcp.orch.graph import Budget, Graph, Node
from pcp.orch.hashing import statement_hash
from pcp.orch.runners.base import Runner
from pcp.orch.schedule import RunReport, Scheduler
from pcp.orch.sentinels import SentinelReport, run_free_sentinels



@dataclass
class ProveConfig:
    file: Path
    target: str
    plan: Path | None = None
    graph_path: Path = Path(".pcp/graph.db")
    workroot: Path = Path(".pcp/work")
    concurrency: int | None = None
    node_seconds: float = 900.0
    max_attempts: int = 2
    budget: Budget = field(default_factory=lambda: Budget(requests=200, seconds=7200))
    skills: Sequence[str] = ()
    #: `pcp mcp` tools granted to each prover, empty for the deterministic-only arm.
    #: This is the ablation switch: the claim under test is that these failures are
    #: tool problems rather than model problems, and the only thing that falsifies it
    #: is running the same rung both ways.
    state_tools: Sequence[str] = ()
    #: Read-only directories every worker may consult (`--library`).
    library: Sequence[Path] = ()
    intent: str = ""
    check_command: str = "pcp check"
    #: Where per-attempt records go.  ``None`` disables recording.
    record_root: Path | None = None
    corpus: str = ""
    #: Orchestration is required, not optional.  A run may not hand the whole goal
    #: to one prover: either the operator supplies a plan, or a decomposer states
    #: the obligations first.  PLAN.md 8.2's control flow *is* the pipeline.
    require_orchestration: bool = True
    #: Runner for the decomposer role.  Read-only by construction; see
    #: `pcp.orch.decomposer`.
    decomposer_runner: object | None = None
    #: The design step is the hardest single call in a run and it is one-shot: there
    #: is no partial credit for a decomposer killed mid-sentence.  900s was arbitrary
    #: and measurably too small -- observed xhigh rounds on `rwcas` ran 892.8s,
    #: 895.5s and 900.1s against it, so roughly one in three died on the clock and
    #: was then reported as a protocol violation.
    decomposer_seconds: float = 1800.0
    #: How many times the design may be revised in the light of a failed proof.
    #: An invariant is wrong in one of two directions and the proof is the only
    #: reliable evidence of which, so deciding it once and freezing it forever makes
    #: the commonest CSL failure terminal.  Bounded, because a design that needs a
    #: fourth revision is a design problem, not a search problem.
    max_design_rounds: int = 3
    #: Which definitions a design round may rewrite.  Declared by the developer, not
    #: inferred from what the model happened to touch.  ``None`` loads the corpus's
    #: own declaration (`design.json`, else `bench.json`), falling back to "nothing".
    contract: object | None = None


@dataclass
class ProveResult:
    report: RunReport
    sentinels: SentinelReport
    graph: Graph
    root: Node
    integrated: bool = False
    integration_detail: str = ""
    #: The finished development, written out when the run integrates.  A ladder rung
    #: hands this to the next rung the way a person hands over their own last proof.
    solution: Path | None = None
    record_dir: Path | None = None
    decomposition: object | None = None
    design_rounds: list = field(default_factory=list)

    def render(self) -> str:
        lines = [self.sentinels.render()] if self.sentinels.hits else []
        if self.decomposition is not None:
            model = getattr(self.decomposition, "model", "")
            lines.append(f"decomposer: {model or 'unknown model'}")
            lines.append(self.decomposition.render())
            lines.append("")
        for i, amendment in enumerate(self.design_rounds, start=2):
            lines.append(f"design revision {i}: {amendment.render()}")
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


def plan_nodes(cfg: ProveConfig) -> tuple[Development, list[NodeSpec], str]:
    dev = Development(cfg.file)
    if dev.block(cfg.target) is None:
        raise SystemExit(f"{cfg.file}: no declaration named {cfg.target!r}")
    specs: list[NodeSpec] = []
    extra_preamble = ""
    if cfg.plan is not None:
        text = Path(cfg.plan).read_text(encoding="utf-8")
        specs = parse_plan(text)
        extra_preamble = plan_preamble(text).strip()
    return dev, specs, extra_preamble


def build_graph(cfg: ProveConfig, dev: Development, specs: list[NodeSpec]) -> tuple[Graph, Node, SentinelReport]:
    """Create or resume the graph, freezing every statement by construction."""
    graph = Graph(cfg.graph_path)
    root_block = dev.block(cfg.target)
    assert root_block is not None

    statements = {s.name: s.statement for s in specs}
    statements[cfg.target] = root_block.statement
    sentinels = run_free_sentinels(statements)

    existing = {n.name for n in graph.nodes()}

    root = graph.by_name(cfg.target)
    if root is None:
        root = graph.add_node(
            Node(
                id=_slug(cfg.target),
                name=cfg.target,
                statement=root_block.statement,
                statement_hash=statement_hash(root_block.statement),
                # A lemma the user hands down is frozen at rank root with no amendment
                # path except human edit (PLAN.md 8.5, Fixed roots).
                rank="root",
                statement_status="frozen",
                owner="human",
                intent=cfg.intent,
                budget=cfg.budget,
                file=str(cfg.file),
                is_glue=True,
                ordering=1_000_000,
            )
        )
    child_budget = cfg.budget.split(max(1, len(specs)))
    for i, spec in enumerate(specs):
        if spec.name in existing:
            continue
        node = graph.add_node(
            Node(
                id=_slug(spec.name),
                name=spec.name,
                statement=spec.statement,
                statement_hash=statement_hash(spec.statement),
                rank="local",
                parent=root.id,
                depth=1,
                statement_status="frozen",
                proof_status="gated" if spec.body else "open",
                body=spec.body,
                mockable=spec.mockable,
                owner="human",
                intent=cfg.intent,
                budget=child_budget,
                file=str(cfg.file),
                ordering=i,
            )
        )
        # Pull-only node creation: the demand edge is the parent's glue referencing
        # the child.  A node nothing uses cannot enter the graph (PLAN.md 8.8).
        graph.add_edge(root.id, node.id)
    return graph, graph.by_name(cfg.target) or root, sentinels


class OrchestrationRequired(SystemExit):
    """The run would have been one prover doing everything."""


class DesignViolatesContract(RuntimeError):
    """The design moved something the contract froze.

    Revisable, not fatal, for the same reason a design that does not typecheck is:
    it is a mistake the decomposer can be told about and can correct, and there is a
    round budget precisely for that. Aborting here made the *commonest* failure on a
    rung whose design is already given -- the decomposer rewriting definitions it was
    only ever allowed to add to -- the one failure the revision loop could not reach.
    It cost a whole rwcas rung before it was caught.
    """


class DesignDoesNotCompile(RuntimeError):
    """The proposed design is not well-formed Rocq.

    Caught rather than raised onward: a design that does not typecheck is exactly
    what the revision loop is for, and the compiler error is the best possible
    evidence to revise from.
    """


async def prove(cfg: ProveConfig, runner: Runner) -> ProveResult:
    started = time.perf_counter()
    dev, specs, extra_preamble = plan_nodes(cfg)
    graph, root, sentinels = build_graph(cfg, dev, specs)

    recorder = None
    if cfg.record_root is not None:
        from pcp.orch.record import Recorder

        recorder = Recorder(cfg.record_root)

    rounds: list[Any] = []
    decomposition = None
    if cfg.require_orchestration and not _has_children(graph, root):
        decomposition = await _decompose(cfg, graph, dev, root, recorder)
        if decomposition is None or not decomposition.ok:
            detail = decomposition.render() if decomposition else (
                "no plan was supplied and no decomposer runner is configured"
            )
            raise OrchestrationRequired(
                "orchestration is required and no obligations were stated.\n"
                + detail
                + "\n\nSupply a plan with --plan, or configure a decomposer. A single "
                "prover taking the whole goal is not an orchestrated run."
            )
        dev, decomposition, design_attempts = await _apply_with_revision(
            cfg, graph, dev, root, decomposition, recorder
        )
        rounds.extend(design_attempts)
        if dev is None:
            # Report the rounds actually spent, not the budget.  A run that stopped
            # early because a round produced no usable design once said "Tried 3
            # design round(s); raise --design-rounds" -- it had spent two, and
            # raising the budget would have changed nothing.
            used = 1 + len(design_attempts)
            raise OrchestrationRequired(
                "no proposed design was usable, so nothing can be proved against one.\n"
                + (decomposition.render() if decomposition else "")
                + f"\n\nTried {used} of {cfg.max_design_rounds} design round(s)"
                + (
                    "; raise --design-rounds to allow more."
                    if used >= cfg.max_design_rounds
                    else ", stopping early because a round returned no usable design. "
                    "The budget was not the limit."
                )
            )
        _adopt_proposal(cfg, graph, root, decomposition.proposal)

    if not sentinels.ok:
        return ProveResult(
            report=RunReport(elapsed_s=time.perf_counter() - started),
            sentinels=sentinels,
            graph=graph,
            root=root,
            integration_detail="blocked by sentinels before any worker was dispatched",
        )

    # A run always resumes from the graph; `--fresh` is what starts over, by
    # deleting it.  There was a `resume` config field beside this, read nowhere.
    reopened = reopen_incomplete(graph)
    if reopened:
        graph.emit("run.resumed", root.id, reopened=reopened)

    gate = Gate(dev)
    scheduler = Scheduler(
        graph,
        dev,
        runner,
        anchor=cfg.target,
        gate=gate,
        workroot=cfg.workroot,
        concurrency=cfg.concurrency,
        node_seconds=cfg.node_seconds,
        max_attempts=cfg.max_attempts,
        skills=cfg.skills,
        state_tools=cfg.state_tools,
        library=cfg.library,
        check_command=cfg.check_command,
        recorder=recorder,
        corpus=cfg.corpus,
    )
    report = await scheduler.run()

    # Progressive design revision.  A proof that dies at an `iInv` close site is
    # evidence about the *invariant*, not about the prover, and the only way to act
    # on it is to let the design change and re-derive against it.
    for round_no in range(2, cfg.max_design_rounds + 1):
        if not _design_failed(graph, report):
            break
        amendment = await _amend_design(cfg, graph, dev, root, report, round_no, recorder)
        if amendment is None or not amendment.ok:
            if amendment is not None:
                rounds.append(amendment)
            break
        rounds.append(amendment)
        try:
            dev = _apply_design(cfg, graph, dev, root, amendment.proposal, round_no=round_no)
        except (DesignDoesNotCompile, DesignViolatesContract) as exc:
            # Feed the checker's own words back in: it is the most precise evidence
            # available, and far better than "the proofs failed".
            amendment.problems.append(_design_problem(exc, revised=True))
            report = _with_design_error(report, str(exc))
            continue
        _adopt_proposal(cfg, graph, root, amendment.proposal)
        kept, reopened = _revalidate(graph, dev, Gate(dev), root)
        # A node that failed against the *old* design must be retried against the new
        # one -- otherwise the very failure that motivated the revision is the one
        # thing the revision cannot fix, and the loop revises into an empty frontier.
        retried = reopen_incomplete(graph)
        graph.emit(
            "design.amended", root.id, round=round_no,
            kept=kept, reopened=reopened, retried=retried,
        )
        gate = Gate(dev)
        scheduler = Scheduler(
            graph, dev, runner, anchor=cfg.target, gate=gate,
            workroot=cfg.workroot, concurrency=cfg.concurrency,
            node_seconds=cfg.node_seconds, max_attempts=cfg.max_attempts,
            skills=cfg.skills, state_tools=cfg.state_tools, library=cfg.library,
            check_command=cfg.check_command,
            recorder=recorder, corpus=cfg.corpus,
        )
        report = await scheduler.run()

    integrated, detail = integrate(graph, dev, gate, root)
    solution = _export_solution(recorder, graph, dev, root, integrated=integrated)
    if solution is not None:
        graph.emit("run.exported", root.id, path=str(solution))
    result = ProveResult(
        report=report,
        sentinels=sentinels,
        graph=graph,
        root=root,
        integrated=integrated,
        integration_detail=detail,
        record_dir=recorder.root if recorder else None,
        decomposition=decomposition,
        design_rounds=rounds,
        solution=solution,
    )
    graph.emit("run.finished", root.id, integrated=integrated, summary=report.render()[:1000])
    return result


def _has_children(graph: Graph, root: Node) -> bool:
    return any(n.id != root.id and n.proof_status != "attic" for n in graph.nodes())


#: How many times a decomposition killed by the clock is given more of it.
DECOMPOSE_DEADLINE_RETRIES = 2


async def _decompose(cfg: ProveConfig, graph: Graph, dev: Development, root: Node, recorder=None):
    """Ask a decomposer to state the obligations.  It cannot prove them.

    A round killed by the clock is retried with more of it. A deadline is not a
    judgement: the decomposer did not propose something wrong, it did not finish --
    and the first round on the largest rungs is exactly where that happens, because
    the design is hardest and the development is longest. `cached_strong` is 3180
    lines and its first round was killed at 1800 s, which ended the run outright,
    while a design that merely failed to *compile* would have been given three
    revisions. Same mistake as the contract check: a recoverable failure on a path
    with no recovery.

    Not retried: an infrastructure failure. A revoked credential does not get better
    with a longer deadline, and the ladder stops on it deliberately.
    """
    if cfg.decomposer_runner is None:
        return None
    from pcp.orch.decomposer import Decomposer
    from pcp.orch.failures import classify

    decomposer = Decomposer(
        graph, dev, cfg.decomposer_runner, workroot=cfg.workroot,
        recorder=recorder, corpus=cfg.corpus, library=cfg.library,
    )
    contract = _contract_for(cfg, dev)
    seconds = cfg.decomposer_seconds
    spent = 0.0
    out = None
    for attempt in range(1, DECOMPOSE_DEADLINE_RETRIES + 2):
        out = await decomposer.propose(root, contract=contract, budget_seconds=seconds)
        if out.ok or getattr(out, "infrastructure", False):
            return out
        if classify(out.violation or "").primary != "deadline":
            return out
        if attempt > DECOMPOSE_DEADLINE_RETRIES:
            return out
        # Never plan an attempt that cannot finish inside the run's own budget.
        # Doubling without this is how a generous first clock (4500 s on the cached
        # rungs) turns into a second attempt of 9000 s inside a 10800 s wall, so the
        # retry is killed by the outer timeout with nothing to show for either round.
        spent += seconds
        remaining = (root.budget.seconds or 0.0) - spent
        nxt = min(seconds * 2, remaining)
        if nxt < seconds:
            graph.emit("decomposer.gave_up", root.id, reason="deadline",
                       spent=spent, remaining=remaining)
            return out
        seconds = nxt
        graph.emit("decomposer.retried", root.id, reason="deadline",
                   attempt=attempt, next_seconds=seconds)
    return out


#: Vernacular that must live in the preamble, outside every Section.
_PREAMBLE_VERNAC = ("Require", "From", "Import", "Export", "Open Scope", "Close Scope",
                    "Set ", "Unset ", "Declare Scope", "Global Open Scope")


def _is_preamble_vernacular(text: str) -> bool:
    stripped = text.lstrip()
    return any(stripped.startswith(head) for head in _PREAMBLE_VERNAC)


def _add_imports(source: str, imports: Iterable[str]) -> str:
    """Append preamble lines after the existing Requires, skipping duplicates."""
    import re as _re

    existing = {" ".join(l.split()) for l in source.splitlines() if _re.match(r"\s*(From|Require)\b", l)}
    new = [line for line in imports if " ".join(line.split()) not in existing]
    if not new:
        return source
    last = 0
    for m in _re.finditer(r"^\s*(?:From\s+\S+\s+)?Require[^.]*\.\s*$", source, _re.M):
        last = m.end()
    return source[:last] + "\n" + "\n".join(new) + source[last:]


def _design_problem(exc: Exception, *, revised: bool = False) -> str:
    """What to tell the decomposer about a rejected design, in its own terms."""
    which = "revised design" if revised else "design"
    if isinstance(exc, DesignViolatesContract):
        return (
            f"your {which} changed a definition the contract freezes: {exc} "
            "You may *add* definitions -- new ghost state, new resource algebras, new "
            "helper predicates -- and they are placed for you. You may not rewrite one "
            "that is already there."
        )
    return f"the {which} does not compile: {exc}"


#: How many times one revision round may re-ask for a well-formed amendment.  This
#: is not extra design rounds: the design question is unchanged, only the answer was
#: unreadable, so re-asking costs a decomposer call and buys back the whole round.
_AMEND_ATTEMPTS = 3


def _amend_evidence(design_error: str, previous: Any) -> str:
    """The compile failure, plus what was wrong with the last answer to it."""
    if previous is None or previous.ok:
        return design_error
    return (
        design_error
        + "\n\nYour previous answer to this was rejected before it could be applied:\n"
        + previous.render()
        + "\n\nReturn the same design again, corrected to the required shape. Every "
        "entry in `definitions` needs both a `name` and a `text`; a definition you do "
        "not intend to change must simply be left out."
    )


async def _apply_with_revision(cfg: ProveConfig, graph: Graph, dev: Development, root: Node,
                               decomposition, recorder):
    """Apply the design, revising it if it does not compile.

    A design that does not typecheck is the *likeliest* first failure and the one the
    compiler describes most precisely, so it must be revisable like any other -- an
    earlier version aborted the run here, which made the commonest case the one case
    the revision loop could not reach.
    """
    attempts: list[Any] = []
    current = decomposition
    for round_no in range(1, cfg.max_design_rounds + 1):
        try:
            return _apply_design(cfg, graph, dev, root, current.proposal, round_no=round_no), current, attempts
        except (DesignDoesNotCompile, DesignViolatesContract) as exc:
            current.problems.append(_design_problem(exc))
            graph.emit("design.rejected", root.id, round=round_no, reason=str(exc)[:400])
            if round_no >= cfg.max_design_rounds:
                return None, current, attempts
            # A malformed *amendment* used to end the run on the spot, which made a
            # formatting slip fatal in exactly the place this loop exists to survive.
            # seqlock_design died this way with 2.5 h of its wall unspent: the
            # amendment came back with `design entry 'bcaf2' has no text`, and the
            # rung reported "no usable design" -- a claim about the design space,
            # made on the strength of a missing JSON field.  So a rejected answer is
            # retried with its own defect fed back, and only a genuine dead end (no
            # decomposer, or the provider itself down) stops the loop.
            revised = None
            for attempt in range(1, _AMEND_ATTEMPTS + 1):
                revised = await _amend_design(
                    cfg, graph, dev, root,
                    _with_design_error(RunReport(), _amend_evidence(str(exc), revised)),
                    round_no + 1, recorder,
                )
                if revised is None or revised.ok or revised.infrastructure:
                    break
                graph.emit(
                    "design.amendment_rejected", root.id, round=round_no + 1,
                    attempt=attempt, reason=revised.render()[:400],
                )
                attempts.append(revised)
            if revised is None or not revised.ok:
                if revised is not None and (not attempts or attempts[-1] is not revised):
                    attempts.append(revised)
                return None, current, attempts
            attempts.append(revised)
            current = revised
    return None, current, attempts


def _place_additions(text: str, additions: list[str]) -> str:  # noqa: D401
    """Insert each new declaration *before the first thing that uses it*.

    Putting every addition in one place cannot work.  A resource algebra the design
    invented is used by the typeclass, which sits above the `Section`; a ghost-state
    definition is used by the invariant, which sits inside it and needs `Σ` from the
    section's `Context`.  Anchoring everything at the first obligation put both after
    the definitions that referred to them, so the design did not compile and the
    decomposer was asked to revise a design that was never wrong.

    The first block whose text mentions the new name is that use, and inserting just
    above it lands on the right side of the `Section` either way.

    Additions also use *each other*, and that is the case anchoring against the
    original file alone cannot see: a helper whose only consumer is another addition
    matches nothing, falls back to the first proof block, and lands below the very
    definition that needed it.  A real design died this way, on a benchmark rung
    whose architecture is deliberately not described here: this file is readable
    from inside a worker's sandbox, so naming the shape of a solution in a comment
    would hand it over.  So dependencies among the additions are resolved too: each
    is pulled up to its earliest consumer, and ties break on dependency depth rather
    than on the order the decomposer happened to list them.
    """
    import re

    from pcp.core.vernac import parse_blocks

    blocks = parse_blocks(text)
    fallback = min(
        (b.statement_start for b in blocks if b.has_proof), default=len(text)
    )

    names = [next((b.name for b in parse_blocks(body) if b.name), None) for body in additions]

    def mentions(name: str, hay: str) -> bool:
        return re.search(rf"(?<![\w']){re.escape(name)}(?![\w'])", hay) is not None

    anchors: list[int] = []
    for name in names:
        anchor = fallback
        if name:
            anchor = min(
                (
                    b.statement_start
                    for b in blocks
                    # The statement is the right scope: a name used only inside a
                    # proof body is still covered, because the fallback is the first
                    # proof block and so precedes every proof.
                    if mentions(name, text[b.statement_start : b.statement_end])
                ),
                default=fallback,
            )
        anchors.append(anchor)

    # `needs[i]` is the set of additions that addition `i` refers to.
    needs = {
        i: {j for j, nm in enumerate(names) if j != i and nm and mentions(nm, body)}
        for i, body in enumerate(additions)
    }

    # A definition has to precede its users, so pull each one up to its earliest
    # consumer.  Iterated to a fixpoint because the pull propagates down a chain,
    # and bounded because a cycle is not expressible in Coq anyway -- if the design
    # contains one it will not compile whatever order we choose, and the decomposer
    # gets that error rather than a hang here.
    for _ in range(len(additions)):
        moved = False
        for i, ds in needs.items():
            for j in ds:
                if anchors[j] > anchors[i]:
                    anchors[j] = anchors[i]
                    moved = True
        if not moved:
            break

    # Within one anchor, order by how deep an addition sits in the dependency chain.
    depth = dict.fromkeys(needs, 0)
    for _ in range(len(additions)):
        moved = False
        for i, ds in needs.items():
            want = max((depth[j] + 1 for j in ds), default=0)
            if want > depth[i]:
                depth[i] = want
                moved = True
        if not moved:
            break

    out: list[str] = []
    cursor = 0
    for i in sorted(range(len(additions)), key=lambda i: (anchors[i], depth[i], i)):
        out.append(text[cursor : anchors[i]])
        out.append(additions[i].strip() + "\n\n")
        cursor = anchors[i]
    out.append(text[cursor:])
    return "".join(out)


def _contract_for(cfg: ProveConfig, dev: Development):
    """The declared design contract for this run."""
    from pcp.orch.contract import DesignContract

    if cfg.contract is not None:
        return cfg.contract
    return DesignContract.from_corpus(dev.path.parent)


def _with_design_error(report: RunReport, error: str) -> RunReport:
    """Carry a compile failure forward as the evidence for the next revision."""
    from pcp.orch.schedule import NodeOutcome

    carried = RunReport(
        outcomes=list(report.outcomes)
        + [NodeOutcome(node_id="design", name="<design>", status="stuck", evidence=error)],
        elapsed_s=report.elapsed_s,
        dispatched=report.dispatched,
    )
    return carried


def _design_failed(graph: Graph, report: RunReport) -> bool:
    """Did anything fail in a way the *design* could be responsible for?

    A protocol violation or a dead provider says nothing about the invariant, so
    revising the design on that evidence would be superstition.
    """
    blameless = {"runner-error", "protocol-violation", "permission-denied"}
    from pcp.orch.failures import classify

    for outcome in report.outcomes:
        if outcome.status == "qed":
            continue
        if outcome.status == "contested":
            return True
        klass = classify(outcome.evidence, status=outcome.status).primary
        if klass not in blameless:
            return True
    return False


def _design_evidence(report: RunReport, limit: int = 6000) -> str:
    """What the provers hit, in the decomposer's terms -- including what they asked for.

    A stuck worker may file `requests`: lemmas it would like to exist. The packet
    promises those "go back to whoever stated this node", and for a long time nothing
    kept that promise -- they were recorded and never read. That made the one channel
    a worker has for saying *this obligation is too large, split it here* a dead end,
    which matters most on exactly the rungs where it was used: `c129_register` asked
    for the bridging lemma it was blocked on, and the request went nowhere.

    Requests are quoted, never adopted. The decomposer decides whether a requested
    lemma becomes an obligation, because stating obligations is its job and a worker
    that could mint its own would be proving under a statement it wrote itself.
    """
    failed = [o for o in report.outcomes if o.status != "qed"]
    proved = [o for o in report.outcomes if o.status == "qed"]
    parts: list[str] = []
    asked: list[str] = []
    if failed:
        parts.append(_granularity_verdict(failed, proved))
    for outcome in failed:
        parts.append(f"--- {outcome.name} ({outcome.status}, {outcome.attempts} attempt(s), "
                     f"{outcome.elapsed_s:.0f}s): {_why_it_failed(outcome)}")
        parts.append(outcome.evidence.strip()[:2000] or "(no evidence recorded)")
        for request in getattr(outcome, "requests", None) or []:
            statement = (request.get("statement") or "").strip()
            if statement:
                asked.append(
                    f"--- {outcome.name} asked for:\n{statement[:1200]}"
                    + (f"\n  why: {request['rationale'].strip()[:400]}"
                       if request.get("rationale") else "")
                )
    if asked:
        parts.append(
            "\n=== lemmas the provers asked to exist ===\n"
            "These are requests, not decisions: a prover cannot state its own "
            "obligations. Judge each one -- a request that merely restates the "
            "prover's own goal is a prover that wants the problem solved for it, but "
            "a request that names a genuinely separate fact is usually a signal that "
            "the obligation you gave it is too large, and should be split there."
        )
        parts.extend(asked)
    return "\n".join(parts)[:limit]


#: What a failed obligation tells the orchestrator, by how it failed. The provers are
#: competent at tightly scoped work and demonstrably fail on obligations that bundle
#: several steps, so a failure is first evidence about the *statement*, not the prover.
def _why_it_failed(outcome: Any) -> str:
    from pcp.orch.failures import classify

    klass = classify(outcome.evidence or "", status=outcome.status).primary
    if outcome.status == "contested":
        return ("the prover argues the statement itself is wrong -- read its reasoning "
                "before restating; it may be right")
    if klass in ("deadline", "no-progress"):
        return ("ran out of clock without finishing: this obligation is too large. "
                "Split it")
    if outcome.requests:
        return ("could not finish and named the lemmas it was missing (below) -- those "
                "names are where this obligation should be cut")
    if outcome.attempts > 1:
        return (f"{outcome.attempts} independent attempts failed. A second prover "
                "failing the same way is evidence about the obligation, not the prover")
    return "did not finish"


def _granularity_verdict(failed: list, proved: list) -> str:
    """Tell the decomposer how to read a set of failures.

    The standard for an obligation is **tightly scoped proof engineering**: one
    self-contained step a competent prover can carry out without re-deriving the
    design. Measured across this ladder, obligations near that scale are nearly all
    proved and large ones are not -- so unproved obligations are, first, a signal that
    the decomposition was too coarse, and only after that a signal about provers.
    """
    return (
        f"=== {len(failed)} of {len(failed) + len(proved)} obligations were not proved ===\n"
        "Read this as a verdict on the decomposition before you read it as a verdict on "
        "the provers. Every obligation you state must be **tightly scoped proof "
        "engineering**: one self-contained step, provable without re-deriving your "
        "design. An obligation that no prover finishes was not that.\n"
        "Your first remedy is to **split the failing obligations further** -- more, "
        "smaller children, stated in the same vocabulary. Revising the design itself is "
        "the right move only when the evidence says the design is wrong (a prover "
        "contests a statement, or an invariant cannot be restored at a close site), not "
        "merely when a proof was hard."
    )


async def _amend_design(cfg: ProveConfig, graph: Graph, dev: Development, root: Node,
                        report: RunReport, round_no: int, recorder=None):
    if cfg.decomposer_runner is None:
        return None
    from pcp.core.vernac import parse_blocks
    from pcp.orch.decomposer import Decomposer

    designed = [
        dev.source[b.statement_start : b.statement_end]
        for b in parse_blocks(dev.source)
        if b.head == "Definition"
    ]
    decomposer = Decomposer(
        graph, dev, cfg.decomposer_runner, workroot=cfg.workroot,
        recorder=recorder, corpus=cfg.corpus, library=cfg.library,
    )
    return await decomposer.amend(
        root,
        design=designed,
        evidence=_design_evidence(report),
        round_no=round_no,
        budget_seconds=cfg.decomposer_seconds,
    )


def _revalidate(graph: Graph, dev: Development, gate: Gate, root: Node) -> tuple[list[str], list[str]]:
    """Replay every existing proof against the amended design before re-dispatching.

    PLAN.md 8.5: salvage is replay-first.  After a small amendment most proofs
    survive verbatim, and replay is deterministic and nearly free -- so spending a
    worker before trying it is pure waste.  What does not survive is *statement
    invalidation*: the proof was written against a definition that now means
    something else, so it re-opens.
    """
    from pcp.orch.assemble import NodeSpec

    kept: list[str] = []
    reopened: list[str] = []
    # Only nodes with a proof need replaying; the rest are re-opened by
    # `reopen_incomplete`, which is what makes a revision reach a stuck node.
    nodes = [n for n in graph.nodes() if n.body]
    for node in nodes:
        specs = [
            NodeSpec(name=o.name, statement=o.statement, body=o.body)
            for o in graph.nodes()
            if o.id != node.id and not dev.block(o.name)
        ]
        is_anchor = bool(dev.block(node.name))
        result = gate.run(
            root.name,
            specs if is_anchor else specs + [NodeSpec(node.name, node.statement, node.body)],
            target_body=node.body if is_anchor else None,
            target=node.name,
            truncate=True,
            stub_prefix=True,
        )
        if result.ok:
            kept.append(node.name)
        else:
            graph.update(node.id, proof_status="open", epoch=node.epoch + 1)
            reopened.append(node.name)
    return kept, reopened


def _apply_design(cfg: ProveConfig, graph: Graph, dev: Development, root: Node, proposal,
                  round_no: int = 1) -> Development:
    """Write the decomposer's design into a working copy of the development.

    A design rung leaves the invariant and the abstract predicate blank, and a prover
    cannot fill them in -- it returns proof bodies, never statements.  So the design
    comes from the decomposer, is applied here, and is then *frozen* for the provers
    exactly like any other spec-zone artifact.

    What may not move: the program and the specifications.  That is checked, not
    trusted -- if the decomposer touched either, the design is rejected.
    """
    if not proposal.definitions and not proposal.imports:
        return dev
    from pcp.core.vernac import parse_blocks

    text = dev.source
    blocks = {b.name: b for b in parse_blocks(text)}
    edits: list[tuple[int, int, str]] = []
    additions: list[str] = []
    hoisted: list[str] = list(proposal.imports)
    for definition in proposal.definitions:
        body = definition.text.strip()
        # `Require` and friends are only legal outside a Section, so they are hoisted
        # rather than being the designer's problem to place.
        if _is_preamble_vernacular(body):
            hoisted.append(body)
            continue
        block = blocks.get(definition.name) if definition.name else None
        if block is None:
            additions.append(body)
            continue
        edits.append((block.statement_start, block.statement_end, body))
    out: list[str] = []
    cursor = 0
    for start, end, replacement in sorted(edits):
        out.append(text[cursor:start])
        out.append(replacement)
        cursor = end
    out.append(text[cursor:])
    patched = "".join(out)

    if hoisted:
        patched = _add_imports(patched, hoisted)

    if additions:
        patched = _place_additions(patched, additions)

    # The contract decides what may move -- the developer declares it, and it is
    # checked here.  Deriving the protected set from what the decomposer proposed
    # would let the decomposer choose its own permissions, which is not a contract.
    contract = _contract_for(cfg, dev)
    check = contract.check(dev.source, patched)
    if not check.ok:
        raise DesignViolatesContract(
            "the design changed something the contract does not permit: "
            + check.detail
            + f"  --  contract: {contract.describe()}"
        )

    target = Path(cfg.workroot) / f"{root.id}.designed{'' if round_no == 1 else round_no}" / dev.path.name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(patched, encoding="utf-8")
    for extra in ("_CoqProject", "DESIGN.md"):
        src = dev.path.parent / extra
        if src.exists():
            (target.parent / extra).write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
    # A design that does not compile poisons every node beneath it, and each of
    # those workers then reports the same unrelated failure.  One compile here costs
    # seconds; skipping it cost five workers twenty turns each.
    designed = Development(target)
    ok, output = Gate(designed)._compile(Assembly(text=patched))
    if not ok:
        raise DesignDoesNotCompile(_first_error(output) or output[-1500:])

    # The same argument, one layer down, and it took a whole seqlock_wf rung to see
    # it: the compile above covers the *definitions*, but a child's **statement** is
    # frozen and inserted into every worker's file as an `Admitted` stub, and Rocq
    # elaborates a Lemma's type even when its proof is admitted. So a child that does
    # not typecheck poisons the file for every sibling. One round proposed
    # `z = 1 + Z.of_nat ver` without `%Z`; in `nat_scope` that does not elaborate,
    # 14 workers were dispatched against a file that could never compile, and each
    # correctly reported a failure that had nothing to do with its own lemma.
    if proposal.children:
        specs = [NodeSpec(name=c.name, statement=c.statement, body=None) for c in proposal.children]
        ok, output = Gate(designed)._compile(
            # The per-node shape, and the fast one: stubbing the other proofs is
            # 5.4 s against 512 s on the cached rungs and changes nothing about
            # whether a statement elaborates.
            designed.assemble(root.name, specs, anchor_body=None, truncate=True, stub_prefix=True)
        )
        if not ok:
            detail = _first_error(output) or output[-1500:]
            raise DesignDoesNotCompile(
                f"a child statement does not typecheck{_blame_child(detail, specs)}: {detail}"
            )

    graph.emit("design.applied", root.id, definitions=proposal.definition_names(), file=str(target))
    graph.set_meta("designed_file", str(target))
    return designed


def _blame_child(detail: str, specs: list[NodeSpec]) -> str:
    """Name the offending child when the compiler's message identifies one.

    "a child statement does not typecheck" sends the decomposer looking through all
    fourteen; naming it sends it to the one line that is wrong.
    """
    named = [s.name for s in specs if s.name and s.name in detail]
    return f" (`{named[0]}`)" if len(named) == 1 else ""


def _adopt_proposal(cfg: ProveConfig, graph: Graph, root: Node, proposal) -> list[Node]:
    """Turn a validated proposal into frozen, dispatchable nodes.

    Nothing about a proof passes through here: a proposal has no proof to carry, and
    the nodes are created `open`.
    """
    budget = cfg.budget.split(max(1, len(proposal.children)))
    created: list[Node] = []
    wanted = {c.name for c in proposal.children}
    for i, child in enumerate(proposal.children):
        existing = graph.by_name(child.name)
        if existing is not None:
            # A revision may bring back an obligation an earlier one dropped. Without
            # this it stays in the attic, because the name is taken -- so the design
            # asks for a lemma the scheduler will never dispatch, and integration
            # then waits for a body that nothing is working on.
            if existing.proof_status == "attic":
                graph.set_proof_status(existing.id, "open" if not existing.body else "gated")
                graph.emit("plan.revived", existing.id, round_of=root.id)
            continue
        node = graph.add_node(
            Node(
                id=_slug(child.name),
                name=child.name,
                statement=child.statement.strip(),
                statement_hash=statement_hash(child.statement),
                rank="local",
                parent=root.id,
                depth=root.depth + 1,
                statement_status="frozen",
                proof_status="open",
                owner="decomposer",
                intent=(child.rationale or proposal.rationale)[:400],
                budget=budget,
                file=str(cfg.file),
                ordering=i,
            )
        )
        graph.add_edge(root.id, node.id)
        created.append(node)
    # Retire what this design no longer asks for. Nothing used to, and `attic` was a
    # status the schema defined and no code ever wrote -- so an amendment that
    # changed the split orphaned the obligations it dropped. They stayed `open`, so
    # the frontier kept dispatching workers at a lemma no design needed (against
    # definitions the revision may have removed), and `integrate()` demands a body
    # from every non-attic node, so the run could never finish.
    #
    # Only *unproved* orphans are retired. A proved one may still be cited by the
    # root's proof, and retiring it would break the assembly; `_revalidate` already
    # re-opens any proof the new definitions invalidated, which turns a stale proved
    # orphan into an unproved one that this retires on the next round.
    retired: list[str] = []
    for node in graph.nodes(parent=root.id):
        if node.name in wanted or node.proof_status == "attic" or node.body:
            continue
        graph.set_proof_status(node.id, "attic")
        retired.append(node.name)
    if retired:
        graph.emit("plan.retired", root.id, retired=retired)
    graph.emit("plan.adopted", root.id,
               children=[c.name for c in proposal.children], retired=retired)
    return created


def reopen_incomplete(graph: Graph) -> list[str]:
    """Make a resumed run pick up where the last one stopped.

    `pcp prove` resumed after a crash picks up from the SQLite graph, so anything a
    previous run left mid-flight has to become dispatchable again:

    * ``claimed`` -- a worker that was in flight when the process died.
    * ``stuck``   -- a node that exhausted its attempts last time.  Its stored
      evidence is carried into the new run's first attempt, so the retry is
      evidence-informed rather than a blind repeat.

    ``contested`` is deliberately *not* re-opened: it is a statement question, and it
    lands back with the human to adjudicate.  Re-dispatching it would spend a worker
    on a lemma someone has already argued is wrong.
    """
    reopened: list[str] = []
    for node in graph.nodes():
        if node.proof_status in ("claimed", "stuck") and node.statement_status == "frozen":
            graph.update(node.id, proof_status="open")
            reopened.append(node.name)
    return reopened


def _export_solution(
    recorder: Any, graph: Graph, dev: Development, root: Node, *, integrated: bool
) -> Path | None:
    """Write out what the run actually produced, finished or not.

    A run's answer otherwise exists only as node bodies in a SQLite graph, which is
    not something a later run can be handed.  This is the artifact a ladder passes
    forward: what *this* system proved, never what the corpus already knew.

    Exported even when the run does not integrate, because a person carrying their
    own work to the next problem carries the half-finished version too -- but then
    the header says so, so nothing downstream reads an `Admitted` as a result.
    """
    if recorder is None:
        return None
    nodes = [n for n in graph.nodes() if n.rank != "root" and n.proof_status != "attic"]
    root_now = graph.get(root.id)
    specs = [NodeSpec(name=n.name, statement=n.statement, body=n.body, mockable=n.mockable) for n in nodes]
    text = dev.assemble(root.name, specs, anchor_body=(root_now.body if root_now else None), truncate=False).text
    proved = sorted(n.name for n in nodes if n.body) + ([root.name] if root_now and root_now.body else [])
    open_ = sorted(n.name for n in nodes if not n.body) + ([] if root_now and root_now.body else [root.name])

    out_dir = recorder.root / "solution"
    out_dir.mkdir(parents=True, exist_ok=True)
    target = out_dir / dev.path.name
    # Ground truth for what is unproved is the artifact itself, not the graph.  A
    # specification the corpus held out but this run never took as an obligation is
    # in neither `proved` nor `open_`, yet it sits in `text` as `Admitted` -- which
    # is precisely the case the docstring above promises the header will catch.
    from pcp.core.vernac import parse_blocks

    admitted = sorted(b.name for b in parse_blocks(text) if b.admitted and b.name)
    target.write_text(
        _solution_header(root, integrated, proved, open_, admitted) + text, encoding="utf-8"
    )
    for extra in ("_CoqProject",):
        src = dev.path.parent / extra
        if src.exists():
            (out_dir / extra).write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
    return target


def _solution_header(
    root: Node,
    integrated: bool,
    proved: list[str],
    open_: list[str],
    admitted: list[str] = (),
) -> str:
    """Describe the artifact honestly, including what it does *not* prove.

    `integrated` is a statement about the root lemma alone: the root Qeds and its
    `Print Assumptions` is clean.  It says nothing about the other specifications the
    corpus held out, which stay `Admitted` in the same file because this run never
    took them as obligations.  Reporting that as "COMPLETE / open: nothing" told a
    reader -- and the next rung, which is handed this file as a worked example -- that
    an axiom was a result.  So the root verdict and the file's remaining admits are
    now two separate claims, and the strong word is reserved for when both hold.
    """
    admitted = [n for n in admitted if n != root.name]
    if not integrated:
        verdict = f"INCOMPLETE: `{root.name}` did not integrate. Anything still `Admitted` below is unproved."
    elif admitted:
        verdict = (
            f"PARTIAL: `{root.name}` Qeds and its `Print Assumptions` is clean, but "
            f"{len(admitted)} other specification(s) in this file are still `Admitted`."
        )
    else:
        verdict = f"COMPLETE: `{root.name}` Qeds and `Print Assumptions` is clean."
    lines = [
        "(* Produced by proof-copilot. This is machine-generated work, not a reference.",
        f"   {verdict}",
        f"   proved: {', '.join(proved) or 'nothing'}",
        f"   open:   {', '.join(open_) or 'nothing'}",
        f"   ADMITTED (unproved) in this file: {', '.join(admitted) or 'nothing'}",
        " *)",
        "",
    ]
    return "\n".join(lines)


def integrate(graph: Graph, dev: Development, gate: Gate, root: Node) -> tuple[bool, str]:
    """Completion has a machine oracle: `Qed` plus a clean `Print Assumptions`.

    A plan *integrates* only when its glue Qeds -- and here the glue is the root
    itself, proved from children that must by then be proved rather than admitted.
    """
    nodes = [n for n in graph.nodes() if n.rank != "root" and n.proof_status != "attic"]
    missing = [n.name for n in nodes if not n.body]
    if missing:
        return False, f"{len(missing)} obligation(s) still open: {', '.join(missing[:6])}"
    root_now = graph.get(root.id)
    if root_now is None or not root_now.body:
        return False, f"the root `{root.name}` is not proved yet"

    specs = [NodeSpec(name=n.name, statement=n.statement, body=n.body, mockable=n.mockable) for n in nodes]
    result = gate.run(
        root.name,
        specs,
        target_body=root_now.body,
        # Per-node checks truncate for speed; integration compiles the whole file,
        # so the rest of the development is checked against the finished root too.
        truncate=False,
        check_assumptions=True,
    )
    if not result.ok:
        return False, "the integration gate failed:\n" + result.render()
    leftover = sorted({a for axioms in result.assumptions.values() for a in axioms})
    if leftover:
        return False, f"`Print Assumptions` is not clean: {', '.join(leftover)}"
    for n in nodes:
        graph.set_proof_status(n.id, "integrated")
    graph.set_proof_status(root.id, "integrated")
    return True, ""


def run(cfg: ProveConfig, runner: Runner) -> ProveResult:
    return asyncio.run(prove(cfg, runner))


def _slug(name: str) -> str:
    return "".join(c if c.isalnum() or c in "_-" else "_" for c in name)[:64]
