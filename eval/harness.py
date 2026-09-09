#!/usr/bin/env python3
"""The held-out-lemma harness (PLAN.md 13; contract §1.16).

Without this you cannot tell whether the tooling helps, and every subsequent design
decision is taste.  Method: hold out lemmas from a real development, replace the
bodies with ``Admitted``, and ask an agent to reprove them.

Every task is **one ordinary ``pcp prove`` run** (:func:`pcp.orch.prove.run` with
``require_orchestration=False`` and a single attempt), so the harness measures the
same packet, the same gate and the same records as the daily loop -- the legacy
harness hand-rolled its own packet and ``pcp-node.json`` and so ran a *different*
arm under the same name as ``pcp prove --state-tools`` (bugs-dash-eval: harness.py:209).

What the structure makes impossible, rather than fixes:

* **The control arm is a control.**  A runner is built *per arm* from that arm's
  :class:`eval.ablations.Ablation`; the baseline's command line therefore carries no
  ``--mcp-config`` and no ``mcp__pcp__*`` allowlist entry, because there is no other
  arm's grant anywhere in reach when it is built (harness.py:349, four reports).
* **Nothing stale is ever scored.**  A task's directory under ``--workroot`` is
  removed before the task starts, and every attempt inside a run gets a fresh
  directory anyway (harness.py:182, two reports).
* **Records are never overwritten.**  Each arm records under its own run id
  (``<record>/<run-id>-<arm>/``), each task under its own subtree (harness.py:255).
* **An outage is not an unsolved lemma.**  ``error`` outcomes (a missing binary, a
  gate that could not run) are counted separately and excluded from the rate the
  ablation deltas compare (harness.py:299).
* **One task cannot lose the others.**  Every task's failure -- a runner raising, a
  ``UsageError`` -- becomes that task's ``error`` outcome.

    python eval/harness.py --files 'iris/heap_lang/lib/*.v' --limit 20 --runner mock
    python eval/harness.py --corpus eval/corpus/bench/rwcas --reference .pcp/reference/rwcas \\
        --sandbox --runner claude --ablations baseline,ledger
"""

from __future__ import annotations

import argparse
import asyncio
import json
import random
import statistics
import sys
import time
from collections.abc import Callable, Mapping, Sequence
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from eval.ablations import LADDER, Ablation, deltas  # noqa: E402
from eval.make_benchmark import hold_out  # noqa: E402
from pcp.cli.common import absolute  # noqa: E402
from pcp.cli.runners import PERMISSION_RUNNERS, effort_for, model_for, pick_auto  # noqa: E402
from pcp.config.env import library_roots  # noqa: E402
from pcp.config.load import load as load_config  # noqa: E402
from pcp.config.schema import Config  # noqa: E402
from pcp.errors import PcpError, UsageError  # noqa: E402
from pcp.orch.failures import summarize  # noqa: E402
from pcp.orch.protocol import Runner  # noqa: E402
from pcp.orch.prove import ProveConfig, ProveResult, prove  # noqa: E402
from pcp.orch.record import load_records  # noqa: E402
from pcp.orch.runners.base import (  # noqa: E402
    RUNNER_NAMES,
    RunnerSpec,
    build_runner,
    is_subprocess_runner,
    provider_for,
)
from pcp.rocq.decls import parse_blocks  # noqa: E402
from pcp.util.io import (  # noqa: E402
    atomic_write_text,
    copy_if_exists,
    ensure_dir,
    json_dump,
    json_load,
    read_text,
    rm_tree,
    slug,
)
from pcp.util.paths import repo_root  # noqa: E402
from pcp.util.text import indent  # noqa: E402

BENCH_FILE = "bench.json"
REFERENCE_FILE = "reference.json"
#: Bodies longer than this are not "a lemma", they are a development.
MAX_BODY_CHARS = 4000
DEFAULT_FILES = "iris/heap_lang/lib/*.v"
DEFAULT_RECORD = Path(".pcp/records")
DEFAULT_WORKROOT = Path(".pcp/eval")
DEFAULT_OUT = Path(".pcp/eval/results.json")
INDEX_PATH = Path(".pcp/docs/index.txt")
BRIEFS = ("full", "spec-only")
ERROR_LIMIT = 2000


def warn(message: str) -> None:
    print(message, file=sys.stderr, flush=True)


# ------------------------------------------------------------------ tasks


@dataclass(frozen=True)
class Task:
    """One held-out lemma.  ``held_out`` says whether ``file`` already lacks the body
    (a corpus built by ``make_benchmark``) or still has it (a library file, copied
    and stubbed per task by :meth:`materialise`; the library is never modified)."""

    file: Path
    lemma: str
    statement: str
    held_out: bool
    reference_body: str = ""
    reference_tactics: int = 0

    @property
    def key(self) -> str:
        """A collision-free directory name (``slug`` hashes anything lossy)."""
        return slug(f"{self.file.stem}__{self.lemma}")

    def materialise(self, dest: Path) -> Path:
        """The file a run proves against.  A corpus is used in place (the run only
        reads it); a library file is copied into ``dest`` with this lemma's body
        replaced by ``Admitted`` -- span edits over the lexer's offsets."""
        if self.held_out:
            return self.file
        text, _ = hold_out(read_text(self.file), [self.lemma])
        out = ensure_dir(dest) / self.file.name
        atomic_write_text(out, text)
        copy_if_exists(self.file.parent / "_CoqProject", dest / "_CoqProject")
        return out

    def to_json(self) -> dict[str, Any]:
        return {
            "file": str(self.file), "lemma": self.lemma, "statement": self.statement,
            "held_out": self.held_out, "reference_tactics": self.reference_tactics,
        }


def collect_benchmark(corpus: Path, reference: Path | None = None) -> list[Task]:
    """Load a corpus built by ``eval/make_benchmark.py``.

    The held-out names come from the corpus's own ``bench.json`` and must resolve to
    ``Admitted`` blocks of the corpus file; a name that does not is *reported*, not
    silently dropped (the legacy harness shrank ``n`` without a word).  Reference
    bodies come from the answer key, which lives elsewhere and is never bound into a
    worker sandbox; scoring is by the gate, not by diffing against it.
    """
    corpus = Path(corpus)
    meta = json_load(corpus / BENCH_FILE)
    source_path = (corpus / meta["file"]).resolve()
    blocks = {b.name: b for b in parse_blocks(read_text(source_path)) if b.name}
    refs: dict[str, str] = {}
    if reference is not None and (Path(reference) / REFERENCE_FILE).exists():
        ref = json_load(Path(reference) / REFERENCE_FILE)
        refs = {h.get("anonymised") or h["name"]: h.get("reference_body", "") for h in ref.get("holdout", [])}
    tasks: list[Task] = []
    for h in meta.get("holdout", []):
        name = h.get("anonymised") or h["name"]
        block = blocks.get(name)
        if block is None:
            warn(f"{corpus.name}: holdout {name!r} is not declared in {meta['file']}; skipped (bench.json and the .v disagree)")
            continue
        if not block.admitted:
            warn(f"{corpus.name}: holdout {name!r} is not Admitted in {meta['file']}; skipped (its proof is present)")
            continue
        tasks.append(Task(
            file=source_path, lemma=name, statement=block.statement, held_out=True,
            reference_body=refs.get(name, ""), reference_tactics=int(h.get("tactics", 0) or 0),
        ))
    return tasks


def collect_tasks(root: Path, pattern: str, *, limit: int, seed: int = 0) -> list[Task]:
    """Hold out lemmas from an installed library: real statements, real ``Qed`` proofs."""
    tasks: list[Task] = []
    files = sorted(p for p in Path(root).glob(pattern) if "__pcp" not in p.stem)
    rng = random.Random(seed)
    rng.shuffle(files)
    for path in files:
        source = read_text(path)
        for block in parse_blocks(source):
            if not block.name or block.kind != "script" or block.ender != "Qed":
                continue
            body = block.body(source).strip()
            if not body or len(body) > MAX_BODY_CHARS:
                continue
            tasks.append(Task(
                file=path.resolve(), lemma=block.name, statement=block.statement, held_out=False,
                reference_body=body, reference_tactics=len(block.tactics()),
            ))
        if len(tasks) >= limit * 3:
            break
    rng.shuffle(tasks)
    return tasks[:limit]


# ------------------------------------------------------------------ outcomes and metrics


@dataclass
class Outcome:
    """One task's result.  ``solved`` is the gate's verdict alone (``status == qed``);
    ``integrated`` additionally says the whole file compiled with clean assumptions.
    ``infrastructure`` marks an ``error``: the run, not the worker, failed."""

    file: str
    lemma: str
    status: str = "stuck"  # qed | stuck | contested | error
    solved: bool = False
    infrastructure: bool = False
    integrated: bool = False
    attempts: int = 1
    elapsed_s: float = 0.0
    tokens: int = 0
    requests: int = 0
    dollars: float = 0.0
    tool_calls: int = 0
    turns: int = 0
    checks: int = 0
    error: str = ""
    record: str = ""

    def to_json(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_json(cls, d: Mapping[str, Any]) -> Outcome:
        known = set(cls.__dataclass_fields__)
        return cls(**{k: v for k, v in d.items() if k in known})


@dataclass
class Metrics:
    """The metrics PLAN.md 13 names, and no vanity ones.

    ``error`` outcomes are counted, printed, and kept out of the denominator: the
    solve rate is over the tasks that were *measured*, so a rung whose binary was
    missing does not read as a rung whose tools did not help.
    """

    ablation: str
    n: int = 0
    solved: int = 0
    errors: int = 0
    outcomes: list[Outcome] = field(default_factory=list)

    @property
    def measured(self) -> int:
        return self.n - self.errors

    @property
    def solve_rate(self) -> float:
        return self.solved / self.measured if self.measured else 0.0

    def add(self, outcome: Outcome) -> None:
        self.outcomes.append(outcome)
        self.n += 1
        self.solved += int(outcome.solved)
        self.errors += int(outcome.status == "error")

    def per_solved(self, attr: str) -> float:
        vals = [getattr(o, attr) for o in self.outcomes if o.solved]
        return statistics.mean(vals) if vals else 0.0

    def render(self) -> str:
        line = (
            f"{self.ablation:<14} solve {self.solved}/{self.measured} ({100 * self.solve_rate:.0f}%)  "
            f"tokens/solved {self.per_solved('tokens'):.0f}  "
            f"tools/solved {self.per_solved('tool_calls'):.1f}  "
            f"checks/solved {self.per_solved('checks'):.1f}  "
            f"wall/solved {self.per_solved('elapsed_s'):.0f}s  "
            f"${sum(o.dollars for o in self.outcomes):.2f}"
        )
        if self.errors:
            line += f"  error {self.errors}"
        return line

    def to_json(self) -> dict[str, Any]:
        return {
            "ablation": self.ablation,
            "n": self.n,
            "measured": self.measured,
            "solved": self.solved,
            "errors": self.errors,
            "solve_rate": self.solve_rate,
            "tokens_per_solved": self.per_solved("tokens"),
            "tool_calls_per_solved": self.per_solved("tool_calls"),
            "wall_per_solved": self.per_solved("elapsed_s"),
            "outcomes": [o.to_json() for o in self.outcomes],
        }

    @classmethod
    def from_json(cls, d: Mapping[str, Any]) -> Metrics:
        m = cls(ablation=str(d["ablation"]))
        for o in d.get("outcomes", []):
            m.add(Outcome.from_json(o))
        return m


# ------------------------------------------------------------------ one runner per arm


def arm_spec(
    name: str,
    arm: Ablation,
    *,
    cfg: Config,
    model: str | None = None,
    sandbox: Any | None = None,
    answers: Mapping[str, str] | None = None,
) -> tuple[RunnerSpec, list[str]]:
    """The :class:`RunnerSpec` for ``arm`` -- and only ``arm``.

    Mirrors ``pcp.cli.runners.select_runner`` (model binding, effort, permission
    mode) so an arm run here is the arm ``pcp prove --state-tools`` would run.  The
    grant is exactly ``arm.tools``: the mock has no command line to grant on, so its
    grant lives in the packet alone (``ProveConfig.state_tools``); a runner that
    cannot honour a grant (``codex``) is refused by the factory rather than run
    without it.
    """
    if name != "auto" and name not in RUNNER_NAMES:
        raise UsageError(f"unknown runner {name!r}; choose from {', '.join(RUNNER_NAMES)}")
    chosen = pick_auto(cfg, "prover") if name == "auto" else name
    provider = provider_for(chosen)
    resolved, note = model_for("prover", cfg, provider, flag=model, flag_name="--model")
    notes = [note] if note else []
    permission = None
    if chosen in PERMISSION_RUNNERS:
        permission = "bypassPermissions" if sandbox is not None else "acceptEdits"
    spec = RunnerSpec(
        runner=chosen,
        model=resolved,
        effort=effort_for("prover", cfg, chosen, flag=None),
        permission_mode=permission,
        mcp_tools=() if chosen == "mock" else tuple(arm.tools),
        sandbox=sandbox,
        answers=dict(answers) if chosen == "mock" and answers else None,
    )
    return spec, notes


def arm_runner(name: str, arm: Ablation, *, cfg: Config, **kw: Any) -> tuple[Runner, list[str]]:
    spec, notes = arm_spec(name, arm, cfg=cfg, **kw)
    return build_runner(spec), notes


def benchmark_sandbox(runner_name: str, *, reference: Path | None, corpus_dir: Path | None) -> Any:
    """``Sandbox.for_benchmark`` for this harness: the answer key masked, the corpus
    under test (if any) bound back, no library.  Each attempt additionally binds the
    directory of the file being proved (``SandboxedRunner``), which is how a per-task
    library copy or a ``--brief spec-only`` staging reaches ``pcp check``."""
    from pcp.orch.runners import sandbox as sb

    if not is_subprocess_runner(build_runner(RunnerSpec(runner_name))):
        raise UsageError(
            f"--sandbox needs a subprocess runner; {runner_name} runs in-process. Use --runner codex or --runner claude."
        )
    if not sb.available():
        raise UsageError("--sandbox needs bubblewrap (`bwrap`); install it or drop --sandbox")
    return sb.Sandbox.for_benchmark(
        repo_root(), reference=reference, corpus_dir=corpus_dir, library=[], provider=provider_for(runner_name),
    )


# ------------------------------------------------------------------ one task, one run


@dataclass(frozen=True)
class ArmPaths:
    """Where one arm's work and records go.  ``record`` is ``None`` when not recording."""

    workroot: Path
    record: Path | None = None

    def task_root(self, task: Task) -> Path:
        return self.workroot / task.key

    def task_record(self, task: Task) -> Path | None:
        return None if self.record is None else self.record / task.key


def task_config(
    task: Task,
    arm: Ablation,
    paths: ArmPaths,
    *,
    timeout: float,
    brief: str = "full",
    corpus_label: str = "",
    cfg: Config | None = None,
    index_path: Path | None = None,
) -> ProveConfig:
    """The ``pcp prove`` configuration for one task: the target is the root, there is
    no plan, one attempt, the arm's tools and skill, ``--node-seconds`` = the timeout."""
    root = paths.task_root(task)
    rm_tree(root)  # fresh per run: nothing an earlier run wrote can be read as this run's answer
    ensure_dir(root)
    file = task.materialise(root / "corpus")
    return ProveConfig(
        file=file,
        target=task.lemma,
        plan=None,
        graph_path=root / "graph.db",
        workroot=root / "work",
        concurrency=1,
        node_seconds=float(timeout),
        max_attempts=1,
        skills=arm.skill_texts(),
        state_tools=list(arm.tools),
        record_root=paths.task_record(task),
        corpus=corpus_label,
        require_orchestration=False,
        brief=brief,
        config=cfg,
        index_path=index_path,
    )


def _attempt_cost(result: ProveResult) -> dict[str, float]:
    """Cost summed over the root's attempt rows (``cost`` is JSON text in the graph)."""
    total: dict[str, float] = {}
    for row in result.graph.attempts_for(result.root.id):
        try:
            cost = json.loads(row.get("cost") or "{}")
        except (TypeError, ValueError):
            continue
        if not isinstance(cost, dict):
            continue
        for key, value in cost.items():
            if isinstance(value, int | float):
                total[key] = total.get(key, 0.0) + float(value)
    return total


def outcome_of(task: Task, result: ProveResult, *, elapsed_s: float) -> Outcome:
    """Read the harness's row off a finished run: the root's outcome, its cost, its record."""
    root = next((o for o in result.report.outcomes if o.node_id == result.root.id), None)
    if root is None:
        return Outcome(
            file=str(task.file), lemma=task.lemma, status="error", infrastructure=True,
            elapsed_s=elapsed_s, attempts=0,
            error=("the run dispatched nothing: " + result.integration_detail)[:ERROR_LIMIT],
            record=str(result.record_dir or ""),
        )
    cost = _attempt_cost(result)
    solved = root.status == "qed"
    return Outcome(
        file=str(task.file),
        lemma=task.lemma,
        status=root.status,
        solved=solved,
        infrastructure=root.status == "error",
        integrated=bool(result.integrated),
        attempts=root.attempts,
        elapsed_s=elapsed_s,
        tokens=int(cost.get("tokens", 0)),
        requests=int(cost.get("requests", 0)),
        dollars=float(cost.get("dollars", 0.0)),
        tool_calls=int(cost.get("tool_calls", 0)),
        turns=int(cost.get("turns", 0)),
        checks=int(cost.get("check_iterations", 0)),
        error="" if solved else root.evidence[:ERROR_LIMIT],
        record=str(result.record_dir or ""),
    )


async def run_task(task: Task, arm: Ablation, runner: Runner, paths: ArmPaths, **kw: Any) -> Outcome:
    """One task = one ``pcp prove`` run.  Any failure of the run itself is this task's
    ``error`` outcome, never an exception that takes the arm down."""
    started = time.perf_counter()
    try:
        cfg = task_config(task, arm, paths, **kw)
        result = await prove(cfg, runner)
    except Exception as exc:  # noqa: BLE001 -- the whole point: one task, not the arm
        return Outcome(
            file=str(task.file), lemma=task.lemma, status="error", infrastructure=True, attempts=0,
            elapsed_s=time.perf_counter() - started,
            error=f"the harness could not run this task ({type(exc).__name__}): {exc}"[:ERROR_LIMIT],
        )
    try:
        return outcome_of(task, result, elapsed_s=time.perf_counter() - started)
    finally:
        result.close()


async def run_arm(
    tasks: Sequence[Task],
    arm: Ablation,
    runner: Runner,
    paths: ArmPaths,
    *,
    concurrency: int = 8,
    on_outcome: Callable[[Task, Outcome], None] | None = None,
    **kw: Any,
) -> Metrics:
    """Every task of one arm, ``concurrency`` at a time, with this arm's runner."""
    sem = asyncio.Semaphore(max(1, int(concurrency)))

    async def one(task: Task) -> Outcome:
        async with sem:
            outcome = await run_task(task, arm, runner, paths, **kw)
        if on_outcome is not None:
            on_outcome(task, outcome)
        return outcome

    metrics = Metrics(ablation=arm.name)
    for outcome in await asyncio.gather(*(one(t) for t in tasks)):
        metrics.add(outcome)
    return metrics


# ------------------------------------------------------------------ the CLI


def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--corpus", type=Path, default=None, help="a benchmark directory built by eval/make_benchmark.py")
    ap.add_argument("--reference", type=Path, default=None, help="its answer key (masked in the sandbox; stats only)")
    ap.add_argument("--sandbox", action="store_true",
                    help="run workers in bubblewrap with the answer key and the forges out of reach")
    ap.add_argument("--record", type=Path, default=DEFAULT_RECORD,
                    help="where attempt records go; `pcp failures` reads them")
    ap.add_argument("--no-record", action="store_true", help="keep no attempt records (smoke runs)")
    ap.add_argument("--root", type=Path, default=None,
                    help="library root for --files (default: the first Rocq library root)")
    ap.add_argument("--files", default=DEFAULT_FILES, help="glob under --root to hold lemmas out of")
    ap.add_argument("--limit", type=int, default=10)
    ap.add_argument("--runner", default="mock", help="auto | codex | claude | claude-code | direct | mock")
    ap.add_argument("--model", default=None, help="prover model (validated against the runner's provider)")
    ap.add_argument("--mock-answers", type=Path, default=None,
                    help="JSON object {lemma: proof body} the mock runner answers with")
    ap.add_argument("--ablations", default="baseline", help="comma list of " + ", ".join(LADDER))
    ap.add_argument("--brief", default="full", choices=BRIEFS,
                    help="what a corpus DESIGN.md tells workers; spec-only stages the corpus without it")
    ap.add_argument("--concurrency", type=int, default=8)
    ap.add_argument("--timeout", type=float, default=600.0, help="per-worker wall clock (--node-seconds)")
    ap.add_argument("--workroot", type=Path, default=DEFAULT_WORKROOT)
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--config", type=Path, default=None, help="config file (default .pcp/config.toml)")
    return ap


def parse_ablations(value: str) -> list[Ablation]:
    names = [a.strip() for a in value.split(",") if a.strip()]
    unknown = [n for n in names if n not in LADDER]
    if unknown:
        raise UsageError(f"unknown ablation {', '.join(map(repr, unknown))}; choose from {', '.join(LADDER)}")
    if not names:
        raise UsageError("no ablation named; choose from " + ", ".join(LADDER))
    return [LADDER[n] for n in names]


def default_root() -> Path:
    roots = library_roots()
    return roots[0] if roots else Path(".").resolve()


def _run(args: argparse.Namespace) -> int:
    corpus = absolute(args.corpus)
    reference = absolute(args.reference)
    record = None if args.no_record else absolute(args.record)
    workroot = absolute(args.workroot)
    out = absolute(args.out)
    root = absolute(args.root) or default_root()
    index_path = absolute(INDEX_PATH)
    assert workroot is not None and out is not None and index_path is not None
    arms = parse_ablations(args.ablations)
    cfg = load_config(absolute(args.config) if args.config else None)
    answers = json_load(absolute(args.mock_answers)) if args.mock_answers else None

    if corpus is not None:
        tasks = collect_benchmark(corpus, reference)
        label = corpus.name
    else:
        tasks = collect_tasks(root, args.files, limit=args.limit, seed=args.seed)
        label = args.files
    if not tasks:
        raise UsageError("no held-out lemmas found")
    warn(f"{len(tasks)} held-out lemma(s) from {label}")

    run_id = time.strftime("%Y%m%d-%H%M%S")
    sandbox_corpus = corpus if (corpus is not None and args.brief == "full") else None
    results: list[Metrics] = []
    runner_name = ""
    for arm in arms:
        paths = ArmPaths(workroot=workroot / arm.name, record=(record / f"{run_id}-{arm.name}") if record else None)
        sandbox = None
        if args.sandbox:
            chosen = pick_auto(cfg, "prover") if args.runner == "auto" else args.runner
            sandbox = benchmark_sandbox(chosen, reference=reference, corpus_dir=sandbox_corpus)
        runner, notes = arm_runner(args.runner, arm, cfg=cfg, model=args.model, sandbox=sandbox, answers=answers)
        runner_name = runner.name
        for line in notes:
            warn(line)
        warn(f"arm {arm.name}: runner {runner.name}; tools {', '.join(arm.tools) or 'none'}; skill {arm.skill or 'none'}")

        def progress(task: Task, outcome: Outcome) -> None:
            warn(f"  {outcome.status:<9} {task.key}  ({outcome.elapsed_s:.0f}s)")

        metrics = asyncio.run(run_arm(
            tasks, arm, runner, paths, concurrency=args.concurrency, on_outcome=progress,
            timeout=args.timeout, brief=args.brief, corpus_label=label, cfg=cfg, index_path=index_path,
        ))
        print(metrics.render(), flush=True)
        if paths.record is not None:
            print()
            print(summarize(load_records(paths.record)).render())
            warn(f"records: {paths.record}   (pcp failures {paths.record})")
        results.append(metrics)

    if len(results) > 1:
        print()
        print("ablation ladder -- what each rung's capability bought:")
        print(indent(deltas(results)))
    json_dump(out, {"runner": runner_name, "results": [m.to_json() for m in results]})
    warn(f"wrote {out}")
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        return _run(args)
    except PcpError as exc:
        warn(str(exc))
        return exc.exit_code
    except KeyboardInterrupt:
        warn("interrupted")
        return 130


if __name__ == "__main__":
    sys.exit(main())
