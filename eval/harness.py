#!/usr/bin/env python3
"""The evaluation harness (PLAN.md 13).

Without this you cannot tell whether the tooling helps, and every subsequent design
decision is taste.  It is deliberately built early -- by Phase 4, not at the end --
because the number that decides whether the whole orchestration thesis pays is
*cheap-model solve rate*, and you cannot get it retroactively.

Method: hold out lemmas from a real development, replace the bodies with `Admitted`,
and ask an agent to reprove them.  The corpus is real Iris, so the difficulty is real.

    python eval/harness.py --files 'iris/heap_lang/lib/*.v' --limit 20 --runner mock
"""

from __future__ import annotations

import argparse
import asyncio
import json
import os
import random
import statistics
import sys
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pcp.core.vernac import parse_blocks  # noqa: E402
from pcp.orch.assemble import Development  # noqa: E402
from pcp.orch.gate import Gate  # noqa: E402
from pcp.orch.packet import render_task  # noqa: E402
from pcp.orch.graph import Node  # noqa: E402
from pcp.orch.runners.base import NodePayload, strip_proof_wrapper  # noqa: E402


@dataclass
class Task:
    file: str
    lemma: str
    statement: str
    reference_body: str


@dataclass
class Outcome:
    file: str
    lemma: str
    solved: bool
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


@dataclass
class Metrics:
    """The metrics PLAN.md 13 names, and no vanity ones."""

    ablation: str
    n: int = 0
    solved: int = 0
    outcomes: list[Outcome] = field(default_factory=list)

    @property
    def solve_rate(self) -> float:
        return self.solved / self.n if self.n else 0.0

    def per_solved(self, attr: str) -> float:
        vals = [getattr(o, attr) for o in self.outcomes if o.solved]
        return statistics.mean(vals) if vals else 0.0

    def render(self) -> str:
        return (
            f"{self.ablation:<14} solve {self.solved}/{self.n} ({100 * self.solve_rate:.0f}%)  "
            f"tokens/solved {self.per_solved('tokens'):.0f}  "
            f"tools/solved {self.per_solved('tool_calls'):.1f}  "
            f"checks/solved {self.per_solved('checks'):.1f}  "
            f"wall/solved {self.per_solved('elapsed_s'):.0f}s  "
            f"${sum(o.dollars for o in self.outcomes):.2f}"
        )

    def to_json(self) -> dict:
        return {
            "ablation": self.ablation,
            "n": self.n,
            "solved": self.solved,
            "solve_rate": self.solve_rate,
            "tokens_per_solved": self.per_solved("tokens"),
            "tool_calls_per_solved": self.per_solved("tool_calls"),
            "wall_per_solved": self.per_solved("elapsed_s"),
            "outcomes": [asdict(o) for o in self.outcomes],
        }


def collect_benchmark(corpus: Path, reference: Path | None = None) -> tuple[list[Task], str]:
    """Load a corpus built by ``eval/make_benchmark.py``.

    The held-out names come from the corpus's own ``bench.json``; the reference
    bodies are read from the *answer key*, which lives elsewhere and is never bound
    into a worker sandbox.  If it is missing the tasks still run -- scoring is done
    by the gate, not by diffing against the reference.
    """
    meta = json.loads((corpus / "bench.json").read_text(encoding="utf-8"))
    source = corpus / meta["file"]
    text = source.read_text(encoding="utf-8")
    blocks = {b.name: b for b in parse_blocks(text)}
    refs: dict[str, str] = {}
    if reference is not None and (reference / "reference.json").exists():
        ref = json.loads((reference / "reference.json").read_text(encoding="utf-8"))
        refs = {h["anonymised"]: h.get("reference_body", "") for h in ref.get("holdout", [])}
    tasks: list[Task] = []
    for h in meta["holdout"]:
        name = h["anonymised"]
        block = blocks.get(name)
        if block is None:
            continue
        tasks.append(
            Task(
                file=str(source),
                lemma=name,
                statement=block.statement,
                reference_body=refs.get(name, ""),
            )
        )
    design = ""
    design_path = corpus / "DESIGN.md"
    if design_path.exists():
        design = design_path.read_text(encoding="utf-8")
    return tasks, design


def collect_tasks(root: Path, pattern: str, *, limit: int, seed: int = 0) -> list[Task]:
    """Hold out lemmas: real statements, real proofs, bodies removed."""
    tasks: list[Task] = []
    files = sorted(root.glob(pattern))
    rng = random.Random(seed)
    rng.shuffle(files)
    for path in files:
        src = path.read_text(encoding="utf-8")
        for block in parse_blocks(src):
            if not block.has_proof or block.ender != "Qed":
                continue
            body = block.body(src).strip()
            if not body or len(body) > 4000:
                continue
            tasks.append(
                Task(
                    file=str(path),
                    lemma=block.name,
                    statement=block.statement,
                    reference_body=body,
                )
            )
        if len(tasks) >= limit * 3:
            break
    rng.shuffle(tasks)
    return tasks[:limit]


async def run_task(
    task: Task,
    runner,
    ablation: "Ablation",
    workroot: Path,
    timeout: float,
    *,
    design: str = "",
    recorder=None,
    corpus: str = "",
) -> Outcome:
    started = time.perf_counter()
    dev = Development(task.file)
    gate = Gate(dev)
    workdir = workroot / f"{Path(task.file).stem}.{task.lemma}"
    workdir.mkdir(parents=True, exist_ok=True)

    node = Node(id=task.lemma, name=task.lemma, statement=task.statement, statement_status="frozen")
    from pcp.orch.packet import describe_tools

    task_text = render_task(
        node, dev, [], scratch_name=Path(task.file).name,
        skills=list(ablation.skills), design=design,
        tools=describe_tools(list(ablation.tools)),
    )
    (workdir / "TASK.md").write_text(task_text, encoding="utf-8")
    # The worker sees the development with only *its* proof missing: everything the
    # original had -- the invariants, the ghost state, the helper lemmas -- is there.
    assembly = dev.assemble(task.lemma, [], anchor_body="admit.", truncate=True)
    (workdir / Path(task.file).name).write_text(assembly.text, encoding="utf-8")
    for name in ("_CoqProject", "DESIGN.md"):
        src = Path(task.file).parent / name
        if src.exists():
            (workdir / name).write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
    if ablation.tools:
        # The rung's tools are only real if the worker's CLI is told where to find
        # them.  Declaring them in the ladder and never wiring them up produced an
        # "ablation" in which every rung was the baseline.
        from pcp.orch.runners.cli import write_mcp_config

        write_mcp_config(workdir)
    (workdir / "pcp-node.json").write_text(
        json.dumps({"node": task.lemma, "target": task.lemma, "anchor": task.lemma,
                    "file": str(Path(task.file).resolve()), "statement": task.statement,
                    "siblings": [], "attempt": 1}, indent=2),
        encoding="utf-8",
    )

    payload = NodePayload(
        node_id=task.lemma,
        name=task.lemma,
        statement=task.statement,
        file=task.file,
        workdir=workdir,
        budget_seconds=timeout,
    )
    result = await runner.run_node(payload)
    body = strip_proof_wrapper(result.proof or "")
    solved = False
    error = result.evidence
    gate_result = None
    if body:
        # `stub_prefix` is what makes this usable on a real development: without it
        # every check recompiles the file's own automation-heavy proofs.
        gate_result = await asyncio.to_thread(
            gate.run, task.lemma, [], target_body=body, truncate=True, stub_prefix=True
        )
        solved = gate_result.ok
        if not solved:
            error = gate_result.render()[:2000]

    outcome = Outcome(
        file=task.file,
        lemma=task.lemma,
        solved=solved,
        elapsed_s=time.perf_counter() - started,
        tokens=int(result.cost.get("tokens", 0)),
        requests=int(result.cost.get("requests", 0)),
        tool_calls=int(result.cost.get("tool_calls", 0)),
        turns=int(result.cost.get("turns", 0)),
        checks=int(result.cost.get("check_iterations", 0)),
        dollars=float(result.cost.get("dollars", 0.0)),
        error=error[:2000],
    )
    if recorder is not None:
        from pcp.orch.record import AttemptRecord

        record = recorder.write(
            AttemptRecord(
                run_id=recorder.run_id, node=task.lemma, lemma=task.lemma, attempt=1,
                runner=getattr(runner, "name", "?"), status=result.status, solved=solved,
                elapsed_s=outcome.elapsed_s, cost=result.cost, evidence=result.evidence,
                gate_report=gate_result.render() if gate_result else "",
                compile_output=(gate_result.compile_output[-8000:] if gate_result else ""),
                gate_checks=(gate_result.to_json()["checks"] if gate_result else []),
                proof=body, requests=[r.to_json() for r in result.requests],
                corpus=corpus or ablation.name, trace=result.trace,
            ),
            workdir=workdir,
            transcript=result.raw,
        )
        outcome.record = str(record)
    return outcome


@dataclass
class Ablation:
    """One rung of the ablation ladder (PLAN.md 13).

    baseline → raw goal dump → +ledger → +retrieval → +speculative.  You need to know
    which features actually earn their context, and to delete the ones that do not.
    """

    name: str
    skills: list[str] = field(default_factory=list)
    tools: list[str] = field(default_factory=list)


async def run_ablation(tasks: list[Task], runner, ablation: Ablation, *, workroot: Path,
                       concurrency: int, timeout: float, design: str = "",
                       recorder=None, corpus: str = "") -> Metrics:
    metrics = Metrics(ablation=ablation.name, n=len(tasks))
    sem = asyncio.Semaphore(concurrency)

    async def one(task: Task) -> Outcome:
        async with sem:
            return await run_task(
                task, runner, ablation, workroot / ablation.name, timeout,
                design=design, recorder=recorder, corpus=corpus,
            )

    for outcome in await asyncio.gather(*(one(t) for t in tasks)):
        metrics.outcomes.append(outcome)
        metrics.solved += int(outcome.solved)
    return metrics


def main() -> int:
    from pcp.cli.main import _pick_runner
    from eval.ablations import LADDER

    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", type=Path, default=None,
                    help="a benchmark directory built by eval/make_benchmark.py")
    ap.add_argument("--reference", type=Path, default=None, help="its answer key (for stats only)")
    ap.add_argument("--sandbox", action="store_true",
                    help="run workers in bubblewrap with the answer key and the forges out of reach")
    ap.add_argument("--record", type=Path, default=Path(".pcp/records"),
                    help="where attempt records go; `pcp failures` reads them")
    ap.add_argument("--root", type=Path, default=Path(os.environ.get("ROCQPATH", "").split(":")[0] or "."))
    ap.add_argument("--files", default="iris/heap_lang/lib/*.v")
    ap.add_argument("--limit", type=int, default=10)
    ap.add_argument("--runner", default="mock")
    ap.add_argument("--model", default=None)
    ap.add_argument("--ablations", default="baseline")
    ap.add_argument("--concurrency", type=int, default=8)
    ap.add_argument("--timeout", type=float, default=600.0)
    ap.add_argument("--workroot", type=Path, default=Path(".pcp/eval"))
    ap.add_argument("--out", type=Path, default=Path(".pcp/eval/results.json"))
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()

    design = ""
    if args.corpus is not None:
        tasks, design = collect_benchmark(args.corpus, args.reference)
        label = args.corpus.name
    else:
        tasks = collect_tasks(args.root, args.files, limit=args.limit, seed=args.seed)
        label = args.files
    if not tasks:
        print("no held-out lemmas found", file=sys.stderr)
        return 2
    print(f"{len(tasks)} held-out lemmas from {label}", file=sys.stderr)

    recorder = None
    if args.record is not None:
        from pcp.orch.record import Recorder

        recorder = Recorder(args.record)
        print(f"recording to {recorder.root}", file=sys.stderr)
    names = [a.strip() for a in args.ablations.split(",") if a.strip()]
    tools = sorted({t for n in names for t in (LADDER[n].tools if n in LADDER else [])})
    if tools:
        print(f"granting MCP tools: {', '.join(tools)}", file=sys.stderr)
    runner = _pick_runner(
        args.runner, args.model, sandbox=args.sandbox, reference=args.reference, mcp_tools=tools,
    )

    results = []
    for name in names:
        ablation = LADDER.get(name)
        if ablation is None:
            print(f"unknown ablation {name!r}; choose from {', '.join(LADDER)}", file=sys.stderr)
            return 2
        metrics = asyncio.run(
            run_ablation(
                tasks, runner, ablation,
                workroot=args.workroot, concurrency=args.concurrency, timeout=args.timeout,
                design=design, recorder=recorder, corpus=label,
            )
        )
        print(metrics.render())
        results.append(metrics.to_json())

    if recorder is not None:
        from pcp.orch.failures import summarize
        from pcp.orch.record import load_records

        print()
        print(summarize(load_records(recorder.root)).render())
        print(f"\nrecords: {recorder.root}   (pcp failures {recorder.root})", file=sys.stderr)

    if len(results) > 1:
        from eval.ablations import deltas

        print()
        print("ablation ladder — what each rung's capability bought:")
        for line in deltas(results):
            print("  " + line)

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps({"runner": runner.name, "results": results}, indent=2), encoding="utf-8")
    print(f"\nwrote {args.out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
