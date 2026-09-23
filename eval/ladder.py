#!/usr/bin/env python3
"""The design-rung ladder (docs/BENCHMARKS.md "Climbing the ladder"; contract §1.16).

The rungs are the same development at growing scale, and a person working through
them would not start each one from nothing: they would have their own previous proof
open in the next buffer, and they would have read the paper.  So each rung may be
given, read-only:

* ``.pcp/library/paper`` -- arXiv:2501.07503, the algorithms paper these developments
  mechanise.  Prose and pseudocode; no Coq, no Iris, no ghost state.
* ``.pcp/library/solved/<earlier rung>`` -- what **this system** produced on every rung
  below, finished or not, with a header saying which.

What stays closed is what was always closed: ``eval/corpus/`` (every *other* rung's
corpus, which for a design rung is the answer), ``.pcp/reference/`` (the real proofs),
``docs/``, ``tests/``, ``.git`` and the operator's ``$HOME``.  The library is bound
back after those masks and holds nothing but this system's own output plus the paper
-- never a reference proof.  That boundary is the whole reason the numbers mean
anything, so it is checked here (:func:`_assert_library_is_clean`), not intended.

Under ``--brief spec-only`` a rung is given the specification and nothing else: no
``DESIGN.md``, no paper, no earlier solution -- the argv carries no ``--library`` at
all, by construction (:func:`rung_argv` refuses one).

Two rules are structural here:

* **An outage is not a result.**  A revoked credential once consumed two rungs in
  under a minute each.  The ladder stops on an outage, and decides "outage" from
  structured signals only -- the orchestrator's exit status and the run's own
  records -- never by grepping the log, which quotes worker evidence and gate tails
  and so can make a stuck proof look like a bwrap failure.
* **Preflight before spend.**  Proof rungs are refused (the design is given there,
  which is a different experiment), budgets must fit a revision round, ``bwrap`` and
  the provider are probed -- each in seconds, each learned from a lost night.

    python eval/ladder.py --stamp overnight                 # the whole ladder
    python eval/ladder.py --only rwcas_design seqlock_design
    python eval/ladder.py --brief spec-only --dry-run       # print the argv, spend nothing
    python eval/ladder.py --only rwcas_design -- --prover-effort high
    python eval/ladder.py --resume overnight                # finish a ladder that stopped

``--resume STAMP`` reuses the stamp's graph, workroot and record directories, drops
``--fresh`` so each rung resumes its own graph, runs only the rungs whose summary row
is missing or not ``exit 0``, and updates the summary in place: an outage at 3 a.m.
costs the rungs after it nothing but the wait.
"""

from __future__ import annotations

import argparse
import asyncio
import shlex
import shutil
import sys
import time
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pcp.errors import PcpError, UsageError  # noqa: E402
from pcp.orch.decomposer import blank_predicates  # noqa: E402
from pcp.orch.record import load_records  # noqa: E402
from pcp.orch.runners import sandbox as sb  # noqa: E402
from pcp.rocq.assemble import Development  # noqa: E402
from pcp.util.io import atomic_write_text, ensure_dir, json_dump, json_load, read_text, rm_tree  # noqa: E402
from pcp.util.proc import run, run_async  # noqa: E402
from pcp.util.text import one_line, tail_lines  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
#: The header every exported solution carries (``pcp.orch.prove.integrate``); read
#: within the first ``HEADER_WINDOW`` characters.
SOLUTION_MARK = "Produced by proof-copilot"
HEADER_WINDOW = 400
BRIEFS = ("full", "spec-only")
DEFAULT_WALL_SECONDS = 10800.0
PROVIDER_PROBE_SECONDS = 60.0
TAIL_LINES = 30
#: The interpreter that runs the ladder runs the rungs: the venv's, when started as
#: ``.venv/bin/python eval/ladder.py``.  ``-u``: a block-buffered log is
#: indistinguishable from a stalled run.
DEFAULT_LAUNCHER: tuple[str, ...] = (sys.executable, "-u", "-m", "pcp.cli.main")


# ------------------------------------------------------------------ where things are


@dataclass(frozen=True)
class Paths:
    """Every path the ladder reads or writes, relative to one root (the repo)."""

    root: Path = ROOT

    @property
    def corpus(self) -> Path:
        return self.root / "eval" / "corpus" / "bench"

    @property
    def library(self) -> Path:
        return self.root / ".pcp" / "library"

    @property
    def paper(self) -> Path:
        return self.library / "paper"

    @property
    def runs(self) -> Path:
        return self.root / ".pcp" / "runs"

    @property
    def reference(self) -> Path:
        return self.root / ".pcp" / "reference"

    @property
    def forbidden(self) -> tuple[Path, ...]:
        """Nothing under these may ever be copied into the library."""
        return (self.corpus, self.reference)

    def solved(self, rung: str) -> Path:
        return self.library / "solved" / rung

    def graph(self, tag: str) -> Path:
        return self.root / ".pcp" / f"graph_{tag}.db"

    def work(self, tag: str) -> Path:
        return self.root / ".pcp" / "work" / tag

    def record(self, tag: str) -> Path:
        return self.runs / tag

    def log(self, tag: str) -> Path:
        return self.runs / f"{tag}.log"

    def summary(self, stamp: str) -> Path:
        return self.runs / f"ladder_{stamp}.json"


DEFAULT_PATHS = Paths()


def tag_for(stamp: str, rung: str) -> str:
    return f"ladder_{stamp}_{rung}"


# ------------------------------------------------------------------ rungs


@dataclass(frozen=True)
class Rung:
    name: str
    #: Seconds a single node may spend.  Scaled by the reference proof's size: the
    #: default 900 s is a rounding error against a 119-tactic ``write_spec``.
    node_seconds: float
    #: Clock for one design round -- set by *design* difficulty, not file length.
    decomposer_seconds: float
    #: Wall-clock cap for the whole rung, enforced outside the process.
    wall_seconds: float = DEFAULT_WALL_SECONDS
    #: Override the "largest holdout" rule (none of the design rungs needs it).
    root_override: str = ""
    corpus_root: Path = field(default=DEFAULT_PATHS.corpus)

    @property
    def dir(self) -> Path:
        return self.corpus_root / self.name

    @property
    def bench(self) -> dict[str, Any]:
        path = self.dir / "bench.json"
        if not path.exists():
            raise UsageError(f"{self.name}: no bench.json in {self.dir}")
        return json_load(path)

    @property
    def file(self) -> Path:
        """The development.  Proof rungs are ``M<hash>.v``, design rungs keep a
        readable name; petanque's ``__pcp`` twins are never a corpus."""
        files = sorted(f for f in self.dir.glob("*.v") if "__pcp" not in f.stem)
        if not files:
            raise UsageError(f"{self.name}: no development in {self.dir}")
        return files[0]

    @property
    def is_design_rung(self) -> bool:
        """The design is the task iff the corpus left predicates blank (``:= True%I.``)
        -- the same discriminator the decomposer uses, so the two cannot drift."""
        return bool(blank_predicates(Development(self.file)))

    @property
    def root_lemma(self) -> str:
        """The largest held-out proof, by reference tactic count, under its
        anonymised name -- the one the rung is actually about."""
        if self.root_override:
            return self.root_override
        holdout = self.bench.get("holdout") or []
        if not holdout:
            raise UsageError(f"{self.name}: bench.json holds nothing out")
        biggest = max(holdout, key=lambda h: int(h.get("tactics", 0) or 0))
        return str(biggest.get("anonymised") or biggest["name"])

    def to_json(self) -> dict[str, Any]:
        return {
            "name": self.name, "node_seconds": self.node_seconds, "decomposer_seconds": self.decomposer_seconds,
            "wall_seconds": self.wall_seconds, "root_override": self.root_override,
        }


#: In difficulty order.  ``rwcas_design`` is the smallest *development* but has the
#: hardest design on the ladder (a prophecy-and-helping registry), so it gets the
#: longest design round.  Every budget satisfies ``decomposer + 2 * node <= wall`` at
#: the default wall (checked in :func:`preflight`), so a round of dispatch can fail,
#: be fed back and be re-dispatched against a revised decomposition.  The cached pair
#: has no design variant (two of its three results are stated in terms of the ghost
#: state a designer would have to invent) and is not on this ladder.
LADDER: tuple[Rung, ...] = (
    Rung("rwcas_design", node_seconds=1800, decomposer_seconds=5400),
    Rung("seqlock_design", node_seconds=2700, decomposer_seconds=2700),
    Rung("seqlock_wf_design", node_seconds=2700, decomposer_seconds=5400),
)


def select_rungs(only: Sequence[str] | None, *, ladder: Sequence[Rung] = LADDER) -> list[Rung]:
    """``--only`` in ladder order; an unknown name is an error, not a silent skip."""
    if only is None:
        return list(ladder)
    known = {r.name for r in ladder}
    unknown = [n for n in only if n not in known]
    if unknown:
        raise UsageError(f"no such rung(s): {', '.join(unknown)}; the ladder is {', '.join(sorted(known))}")
    return [r for r in ladder if r.name in set(only)]


# ------------------------------------------------------------------ the boundary


def _assert_library_is_clean(paths: Sequence[Path], forbidden: Sequence[Path] = DEFAULT_PATHS.forbidden) -> None:
    """The library must hold only this system's output and the paper.

    Cheap to check and catastrophic to get wrong: a reference proof reaching a
    worker does not make the run fail, it makes every number after it a lie.
    """
    fences = [f.resolve() for f in forbidden]
    for path in paths:
        resolved = Path(path).resolve()
        for fence in fences:
            if resolved == fence or fence in resolved.parents:
                raise UsageError(f"refusing to run: library path {path} is inside {fence}")
        for v in sorted(resolved.rglob("*.v")):
            if SOLUTION_MARK not in read_text(v)[:HEADER_WINDOW]:
                raise UsageError(
                    f"refusing to run: {v} is in the library but was not produced by a run. "
                    "Only this system's own exported solutions belong here."
                )


def _header(directory: Path) -> str:
    for v in sorted(directory.glob("*.v")):
        return read_text(v)[:HEADER_WINDOW]
    return ""


def publish(rung: Rung, record_dir: Path, paths: Paths = DEFAULT_PATHS) -> Path | None:
    """Copy a finished rung's exported solution into the library for the next one.

    The verdict word is read *negative first*: ``"COMPLETE" in "INCOMPLETE"`` once
    told a worker that a rung with a contested obligation was a complete solution.
    """
    solutions = sorted(record_dir.glob("*/solution")) if record_dir.exists() else []
    if not solutions:
        return None
    dest = paths.solved(rung.name)
    rm_tree(dest)
    shutil.copytree(solutions[-1], dest)
    header = _header(dest)
    status = "incomplete" if "INCOMPLETE" in header else ("partial" if "PARTIAL" in header else "complete")
    atomic_write_text(
        dest / "README.md",
        f"# `{rung.name}`, as this system solved it ({status})\n\n"
        f"Machine-generated by proof-copilot on the `{rung.name}` rung, root lemma "
        f"`{rung.root_lemma}`. Not a reference solution and not checked by a human.\n\n"
        "Read it as a worked example of this codebase's idiom -- the ghost state it "
        "settled on, the shape of its invariants, how it opens an atomic update. "
        "The problem you have been given is a different one.\n",
    )
    return dest


def library_for(
    rung: Rung,
    paths: Paths = DEFAULT_PATHS,
    *,
    brief: str = "full",
    carry: bool = True,
    paper: bool = True,
    fresh: Mapping[str, Path] | None = None,
    ladder: Sequence[Rung] = LADDER,
) -> list[Path]:
    """What ``rung`` may consult: every earlier rung's solution (this invocation's
    fresh one, else the one a previous invocation published -- so a ladder resumed
    with ``--only`` carries exactly what it claims to), then the paper.  Nothing at
    all under ``spec-only``."""
    if brief == "spec-only":
        return []
    out: list[Path] = []
    if carry:
        for earlier in ladder:
            if earlier.name == rung.name:
                break
            published = (fresh or {}).get(earlier.name)
            if published is None and paths.solved(earlier.name).exists():
                published = paths.solved(earlier.name)
            if published is not None:
                out.append(Path(published))
    if paper and paths.paper.exists():
        out.append(paths.paper)
    return out


# ------------------------------------------------------------------ preflight


def budget_problem(rung: Rung) -> str:
    """A revision round only starts once the whole frontier has finished, so the wall
    must fit the design round *plus* two rounds of dispatch."""
    needed = rung.decomposer_seconds + 2 * rung.node_seconds
    if needed <= rung.wall_seconds:
        return ""
    return (
        f"{rung.name}: budget cannot fit a revision -- design {rung.decomposer_seconds:.0f}s "
        f"+ 2 dispatch rounds of {rung.node_seconds:.0f}s = {needed:.0f}s > wall "
        f"{rung.wall_seconds:.0f}s. Lower --node-seconds or raise --wall-seconds."
    )


def rung_problems(rung: Rung) -> list[str]:
    """Everything wrong with a rung's corpus, as messages; never a traceback."""
    if not rung.dir.exists():
        return [f"{rung.name}: no corpus at {rung.dir}"]
    problems: list[str] = []
    try:
        _file, _root = rung.file, rung.root_lemma
        if not rung.is_design_rung:
            problems.append(
                f"{rung.name}: the design is GIVEN here (no blank predicates), so this "
                "is a proof rung, not a design rung"
            )
    except (PcpError, OSError, KeyError, ValueError) as exc:
        problems.append(f"{rung.name}: {exc}")
    budget = budget_problem(rung)
    if budget:
        problems.append(budget)
    return problems


def provider_problem(timeout: float = PROVIDER_PROBE_SECONDS) -> str:
    """Is ``claude -p`` reachable?  Bounded, and a failure is a sentence."""
    probe = run(["claude", "-p"], stdin="Reply with exactly: OK", timeout=timeout)
    if probe.spawn_error:
        return f"the provider CLI is not on PATH ({probe.spawn_error}); install `claude` and log in"
    if probe.timed_out:
        return f"`claude -p` did not answer within {timeout:.0f}s; check the login and the network"
    if probe.returncode != 0 or "OK" not in probe.stdout:
        return "the provider is not reachable -- re-authenticate before starting: " + one_line(probe.output, 200)
    return ""


def preflight(
    rungs: Sequence[Rung],
    paths: Paths = DEFAULT_PATHS,
    *,
    launcher: Sequence[str] = DEFAULT_LAUNCHER,
    probes: bool = True,
) -> list[str]:
    """Cheap checks, before anything expensive is spent.  ``probes=False`` skips the
    three that touch the machine (the orchestrator's import, ``bwrap``, the provider)."""
    problems: list[str] = []
    for rung in rungs:
        problems += rung_problems(rung)
    if not probes:
        return problems
    # Start the orchestrator exactly the way a rung will: a launcher that cannot even
    # import is a zero-second "failure" on every rung in the list.
    proc = run([*launcher, "prove", "--help"], cwd=paths.root, timeout=120)
    if not proc.ok:
        problems.append("the orchestrator will not start: " + one_line(proc.spawn_error or proc.output, 200))
    if not sb.available():
        problems.append("bubblewrap (`bwrap`) is not installed; --sandbox runs cannot start")
    provider = provider_problem()
    if provider:
        problems.append(provider)
    return problems


# ------------------------------------------------------------------ the run


def rung_argv(
    rung: Rung,
    paths: Paths = DEFAULT_PATHS,
    *,
    stamp: str,
    library: Sequence[Path] = (),
    brief: str = "full",
    runner: str | None = None,
    decomposer: str | None = None,
    prover_model: str | None = None,
    extra: Sequence[str] = (),
    launcher: Sequence[str] = DEFAULT_LAUNCHER,
    fresh: bool = True,
) -> list[str]:
    """The ``pcp prove`` command line for one rung (contract §1.16).  ``fresh=False``
    (a ``--resume``) leaves the rung's graph to be resumed."""
    if brief not in BRIEFS:
        raise UsageError(f"unknown brief {brief!r}; one of {', '.join(BRIEFS)}")
    if brief == "spec-only" and library:
        raise UsageError("--brief spec-only gives a rung the specification and nothing else; no --library is allowed")
    tag = tag_for(stamp, rung.name)
    argv = [
        *launcher, "prove", str(rung.file), rung.root_lemma,
        "--sandbox", *(["--fresh"] if fresh else []), "--state-tools",
        "--graph", str(paths.graph(tag)),
        "--workroot", str(paths.work(tag)),
        "--record", str(paths.record(tag)),
        "--corpus", rung.name,
        "--node-seconds", f"{rung.node_seconds:g}",
        "--decomposer-seconds", f"{rung.decomposer_seconds:g}",
        "--reference", str(paths.reference / rung.name),
        "--brief", brief,
    ]
    if runner:
        argv += ["--runner", runner]
    if decomposer:
        argv += ["--decomposer", decomposer]
    if prover_model:
        argv += ["--prover-model", prover_model]
    for path in library:
        argv += ["--library", str(path)]
    argv += [str(a) for a in extra]
    return argv


def outage_of(*, exit_code: int | None, timed_out: bool, spawn_error: str, record_dir: Path) -> str:
    """Why this rung could not run, if the reason was not about proving -- from
    structured signals only (module docstring).

    * the orchestrator could not be started, or refused to (usage error, exit 2,
      with no attempt recorded -- a run that spent its design rounds and exited
      is a result);
    * it exited non-zero before a single attempt was recorded;
    * every recorded attempt is a ``runner-error`` (the provider, its CLI or the
      sandbox failed underneath every worker).

    A rung killed at its wall ran; a rung with one ordinary failure among its
    records ran.  Neither is an outage.
    """
    if spawn_error:
        return f"the orchestrator could not be started: {spawn_error}"
    if timed_out or exit_code == 0:
        return ""
    records = list(load_records(record_dir)) if record_dir.exists() else []
    if exit_code == 2 and not records:
        return "pcp prove refused to start (usage error, exit 2)"
    if not records:
        return f"pcp prove exited {exit_code} before any attempt was recorded"
    infra = [r for r in records if r.get("primary_failure") == "runner-error" or r.get("status") == "error"]
    if len(infra) == len(records):
        first = infra[0]
        why = first.get("failure_evidence") or first.get("evidence") or ""
        return f"every attempt failed with runner-error: {one_line(why, 160)}"
    return ""


def run_rung(
    rung: Rung,
    paths: Paths = DEFAULT_PATHS,
    *,
    stamp: str,
    library: Sequence[Path] = (),
    brief: str = "full",
    carry: bool = True,
    runner: str | None = None,
    decomposer: str | None = None,
    prover_model: str | None = None,
    extra: Sequence[str] = (),
    launcher: Sequence[str] = DEFAULT_LAUNCHER,
    fresh: bool = True,
) -> dict[str, Any]:
    """One rung: run ``pcp prove`` under the wall (process-group kill), log it live,
    publish its solution when carrying, and say whether it was an outage.  A resumed
    rung (``fresh=False``) appends to its log rather than starting one."""
    tag = tag_for(stamp, rung.name)
    argv = rung_argv(
        rung, paths, stamp=stamp, library=library, brief=brief, runner=runner,
        decomposer=decomposer, prover_model=prover_model, extra=extra, launcher=launcher, fresh=fresh,
    )
    log = paths.log(tag)
    ensure_dir(log.parent)
    print(f"\n=== {rung.name}: {rung.file.name} / {rung.root_lemma} "
          f"(node {rung.node_seconds:.0f}s, wall {rung.wall_seconds:.0f}s){'' if fresh else ' [resumed]'}", flush=True)
    print(f"    brief: {brief}, library: {', '.join(str(p) for p in library) or 'none'}", flush=True)
    print(f"    log: {log}", flush=True)

    started = time.time()
    with log.open("ab" if not fresh else "wb") as fh:
        fh.write(f"# {shlex.join(argv)}\n# brief: {brief}, library: {', '.join(str(p) for p in library) or 'none'}\n".encode())
        fh.flush()

        def on_chunk(chunk: bytes) -> None:
            fh.write(chunk)
            fh.flush()

        streamed = asyncio.run(run_async(argv, cwd=paths.root, timeout=rung.wall_seconds, on_chunk=on_chunk))
    elapsed = time.time() - started
    code = streamed.returncode
    published = publish(rung, paths.record(tag), paths) if carry else None
    outage = outage_of(
        exit_code=code, timed_out=streamed.timed_out, spawn_error=streamed.spawn_error, record_dir=paths.record(tag),
    )
    row = {
        "outage": outage,
        "rung": rung.name,
        "root": rung.root_lemma,
        "exit": code,
        "timed_out": streamed.timed_out,
        "elapsed_s": round(elapsed, 1),
        "record": str(paths.record(tag)),
        "log": str(log),
        "published": str(published) if published else None,
        "tail": tail_lines(streamed.text, TAIL_LINES),
        "brief": brief,
    }
    print(f"    -> exit {code}{' (WALL TIMEOUT)' if streamed.timed_out else ''} in {elapsed / 60:.1f} min"
          f"{'; published ' + published.name if published else '; nothing published'}", flush=True)
    return row


# ------------------------------------------------------------------ the CLI


def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--stamp", default=time.strftime("%Y%m%d_%H%M%S"))
    ap.add_argument("--resume", default=None, metavar="STAMP",
                    help="finish the ladder run STAMP: reuse its paths, resume each rung's graph (no --fresh), "
                         "run only rungs not yet at exit 0, update its summary in place")
    ap.add_argument("--only", nargs="*", default=None, metavar="RUNG", help="run just these rungs, in ladder order")
    ap.add_argument("--wall-seconds", type=float, default=DEFAULT_WALL_SECONDS,
                    help="wall-clock cap per rung (default: 3 hours)")
    ap.add_argument("--no-paper", action="store_true", help="withhold the paper")
    ap.add_argument("--no-carry", action="store_true",
                    help="withhold earlier rungs' solutions (each rung starts cold); nothing is published either")
    ap.add_argument("--brief", default="full", choices=BRIEFS,
                    help="spec-only: the specification and nothing else -- no DESIGN.md, no paper, no carry")
    ap.add_argument("--runner", default=None, help="passed to `pcp prove --runner`")
    ap.add_argument("--decomposer", default=None, metavar="MODEL", help="passed to `pcp prove --decomposer`")
    ap.add_argument("--prover-model", default=None, metavar="MODEL", help="passed to `pcp prove --prover-model`")
    ap.add_argument("--skip-preflight", action="store_true")
    ap.add_argument("--dry-run", action="store_true", help="print each rung's command line and exit")
    ap.add_argument("extra", nargs="*", help="extra flags for `pcp prove` (after `--`)")
    return ap


def previous_rows(summary_path: Path) -> dict[str, dict[str, Any]]:
    """The rows of an earlier ladder run, by rung; empty when there is no summary."""
    if not summary_path.exists():
        return {}
    try:
        rows = json_load(summary_path)
    except (ValueError, OSError):
        return {}
    return {str(r.get("rung")): r for r in rows if isinstance(r, dict) and r.get("rung")}


def rungs_to_run(rungs: Sequence[Rung], previous: Mapping[str, Mapping[str, Any]]) -> list[Rung]:
    """Under ``--resume``: the rungs whose row is missing or not ``exit 0``."""
    return [r for r in rungs if previous.get(r.name, {}).get("exit") != 0]


def _run(args: argparse.Namespace, paths: Paths, launcher: Sequence[str]) -> int:
    resume = args.resume is not None
    if resume:
        args.stamp = args.resume
    rungs = [replace(r, wall_seconds=float(args.wall_seconds)) for r in select_rungs(args.only)]
    carry = not args.no_carry and args.brief != "spec-only"
    paper = not args.no_paper and args.brief != "spec-only"
    common: dict[str, Any] = dict(
        stamp=args.stamp, brief=args.brief, runner=args.runner, decomposer=args.decomposer,
        prover_model=args.prover_model, extra=list(args.extra), launcher=launcher, fresh=not resume,
    )
    summary_path = paths.summary(args.stamp)
    previous = previous_rows(summary_path) if resume else {}
    todo = rungs_to_run(rungs, previous) if resume else list(rungs)

    if args.dry_run:
        for rung in todo:
            library = library_for(rung, paths, brief=args.brief, carry=carry, paper=paper)
            print(shlex.join(rung_argv(rung, paths, library=library, **common)))
        return 0

    if not args.skip_preflight:
        problems = preflight(rungs, paths, launcher=launcher)
        if problems:
            print("preflight failed -- nothing has been spent:")
            for problem in problems:
                print(f"  · {problem}")
            return 2

    if resume:
        done = [r.name for r in rungs if r not in todo]
        print(f"resuming ladder {args.stamp}: keeping {', '.join(done) or 'nothing'}; "
              f"running {', '.join(r.name for r in todo) or 'nothing'}", flush=True)
    rows: dict[str, dict[str, Any]] = dict(previous)
    fresh: dict[str, Path] = {}
    for rung in todo:
        library = library_for(rung, paths, brief=args.brief, carry=carry, paper=paper, fresh=fresh)
        _assert_library_is_clean(library, paths.forbidden)
        row = run_rung(rung, paths, library=library, carry=carry, **common)
        rows[rung.name] = row
        # Rewritten after every rung, so an interrupted ladder still has its rows.
        json_dump(summary_path, _ordered(rows, rungs))
        if row["published"] and carry:
            fresh[rung.name] = Path(row["published"])
        if row["outage"]:
            remaining = " ".join(r.name for r in todo[todo.index(rung):])
            print(f"\nSTOPPING: {rung.name} could not run ({row['outage']}). "
                  "This is an outage, not a result -- fix it and re-run the remaining "
                  f"rungs with --resume {args.stamp} (or --only {remaining})", flush=True)
            break

    results = _ordered(rows, rungs)
    print(f"\nladder summary: {summary_path}")
    for r in results:
        mark = "ok  " if r["exit"] == 0 else "OUT " if r["outage"] else "TIME" if r["timed_out"] else "fail"
        print(f"  [{mark}] {r['rung']:18} {r['elapsed_s'] / 60:6.1f} min  {r['record']}")
    return 0 if results and all(r["exit"] == 0 for r in results) else 1


def _ordered(rows: Mapping[str, dict[str, Any]], rungs: Sequence[Rung]) -> list[dict[str, Any]]:
    """Summary rows in ladder order; rows for rungs outside this selection keep their place after."""
    names = [r.name for r in rungs]
    ordered = [rows[n] for n in names if n in rows]
    ordered += [row for name, row in rows.items() if name not in names]
    return ordered


def main(
    argv: Sequence[str] | None = None, *, paths: Paths = DEFAULT_PATHS, launcher: Sequence[str] = DEFAULT_LAUNCHER
) -> int:
    args = build_parser().parse_args(argv)
    try:
        return _run(args, paths, launcher)
    except PcpError as exc:
        print(str(exc), file=sys.stderr)
        return exc.exit_code
    except KeyboardInterrupt:
        print("interrupted", file=sys.stderr)
        return 130


if __name__ == "__main__":
    sys.exit(main())
