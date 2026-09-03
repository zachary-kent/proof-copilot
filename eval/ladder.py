#!/usr/bin/env python3
"""Run the benchmark ladder, each rung carrying forward what the last one produced.

The rungs are the same development at growing scale (`docs/BENCHMARKS.md`), and a
person working through them would not start each one from nothing: they would have
their own previous proof open in the next buffer, and they would have read the paper.
So each rung is given, read-only:

* `.pcp/library/paper` — arXiv:2501.07503, the algorithms paper these developments
  mechanise. Prose and pseudocode; no Coq, no Iris, no ghost state.
* `.pcp/library/solved/<earlier rung>` — what **this system** produced on every rung
  below, finished or not, with a header saying which.

What stays closed is what was always closed: `eval/corpus/` (every *other* rung's
corpus, which for a design rung is the answer), `.pcp/reference/` (the real proofs),
`docs/`, `tests/`, `.git`, and the operator's `$HOME`. The library is bound back
after those masks and contains nothing but this system's own output plus the paper —
never a reference proof. That boundary is the whole reason the numbers mean anything,
so it is checked here (`_assert_library_is_clean`) and not merely intended.

    python eval/ladder.py --stamp overnight            # the whole ladder
    python eval/ladder.py --only rwcas seqlock         # a prefix of it
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "eval" / "corpus" / "bench"
LIBRARY = ROOT / ".pcp" / "library"
RUNS = ROOT / ".pcp" / "runs"


@dataclass
class Rung:
    name: str
    #: Seconds a single node may spend.  Scaled by the reference proof's size: the
    #: default 900 s is a rounding error against a 1069-tactic `cas_spec`.
    node_seconds: float
    #: Wall-clock cap for the whole rung, enforced outside the process.
    wall_seconds: float = 10800.0
    #: Override the "largest holdout" rule.  Needed exactly once; see `LADDER`.
    root_override: str = ""
    #: Clock for one design round. Scales with the development, because the
    #: decomposer has to *read* it before it can decompose it: 1800 s was enough for
    #: 317-line rwcas and killed the first round on 3180-line cached_strong outright.
    decomposer_seconds: float = 1800.0

    @property
    def dir(self) -> Path:
        return CORPUS / self.name

    @property
    def bench(self) -> dict:
        return json.loads((self.dir / "bench.json").read_text(encoding="utf-8"))

    @property
    def file(self) -> Path:
        # Proof rungs are `M<hash>.v` (anonymised); design rungs keep a readable
        # module name (`Rwcas.v`). Match any source, not just the anonymised shape.
        files = sorted(f for f in self.dir.glob("*.v") if "__pcp" not in f.stem)
        if not files:
            raise SystemExit(f"{self.name}: no development in {self.dir}")
        return files[0]

    @property
    def is_design_rung(self) -> bool:
        """Whether the design is the task, rather than given."""
        from pcp.orch.assemble import Development
        from pcp.orch.decomposer import blank_predicates

        return bool(blank_predicates(Development(self.file)))

    @property
    def root_lemma(self) -> str:
        """The largest held-out proof: the one the rung is actually about.

        Named by its *anonymised* identifier, which is what is in the file.
        """
        if self.root_override:
            return self.root_override
        holdout = self.bench["holdout"]
        biggest = max(holdout, key=lambda h: h.get("tactics", 0))
        return biggest["anonymised"]


#: In difficulty order, which for the last two is also the order that keeps them
#: from measuring the same thing twice.
#:
#: `cached_wf` and `cached_strong` share their `cas_spec` **byte for byte** (both
#: reference proofs hash to 4c2392c6…, 1069 tactics), and so do their
#: `new_big_atomic_spec`s. The rungs differ only in `read'_spec`: 389 tactics with
#: prophecy against 198 without. Rooting both at the largest holdout would therefore
#: have made the second of the pair a copy job the moment the first one's solution
#: was carried forward -- a "solve" that measures transfer, not proving. So
#: `cached_strong` (the smaller `read'_spec`) takes `cas_spec`, and `cached_wf` is
#: rooted at the one lemma on this ladder that nothing carried forward can supply.
#: Budgets satisfy `decomposer + 2 * node <= wall` (checked in `preflight`), so a
#: round of dispatch can fail, be fed back, and be re-dispatched against a revised
#: decomposition inside the wall. A node budget large enough to consume the whole
#: wall buys one attempt at a decomposition nobody ever gets to correct.
#: **Design** rungs: the invariant, the client predicate and the handle are blanked to
#: `True` and inventing them is the task. The proof rungs of the same names (`rwcas`,
#: `seqlock`, ...) hand the design over and hold out only the tactics -- they measure
#: something else, and running the ladder on them by mistake cost a full night.
#: `blank_predicates(dev)` tells the two apart in one line.
#:
#: `cached_strong` and `cached_wf` have no design variant: two of their three held-out
#: results are stated in terms of the ghost state a designer would have to invent
#: (see `build.sh`). They stay on the ladder only as proof rungs, and are not run here.
# Decomposer clocks are set by *design* difficulty, not by how long the file is.
# On 2026-09-01 two of three rungs died with no plan at all: rwcas at 1800s then
# 3600s, seqlock_wf at 3000s then 4200s -- 210 minutes for nothing.  The one that
# landed, seqlock, needed ~1500s of its 2400s.  rwcas is listed first because it is
# the smallest *development* (53 lines), but it has the hardest design in the ladder:
# a prophecy-and-helping registry, whose reference `write_spec` alone is 92 lines and
# 119 tactics.  So it was given the least time for the most work.  These budgets fit
# preflight's "design + 2 dispatch rounds <= wall" rule at the 10800s wall.
LADDER = [
    Rung("rwcas_design", node_seconds=1800, decomposer_seconds=5400),
    Rung("seqlock_design", node_seconds=2700, decomposer_seconds=2700),
    Rung("seqlock_wf_design", node_seconds=2700, decomposer_seconds=5400),
]


# --------------------------------------------------------------- the boundary

#: Nothing under these may ever be copied into the library.  A rung's own record
#: directory is safe; the corpus and the answer key are not.
FORBIDDEN_SOURCES = (ROOT / "eval" / "corpus", ROOT / ".pcp" / "reference")


def _assert_library_is_clean(paths: list[Path]) -> None:
    """The library must hold only this system's output and the paper.

    Cheap to check and catastrophic to get wrong: a reference proof reaching a
    worker does not make the run fail, it makes every number after it a lie.
    """
    for path in paths:
        resolved = path.resolve()
        for forbidden in FORBIDDEN_SOURCES:
            if forbidden.exists() and (resolved == forbidden.resolve()
                                       or forbidden.resolve() in resolved.parents):
                raise SystemExit(f"refusing to run: library path {path} is inside {forbidden}")
        for v in resolved.rglob("*.v"):
            head = v.read_text(encoding="utf-8", errors="replace")[:400]
            if "Produced by proof-copilot" not in head:
                raise SystemExit(
                    f"refusing to run: {v} is in the library but was not produced by a run. "
                    "Only this system's own exported solutions belong here."
                )


def publish(rung: Rung, record_dir: Path) -> Path | None:
    """Copy a finished rung's exported solution into the library for the next one."""
    solutions = sorted(record_dir.glob("*/solution"))
    if not solutions:
        return None
    dest = LIBRARY / "solved" / rung.name
    if dest.exists():
        shutil.rmtree(dest)
    shutil.copytree(solutions[-1], dest)
    # `"COMPLETE" in "INCOMPLETE"` is True, and this told a worker that rwcas -- which
    # had a contested obligation and never integrated -- was a complete solution.
    # Test the negative marker first; a substring test on an English word is a trap.
    header = _header(dest)
    status = "incomplete" if "INCOMPLETE" in header else "complete"
    (dest / "README.md").write_text(
        f"# `{rung.name}`, as this system solved it ({status})\n\n"
        f"Machine-generated by proof-copilot on the `{rung.name}` rung, root lemma "
        f"`{rung.root_lemma}`. Not a reference solution and not checked by a human.\n\n"
        "Read it as a worked example of this codebase's idiom -- the ghost state it "
        "settled on, the shape of its invariants, how it opens an atomic update. "
        "The problem you have been given is a different one.\n",
        encoding="utf-8",
    )
    return dest


def _header(dest: Path) -> str:
    for v in sorted(dest.glob("*.v")):
        return v.read_text(encoding="utf-8", errors="replace")[:400]
    return ""


# -------------------------------------------------------------- pinned source

SNAPSHOTS = ROOT / ".pcp" / "snapshots"

#: Copied into a snapshot. Everything else -- `.pcp`, `.venv`, `.git`, caches -- is
#: either state, huge, or both.
_SOURCE = ("pcp", "eval", "skills", "coq", "scripts", "pyproject.toml", "env.sh")


def snapshot_source(stamp: str) -> Path:
    """Freeze the harness's source for the duration of a ladder run.

    A 15-hour experiment running out of a tree that is simultaneously being edited is
    not a reproducible experiment, and it is not even a safe one: a long-lived process
    imports some modules at startup and others lazily, so an edit in between leaves it
    running two different vintages of the same codebase at once. That is not a
    hypothetical -- it killed a live rung 30 minutes in, when a lazily imported symbol
    did not exist in the `failures` module the process had cached at startup.

    Snapshotting also makes a result *attributable*: this run used this code, and the
    directory is still there to prove it.
    """
    dest = SNAPSHOTS / stamp
    if dest.exists():
        return dest
    dest.mkdir(parents=True)
    for name in _SOURCE:
        src = ROOT / name
        if not src.exists():
            continue
        if src.is_dir():
            shutil.copytree(src, dest / name,
                            ignore=shutil.ignore_patterns("__pycache__", "*.pyc", "*.vo", "*.vok",
                                                          "*.vos", "*.glob"))
        else:
            shutil.copy2(src, dest / name)
    return dest


# --------------------------------------------------------------- preflight

def preflight(rungs: list[Rung], source: Path | None = None) -> list[str]:
    """Cheap checks, before anything expensive is spent.

    Ordered by what this ladder actually lost time to: a revoked credential consumed
    two rungs before anyone noticed, and a rung whose corpus does not compile cannot
    produce anything but noise. Both are seconds to check and hours to discover.
    """
    problems: list[str] = []
    for rung in rungs:
        if not rung.dir.exists():
            problems.append(f"{rung.name}: no corpus at {rung.dir}")
            continue
        # The whole point of this ladder is that the invariant is not given. Running
        # it on a proof rung measures tactic work against a handed-over design, which
        # is a different experiment -- and is exactly the mistake that cost a night.
        if not rung.is_design_rung:
            problems.append(
                f"{rung.name}: the design is GIVEN here (no blank predicates), so this "
                "is a proof rung, not a design rung"
            )
        try:
            rung.file, rung.root_lemma
        except SystemExit as exc:
            problems.append(f"{rung.name}: {exc}")
    # Start the orchestrator exactly the way a rung will. A launcher that cannot even
    # import is a zero-second "failure" on every rung in the list -- which is how both
    # cached rungs were consumed by a missing `import sys`.
    entry = (["-c", f"import sys; sys.path.insert(0, {str(source)!r}); "
                    "from pcp.cli.main import main; sys.exit(main())"]
             if source else ["-m", "pcp.cli.main"])
    proc = subprocess.run([str(ROOT / ".venv" / "bin" / "python"), *entry, "prove", "--help"],
                          cwd=str(ROOT), capture_output=True, text=True, timeout=120)
    if proc.returncode != 0:
        problems.append("the orchestrator will not start: "
                        + " ".join((proc.stdout + proc.stderr).split())[-200:])
    # A revision round only starts once the whole frontier has finished, so the wall
    # must fit the design round *plus* at least two rounds of dispatch. cached_strong
    # spent 4500 s designing and 5400 s per node inside a 10800 s wall: the first
    # round could not finish in time, so the granularity feedback -- the entire point
    # of dispatching, failing and revising -- was never delivered once.
    for rung in rungs:
        needed = rung.decomposer_seconds + 2 * rung.node_seconds
        if needed > rung.wall_seconds:
            problems.append(
                f"{rung.name}: budget cannot fit a revision -- design {rung.decomposer_seconds:.0f}s "
                f"+ 2 dispatch rounds of {rung.node_seconds:.0f}s = {needed:.0f}s > wall "
                f"{rung.wall_seconds:.0f}s. Lower --node-seconds or raise --wall-seconds."
            )
    if shutil.which("bwrap") is None:
        problems.append("bubblewrap (`bwrap`) is not installed; --sandbox runs cannot start")
    proc = subprocess.run(["claude", "-p"], input="Reply with exactly: OK",
                          capture_output=True, text=True, timeout=180)
    if proc.returncode != 0 or "OK" not in proc.stdout:
        problems.append(
            "the provider is not reachable -- re-authenticate before starting: "
            + " ".join((proc.stdout + proc.stderr).split())[:200]
        )
    return problems


# ------------------------------------------------------------------- the run

def run_rung(rung: Rung, *, stamp: str, library: list[Path], extra: list[str],
             source: Path | None = None) -> dict:
    tag = f"ladder_{stamp}_{rung.name}"
    record = RUNS / tag
    # Plain `-m` unless a snapshot is pinned. The snapshot path needs `-c` because
    # the working directory must stay the repo (the docs index and `.pcp` resolve
    # relative to it) while the *code* comes from the copy, and `-m` would let the
    # working directory win.
    entry = (
        ["-c", f"import sys; sys.path.insert(0, {str(source)!r}); "
               "from pcp.cli.main import main; sys.exit(main())"]
        if source else ["-m", "pcp.cli.main"]
    )
    argv = [
        # `-u`: a block-buffered log is indistinguishable from a stalled run, and
        # reading one cost real time before it turned out the run was fine.
        str(ROOT / ".venv" / "bin" / "python"), "-u", *entry, "prove",
        str(rung.file), rung.root_lemma,
        "--sandbox",
        "--fresh",
        "--state-tools",
        "--graph", str(ROOT / ".pcp" / f"graph_{tag}.db"),
        "--workroot", str(ROOT / ".pcp" / "work" / tag),
        "--record", str(record),
        "--corpus", rung.name,
        "--node-seconds", str(rung.node_seconds),
        "--decomposer-seconds", str(rung.decomposer_seconds),
        "--reference", str(ROOT / ".pcp" / "reference" / rung.name),
        # Pinned rather than left to the provider default. The design step is the
        # one decision the rest of the run cannot recover from, and the ladder's
        # whole premise is that a design transfers between rungs -- so it is also
        # the step that must not drift between them.
        "--decomposer", "claude-opus-5",
    ]
    for path in library:
        argv += ["--library", str(path)]
    argv += extra

    log = RUNS / f"{tag}.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    print(f"\n=== {rung.name}: {rung.file.name} / {rung.root_lemma} "
          f"(node {rung.node_seconds:.0f}s, wall {rung.wall_seconds:.0f}s)", flush=True)
    print(f"    library: {[str(p) for p in library] or 'nothing'}", flush=True)
    print(f"    log: {log}", flush=True)

    started = time.time()
    timed_out = False
    with log.open("w", encoding="utf-8") as fh:
        proc = subprocess.Popen(argv, cwd=str(ROOT), stdout=fh, stderr=subprocess.STDOUT)
        try:
            code = proc.wait(timeout=rung.wall_seconds)
        except subprocess.TimeoutExpired:
            timed_out = True
            proc.kill()
            code = proc.wait()
    elapsed = time.time() - started

    published = publish(rung, record)
    outage = looks_like_an_outage(log) if code != 0 else ""
    result = {
        "outage": outage,
        "rung": rung.name,
        "root": rung.root_lemma,
        "exit": code,
        "timed_out": timed_out,
        "elapsed_s": round(elapsed, 1),
        "record": str(record),
        "log": str(log),
        "published": str(published) if published else None,
        "tail": _tail(log, 30),
    }
    print(f"    -> exit {code}{' (WALL TIMEOUT)' if timed_out else ''} in {elapsed / 60:.1f} min"
          f"{'; published ' + published.name if published else '; nothing to publish'}", flush=True)
    return result


#: Text in a rung's log that means the run never got off the ground: the provider
#: was unreachable, the credential was revoked, a binary was missing. Not a result.
_INFRASTRUCTURE = (
    "could not run at all",
    "access token has been revoked",
    "Failed to authenticate",
    "is not on PATH",
    "bwrap:",
)


def looks_like_an_outage(log: Path) -> str:
    """Why this rung could not run, if the reason was not about proving.

    A revoked credential took out two cached rungs in under a minute each and the
    ladder marched on to report them as failures. An outage is not a measurement:
    it must stop the ladder so the rungs can be re-run, not consume them.
    """
    text = _tail(log, 40)
    for marker in _INFRASTRUCTURE:
        if marker.lower() in text.lower():
            return marker
    return ""


def _tail(log: Path, n: int) -> str:
    if not log.exists():
        return ""
    return "\n".join(log.read_text(encoding="utf-8", errors="replace").splitlines()[-n:])


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--stamp", default=time.strftime("%Y%m%d_%H%M%S"))
    ap.add_argument("--only", nargs="*", default=None, metavar="RUNG",
                    help="run just these rungs, in ladder order")
    ap.add_argument("--wall-seconds", type=float, default=10800.0,
                    help="wall-clock cap per rung (default: 3 hours)")
    ap.add_argument("--no-paper", action="store_true", help="withhold the paper")
    ap.add_argument("--no-carry", action="store_true",
                    help="withhold earlier rungs' solutions (each rung starts cold)")
    # OFF until the sandbox can be told where the real repo is. `Sandbox.for_benchmark`
    # derives `repo` from `__file__`, and that path decides what gets **masked** --
    # the answer key included. Running from a snapshot silently redefines "the repo",
    # which is not something to get subtly wrong in the isolation layer to save an
    # occasional restart. Until `repo` is passed explicitly, the discipline (do not
    # edit `pcp/` while a run is live) is the safe control.
    ap.add_argument("--snapshot", action="store_true",
                    help="run from a frozen copy of the source. NOT READY: the sandbox "
                         "resolves the repo from the code's own location, so a snapshot "
                         "changes what is masked. See eval/ladder.py.")
    ap.add_argument("--skip-preflight", action="store_true")
    ap.add_argument("extra", nargs="*", help="extra flags passed straight to `pcp prove`")
    args = ap.parse_args()

    rungs = [r for r in LADDER if args.only is None or r.name in args.only]
    if not rungs:
        raise SystemExit(f"no such rung(s): {args.only}")
    for rung in rungs:
        rung.wall_seconds = args.wall_seconds

    source = snapshot_source(args.stamp) if args.snapshot else None
    if source is not None:
        print(f"source pinned at {source}")

    if not args.skip_preflight:
        problems = preflight(rungs, source)
        if problems:
            print("preflight failed -- nothing has been spent:")
            for problem in problems:
                print(f"  · {problem}")
            return 2

    summary_path = RUNS / f"ladder_{args.stamp}.json"
    results: list[dict] = []
    paper = LIBRARY / "paper"

    # A ladder gets interrupted -- a repair, a machine, a rethink -- and `--only` is
    # how it resumes.  Seed the carry from what earlier rungs already published, or
    # resuming at rung 3 silently runs it cold and the carry stops being what the
    # experiment says it is.
    carried: list[Path] = []
    for earlier in LADDER:
        if earlier.name in {r.name for r in rungs}:
            break
        published = LIBRARY / "solved" / earlier.name
        if published.exists():
            carried.append(published)
    if carried:
        print(f"resuming: carrying forward {[p.name for p in carried]}", flush=True)

    for rung in rungs:
        library = list(carried)
        if not args.no_paper and paper.exists():
            library.append(paper)
        _assert_library_is_clean(library)
        results.append(run_rung(rung, stamp=args.stamp, library=library,
                                extra=args.extra, source=source))
        published = results[-1]["published"]
        if published and not args.no_carry:
            carried.append(Path(published))
        summary_path.write_text(json.dumps(results, indent=2), encoding="utf-8")
        if results[-1]["outage"]:
            print(f"\nSTOPPING: {rung.name} could not run ({results[-1]['outage']}). "
                  "This is an outage, not a result -- fix it and re-run the remaining "
                  f"rungs with --only {' '.join(r.name for r in rungs[rungs.index(rung):])}",
                  flush=True)
            break

    print(f"\nladder summary: {summary_path}")
    for r in results:
        mark = ("ok  " if r["exit"] == 0 else
                "OUT " if r.get("outage") else
                "TIME" if r["timed_out"] else "fail")
        print(f"  [{mark}] {r['rung']:15} {r['elapsed_s'] / 60:6.1f} min  {r['record']}")
    return 0 if all(r["exit"] == 0 for r in results) else 1


if __name__ == "__main__":
    sys.exit(main())
