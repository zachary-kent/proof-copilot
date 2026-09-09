#!/usr/bin/env python3
"""Extract golden IPM states by replaying real Iris proofs through petanque (contract 1.16, 5.8).

Printer parsing is layout-fragile, so it needs per-version golden tests, and the goldens
have to come from *real* proofs rather than from what the parser's author imagined
Iris prints (PLAN.md 14).  This walks a library root, replays each proof script tactic
by tactic through a :class:`~pcp.state.pool.SessionPool`, and records every goal it
sees along the way -- the raw ``ty`` text and the structured Coq context, plus the
provenance ``(file, lemma, step)``.  Nothing is interpreted here; interpretation is what
the tests check.

    python eval/extract_goldens.py --limit-files 12 --limit-lemmas 8

Scripts come from ``pcp.rocq.decls`` (the one lexer): comments are stripped and bullets
are their own sentences, so a fused ``(* comment *) -`` sentence can never be sent.
petanque runs tactics serially inside one process, so the only way to use a big
machine is more processes over disjoint files: ``--shard i/n``.
"""

from __future__ import annotations

import argparse
import json
import os
import random
import sys
import time
from pathlib import Path
from typing import Any, TextIO

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pcp.config import env as penv  # noqa: E402
from pcp.errors import PcpError  # noqa: E402
from pcp.rocq.decls import ProofBlock, parse_blocks  # noqa: E402
from pcp.state.pool import SessionPool  # noqa: E402
from pcp.util.io import read_text  # noqa: E402

START_TACTIC = "<start>"
DEFAULT_OUT = Path("tests/goldens/ipm_states.jsonl")


def default_root() -> Path | None:
    """The first ``ROCQPATH``/``COQPATH`` entry (then the pinned switch) that holds Iris."""
    return penv.iris_root()


def parse_shard(text: str) -> tuple[int, int]:
    try:
        i, n = (int(x) for x in text.split("/"))
    except ValueError:
        raise SystemExit(f"--shard must be i/n, got {text!r}") from None
    if n <= 0 or not 0 <= i < n:
        raise SystemExit(f"--shard {text!r}: need 0 <= i < n")
    return i, n


def select_files(root: Path, pattern: str, *, seed: int, shard: tuple[int, int], limit: int) -> list[Path]:
    files = sorted(p for p in root.glob(pattern) if p.is_file())
    random.Random(seed).shuffle(files)
    i, n = shard
    return files[i::n][:limit]


def proof_blocks(source: str) -> list[ProofBlock]:
    """Opaque tactic proofs only: ``Defined`` bodies may be computed with, and a term proof has no steps."""
    return [b for b in parse_blocks(source) if b.has_proof and b.ender == "Qed" and b.name and b.tactics()]


def dump(fh: TextIO, file: str, thm: str, step: int, tactic: str, goals: list[Any]) -> int:
    for i, g in enumerate(goals):
        row = {
            "file": file,
            "thm": thm,
            "step": step,
            "tactic": tactic,
            "goal_index": i,
            "ty": g.ty,
            "hyps": [{"names": list(h.names), "ty": h.ty} for h in (g.hyps or ())],
        }
        fh.write(json.dumps(row, ensure_ascii=False) + "\n")
    return len(goals)


def replay(pool: SessionPool, path: Path, rel: str, block: ProofBlock, *, limit_steps: int, fh: TextIO) -> int:
    """Replay one proof from its root; states are immutable, so goals are read after the run."""
    assert block.name is not None
    session = pool.open(path, block.name)
    root = session.start()
    written = dump(fh, rel, block.name, 0, START_TACTIC, session.goals(root))
    for i, result in enumerate(session.replay(block.tactics()[:limit_steps]), start=1):
        if not result.ok or result.state is None:
            break
        written += dump(fh, rel, block.name, i, result.tactic, session.goals(result.state))
        if result.proof_finished:
            break
    return written


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--root", type=Path, default=None, help="library root (default: the one holding iris/)")
    ap.add_argument("--pattern", default="iris/**/*.v")
    ap.add_argument("--limit-files", type=int, default=12)
    ap.add_argument("--limit-lemmas", type=int, default=8)
    ap.add_argument("--limit-steps", type=int, default=40)
    ap.add_argument("--timeout", type=float, default=20.0, help="per-tactic seconds")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--shard", default="0/1", help="i/n -- take every n-th file starting at i")
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = ap.parse_args(argv)

    root = (args.root or default_root())
    if root is None:
        print("cannot find the Iris library root; set ROCQPATH or pass --root", file=sys.stderr)
        return 2
    root = root.resolve()
    if not root.is_dir():
        print(f"--root {root}: no such directory", file=sys.stderr)
        return 2
    files = select_files(root, args.pattern, seed=args.seed, shard=parse_shard(args.shard), limit=args.limit_files)
    if not files:
        print(f"no files match {args.pattern!r} under {root}", file=sys.stderr)
        return 2

    out: Path = args.out.resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    partial = out.with_name(out.name + ".partial")
    rng = random.Random(args.seed)
    written = lemmas = 0
    started = time.time()
    pool = SessionPool(root, size=1, step_timeout=args.timeout)
    try:
        with partial.open("w", encoding="utf-8") as fh:
            for path in files:
                rel = str(path.relative_to(root))
                blocks = proof_blocks(read_text(path))
                rng.shuffle(blocks)
                for block in blocks[: args.limit_lemmas]:
                    try:
                        written += replay(pool, path, rel, block, limit_steps=args.limit_steps, fh=fh)
                        lemmas += 1
                    except (PcpError, OSError) as exc:  # one bad lemma must not stop the sweep
                        print(f"  ! {rel}:{block.name}: {type(exc).__name__}: {exc}", file=sys.stderr)
                print(f"{rel}: {written} states so far ({time.time() - started:.0f}s)", file=sys.stderr)
        os.replace(partial, out)
    finally:
        pool.close()
    print(f"wrote {written} goal states from {lemmas} lemmas to {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
