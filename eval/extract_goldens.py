#!/usr/bin/env python3
"""Extract golden IPM states by replaying real Iris proofs through petanque.

The point is stated in PLAN.md 14: printer parsing is layout-fragile, so it needs
per-version golden tests, and the goldens have to come from *real* proofs rather than
from what the parser's author imagined Iris prints.  This walks the installed Iris
library, replays each proof script tactic by tactic, and records every goal render it
sees along the way.

    python eval/extract_goldens.py --limit-files 12 --limit-lemmas 8

Writes JSONL to ``tests/goldens/ipm_states.jsonl``: one record per goal, carrying the
raw ``ty`` text, the structured Coq context, and the provenance (file, lemma, step).
Nothing is interpreted here -- interpretation is what the tests check.
"""

from __future__ import annotations

import argparse
import json
import os
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pcp.core.session import ProofSession, SessionPool  # noqa: E402
from pcp.core.vernac import parse_blocks  # noqa: E402

DEFAULT_ROOT = Path(os.environ.get("COQPATH", "")) if os.environ.get("COQPATH") else None


def iris_root() -> Path:
    if DEFAULT_ROOT and (DEFAULT_ROOT / "iris").exists():
        return DEFAULT_ROOT
    guess = Path.home() / ".opam" / "pcp" / "lib" / "coq" / "user-contrib"
    if (guess / "iris").exists():
        return guess
    raise SystemExit("cannot find the Iris user-contrib root; set COQPATH")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, default=None)
    ap.add_argument("--pattern", default="iris/**/*.v")
    ap.add_argument("--limit-files", type=int, default=12)
    ap.add_argument("--limit-lemmas", type=int, default=8)
    ap.add_argument("--limit-steps", type=int, default=40)
    ap.add_argument("--timeout", type=float, default=20.0)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--shard", default="0/1", help="i/n -- take every n-th file starting at i")
    ap.add_argument("--out", type=Path, default=Path("tests/goldens/ipm_states.jsonl"))
    args = ap.parse_args()

    root = args.root or iris_root()
    files = sorted(root.glob(args.pattern))
    rng = random.Random(args.seed)
    rng.shuffle(files)
    i, n = (int(x) for x in args.shard.split("/"))
    # petanque runs tactics serially inside one process, so the only way to use a
    # big machine is more processes over disjoint files.
    files = files[i::n][: args.limit_files]

    args.out.parent.mkdir(parents=True, exist_ok=True)
    pool = SessionPool(root, size=1, step_timeout=args.timeout)
    written = 0
    lemmas = 0
    started = time.time()
    with args.out.open("w", encoding="utf-8") as fh:
        for path in files:
            src = path.read_text(encoding="utf-8")
            blocks = [b for b in parse_blocks(src) if b.has_proof and b.ender == "Qed" and b.tactics()]
            rng.shuffle(blocks)
            for block in blocks[: args.limit_lemmas]:
                rel = str(path.relative_to(root))
                try:
                    written += replay(pool, path, rel, block, args, fh)
                    lemmas += 1
                except Exception as exc:  # noqa: BLE001 -- one bad lemma must not stop the sweep
                    print(f"  ! {rel}:{block.name}: {type(exc).__name__}: {exc}", file=sys.stderr)
            print(f"{rel}: {written} states so far ({time.time() - started:.0f}s)", file=sys.stderr)
    pool.close()
    print(f"wrote {written} goal states from {lemmas} lemmas to {args.out}")
    return 0


def replay(pool: SessionPool, path: Path, rel: str, block, args, fh) -> int:
    session = ProofSession(pool, path, block.name, step_timeout=args.timeout)
    state = session.start()
    n = 0
    n += dump(fh, rel, block.name, 0, "<start>", session.goals(state))
    for i, tactic in enumerate(block.tactics()[: args.limit_steps], start=1):
        result = session.run(tactic)
        if not result.ok:
            break
        n += dump(fh, rel, block.name, i, tactic, session.goals(result.state))
        if result.proof_finished:
            break
    return n


def dump(fh, file: str, thm: str, step: int, tactic: str, goals) -> int:
    for i, g in enumerate(goals):
        fh.write(
            json.dumps(
                {
                    "file": file,
                    "thm": thm,
                    "step": step,
                    "tactic": tactic,
                    "goal_index": i,
                    "ty": g.ty,
                    "hyps": [{"names": list(h.names), "ty": h.ty} for h in getattr(g, "hyps", [])],
                },
                ensure_ascii=False,
            )
            + "\n"
        )
    return len(goals)


if __name__ == "__main__":
    raise SystemExit(main())
