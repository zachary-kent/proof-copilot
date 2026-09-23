"""``pcp trace`` / ``state`` / ``ledger`` / ``destruct``: the state layer from the shell (contract 1.7-1.10).

``trace`` is the only command here that talks to petanque; ``state`` and ``ledger`` read
the JSONL it wrote, and ``destruct`` is pure (skeleton in, pattern out).  Paths are
resolved against the invocation directory *here*, so nothing below the CLI ever sees a
relative path (ARCHITECTURE.md 3).
"""

from __future__ import annotations

import argparse
import os
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Any

from pcp.cli.common import absolute, note
from pcp.errors import UsageError
from pcp.util.io import read_text

if TYPE_CHECKING:
    from pcp.state.ipm.reflect import Reflector
    from pcp.state.pool import SessionPool
    from pcp.state.session import ProofSession
    from pcp.state.trace import Tracer

DEFAULT_TRACE_DIR = Path(".pcp/traces")
DEFAULT_COQ_ROOT = Path(".pcp/coq")


# ---------------------------------------------------------------------- trace


def script_tactics(text: str) -> list[str]:
    """A script file as tactic sentences, by the lexer -- not by physical line.

    A tactic wrapped over two lines is one sentence and a comment line is no sentence
    at all; neither half of a wrapped tactic, nor a comment, is sent to Rocq alone.
    """
    from pcp.rocq.lexer import split_sentences

    return [s.code for s in split_sentences(text) if s.code.strip()]


@dataclass
class TraceRun:
    """One ``pcp trace`` session: its own single-process pool, closed when done.

    Exposed as an object so a test can hold the session and prove the reflected path
    is live (a per-hypothesis ``Set Printing All`` probe answers only through ``IDump``).
    """

    pool: SessionPool
    session: ProofSession
    tracer: Tracer
    reflector: Reflector | None = None

    @classmethod
    def open(cls, file: Path, lemma: str, *, reflect: bool = False, coq_root: Path | None = None) -> TraceRun:
        """``reflect`` builds ``IDump`` under ``coq_root`` and spawns the pool with it on the load path.

        The env is passed to the pool, never written into ``os.environ``, and keeps every
        existing ``ROCQPATH``/``COQPATH`` entry (overwriting ``ROCQPATH`` with a
        ``COQPATH``-derived value would lose Iris on a ROCQPATH-only machine).
        """
        from pcp.state.ipm.reflect import REQUIRE, Reflector, build_idump, env_with_idump
        from pcp.state.ledger.diff import attach
        from pcp.state.pool import SessionPool
        from pcp.state.trace import Tracer

        env: dict[str, str] | None = None
        pre: str | None = None
        if reflect:
            root = coq_root if coq_root is not None else absolute(DEFAULT_COQ_ROOT)
            assert root is not None
            build_idump(root)
            env = env_with_idump(dict(os.environ), root)
            pre = REQUIRE
        pool = SessionPool(file.parent, size=1, env=env)
        try:
            session = pool.open(file, lemma, pre_commands=pre)
            reflector = Reflector(session) if reflect else None
            tracer = attach(Tracer(session, reflector=reflector))
        except BaseException:
            pool.close()
            raise
        return cls(pool, session, tracer, reflector)

    def annotate(self) -> None:
        """The persistence oracle on the focused goal of every successful step, at that step's state.

        Probing every step at the *final* state would make a hypothesis consumed earlier
        answer "error" and a later namesake answer for the wrong prop.
        """
        from pcp.state.ipm.oracle import annotate

        for step in self.tracer.trace.steps:
            if not step.ok or step.state_id < 0 or not step.goals:
                continue
            annotate(self.session, step.goals[0], state=self.session.state(step.state_id))

    def close(self) -> None:
        self.pool.close()


def cmd_trace(args: argparse.Namespace) -> int:
    file = absolute(args.file)
    assert file is not None
    if not file.is_file():
        raise UsageError(f"{args.file}: no such file")
    lemma: str = args.lemma
    if args.script:
        script = absolute(args.script)
        assert script is not None
        tactics = script_tactics(read_text(script))
    else:
        from pcp.rocq.decls import find_block

        block = find_block(read_text(file), lemma)
        if block is None or not block.has_proof:
            raise UsageError(f"{args.file}: {lemma} has no proof to trace; pass --script")
        tactics = block.tactics()
    out = absolute(args.out) if args.out else absolute(DEFAULT_TRACE_DIR / f"{file.stem}.{lemma}.jsonl")
    assert out is not None

    run = TraceRun.open(file, lemma, reflect=bool(args.reflect))
    try:
        run.tracer.start()
        trace = run.tracer.run_script(tactics)
        if args.oracle:
            run.annotate()
        trace.to_jsonl(out)
    finally:
        run.close()
    print(f"{len(trace.steps)} steps, {len(trace.events)} ledger events → {out}")
    if trace.error:
        note(f"stopped at step {trace.failed_at}: {trace.error}")
    return 0


# ---------------------------------------------------------------------- state


def _load_trace(path: Path | str) -> Any:
    from pcp.state.trace import Trace

    resolved = absolute(path)
    assert resolved is not None
    if not resolved.is_file():
        raise UsageError(f"{path}: no such trace")
    return Trace.from_jsonl(resolved)


def cmd_state(args: argparse.Namespace) -> int:
    from pcp.state.render import render_goal

    trace = _load_trace(args.trace)
    step = trace.step_at(args.step) if args.step is not None else trace.final
    if step is None or not step.goals:
        raise UsageError("no goals at that step")
    diff_only = not args.all
    prev_goals: list[Any] = []
    if diff_only and step.step > 0:
        prev = trace.step_at(step.step - 1)
        prev_goals = list(prev.goals) if prev is not None else []
    if not step.ok:
        note(f"step {step.step} failed ({step.error}); showing the goals before it")
    for i, goal in enumerate(step.goals):
        # Positional baseline: goal i against the previous goal i (against the previous
        # *first* goal, a split's second goal would read as all-changed).
        base = prev_goals[i] if i < len(prev_goals) else None
        rendered = render_goal(
            goal,
            select=args.select,
            mode=args.mode,
            budget=args.budget,
            diff_only=diff_only and base is not None,
            prev=base,
            store=trace.store,
        )
        print(rendered.text)
        print()
    return 0


# --------------------------------------------------------------------- ledger


def cmd_ledger(args: argparse.Namespace) -> int:
    from pcp.state.ledger.query import (
        blame,
        leftovers,
        render_blame,
        render_events,
        render_leftovers,
        render_provenance,
        render_unused,
        unused_at_qed,
        where_did_it_go,
    )

    trace = _load_trace(args.trace)
    query: str = args.query
    if query in ("where", "blame") and not args.hyp:
        raise UsageError("--hyp is required")
    if query == "events":
        text = render_events(trace.events)
        if text:
            print(text)
    elif query == "where":
        print(render_provenance(where_did_it_go(trace, args.hyp)))
    elif query == "blame":
        # The failed step, else the one that would run next -- never a step past the
        # end of a stopped trace (not `len(steps)`).
        if args.step is not None:
            at = args.step
        elif trace.failed_at is not None:
            at = trace.failed_at
        else:
            at = trace.final.step + 1 if trace.final is not None else 0
        print(render_blame(blame(trace, at, args.hyp)))
    elif query == "leftovers":
        print(render_leftovers(leftovers(trace, args.step)))
    elif query == "unused":
        print(render_unused(unused_at_qed(trace)))
    else:  # argparse restricts the choices; keep the failure loud all the same
        raise UsageError(f"unknown ledger query {query!r}")
    return 0


# ------------------------------------------------------------------- destruct


def cmd_destruct(args: argparse.Namespace) -> int:
    """Offline: no Rocq.  Synthesise a pattern, or align the one given (exit 1 if it does not fit)."""
    from pcp.state.ipm.pattern import PatternSyntaxError, align, compile_auto
    from pcp.state.ipm.skeleton import parse_skeleton

    skel = parse_skeleton(args.prop)
    if args.pattern:
        try:
            report = align(args.pattern, skel)
        except PatternSyntaxError as exc:
            raise UsageError(f"the pattern {args.pattern!r} does not parse: {exc}") from None
        print(report.render())
        return 0 if report.ok else 1
    d = compile_auto(skel, args.name)
    print(d.idestruct(args.name))
    print()
    print("prop skeleton:")
    print(skel.render(1))
    return 0
