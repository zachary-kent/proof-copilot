"""Post-hoc diagnosis of a failed compile, for ``pcp check`` (PLAN.md 7; contract 1.2).

``diagnose`` needs a live ``IrisGoal``; ``coqc`` output alone cannot give one.  So this
module finds the proof the compiler failed inside, replays it through petanque a
tactic at a time, and hands ``diagnose`` the goal as it stood *before* the failing
tactic.  It rides on the command every worker already runs, so it costs no turn.

Locating is by the error's **character offset** (``CompileResult.error_location``,
which ignores located warnings), not by the node under test and not by the line's
start (legacy bugs: a warning's location was taken for the error's; one-line proofs
were never found).  A Qed-time error (``Attempt to save an incomplete proof``) is
located on the ender line and maps to the body before it.

The replay opens a twin ``<stem>__pcpexplain.v`` written atomically and removed
afterwards; the ``__pcp`` infix keeps it out of every "which file is the worker's"
search.  ``explain`` never raises: a diagnosis that breaks the checker is worse than
none.  With ``verbose`` the reason for an empty answer is returned instead.
"""

from __future__ import annotations

import contextlib
import os
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from pcp.config.env import petanque_available
from pcp.errors import PcpError
from pcp.rocq.body import tactic_sentences
from pcp.rocq.decls import ProofBlock, parse_blocks
from pcp.rocq.project import CompileResult
from pcp.state.diagnose import diagnose
from pcp.util.io import atomic_write_text
from pcp.util.text import indent, one_line

TWIN_INFIX = "__pcpexplain"
DEFAULT_MAX_TACTICS = 400
DEFAULT_BUDGET_SECONDS = 90.0
_INCOMPLETE = "incomplete proof"


@dataclass(frozen=True)
class Located:
    name: str
    body_start: int
    body_end: int
    #: The error is on the proof's ender (``Qed``), not inside the body.
    at_qed: bool = False


def _as_result(output: str | CompileResult) -> CompileResult:
    return output if isinstance(output, CompileResult) else CompileResult(False, stdout=output or "")


def _line_bounds(text: str, line: int) -> tuple[int, int] | None:
    if line < 1:
        return None
    start = 0
    for _ in range(line - 1):
        nl = text.find("\n", start)
        if nl < 0:
            return None
        start = nl + 1
    end = text.find("\n", start)
    return start, (len(text) if end < 0 else end)


def error_offsets(text: str, line: int, char: int) -> list[int]:
    """Absolute offsets for ``(line, char)``: as UTF-8 bytes first, then as code points.

    Rocq's ``characters a-b`` are byte positions (verified on 9.1.1: an error after
    ``∗∗∗`` on the line reported the byte column); the code-point reading is kept as a
    fallback, and the first reading that lands in a proof body wins.
    """
    bounds = _line_bounds(text, line)
    if bounds is None:
        return []
    start, end = bounds
    line_text = text[start:end]
    as_bytes = start + len(line_text.encode("utf-8")[:char].decode("utf-8", errors="ignore"))
    as_chars = start + min(char, len(line_text))
    return [as_bytes] if as_chars == as_bytes else [as_bytes, as_chars]


def locate_failure(
    text: str,
    output: str | CompileResult,
    *,
    spans: dict[str, tuple[int, int]] | None = None,
    target: str | None = None,
) -> Located | None:
    """The proof block the compiler failed inside, by the error's character offset."""
    result = _as_result(output)
    loc = result.error_location()
    blocks = [b for b in parse_blocks(text) if b.kind == "script" and b.body_start is not None and b.body_end is not None]
    if loc is None:
        return _by_name(blocks, spans, target)
    offsets = error_offsets(text, loc.line, loc.char_start)
    for off in offsets:
        for name, (s, e) in (spans or {}).items():
            if s <= off <= e:
                return Located(name, s, e)
        for b in blocks:
            assert b.body_start is not None and b.body_end is not None
            if b.body_start <= off <= b.body_end:
                return Located(b.name or "", b.body_start, b.body_end)
    # Qed-time: the location is the ender sentence (or its line).
    bounds = _line_bounds(text, loc.line)
    for b in blocks:
        if b.ender_start is None or b.ender_end is None:
            continue
        on_ender = any(b.ender_start <= off < b.ender_end for off in offsets)
        on_line = bounds is not None and bounds[0] <= b.ender_start < bounds[1]
        if on_ender or on_line:
            assert b.body_start is not None and b.body_end is not None
            return Located(b.name or "", b.body_start, b.body_end, at_qed=True)
    return None


def _by_name(blocks: list[ProofBlock], spans: dict[str, tuple[int, int]] | None, target: str | None) -> Located | None:
    if not target:
        return None
    if spans and target in spans:
        s, e = spans[target]
        return Located(target, s, e)
    for b in blocks:
        if b.name == target:
            assert b.body_start is not None and b.body_end is not None
            return Located(target, b.body_start, b.body_end)
    return None


# ------------------------------------------------------------------- explain


def explain(
    *,
    assembly_text: str,
    assembled_path_name: str,
    compile_output_or_result: str | CompileResult,
    dev: Any = None,
    root: str | Path,
    target: str = "",
    body: str = "",
    budget_seconds: float = DEFAULT_BUDGET_SECONDS,
    max_tactics: int = DEFAULT_MAX_TACTICS,
    pool: Any = None,
    spans: dict[str, tuple[int, int]] | None = None,
    step_timeout: float = 30.0,
    verbose: bool = False,
) -> str:
    """Diagnose the failure in the compiler output against the assembled source.

    Returns ``""`` when there is nothing honest to say (``verbose`` returns the reason
    instead).  Never raises.
    """
    try:
        return _explain(
            assembly_text, assembled_path_name, compile_output_or_result, Path(root), target,
            budget_seconds=budget_seconds, max_tactics=max_tactics, pool=pool, spans=spans,
            step_timeout=step_timeout, verbose=verbose,
        )
    except Exception as exc:  # noqa: BLE001 -- best effort by construction
        return f"(diagnosis unavailable: {type(exc).__name__}: {exc})" if verbose else ""


def _quiet(reason: str, verbose: bool) -> str:
    return f"(no diagnosis: {reason})" if verbose else ""


def _explain(
    text: str, path_name: str, output: str | CompileResult, root: Path, target: str, *,
    budget_seconds: float, max_tactics: int, pool: Any, spans: dict[str, tuple[int, int]] | None,
    step_timeout: float, verbose: bool,
) -> str:
    if not petanque_available():
        return _quiet("petanque is not on PATH", verbose)
    located = locate_failure(text, output, spans=spans, target=target or None)
    if located is None:
        return _quiet("the compile error is not inside a proof body", verbose)
    tactics = tactic_sentences(text[located.body_start : located.body_end])
    if not tactics:
        return _quiet(f"the failing proof `{located.name}` has an empty body", verbose)
    if len(tactics) > max_tactics:
        return _quiet(f"`{located.name}` has {len(tactics)} tactics, above the replay cap of {max_tactics}", verbose)
    twin = twin_path(root, path_name)
    atomic_write_text(twin, text)
    try:
        return _replay(twin, located, tactics, pool=pool, budget_seconds=budget_seconds,
                       step_timeout=step_timeout, verbose=verbose,
                       incomplete=_INCOMPLETE in _as_result(output).output)
    finally:
        for leftover in (twin, twin.with_name(f"{twin.stem}__pcpfast.v")):
            with contextlib.suppress(OSError):
                leftover.unlink()


def twin_path(root: Path, path_name: str) -> Path:
    """``<stem>__pcpexplain.v`` beside the assembled file; pid-suffixed if one is in use."""
    stem = Path(path_name).stem
    twin = Path(root) / f"{stem}{TWIN_INFIX}.v"
    if twin.exists():
        twin = Path(root) / f"{stem}{TWIN_INFIX}{os.getpid()}.v"
    return twin


def open_session(pool: Any, file: Path, thm: str, *, step_timeout: float = 30.0, stub_prefix: bool = False) -> Any:
    """A ``ProofSession`` on ``file``/``thm`` from ``pool`` (the pool owns the process).

    ``stub_prefix`` opens the statements-only twin beside ``file`` -- never used on a
    corpus file, only on scratch copies, because it writes next to the source.
    """
    return pool.open(file, thm, step_timeout=step_timeout, stub_prefix=stub_prefix)


def _replay(
    twin: Path, located: Located, tactics: list[str], *, pool: Any, budget_seconds: float,
    step_timeout: float, verbose: bool, incomplete: bool,
) -> str:
    from pcp.state.ledger.diff import attach
    from pcp.state.trace import Tracer

    own_pool = pool is None
    if own_pool:
        from pcp.state.pool import SessionPool

        # The wall budget is the worker's clock: `petanque/start` on the twin is bounded
        # by it too (v1 left the 600 s default, so a wedged start ate ten minutes).
        pool = SessionPool(twin.parent, size=1, start_timeout=max(60.0, budget_seconds))
    ran = 0
    try:
        session = open_session(pool, twin, located.name, step_timeout=step_timeout, stub_prefix=True)
        tracer = attach(Tracer(session))
        deadline = time.monotonic() + budget_seconds
        for tactic in tactics:
            step = tracer.step(tactic)
            ran += 1
            if not step.ok or time.monotonic() > deadline:
                break
        trace = tracer.trace
    except PcpError as exc:
        return _quiet(f"the replay could not run: {exc}", verbose)
    finally:
        if own_pool:
            pool.close()

    if trace.failed_at is None:
        if ran < len(tactics):
            return (
                f"diagnosis: replayed the first {ran} of {len(tactics)} tactics in `{located.name}` within the "
                f"budget without reaching the failure, so it is further down than tactic {ran}. Nothing more "
                f"can be said without spending more of your clock than the answer is worth."
            )
        last = trace.steps[-1] if trace.steps else None
        return _no_tactic_failed(located, tactics, bool(trace.finished), incomplete,
                                 no_goals_shown=last is not None and not last.goals)
    step = trace.steps[-1]
    goal = step.goals[0] if step.goals else None
    report = diagnose(step.tactic, step.error or "", goal)
    head = f"diagnosis: replayed `{located.name}`; tactic {trace.failed_at} of {len(tactics)} is where it stops."
    return "\n".join([head, f"  {one_line(step.tactic, 300)}", "", indent(report)])


def _no_tactic_failed(
    located: Located, tactics: list[str], finished: bool, incomplete: bool, *, no_goals_shown: bool = False
) -> str:
    """The replay ran clean but coqc did not.  That is itself a diagnosis."""
    if finished and not incomplete:
        return (
            f"diagnosis: every tactic in `{located.name}` succeeded and the goal closed, so the rejection is "
            f"not in the script -- it is at `Qed` (universe or guard checking, or an unresolved evar or "
            f"typeclass that only the kernel sees)."
        )
    if no_goals_shown and not finished:
        # petanque shows no goal yet reports the proof unfinished: a shelved goal (an
        # evar left by `iExists _`, `eexists`, an `iApply` that could not infer an
        # argument) -- not a bullet problem, and `Unshelve.` makes it visible.
        return (
            f"diagnosis: all {len(tactics)} tactics in `{located.name}` ran without error and no goal is "
            f"displayed, but the proof is not complete: a shelved goal remains (an existential or an argument "
            f"left as `_` that nothing instantiated). `Unshelve.` at the end shows it; instantiate it "
            f"explicitly (`iExists v`, `iApply (lem $! v)`) or prove it after `Unshelve.`"
        )
    return (
        f"diagnosis: all {len(tactics)} tactics in `{located.name}` ran without error but the proof is not "
        f"closed, so goals remain. A bullet or brace is swallowing them; check that every subgoal opened is "
        f"discharged."
    )
