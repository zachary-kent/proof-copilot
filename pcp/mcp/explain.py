"""Post-hoc diagnosis of a failed compile, for `pcp check` (PLAN.md 7).

`pcp/mcp/diagnose.py` answers the two failure families that eat a worker's turns --
pattern mismatches and unification failures -- but only from a live `IrisGoal`.
Given an error string alone it returns the error string, so a diagnostic that rides
on `coqc` output can add nothing:

    iDestruct "H" as "[H1 [H2 H3]]"  ->  iOrDestruct: cannot destruct
    iModIntro                        ->  iModIntro: the goal is not a modality.

So this module reconstructs the state instead of guessing at it: it finds the proof
the compiler failed inside, replays that proof through petanque a tactic at a time,
and hands `diagnose` the goal as it stood *before* the tactic that failed.

Why here and not in an MCP tool.  Every worker runs the compiler; the last ablation
measured five of seven never touching a granted tool.  A diagnosis attached to the
command they already run costs them no turn and no decision, and it works for a
runner that speaks no MCP at all.  It does not replace `proof_step`: this is
post-hoc, one shot, on a failure that already happened, where the tools are
speculative and interactive.

This is pcp-state.  Nothing in `pcp/orch` may import it -- the daily loop must still
run on a box whose only Rocq binary is `coqc` (`tests/test_layering.py`), so the CLI
calls in lazily and falls back to silence when petanque is absent.
"""

from __future__ import annotations

import contextlib
import re
from pathlib import Path

from pcp.core.vernac import ProofBlock, parse_blocks

#: coqc's location line.  `Error:` may follow on the same line or the next.
_LOCATION = re.compile(
    r'^File\s+"[^"]*",\s+line[s]?\s+(\d+)(?:-(\d+))?,\s+characters\s+(\d+)-(\d+)', re.M
)

#: The replay opens a twin of the assembled file rather than the assembled file
#: itself, so a concurrent gate run never sees a half-written source.  The `__pcp`
#: infix is the machine-scratch convention `_stubbed_copy` already uses: `pcp check`
#: skips those when it goes looking for the worker's `.v`, so a twin left behind by
#: a killed process can never be mistaken for the proof under test.
TWIN_STEM = "Pcp__pcpexplain"

#: Past this many tactics the replay costs more than the compile it is explaining.
MAX_TACTICS = 400

#: And a wall budget on top of it, because tactic count is a poor proxy for time:
#: one `iInv` on the cached rungs costs what fifty `iIntros` do.  A worker's node
#: clock is the scarce resource here -- a diagnosis that eats it has done harm, so
#: the replay reports how far it got rather than running to the end.
BUDGET_SECONDS = 90.0


def available() -> bool:
    """Whether a replay could run at all (no side effects, no process spawned)."""
    from pcp.core.session import toolchain_available

    return toolchain_available()


def explain(
    assembled: str,
    *,
    workdir: Path,
    compile_output: str = "",
    prefer: str | None = None,
    stub_prefix: bool = True,
    step_timeout: float = 30.0,
    budget_seconds: float = BUDGET_SECONDS,
) -> str:
    """Diagnose the failure in ``compile_output`` against the source ``assembled``.

    Returns "" whenever there is nothing honest to say -- no petanque, no error
    location, an error outside any proof body, or a replay that does not reproduce
    the failure.  Never raises: a diagnosis that breaks the checker is worse than no
    diagnosis, and this runs on the worker's critical path.
    """
    try:
        return _explain(
            assembled,
            workdir=Path(workdir),
            compile_output=compile_output,
            prefer=prefer,
            stub_prefix=stub_prefix,
            step_timeout=step_timeout,
            budget_seconds=budget_seconds,
        )
    except Exception:  # noqa: BLE001 -- best effort by construction
        return ""


def _explain(
    assembled: str,
    *,
    workdir: Path,
    compile_output: str,
    prefer: str | None,
    stub_prefix: bool,
    step_timeout: float,
    budget_seconds: float,
) -> str:
    if not available():
        return ""
    block = locate_failure(assembled, compile_output, prefer=prefer)
    if block is None:
        return ""
    tactics = block.tactics()
    if not tactics or len(tactics) > MAX_TACTICS:
        return ""

    twin = workdir / f"{TWIN_STEM}.v"
    twin.write_text(assembled, encoding="utf-8")
    try:
        return _replay(twin, block, tactics, stub_prefix=stub_prefix,
                       step_timeout=step_timeout, budget_seconds=budget_seconds)
    finally:
        for leftover in (twin, twin.with_name(f"{TWIN_STEM}__pcpfast.v")):
            with contextlib.suppress(OSError):
                leftover.unlink()


def _replay(
    twin: Path, block: ProofBlock, tactics: list[str], *, stub_prefix: bool,
    step_timeout: float, budget_seconds: float
) -> str:
    import time

    from pcp.core.session import SessionPool, ProofSession
    from pcp.core.trace import Tracer
    from pcp.mcp.diagnose import diagnose

    pool = SessionPool(twin.parent, size=1, step_timeout=step_timeout)
    ran = 0
    try:
        session = ProofSession(pool, twin, block.name, step_timeout=step_timeout, stub_prefix=stub_prefix)
        tracer = Tracer(session)
        deadline = time.monotonic() + budget_seconds
        for tactic in tactics:
            step = tracer.step(tactic)
            ran += 1
            if not step.ok or time.monotonic() > deadline:
                break
        trace = tracer.trace
    finally:
        pool.close()

    if trace.failed_at is None:
        if ran < len(tactics):
            return (
                f"diagnosis: replayed the first {ran} of {len(tactics)} tactics in "
                f"`{block.name}` within the budget without reaching the failure, so it is "
                f"further down than tactic {ran}. Nothing more can be said without spending "
                f"more of your clock than the answer is worth."
            )
        return _no_tactic_failed(block, tactics, trace.finished)

    step = trace.steps[-1]
    goal = step.goals[0] if step.goals else None
    report = diagnose(step.tactic, step.error or "", goal)
    head = (
        f"diagnosis: replayed `{block.name}`; tactic {trace.failed_at} of {len(tactics)} "
        f"is where it stops."
    )
    return "\n".join([head, f"  {_one_line(step.tactic)}", "", _indent(report)])


def _no_tactic_failed(block: ProofBlock, tactics: list[str], finished: bool) -> str:
    """The replay ran clean but coqc did not.  That is itself a diagnosis."""
    if finished:
        return (
            f"diagnosis: every tactic in `{block.name}` succeeded and the goal closed, so the "
            f"rejection is not in the script -- it is at `Qed` (universe or guard checking, or "
            f"an unresolved evar or typeclass that only the kernel sees)."
        )
    return (
        f"diagnosis: all {len(tactics)} tactics in `{block.name}` ran without error but the proof "
        f"is not closed, so goals remain. A bullet or brace is swallowing them; check that every "
        f"subgoal opened is discharged."
    )


# ------------------------------------------------------------------- locating it

def locate_failure(source: str, compile_output: str, *, prefer: str | None = None) -> ProofBlock | None:
    """The proof block coqc failed inside.

    Located from the error's *line*, not from the node under test: in `--full` mode
    or on a design check the failure is often in some other proof, and replaying the
    one we were told about would diagnose the wrong thing.
    """
    blocks = [b for b in parse_blocks(source) if b.has_proof and b.sentences]
    line = _error_line(compile_output)
    if line is not None:
        offset = _offset_of_line(source, line)
        if offset is not None:
            for block in blocks:
                if block.body_start is not None and block.body_start <= offset <= (block.body_end or 0):
                    return block
            return None  # the error is real but outside every proof body
    if prefer is not None:
        return next((b for b in blocks if b.name == prefer), None)
    return None


def _error_line(compile_output: str) -> int | None:
    """The line of the *first* error location coqc reported."""
    match = _LOCATION.search(compile_output or "")
    if match is None:
        return None
    return int(match.group(1))


def _offset_of_line(source: str, line: int) -> int | None:
    if line < 1:
        return None
    offset = 0
    for _ in range(line - 1):
        nl = source.find("\n", offset)
        if nl < 0:
            return None
        offset = nl + 1
    return offset


def _one_line(text: str) -> str:
    collapsed = " ".join((text or "").split())
    return collapsed if len(collapsed) <= 300 else collapsed[:297] + "..."


def _indent(text: str) -> str:
    return "\n".join(f"  {line}" if line else "" for line in (text or "").splitlines())
