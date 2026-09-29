"""Per-sentence time budgets: when a timeout is the machine's, not the proof's (session 4, 28/29/33).

``coqc`` has no per-sentence limit; petanque runs every sentence under ``Timeout n``.  So
a sentence ``coqc`` accepts can time out here -- on a machine whose load is far above its
core count, or on a slow ``set_solver`` in a 200-hypothesis context -- and the answer
used to read like a proof failure, sometimes with a confident diagnosis of a missing
resource.  This module says how loaded the machine is, whether a sentence is known to
pass (it passed at this place in the last trace of the lemma, or it is unchanged since
the last commit), and so whether one retry at a larger budget is worth it.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import Any

from pcp.state.petanque import DEFAULT_STEP_TIMEOUT
from pcp.util.proc import run

#: 1-minute load per core above which the machine counts as busy.
BUSY_LOAD_PER_CPU = 0.75
#: A retried sentence gets this many times its first budget ...
RETRY_FACTOR = 2.0
#: ... and never more than this (s), so one retry cannot run away with a client's call.
MAX_RETRY_S = 120.0
#: The largest per-sentence budget a caller may ask for (s).
MAX_TIMEOUT_S = 600.0


def cpus() -> int:
    try:
        return len(os.sched_getaffinity(0))
    except (AttributeError, OSError):
        return os.cpu_count() or 1


def load() -> dict[str, Any]:
    """``{"load_1m", "cpus", "busy"}``; ``load_1m`` is ``None`` where the OS does not say."""
    n = cpus()
    try:
        one = round(os.getloadavg()[0], 1)
    except (AttributeError, OSError):
        return {"load_1m": None, "cpus": n, "busy": False}
    return {"load_1m": one, "cpus": n, "busy": one >= BUSY_LOAD_PER_CPU * n}


def step_budget(timeout: float | None) -> float:
    """The per-sentence budget for a caller's ``timeout`` (``None``/``0``: the default)."""
    if not timeout or timeout <= 0:
        return DEFAULT_STEP_TIMEOUT
    return min(float(timeout), MAX_TIMEOUT_S)


def retry_budget(first_s: float, *, busy: bool, known_good: bool) -> float | None:
    """The one retry a timed-out sentence gets: only on a busy machine or a sentence known to pass."""
    if not (busy or known_good) or first_s >= MAX_RETRY_S:
        return None
    return min(first_s * RETRY_FACTOR, MAX_RETRY_S)


def committed_text(path: Path, *, timeout: float = 5.0) -> str | None:
    """``path`` as of ``HEAD`` in its git repository, or ``None`` (not tracked, no git)."""
    out = run(["git", "-C", str(path.parent), "show", f"HEAD:./{path.name}"], timeout=timeout)
    return out.stdout if out.returncode == 0 and not out.timed_out else None


def timeout_info(*, budget_s: float, elapsed_ms: int, retried_from_s: float | None, known_good: bool) -> dict[str, Any]:
    """What a timed-out result carries so a budget problem is not taken for a proof problem."""
    info: dict[str, Any] = {"budget_s": budget_s, "elapsed_s": round(elapsed_ms / 1000, 1), **load()}
    if retried_from_s is not None:
        info["first_budget_s"] = retried_from_s
    if known_good:
        info["known_good"] = True
    return info
