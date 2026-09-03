"""The persistence and affinity oracles (PLAN.md 4.3).

For each spatial hypothesis, ask Rocq whether it is ``Persistent`` (and whether it is
``Affine``) at this state.  If it is persistent the agent never has to reason about
consuming it, which removes an entire failure category -- #5, persistent vs spatial
confusion -- for the price of one speculative typeclass query.

The queries are asked in IPM's own language rather than by re-parsing printed props
back into terms:

* ``iDestruct "H" as "#H"`` succeeds exactly when ``H`` is ``Persistent``;
* ``iClear "H"`` succeeds exactly when ``H`` can be dropped, i.e. is ``Affine``.

Both run speculatively -- the session does not move -- and both are asked by *name*,
so nothing depends on the printed form being re-parsable.  A query that errors for
any other reason leaves the field ``None``: unknown, never guessed.
"""

from __future__ import annotations

from dataclasses import dataclass

from pcp.core.ipm.model import IrisGoal
from pcp.core.session import ProofSession


@dataclass
class OracleResult:
    hyp: str
    persistent: bool | None
    affine: bool | None
    error: str | None = None


def query_hyp(session: ProofSession, hyp: str, *, state=None, affine: bool = True) -> OracleResult:
    """Ask about one hypothesis.  Never commits, never raises."""
    persistent: bool | None = None
    is_affine: bool | None = None
    error: str | None = None

    probe = session.run(f'iDestruct "{hyp}" as "#{hyp}".', from_state=state, commit=False)
    if probe.ok:
        persistent = True
    elif _is_typecheck_failure(probe.error):
        persistent = False
    else:
        error = probe.error

    if affine:
        clear = session.run(f'iClear "{hyp}".', from_state=state, commit=False)
        if clear.ok:
            is_affine = True
        elif _is_typecheck_failure(clear.error):
            is_affine = False
        else:
            error = error or clear.error
    return OracleResult(hyp=hyp, persistent=persistent, affine=is_affine, error=error)


def annotate(session: ProofSession, goal: IrisGoal, *, state=None, affine: bool = False) -> IrisGoal:
    """Fill in ``persistent``/``affine`` on a goal's spatial hypotheses, in place.

    Intuitionistic hypotheses are persistent by construction and are not probed --
    the oracle costs one Rocq round trip per hypothesis, so it is spent only where
    the answer is not already known.
    """
    for h in goal.intuitionistic:
        h.persistent = True
    for h in goal.spatial:
        if h.persistent is not None:
            continue
        result = query_hyp(session, h.id, state=state, affine=affine)
        h.persistent = result.persistent
        if result.affine is not None:
            h.affine = result.affine
    return goal


#: Substrings that mean "Rocq understood the question and the answer is no", as
#: opposed to "the probe itself was malformed".
_TYPECHECK_MARKERS = (
    "not persistent",
    "cannot be turned into",
    "Cannot find an instance",
    "unable to satisfy",
    "No applicable tactic",
    "not affine",
    "cannot be cleared",
    "Tactic failure",
    "cannot eliminate",
)


def _is_typecheck_failure(error: str | None) -> bool:
    if not error:
        return False
    lowered = error.lower()
    return any(marker.lower() in lowered for marker in _TYPECHECK_MARKERS)
