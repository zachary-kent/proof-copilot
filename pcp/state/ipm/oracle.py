"""The persistence and affinity oracle (PLAN.md 4.3).

For each spatial hypothesis, ask Rocq -- not the printed form -- whether it is
``Persistent`` (and ``Affine``) *at the given state*, speculatively:

* ``iDestruct "H" as "#H"`` succeeds exactly when ``IntoPersistent`` resolves (and the
  affinity side condition holds);
* ``iClear "H"`` succeeds exactly when ``H`` can be dropped.

Both are asked by *name*, so nothing depends on the printed prop being re-parsable.
The answers are decoded from Iris's exact failure prefixes (``ltac_tactics.v``):
``iIntuitionistic: P not persistent`` is a definite no; ``... not affine and the goal
not absorbing`` means the persistence check *passed* and the affinity one failed.
Anything else leaves the field ``None`` -- unknown, never guessed (PLAN.md 4.4).

``state`` is required: v1 defaulted to "wherever the session is now", and ``pcp trace
--oracle`` then probed every historical step against the final state.
"""

from __future__ import annotations

from dataclasses import dataclass

from pcp.state.ipm.model import IrisGoal
from pcp.state.petanque import StateHandle
from pcp.state.session import ProofSession

_NOT_PERSISTENT = "not persistent"
_NOT_AFFINE = "not affine and the goal not absorbing"


@dataclass
class OracleResult:
    hyp: str
    persistent: bool | None
    affine: bool | None
    error: str | None = None


def query_hyp(session: ProofSession, hyp: str, *, state: StateHandle, affine: bool = True) -> OracleResult:
    """Ask about one hypothesis at ``state``.  Never commits; never raises for a Rocq answer."""
    persistent: bool | None = None
    is_affine: bool | None = None
    error: str | None = None

    probe = session.run(f'iDestruct "{hyp}" as "#{hyp}".', from_state=state, commit=False)
    if probe.ok:
        persistent = True
    else:
        err = probe.error or ""
        if "iIntuitionistic:" in err and _NOT_AFFINE in err:
            persistent, is_affine = True, False
        elif "iIntuitionistic:" in err and err.rstrip(". \n").endswith(_NOT_PERSISTENT):
            persistent = False
        else:
            error = err

    if affine and is_affine is None:
        clear = session.run(f'iClear "{hyp}".', from_state=state, commit=False)
        if clear.ok:
            is_affine = True
        else:
            err = clear.error or ""
            if "iClear:" in err and _NOT_AFFINE in err:
                is_affine = False
            else:
                error = error or err
    return OracleResult(hyp=hyp, persistent=persistent, affine=is_affine, error=error)


def annotate(session: ProofSession, goal: IrisGoal, *, state: StateHandle, affine: bool = False) -> IrisGoal:
    """Fill ``persistent``/``affine`` on the spatial hypotheses of ``goal`` (in place; returned).

    Intuitionistic hypotheses are persistent by construction and are not probed; a
    spatial hypothesis already answered is not probed again.  Anonymous hypotheses
    cannot be named in IPM, so they stay unknown.
    """
    for h in goal.intuitionistic:
        h.persistent = True
    for h in goal.spatial:
        if h.persistent is not None or h.anonymous:
            continue
        result = query_hyp(session, h.id, state=state, affine=affine)
        h.persistent = result.persistent
        if result.affine is not None:
            h.affine = result.affine
    return goal
