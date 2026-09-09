"""The obligation-graph vocabulary: nodes, budgets, statuses and the transition lattice.

PLAN.md 8.1 gives a node two ledgers with separate lifecycles::

    statement:  proposed → audited → frozen@e ──amend──▶ frozen@e+1
                                        └────────────▶ refuted   (terminal)
    proof:      open → claimed → qed → gated → integrated        (per epoch)
                          └──▶ contested(evidence) | stuck(evidence, requests)

The legacy store accepted any status string and any move (``attic → integrated``
included), so the lattice lived in callers' heads and drifted.  Here it is a table,
:func:`transition` checks every move against it, and :class:`pcp.orch.graph.Graph`
refuses what it rejects -- ARCHITECTURE.md §3 rule 7.
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass, field
from typing import Any

from pcp.errors import PcpError, UsageError
from pcp.util.io import slug

STATEMENT_STATUSES: tuple[str, ...] = ("proposed", "audited", "frozen", "refuted")
PROOF_STATUSES: tuple[str, ...] = (
    "open", "claimed", "qed", "gated", "integrated", "contested", "stuck", "attic",
)
RANKS: tuple[str, ...] = ("root", "interface", "local")
OWNERS: tuple[str, ...] = ("human", "decomposer")
#: Roles that may attach proof text.  Exactly one, on purpose (PLAN.md 8.6).
PROOF_BEARING_ROLES: tuple[str, ...] = ("prover",)
#: What an attempt row may end as (``claimed`` while in flight).
ATTEMPT_STATUSES: tuple[str, ...] = ("claimed", "qed", "stuck", "contested", "error")

#: A proof is *proved* in these states: its body is load-bearing for dependents.
PROVED_STATUSES: frozenset[str] = frozenset({"gated", "integrated"})

#: The lattice: ``current -> {allowed next}`` for moves that need no further
#: qualification.  Qualified moves (human only, unproved only) are handled in
#: :func:`transition` and documented there.
_MOVES: dict[str, frozenset[str]] = {
    "open": frozenset({"claimed"}),
    # ``claimed -> gated`` is the one shortcut: a worker's ``qed`` that passed the
    # gate in the same step.  ``qed`` is a transient the scheduler may skip.
    "claimed": frozenset({"qed", "gated", "stuck", "contested", "open"}),
    "qed": frozenset({"gated", "stuck", "open"}),
    "gated": frozenset({"integrated", "open"}),      # open = revalidation (epoch+1)
    "integrated": frozenset({"open"}),               # revalidation only
    "stuck": frozenset({"open"}),
    "contested": frozenset(),                        # open: human only (see below)
    "attic": frozenset({"open"}),                    # revive
}

#: Moves into ``open`` from a proved state invalidate the proof: the graph bumps the
#: epoch and clears the body (contract §5.1 "epoch+1 when a proof was invalidated").
INVALIDATING_MOVES: frozenset[tuple[str, str]] = frozenset({("gated", "open"), ("integrated", "open")})


class InvalidTransition(PcpError):
    """A proof-status move the PLAN.md 8.1 lattice forbids."""


def transition(current: str, new: str, *, proved: bool = False, human: bool = False) -> None:
    """Raise :class:`InvalidTransition` unless ``current -> new`` is a lattice move.

    ``proved`` says whether the node carries a load-bearing body (anything may go to
    the attic *only* while unproved: the root may still cite a proved orphan).
    ``human`` marks a human-authored write: ``contested -> open`` is adjudication and
    ``stuck -> contested`` is a verdict; no model may perform either.  A no-op
    (``current == new``) is never a move.
    """
    if new not in PROOF_STATUSES:
        raise InvalidTransition(f"unknown proof status {new!r}; one of {', '.join(PROOF_STATUSES)}")
    if current not in PROOF_STATUSES:
        raise InvalidTransition(f"node is in unknown proof status {current!r}")
    if current == new:
        return
    if new == "attic":
        if proved:
            raise InvalidTransition(
                f"{current} -> attic: a proved node cannot be retired to the attic; its body may be cited"
            )
        return
    if current == "contested" and new == "open":
        if not human:
            raise InvalidTransition("contested -> open is adjudication: only a human may reopen a contested node")
        return
    if current == "stuck" and new == "contested":
        # The approver, as the human's delegate, reviewed a stuck node and found the
        # statement wrong: the node now carries that claim.  No model may make it.
        if not human:
            raise InvalidTransition("stuck -> contested is a verdict: only a human may contest a stuck node")
        return
    if new in _MOVES[current]:
        return
    raise InvalidTransition(f"{current} -> {new} is not a move the proof lattice allows (PLAN.md 8.1)")


def node_id(name: str) -> str:
    """The graph id of a node: a collision-free slug of its Rocq name."""
    return slug(name)


@dataclass
class Budget:
    """A budget is a **vector, denominated per provider** (PLAN.md 11, Economics).

    A flat-rate subscription's capacity is requests per window and its marginal token
    cost is ~0; a metered API's is dollars.  Mixing them into one scalar is how you
    end up throttling the free tier to protect a budget it does not spend.
    """

    requests: int = 0
    tokens: int = 0
    dollars: float = 0.0
    seconds: float = 0.0

    def split(self, n: int, *, share: float = 1.0) -> Budget:
        """Divide the metered dimensions among ``n`` siblings -- but not the clock.

        Children are dispatched concurrently, so a second spent by one is not a
        second denied to another; dividing the clock gave every child the same
        deadline whether it was a one-liner or the hardest obligation in the plan
        (measured on seqlock_wf: 2738 s of siblings' allowance never spent, on the two
        obligations that were killed).  ``share`` still scales the clock, because "use
        a fraction of the parent's time" is a real instruction; ``/n`` is not.
        """
        n = max(1, n)
        return Budget(
            requests=int(self.requests * share) // n,
            tokens=int(self.tokens * share) // n,
            dollars=self.dollars * share / n,
            seconds=self.seconds * share,
        )

    @property
    def unset(self) -> bool:
        """No budget configured at all -- which is not the same as spent."""
        return self.requests == 0 and self.tokens == 0 and self.dollars == 0.0 and self.seconds == 0.0

    def exhausted(self) -> bool:
        """Nothing left on any dimension.

        A clock-only budget (``requests = tokens = dollars = 0``, ``seconds > 0``) is
        *live*: the legacy check ignored the clock and reported every such budget as
        exhausted, which silently refused every decomposition under the default
        ``Budget(requests=200, seconds=7200)`` split more than 200 ways.
        """
        if self.unset:
            return False
        return self.requests <= 0 and self.tokens <= 0 and self.dollars <= 0.0 and self.seconds <= 0.0

    def to_json(self) -> dict[str, Any]:
        return asdict(self)

    def dumps(self) -> str:
        return json.dumps(self.to_json())

    @classmethod
    def from_json(cls, data: str | dict[str, Any] | None) -> Budget:
        """Read a budget; unknown keys are ignored rather than resetting the vector."""
        if not data:
            return cls()
        if isinstance(data, str):
            try:
                data = json.loads(data)
            except json.JSONDecodeError as exc:
                raise UsageError(f"malformed budget JSON: {exc}") from None
        if not isinstance(data, dict):
            raise UsageError("malformed budget: expected a JSON object")
        return cls(
            requests=int(data.get("requests", 0) or 0),
            tokens=int(data.get("tokens", 0) or 0),
            dollars=float(data.get("dollars", 0.0) or 0.0),
            seconds=float(data.get("seconds", 0.0) or 0.0),
        )


@dataclass
class Node:
    """One row of ``nodes``: a statement plus the state of its proof."""

    id: str
    name: str
    statement: str
    statement_hash: str = ""
    rank: str = "local"
    parent: str | None = None
    depth: int = 0
    epoch: int = 0
    statement_status: str = "proposed"
    proof_status: str = "open"
    closure_hash: str = ""
    preamble_hash: str = ""
    mockable: bool = True
    #: A ``Defined`` obligation: rendered transparent so dependents may compute with it.
    transparent: bool = False
    is_glue: bool = False
    owner: str = "human"
    intent: str = ""
    budget: Budget = field(default_factory=Budget)
    cost: dict[str, Any] = field(default_factory=dict)
    attempts: int = 0
    file: str = ""
    body: str | None = None
    evidence: str = ""
    ordering: int = 0
    created_at: float = 0.0
    updated_at: float = 0.0

    @property
    def frozen(self) -> bool:
        return self.statement_status == "frozen"

    @property
    def dispatchable(self) -> bool:
        """The scheduling invariant in one line (PLAN.md 8.1): frozen and open."""
        return self.frozen and self.proof_status == "open"

    @property
    def done(self) -> bool:
        return self.proof_status in PROVED_STATUSES

    @property
    def proved(self) -> bool:
        return self.body is not None and self.proof_status in PROVED_STATUSES

    def to_json(self) -> dict[str, Any]:
        data = asdict(self)
        data["budget"] = self.budget.to_json()
        return data

    @classmethod
    def from_json(cls, data: dict[str, Any]) -> Node:
        kwargs = dict(data)
        kwargs["budget"] = Budget.from_json(kwargs.get("budget"))
        kwargs["cost"] = dict(kwargs.get("cost") or {})
        kwargs["mockable"] = bool(kwargs.get("mockable", True))
        kwargs["transparent"] = bool(kwargs.get("transparent", False))
        kwargs["is_glue"] = bool(kwargs.get("is_glue", False))
        known = {f for f in cls.__dataclass_fields__}
        return cls(**{k: v for k, v in kwargs.items() if k in known})

#: Graph meta ``contest_adjudicated:<node id>`` -> the epoch the approver's verdict was
#: about.  Read by the scheduler (a reviewed epoch is not reviewed twice) and written
#: by the amendment path.
ADJUDICATED_META = "contest_adjudicated"
