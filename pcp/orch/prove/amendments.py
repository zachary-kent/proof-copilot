"""Incremental invariant amendments: the one-conjunct route back to the design.

Provers discover mid-proof that the invariant lacks a fact or a modality guard --
the registry entry stored ``Q`` where the close site needs ``▷ Q``.  Without this
module the only route back is ``contested``/``stuck`` -> a **full** design revision at design effort (30-45 minutes, a replay of everything,
a re-dispatch of everything).  That is the right shape for "the invariant is wrong"
and the wrong shape for "add one conjunct".  The human's workflow is incremental --
add the fact, re-check what broke, continue -- and this is that workflow, with the
lattice of PLAN.md 8.5 deciding who gets to say yes:

* ``add`` is a **strengthening** of the definition: ``new ⊢ old`` by construction
  (``(old) ∗ (add)``, the conjunct kept inside its own parentheses), so its *form* is
  machine-checked -- it compiles against the contract or it does not.  Its *direction*
  is not: a definition the goal *assumes* gets weaker as a theorem when its
  hypothesis gets stronger, and ``add = False`` on ``is_lock`` proves every
  specification that assumes ``is_lock`` (checked in Rocq: a false
  ``amend_inv n -∗ ⌜n = 42⌝`` integrates with a clean ``Print Assumptions``).  So an
  ``add`` is put to the **approver** whenever one is configured -- accept is the
  expected answer and the round is short -- and auto-accepted, marked *unreviewed*
  in the report, only in a run with no approver at all, where the human reading the
  report is the auditor (PLAN.md 8.5: ``weaken`` is an AUDIT rung).
* ``replace`` is anything else and always goes to the approver (the decomposer's
  runner at a lower effort, agent B's ``Decomposer.adjudicate_amendment``): accept,
  adjust the sentence once, or reject with a reason the prover reads next time.
* Either way the change is applied through :func:`pcp.orch.prove.design.apply_design`
  -- contract check, static scan of the fragment, compile, every frozen statement
  typechecked as a stub -- so an amendment is a design edit in every respect except
  who asked for it.

Salvage is **replay-first** (PLAN.md 8.5): every proved body is replayed against the
amended development and kept where it still gates; the two taint channels then run
-- proofs that no longer gate reopen, and statements that *mention* the amended
definition (agent B's ``statement_invalidated``, one level of unfolding) reopen when
they were stuck or contested against the old meaning.  The requester itself is
reopened at its own epoch while it has attempts left, so its partial proof reaches
its next packet; every reopened node's evidence starts with
:data:`~pcp.orch.protocol.AMENDED_MARKER` and says exactly what changed.

Amendments never count against ``--design-rounds``; ``--amendments N`` bounds how
many are *applied* per run, and the loop stops the moment a dispatch asks for
nothing new.  A request that is *refused* still buys its requester the ordinary
evidence-informed retry, with the refusal as evidence: the scheduler withheld that
retry on the prover's word that the design was short a fact, and the answer "no,
it is not" must reach the same prover in the same run rather than cost a design
round (or, in a plan run, be lost).  Contested nodes are adjudicated the same way (PLAN.md 8.9: "a node
escalated twice is a statement problem" -- but a prover that registered its atomic
update at the wrong program point is a strategy problem, and an approver can tell
the two apart in one short round where a design revision costs an hour).
"""

from __future__ import annotations

import json
import time
from collections.abc import Awaitable, Callable, Iterable
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any

from pcp.errors import PcpError
from pcp.orch.decomposer import (
    ChildStatement,
    DesignDefinition,
    PlanProposal,
    ProofEngineeringAttempt,
    Verdict,
    current_design,
    declared_name,
)
from pcp.orch.gate import Gate
from pcp.orch.graph import Graph
from pcp.orch.model import ADJUDICATED_META, PROVED_STATUSES, Node
from pcp.orch.protocol import ADJUDICATED_MARKER, AMENDED_MARKER, AmendmentRequest
from pcp.orch.prove.design import (
    ADOPTED_PROPOSAL_META,
    DesignError,
    adopted_proposal,
    apply_design,
    revalidate,
    scan_fragment,
)
from pcp.orch.prove.integrate import obligations
from pcp.orch.prove.resume import DESIGNED_FILE_META, last_evidence, reopen_incomplete
from pcp.orch.schedule import BLOCKED_PREFIX, RunReport, attempts_spent, repin_edges
from pcp.rocq.assemble import Development
from pcp.rocq.decls import parse_blocks
from pcp.rocq.lexer import (
    first_word,
    has_top_level_token,
    iter_comments,
    skip_comment,
    skip_string,
    split_sentences,
    strip_comments,
)
from pcp.util.text import one_line

if TYPE_CHECKING:
    from pcp.orch.prove import ProveConfig
    from pcp.orch.prove.design import DesignDriver

__all__ = [
    "AmendmentOutcome",
    "AmendmentRefused",
    "AmendmentRun",
    "amendment_detail",
    "amendment_loop",
    "apply_amendment",
    "has_approver",
    "strengthened_definition",
]

Dispatch = Callable[[Development, int], Awaitable[RunReport]]

#: Iris separating conjunction: a strengthening is ``(old) ∗ (add)``.
SEP = "∗"
#: The approver reads this much of the requester's evidence.
EVIDENCE_SHOWN = 4000
#: Meta key: ``contest_adjudicated:<node id>`` -> the epoch the verdict was about
#: (defined with the graph model; the scheduler reads it too).
#: Verdict-driven reopenings (a `strategy` hint, a restatement) per node, ever:
#: PLAN.md 8.9 -- a node escalated twice is a statement problem, not a third hint.
MAX_VERDICT_REOPENS = 2


class AmendmentRefused(PcpError):
    """A request that cannot be applied as asked; the reason goes back to the prover."""


# ------------------------------------------------------------------ text surgery


def _top_level_index(code: str, token: str) -> int:
    """Offset of the first ``token`` outside brackets, comments and strings, else -1
    (the position-returning twin of :func:`pcp.rocq.lexer.has_top_level_token`)."""
    depth = 0
    i, n = 0, len(code)
    while i < n:
        ch = code[i]
        if ch == "(" and code.startswith("(*", i):
            i = skip_comment(code, i)
            continue
        if ch == '"':
            i = skip_string(code, i)
            continue
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and code.startswith(token, i):
            return i
        i += 1
    return -1


def _wrapped(text: str) -> bool:
    """Whether ``text`` is one parenthesised group: ``(∃ n, own γ n)`` is, ``(a) ∗ (b)`` is not."""
    if not text.startswith("(") or not text.endswith(")"):
        return False
    depth = 0
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch == '"':
            i = skip_string(text, i)
            continue
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return i == n - 1
        i += 1
    return False


def _group(text: str) -> str:
    """Parenthesise unless it is already one group or one token: ``∃ n, own γ n`` must
    be wrapped before ``∗`` is appended, ``True`` or ``P`` need not be."""
    if _wrapped(text) or len(text.split()) == 1:
        return text
    return f"({text})"


def _unclosed_comment(text: str) -> bool:
    """A ``(*`` with no ``*)`` swallows everything after it -- the closing paren, the
    final ``.``, the rest of the file -- so the text that *looks* like one term is not."""
    return any(not comment.endswith("*)") for _start, _end, comment in iter_comments(text))


def strengthened_definition(block_text: str, add: str) -> str:
    """``Definition name binders : T := body.`` with ``body`` replaced by
    ``(body) ∗ (add)`` -- a strengthening by construction (PLAN.md 8.5: ``new ⊢ old``
    needs no shim when ``new`` is literally ``old ∗ more``).

    A body in ``%I`` scope keeps the scope outside the parentheses
    (``(body ∗ (add))%I``) so the conjunct is read in the same scope as the body.
    Refused when the sentence is not a ``Definition`` with a top-level ``:=``: a
    ``Lemma`` is an obligation and goes through the statement pipeline, a
    ``Fixpoint`` or ``Inductive`` has no conjunct to add to.

    The conjunct must be **one term**: ``(add)`` has to stay one parenthesised group.
    ``add = "True) ∨ (False"`` compiles to ``(body) ∗ (True) ∨ (False)`` -- ``∨``
    binds looser than ``∗``, so that is ``(body ∗ True) ∨ False``, not a
    strengthening -- and ``add = "True) -∗ (⌜n = 7⌝"`` to a definition that is
    *weaker* than the old one (checked with ``coqc``).  Every such
    escape is refused here, before anything is compiled.
    """
    code = strip_comments(block_text).strip()
    conjunct = add.strip()
    if not conjunct:
        raise AmendmentRefused("an `add` amendment names nothing to add")
    # The declaration parser owns attributes (`#[local]`) and modifiers (`Local`).
    blocks = parse_blocks(code)
    head = blocks[0].head if blocks else first_word(code)
    name = (blocks[0].name if blocks else None) or "?"
    if head != "Definition":
        raise AmendmentRefused(
            f"`{name}` is a {head or 'sentence'}, not a Definition: only a Definition body can be strengthened"
        )
    if _unclosed_comment(conjunct) or not _wrapped(f"({strip_comments(conjunct)})"):
        raise AmendmentRefused(
            f"the conjunct for `{name}` is not one term: `({' '.join(conjunct.split())})` does not stay one "
            "parenthesised group, so `(body) ∗ (add)` would not be a strengthening"
        )
    if not has_top_level_token(code, ":="):
        raise AmendmentRefused(f"`{name}` has no `:=` body to strengthen")
    if not code.endswith("."):
        raise AmendmentRefused(f"`{name}` is not a complete sentence (no final `.`)")
    at = _top_level_index(code, ":=")
    header = " ".join(code[: at + 2].split())  # a stripped comment leaves a gap; the header is one line
    body = code[at + 2 : -1].strip()
    if not body:
        raise AmendmentRefused(f"`{name}` has an empty body")
    if body.endswith("%I"):
        inner = body[:-2].rstrip()
        new_body = f"({_group(inner)} {SEP} ({conjunct}))%I"
    else:
        new_body = f"{_group(body)} {SEP} ({conjunct})"
    return f"{header} {new_body}."


def amendment_detail(req: AmendmentRequest, text: str = "") -> str:
    """What a reopened node is told, marker first (the packet turns it into the
    heading "The design changed since your last attempt")."""
    who = f"requested by `{req.requester or '?'}`" + (f" at {req.at}" if req.at else "") + (f": {req.why}" if req.why else "")
    if req.kind == "add":
        return f"{AMENDED_MARKER} `{req.definition}` now also carries `{' '.join(req.add.split())}` ({who})"
    shown = text.strip() or req.replace.strip()
    return f"{AMENDED_MARKER} `{req.definition}` was restated ({who}):\n{shown}"


# ------------------------------------------------------------------ the outcome


@dataclass
class AmendmentOutcome:
    """One request, decided.  One line in the report; the record keeps the rest."""

    request: AmendmentRequest
    applied: bool = False
    #: ``auto-accepted`` (a strengthening compiled and no approver is configured to
    #: review it) | ``accept`` | ``adjust`` (approver) | ``reject`` | ``refused`` (a
    #: check said no) | ``capped`` | ``no approver`` | ``no verdict``.
    verdict: str = ""
    problems: list[str] = field(default_factory=list)
    reopened: list[str] = field(default_factory=list)
    kept: list[str] = field(default_factory=list)
    round_no: int = 0
    elapsed_s: float = 0.0
    #: The definition sentence as applied, and the designed file it went into.
    text: str = ""
    file: str = ""

    def refuse(self, verdict: str, problem: str) -> AmendmentOutcome:
        self.applied = False
        self.verdict = verdict
        if problem:
            self.problems.append(problem)
        return self

    def render(self) -> str:
        req = self.request
        who = f"requested by {req.requester or '?'}"
        if self.applied:
            if req.kind == "add":
                what = req.describe() + (" (adjusted by the approver)" if self.verdict == "adjust" else "")
            else:
                what = f"{req.definition}: replaced ({self.verdict})"
            # The human reading this line is the only audit an unreviewed change gets.
            review = "; unreviewed: no approver is configured" if self.verdict == "auto-accepted" else ""
            return f"amended {what}  ({who}; reopened {', '.join(self.reopened) or 'nothing'}; kept {len(self.kept)}{review})"
        why = self.problems[0] if self.problems else (self.verdict or "not applied")
        return f"amendment refused {req.describe()}  ({who}): {one_line(why, 160)}"

    def to_json(self) -> dict[str, Any]:
        return {
            "request": self.request.to_json(),
            "applied": self.applied,
            "verdict": self.verdict,
            "problems": list(self.problems),
            "reopened": list(self.reopened),
            "kept": list(self.kept),
            "round": self.round_no,
            "elapsed_s": self.elapsed_s,
            "text": self.text,
            "file": self.file,
        }


# ------------------------------------------------------------------ applying one


def has_approver(cfg: Any) -> bool:
    """A ``replace`` (or a contest) can be adjudicated: the approver runner, else the
    decomposer's own runner stands in (``Decomposer.adjudicate_*`` use ``approver or runner``)."""
    return getattr(cfg, "approver_runner", None) is not None or getattr(cfg, "decomposer_runner", None) is not None


def _mutable(contract: Any, name: str) -> bool:
    """Fail closed: no contract means nothing may change."""
    if contract is None:
        return False
    may_amend = getattr(contract, "may_amend", None)
    if callable(may_amend):
        return bool(may_amend(name))
    if name in getattr(contract, "results", frozenset()):
        return False
    return name in getattr(contract, "mutable", frozenset())


def _sentence(dev: Development, name: str) -> str:
    block = dev.require_block(name)
    return dev.source[block.statement_start : block.statement_end]


def _definition(name: str, text: str, *, rationale: str) -> DesignDefinition:
    """The checks ``apply_design`` runs, before anything is written: statement-only
    (``DesignDefinition``), no escape hatch or axiom (``scan_fragment``), exactly one
    sentence declaring ``name`` -- a conjunct ``True. Definition evil := ...`` would
    otherwise be a design addition smuggled in by a prover."""
    definition = DesignDefinition(name, text, rationale=rationale)  # statement-only, or ProofEngineeringAttempt
    if _unclosed_comment(text):
        raise AmendmentRefused(f"the amended `{name}` has an unclosed comment")
    sentences = [s for s in split_sentences(strip_comments(text)) if s.code.strip()]
    if len(sentences) != 1:
        raise AmendmentRefused(f"the amended `{name}` is not a single sentence ({len(sentences)} sentences)")
    scan_fragment(text, name)
    declared = declared_name(text)
    if declared != name:
        raise AmendmentRefused(f"the replacement declares `{declared or '?'}`, not `{name}`")
    return definition


def _apply_definition(
    cfg: ProveConfig, graph: Graph, dev: Development, root: Node, definition: DesignDefinition,
    *, contract: Any, round_no: int, preamble: str,
) -> Development:
    """Through :func:`apply_design`, with every frozen obligation typechecked as a stub
    against the amended definition -- a ``replace`` that changes an arity breaks
    statements, and one bad frozen statement poisons every sibling's file."""
    children = tuple(
        ChildStatement(n.name, n.statement)
        for n in obligations(graph, dev)
        if n.mockable  # a non-mockable obligation cannot be stubbed into the check
    )
    proposal = PlanProposal(children=children, definitions=(definition,))
    return apply_design(
        cfg, graph, dev, root, proposal, contract=contract, round_no=round_no, workroot=cfg.workroot, preamble=preamble,
    )


def _restore_designed_file(graph: Graph, dev: Development, previous: str | None) -> None:
    """A rejected ``replace`` was compiled into a designed copy before the approver
    spoke; the graph must not point a resumed run at it."""
    graph.set_meta(DESIGNED_FILE_META, previous or str(dev.path))


def _tell_requester(graph: Graph, req: AmendmentRequest, problem: str) -> None:
    """The refusal reaches the prover's next packet rather than only the report."""
    node = graph.by_name(req.requester) if req.requester else None
    if node is None or node.proof_status in PROVED_STATUSES or node.proof_status == "attic":
        return
    note = f"your amendment request ({req.describe()}) was not applied: {problem}"
    current = node.evidence or ""
    # A node already told "the design changed" keeps that heading; the refusal is a
    # detail under it.  Otherwise the verdict comes before the old failure.
    parts = [current, note] if current.startswith((AMENDED_MARKER, ADJUDICATED_MARKER)) else [note, current]
    graph.update(node.id, evidence="\n\n".join(filter(None, parts)))


def _file_refusal(graph: Graph, root: Node, req: AmendmentRequest, outcome: AmendmentOutcome) -> AmendmentOutcome:
    """Every request that is not applied -- refused by a check, rejected by the approver,
    capped -- is filed the same way: the event, and the reason in the requester's evidence."""
    problem = outcome.problems[0] if outcome.problems else outcome.verdict
    graph.emit(
        "amendment.rejected", root.id, definition=req.definition.strip(), kind=req.kind, requester=req.requester,
        verdict=outcome.verdict, reason=problem[:400],
    )
    _tell_requester(graph, req, problem)
    return outcome


def _remember(graph: Graph, definition: DesignDefinition) -> None:
    """Later design revisions complete from the adopted proposal; the amended
    definition must be in it or the next revision silently reverts the conjunct."""
    merged = PlanProposal(definitions=(definition,)).merged_over(adopted_proposal(graph))
    graph.set_meta(ADOPTED_PROPOSAL_META, json.dumps(merged.to_json()))


async def apply_amendment(
    cfg: ProveConfig,
    graph: Graph,
    dev: Development,
    root: Node,
    req: AmendmentRequest,
    *,
    contract: Any,
    preamble: str = "",
    round_no: int,
    driver: DesignDriver | None = None,
    approved: bool = False,
) -> tuple[Development, AmendmentOutcome]:
    """Apply one request (module docstring).  Returns the development to prove
    against from now on -- the amended copy when applied, ``dev`` unchanged when not
    -- and the outcome.  ``approved`` marks a ``replace`` the approver already
    produced (a contest verdict's fix), so it is not adjudicated twice.

    Who decides: a request the approver already produced is applied as is; otherwise
    every request -- ``add`` included -- goes to the approver when one is configured
    (``has_approver``), a ``replace`` without one is refused, and an ``add`` without
    one is auto-accepted and reported as unreviewed (module docstring: a strengthened
    hypothesis is a weakened theorem, so the direction of an ``add`` is a judgement
    the compiler cannot make).
    """
    started = time.perf_counter()
    outcome = AmendmentOutcome(request=req, round_no=round_no)
    name = req.definition.strip()

    def done(result: AmendmentOutcome, *, applied_dev: Development = dev) -> tuple[Development, AmendmentOutcome]:
        result.elapsed_s = time.perf_counter() - started
        if not result.applied:
            _file_refusal(graph, root, req, result)
        return applied_dev, result

    if dev.block(name) is None:
        return done(outcome.refuse("refused", f"no definition named `{name}` in {dev.path.name}"))
    if not _mutable(contract, name):
        describe = getattr(contract, "describe", lambda: "nothing may change")
        return done(outcome.refuse("refused", f"`{name}` is not contract-mutable ({describe()})"))
    try:
        text = strengthened_definition(_sentence(dev, name), req.add) if req.kind == "add" else req.replace.strip()
        definition = _definition(name, text, rationale=req.why)
    except (AmendmentRefused, ProofEngineeringAttempt, DesignError) as exc:
        return done(outcome.refuse("refused", str(exc)))

    previous_designed = graph.get_meta(DESIGNED_FILE_META)
    try:
        new_dev = _apply_definition(cfg, graph, dev, root, definition, contract=contract, round_no=round_no, preamble=preamble)
    except DesignError as exc:
        return done(outcome.refuse("refused", str(exc)))
    reviewable = has_approver(cfg) and driver is not None
    if approved:
        outcome.verdict = "accept"
    elif not reviewable and req.kind == "replace":
        _restore_designed_file(graph, dev, previous_designed)
        return done(outcome.refuse("no approver", "a `replace` amendment needs an approver (configure a decomposer)"))
    elif not reviewable:
        outcome.verdict = "auto-accepted"  # an `add` with nobody to ask: the report says so

    if not approved and reviewable:
        assert driver is not None
        verdict = await driver.decomposer(dev).adjudicate_amendment(
            root, req, evidence=_requester_evidence(graph, req), budget_seconds=cfg.approver_seconds,
            contract=contract, design=current_design(dev),
        )
        graph.emit("amendment.adjudicated", root.id, definition=name, requester=req.requester, verdict=verdict.verdict,
                   ok=verdict.ok, detail=verdict.summary()[:400])
        if not verdict.ok or verdict.verdict == "reject":
            _restore_designed_file(graph, dev, previous_designed)
            why = verdict.hint if verdict.ok else f"the approver gave no usable verdict: {verdict.summary()}"
            return done(outcome.refuse(verdict.verdict or "no verdict", why))
        outcome.verdict = verdict.verdict
        if verdict.verdict == "adjust":
            adjusted = verdict.definition.strip() or name
            try:
                if not _mutable(contract, adjusted):
                    raise AmendmentRefused(f"the approver's adjustment names `{adjusted}`, which is not contract-mutable")
                definition = _definition(adjusted, verdict.text.strip(), rationale=verdict.hint or req.why)
                new_dev = _apply_definition(cfg, graph, dev, root, definition, contract=contract, round_no=round_no, preamble=preamble)
            except (AmendmentRefused, ProofEngineeringAttempt, DesignError) as exc:
                _restore_designed_file(graph, dev, previous_designed)
                return done(outcome.refuse("adjust", f"the approver's adjustment could not be applied: {exc}"))
            name = adjusted

    outcome.text, outcome.file = definition.text, str(new_dev.path)
    gate = (driver.gate_factory if driver is not None else Gate)(new_dev)
    outcome.kept, outcome.reopened = _replay_and_reopen(cfg, graph, new_dev, gate, root, req, name, definition.text, preamble=preamble)
    _remember(graph, definition)
    graph.emit(
        "amendment.applied", root.id, definition=name, kind=req.kind, requester=req.requester, verdict=outcome.verdict,
        reopened=outcome.reopened, kept=outcome.kept, file=str(new_dev.path), round=round_no,
    )
    outcome.applied = True
    return done(outcome, applied_dev=new_dev)


def _requester_evidence(graph: Graph, req: AmendmentRequest) -> str:
    node = graph.by_name(req.requester) if req.requester else None
    if node is None:
        return req.why
    return (node.evidence or last_evidence(graph, node) or req.why)[:EVIDENCE_SHOWN]


def _replay_and_reopen(
    cfg: ProveConfig, graph: Graph, new_dev: Development, gate: Gate, root: Node, req: AmendmentRequest,
    name: str, text: str, *, preamble: str,
) -> tuple[list[str], list[str]]:
    """Replay-first salvage, then the two taint channels (module docstring).  Returns
    ``(kept, reopened)`` by node name."""
    from pcp.orch.amend import mentions_definition, reopen_for_amendment, statement_invalidated

    detail = amendment_detail(req, text)
    kept, stale = revalidate(graph, new_dev, gate, root, preamble=preamble)
    reopened: list[str] = list(stale)
    for node_name in stale:
        node = graph.by_name(node_name)
        if node is not None:
            graph.update(node.id, evidence=detail)
    # The requester first: at its own epoch while it has attempts left, so the partial
    # it left behind reaches the next packet (``schedule.last_partial`` is per epoch).
    requester = graph.by_name(req.requester) if req.requester else None
    if requester is not None and requester.proof_status == "stuck" and attempts_spent(graph, requester) < cfg.max_attempts:
        graph.set_proof_status(requester.id, "open", evidence=detail)
        reopened.append(requester.name)
    seen = set(reopened)
    tainted = [
        n for n in statement_invalidated(graph, new_dev, name)
        if n.proof_status in ("stuck", "contested") and n.name not in seen
    ]
    if (
        requester is not None and requester.name not in seen and requester.proof_status in ("stuck", "contested")
        and all(n.id != requester.id for n in tainted)
    ):
        tainted.append(requester)
    # `statement_invalidated` leaves the root to the replay; a root that is not proved
    # but failed *against the old meaning* of a definition its statement names is in
    # the same position as any child, so a contested root reopens too.
    root_now = graph.require(root.id)
    if (
        root_now.proof_status in ("stuck", "contested") and root_now.name not in seen
        and all(n.id != root_now.id for n in tainted) and mentions_definition(new_dev, root_now.statement, name)
    ):
        tainted.append(root_now)
    if tainted:
        reopened += reopen_for_amendment(graph, tainted, definition=name, detail=detail)
    seen = set(reopened)
    # Everything else still stuck with attempts left goes again too: its proof may
    # have died where the old definition was opened, and it is told what changed.
    for node_name in reopen_incomplete(graph, max_attempts=cfg.max_attempts):
        node = graph.by_name(node_name)
        if node is not None and node_name not in seen:
            graph.update(node.id, evidence="\n\n".join(filter(None, [detail, node.evidence or ""])))
            reopened.append(node_name)
    # A node an earlier amendment in this pass already reopened is `open` now, and so
    # may be the requester of this one: it is told about this change too, so what its
    # packet says is true of the file it gets (the requester of an `add` reopened by a
    # `replace` is still told its conjunct landed).
    seen = set(reopened)
    for node in graph.nodes():
        if node.proof_status != "open" or node.name in seen:
            continue
        told = (node.evidence or "").startswith((AMENDED_MARKER, ADJUDICATED_MARKER))
        is_requester = requester is not None and node.id == requester.id
        if told and detail not in (node.evidence or ""):
            graph.update(node.id, evidence=f"{node.evidence}\n\n{detail}")
        elif is_requester and not told:
            graph.update(node.id, evidence="\n\n".join(filter(None, [detail, node.evidence or ""])))
    _follow_epochs(graph, reopened)
    return kept, reopened


def _follow_epochs(graph: Graph, names: Iterable[str]) -> None:
    """A reopened node's *statement* is unchanged -- a definition or its attempt budget
    moved, not what it says -- so a proved dependent's pin follows the new epoch, as
    :func:`pcp.orch.prove.design.refresh_after_revision` does.  Without this the
    root's demand edge on a reopened child goes stale and integration refuses a fully
    proved graph."""
    for name in names:
        node = graph.by_name(name)
        if node is None:
            continue
        for dependent in graph.dependents(node.id):
            repin_edges(graph, dependent)


# ------------------------------------------------------------------ the loop


@dataclass
class AmendmentRun:
    """The amendment path's state for one ``pcp prove``: what was applied, what was
    asked and refused, which contests were adjudicated.  Bounded by
    ``cfg.max_amendments`` applied changes; a request already seen (applied, refused
    or capped) is never re-processed, so a prover asking for the same rejected
    conjunct twice costs nothing the second time."""

    driver: DesignDriver
    outcomes: list[AmendmentOutcome] = field(default_factory=list)
    seen: set[str] = field(default_factory=set)
    #: ``(node id, epoch)`` pairs with a usable verdict this run: an epoch is asked once,
    #: and a node reopened at ``epoch+1`` by a verdict may be asked again there.
    adjudicated: set[tuple[str, int]] = field(default_factory=set)
    #: Obligations the approver restated (each one wrote a design directory).
    restated: int = 0

    @property
    def cfg(self) -> ProveConfig:
        return self.driver.cfg

    @property
    def applied(self) -> int:
        return sum(1 for o in self.outcomes if o.applied)

    @property
    def rounds_taken(self) -> int:
        """Design directories this run has written after the decomposer's: amendments and restatements."""
        return self.applied + self.restated

    @property
    def base_round(self) -> int:
        return max(1, self.driver.rounds_used)

    @property
    def enabled(self) -> bool:
        return int(self.cfg.max_amendments) > 0

    async def apply(self, dev: Development, requests: Iterable[AmendmentRequest], *, approved: bool = False) -> tuple[Development, bool]:
        """Apply each unseen request.  ``True`` when the development changed.

        ``replace`` requests go first, then ``add``s, each kind in request order: a
        conjunct joins whatever the definition says *after* any restatement in the same
        pass; the other order would apply the conjunct, tell its requester the
        definition "now also carries" it, and then let the restatement drop it.
        """
        changed = False
        ordered = sorted(requests, key=lambda r: r.kind != "replace")  # stable: replaces first
        for req in ordered:
            if req.key() in self.seen:
                continue
            self.seen.add(req.key())
            if self.applied >= int(self.cfg.max_amendments):
                capped = AmendmentOutcome(req).refuse("capped", f"--amendments {self.cfg.max_amendments} already applied this run")
                self.outcomes.append(_file_refusal(self.driver.graph, self.driver.root, req, capped))
                continue
            dev, outcome = await apply_amendment(
                self.cfg, self.driver.graph, dev, self.driver.root, req, contract=self.driver.contract,
                preamble=self.driver.preamble, round_no=self.base_round + self.rounds_taken + 1, driver=self.driver, approved=approved,
            )
            self.outcomes.append(outcome)
            changed = changed or outcome.applied
        return dev, changed

    async def adjudicate(
        self, dev: Development, nodes: Iterable[Node], *, review: Iterable[str] = ()
    ) -> tuple[Development, list[str], list[AmendmentRequest]]:
        """Contested nodes -- and nodes parked ``stuck`` for review after
        ``review_after`` failed attempts -- to the approver, once per node per epoch
        (and per run).

        ``strategy``: the statement stands; the node reopens at ``epoch+1`` with the
        hint as evidence -- a fresh attempt budget, because the old one was spent on
        the wrong strategy.  ``statement`` with a one-definition fix: returned as a
        pre-approved ``replace`` for :meth:`apply`.  ``statement`` with a
        ``restatement`` (the obligation's own sentence corrected): applied here by
        :meth:`restate`, and the node reopens against it.  ``statement`` with neither:
        a contested node stays contested, a reviewed stuck node *becomes* contested
        (the human's delegate says the statement is wrong), and the design revision
        (if any) takes it from here.
        """
        graph, cfg = self.driver.graph, self.cfg
        reopened: list[str] = []
        fixes: list[AmendmentRequest] = []
        for_review = set(review)  # node ids the scheduler parked ``stuck`` for a verdict
        if not has_approver(cfg):
            return dev, reopened, fixes
        for listed in nodes:
            node = graph.get(listed.id)
            if node is None or (node.id, node.epoch) in self.adjudicated:
                continue
            if node.proof_status != "contested" and not (node.proof_status == "stuck" and node.id in for_review):
                continue
            key = f"{ADJUDICATED_META}:{node.id}"
            if graph.get_meta(key) == str(node.epoch):
                continue
            evidence = (node.evidence or last_evidence(graph, node))[:EVIDENCE_SHOWN]
            reviewing = node.proof_status == "stuck"
            extra: dict[str, Any] = {"failed_attempts": attempts_spent(graph, node)} if reviewing else {}
            verdict = await self.driver.decomposer(dev).adjudicate_contest(
                self.driver.root, node, evidence=evidence, budget_seconds=cfg.approver_seconds,
                contract=self.driver.contract, design=current_design(dev), **extra,
            )
            graph.emit("contest.adjudicated", node.id, verdict=verdict.verdict, ok=verdict.ok,
                       definition=verdict.definition, detail=verdict.summary()[:400])
            if not verdict.ok:
                continue  # an outage is not a verdict; this run or the next may ask again
            # Remembered only once a usable verdict is back, and durable only once its
            # effect is: the meta is written in the same transaction as the move.
            self.adjudicated.add((node.id, node.epoch))
            restatement = str(getattr(verdict, "restatement", "") or "").strip()
            one_definition = bool(verdict.text.strip() and verdict.definition.strip())
            reopens_key = f"{ADJUDICATED_META}:reopens:{node.id}"
            reopens = int(graph.get_meta(reopens_key) or 0)
            marks = (graph, key, node.epoch, reopens_key, reopens)

            if verdict.verdict == "strategy":
                if reopens >= MAX_VERDICT_REOPENS:
                    # PLAN.md 8.9: a node escalated twice is a statement problem.  Verdicts
                    # reopen a node at most MAX_VERDICT_REOPENS times; after that the epoch
                    # counts as reviewed and whatever budget it has is spent normally.
                    graph.emit("contest.reopens_exhausted", node.id, epoch=node.epoch, reopens=reopens, verdict="strategy")
                    _mark_adjudicated(*marks)
                    continue
                was = "Your last attempt's evidence was" if reviewing else "Your contest was"
                detail = f"{ADJUDICATED_MARKER} {verdict.hint.strip() or 'the statement stands; change your approach'}\n\n{was}: {node.evidence}"
                with graph.transaction():
                    graph.update(node.id, proof_status="open", epoch=node.epoch + 1, evidence=detail, role="human")
                    graph.emit("node.reopened_by_adjudication", node.id, from_epoch=node.epoch, to_epoch=node.epoch + 1, role="human")
                    _mark_adjudicated(*marks, bump=True)
                _follow_epochs(graph, [node.name])
                reopened.append(node.name)
                continue
            # `statement`: a definition fix, a restatement, both, or neither.
            live = node
            if one_definition:
                fix = AmendmentRequest(
                    definition=verdict.definition.strip(), replace=verdict.text.strip(), at=node.name,
                    why=verdict.hint.strip() or "the approver found the statement wrong as designed", requester=node.name,
                )
                before = len(self.outcomes)
                dev, applied = await self.apply(dev, [fix], approved=True)
                if applied:
                    for outcome in self.outcomes[before:]:
                        reopened.extend(n for n in outcome.reopened if n not in reopened)
                    live = graph.require(node.id)  # reopened against the fixed definition
                elif restatement:
                    graph.emit("restatement.rejected", node.id, role="human",
                               reason=f"its companion fix to `{fix.definition}` was not applied")
                    restatement = ""
            if restatement and reopens >= MAX_VERDICT_REOPENS:
                graph.emit("contest.reopens_exhausted", node.id, epoch=node.epoch, reopens=reopens, verdict="restatement")
                restatement = ""
            if restatement:
                restated = await self.restate(dev, live, verdict)
                if restated is not None:
                    dev = restated
                    if node.name not in reopened:
                        reopened.append(node.name)
                    _mark_adjudicated(*marks, bump=True)
                    continue
            live = graph.require(node.id)
            if live.proof_status == "open":
                # The fix reopened it: that retry is the move.  (Contesting an open node is
                # not a lattice move.)
                if node.name not in reopened:
                    reopened.append(node.name)
                _mark_adjudicated(*marks)
                continue
            # Nothing applicable: the verdict itself is the move.  A contested node stays
            # contested; a reviewed stuck node *becomes* contested -- the design revision's
            # evidence, not two more attempts against the same wall.
            with graph.transaction():
                if live.proof_status == "stuck":
                    detail = (
                        f"{ADJUDICATED_MARKER} the approver finds this statement wrong as designed"
                        f"{': ' + verdict.hint.strip() if verdict.hint.strip() else ''}\n\nThe last attempt's evidence was: {live.evidence}"
                    )
                    graph.set_proof_status(node.id, "contested", evidence=detail, role="human")
                    graph.emit("node.contested_by_adjudication", node.id, epoch=node.epoch, role="human")
                _mark_adjudicated(*marks)
        if reopened:
            # Siblings the scheduler parked "blocked: non-mockable obligation ... unproved"
            # because of a node just reopened never spent an attempt; that node's next
            # dispatch is their chance too (only with budget left, and without the note).
            for sibling in graph.nodes(parent=self.driver.root.id):
                if sibling.proof_status != "stuck" or not (sibling.evidence or "").startswith(BLOCKED_PREFIX):
                    continue
                blockers = {b.strip() for b in sibling.evidence[len(BLOCKED_PREFIX):].split(" are unproved")[0].split(",")}
                if not (blockers & set(reopened)) or attempts_spent(graph, sibling) >= cfg.max_attempts:
                    continue
                with graph.transaction():
                    graph.set_proof_status(sibling.id, "open")
                    graph.update(sibling.id, evidence="")
                    graph.emit("node.unblocked", sibling.id, by=sorted(blockers & set(reopened)))
                if sibling.name not in reopened:
                    reopened.append(sibling.name)
        return dev, reopened, fixes

    async def restate(self, dev: Development, node: Node, verdict: Verdict) -> Development | None:
        """The approver corrected the obligation's own statement (a resource stated
        outside a ``□``-boxed triple, a missing hypothesis, a wrong postcondition).

        The corrected sentence replaces the node's in the *adopted* design, that design
        is compiled and checked exactly as a decomposer's would be (contract,
        sentinels, typecheck), and adopted: the node restates at ``epoch+1`` with its
        body cleared and every proof that used the old statement is replayed.  No
        design round is spent -- the decomposer's rounds are for the design being
        wrong, and this is a statement being wrong.  Rejected (the node stays
        contested, ``restatement.rejected`` says why) when the sentence does not
        compile, trips a sentinel, or names nothing the design adopted.
        """
        from dataclasses import replace as dc_replace

        from pcp.orch.decomposer import validate_proposal
        from pcp.orch.prove.design import (
            DesignError,
            adopt_proposal,
            adopted_proposal,
            apply_design,
            revalidate,
        )
        from pcp.orch.sentinels import body_hash, run_free_sentinels
        from pcp.rocq.statement import statement_hash

        graph, cfg, root = self.driver.graph, self.cfg, self.driver.root
        statement = verdict.restatement.strip()

        def reject(reason: str) -> None:
            graph.emit("restatement.rejected", node.id, reason=" ".join(reason.split())[:400], role="human")

        base = adopted_proposal(graph)
        if base is None or node.parent != root.id:
            return reject("the obligation is not a child of the adopted design")
        # The proposal is the graph's *live* children -- their statements as they stand,
        # not the stored copy (a sibling restated since would be reverted, an extra child
        # retired) -- with this one's sentence replaced; definitions from the adopted design.
        live = sorted(
            (n for n in graph.nodes(parent=root.id) if n.proof_status != "attic"),
            key=lambda n: (n.ordering, n.name),
        )
        if not any(n.id == node.id for n in live):
            return reject("the obligation is not among the design's live children")
        try:
            children = tuple(
                ChildStatement(
                    name=n.name,
                    statement=statement if n.id == node.id else n.statement,
                    rationale=(verdict.hint.strip() if n.id == node.id and verdict.hint.strip() else (n.intent or "")),
                )
                for n in live
            )
        except ProofEngineeringAttempt as exc:
            return reject(str(exc))
        proposal = dc_replace(base, children=children)
        problems = validate_proposal(proposal)
        if problems:
            return reject("; ".join(problems))
        # Sentinels over the restated child alone: its siblings were adopted (some proved)
        # exactly as they stand, and a note on one of them is not this sentence's problem.
        restated_child = next(c for c in children if c.name == node.name)
        known: dict[str, str] = {}
        for c in children:
            if c.name != node.name:
                known[statement_hash(c.statement)] = c.name
                known[body_hash(c.statement)] = c.name
        sentinels = run_free_sentinels(
            [restated_child], root_statement=root.statement, existing_hashes=known,
            definitions={d.name: d.text for d in proposal.definitions if d.name},
        )
        if sentinels.blocking:
            return reject("\n".join(h.render() for h in sentinels.blocking))
        if self.rounds_taken >= int(cfg.max_amendments):
            return reject(f"--amendments {cfg.max_amendments}: this run has written its design directories")
        round_no = self.base_round + self.rounds_taken + 1
        try:
            new_dev = apply_design(
                cfg, graph, dev, root, proposal, contract=self.driver.contract, round_no=round_no,
                workroot=cfg.workroot, preamble=self.driver.preamble,
            )
        except DesignError as exc:
            return reject(str(exc))
        self.restated += 1
        adopt_proposal(cfg, graph, new_dev, root, proposal, round_no=round_no)
        fresh = graph.by_name(node.name)
        if fresh is not None:
            detail = (
                f"{ADJUDICATED_MARKER} the approver corrected this obligation's statement"
                f"{': ' + verdict.hint.strip() if verdict.hint.strip() else ''}\n\n"
                f"The old statement was:\n{node.statement.strip()}\n\nYour contest was: {node.evidence or ''}"
            )
            graph.update(fresh.id, evidence=detail, role="human")
        # Replay-first (PLAN.md 8.5): every proof that used the old statement is checked
        # against the new one.  No blanket refresh -- only this node's statement changed,
        # and `adopt_proposal` already gave it its new epoch and cleared its body.
        kept, reopened = revalidate(graph, new_dev, self.driver.gate_factory(new_dev), root, preamble=self.driver.preamble)
        graph.emit(
            "node.restated_by_adjudication", node.id, from_epoch=node.epoch, to_epoch=node.epoch + 1,
            kept=kept, reopened=reopened, round=round_no, role="human",
        )
        _follow_epochs(graph, [node.name])
        return new_dev

    def retry_refused(self, outcomes: Iterable[AmendmentOutcome]) -> list[str]:
        """The requester of a request that was *not* applied gets its ordinary retry now.

        The scheduler withholds the evidence-informed retry from a ``stuck`` that asks
        for an amendment, on the prover's word that the design is short a fact.  When
        the answer is "no" -- refused by a check, rejected by the approver, capped --
        that retry must still happen in this run, with the refusal as its evidence
        (``_tell_requester`` wrote it), rather than be lost (a plan run) or bought with
        a full design revision.  Bounded
        by the node's attempt budget like any retry; a node already reopened by an
        applied amendment's salvage is left alone.
        """
        graph, cfg = self.driver.graph, self.cfg
        retried: list[str] = []
        for outcome in outcomes:
            requester = outcome.request.requester
            if outcome.applied or not requester or requester in retried:
                continue
            node = graph.by_name(requester)
            if node is None or node.proof_status != "stuck" or attempts_spent(graph, node) >= cfg.max_attempts:
                continue
            graph.set_proof_status(node.id, "open")
            graph.emit("node.retried_after_refusal", node.id, definition=outcome.request.definition, verdict=outcome.verdict)
            retried.append(node.name)
        return retried

    async def loop(self, dev: Development, report: RunReport, dispatch: Dispatch) -> tuple[Development, RunReport]:
        """Apply what the last dispatch asked for, re-dispatch, repeat until a dispatch
        asks for nothing new or the cap is reached (module docstring)."""
        reports = [report]
        while self.enabled:
            first = len(self.outcomes)
            dev, changed = await self.apply(dev, report.amendments())
            review = {o.node_id for o in report.by_status("stuck") if getattr(o, "review", False)}
            listed = report.by_status("contested") + [o for o in report.by_status("stuck") if o.node_id in review]
            contested = [graph_node for o in listed if (graph_node := self.driver.graph.get(o.node_id)) is not None]
            dev, reopened, fixes = await self.adjudicate(dev, contested, review=review)
            if fixes:
                dev, fixed = await self.apply(dev, fixes, approved=True)
                changed = changed or fixed
            changed = changed or any(o.applied for o in self.outcomes[first:])  # incl. fixes adjudicate applied itself
            retried = self.retry_refused(self.outcomes[first:])
            if not (changed or reopened or retried):
                break
            report = await dispatch(dev, self.base_round + self.rounds_taken)
            reports.append(report)
        return dev, RunReport.combined(reports)


async def amendment_loop(
    driver: DesignDriver, dev: Development, report: RunReport, dispatch: Dispatch,
) -> tuple[Development, RunReport, list[AmendmentOutcome]]:
    """The loop as one call: ``(dev, combined report, outcomes)``."""
    run = AmendmentRun(driver)
    dev, report = await run.loop(dev, report, dispatch)
    return dev, report, run.outcomes


def _mark_adjudicated(graph: Graph, key: str, epoch: int, reopens_key: str, reopens: int, *, bump: bool = False) -> None:
    """The epoch had its verdict (and, with ``bump``, one more verdict-driven reopening)."""
    graph.set_meta(key, str(epoch))
    if bump:
        graph.set_meta(reopens_key, str(reopens + 1))


def contested_nodes(graph: Graph) -> list[Node]:
    return [n for n in graph.nodes() if n.proof_status == "contested" and n.statement_status == "frozen"]


def review_after(cfg: Any) -> int:
    """The scheduler's review threshold as configured, or 0 when nothing could act on it
    (no approver, or the amendment path -- which does the adjudicating -- disabled)."""
    if int(getattr(cfg, "max_amendments", 0)) <= 0 or not has_approver(cfg):
        return 0
    return max(0, int(getattr(cfg, "review_after", 0)))


def parked_for_review(graph: Graph, cfg: Any) -> list[Node]:
    """Stuck nodes a resumed run should hand to the approver first: enough failed
    attempts at their epoch, no verdict yet, not merely blocked on a sibling.  Without
    this a node parked for review by a run that then crashed -- or whose budget was
    spent before the review existed -- waited for a dispatch that never came."""
    threshold = review_after(cfg)
    if not threshold:
        return []
    return [
        n for n in graph.nodes()
        if n.proof_status == "stuck" and n.statement_status == "frozen"
        and not (n.evidence or "").startswith((BLOCKED_PREFIX, AMENDED_MARKER))
        and attempts_spent(graph, n) >= threshold
        and graph.get_meta(f"{ADJUDICATED_META}:{n.id}") != str(n.epoch)
    ]
