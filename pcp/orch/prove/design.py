"""The decomposer-driven path: design application and bounded revision (PLAN.md 9, 8.5).

A design rung leaves the invariant and the abstract predicates blank; a prover
cannot fill them in (it returns proof bodies, never statements).  So the design
comes from the decomposer, is applied to a working copy of the development, is
checked against the developer's *contract*, compiled, and frozen for the provers
like any other spec-zone artifact.  Failed proofs are evidence about the design,
fed back for a bounded number of revisions, with replay-first salvage of the proofs
that survive.

What this module fixes structurally (bugs-pipeline.md, map-prove §6):

* the contract is loaded **once** from the original corpus and carried through
  every round -- round 2 no longer runs under ``everything_frozen()``;
* every design fragment and every hoisted preamble line passes the gate's static
  scan: ``Unset Guard Checking`` in a definition is a contract violation, never
  hoisted above the file where nothing looks;
* a children-only proposal still typechecks its child statements, because one bad
  frozen statement poisons every sibling's file;
* imports are inserted by the lexer-based :func:`pcp.rocq.assemble.insert_preamble`;
  additions are anchored before their first use over *every* sentence, with a
  section-aware fallback, and pulled up to their earliest consumer to a fixpoint;
* design directories are never overwritten, rounds are counted once, an amendment
  that omits a definition keeps the previous one, and a rejected answer is re-asked
  with the checker's own words rather than a granularity verdict about proofs.
"""

from __future__ import annotations

import time
from collections.abc import Awaitable, Callable, Sequence
from pathlib import Path
from typing import TYPE_CHECKING, Any, cast

from pcp.errors import PcpError, ToolchainError, UsageError
from pcp.orch.decomposer import (
    Decomposer,
    DecompositionResult,
    PlanProposal,
    ProofEngineeringAttempt,
    declared_name,
)
from pcp.orch.gate import Gate, escape_hatch
from pcp.orch.graph import Graph
from pcp.orch.model import PROVED_STATUSES, Node, node_id
from pcp.orch.prove.resume import DESIGNED_FILE_META, reopen_incomplete
from pcp.orch.schedule import NodeOutcome, RunReport, ensure_edge, repin_edges
from pcp.rocq.assemble import Development, NodeSpec, insert_preamble
from pcp.rocq.decls import parse_blocks
from pcp.rocq.lexer import first_word, identifiers, split_sentences, strip_comments
from pcp.rocq.project import compile_text, coq_project_flags
from pcp.rocq.statement import statement_hash
from pcp.util.io import atomic_write_text, copy_if_exists, ensure_dir, json_dump, read_text

if TYPE_CHECKING:
    from pcp.orch.protocol import Runner
    from pcp.orch.prove import ProveConfig

#: How many times a decomposition killed by the clock is given more of it.
DECOMPOSE_DEADLINE_RETRIES = 2
STAGED_FILES = ("_CoqProject", "Makefile", "dune-project")
#: Vernacular that is only legal outside every Section: hoisted after the last Require.
PREAMBLE_HEADS = frozenset({"Require", "From", "Import", "Export", "Declare"})
AXIOM_HEADS = frozenset({"Axiom", "Axioms", "Parameter", "Parameters", "Conjecture"})
_MODIFIERS = frozenset({"Local", "Global", "Program", "Polymorphic", "Monomorphic", "Cumulative", "NonCumulative", "Private"})
EVIDENCE_LIMIT = 6000
BLAMELESS = frozenset({"runner-error", "protocol-violation", "permission-denied"})


class DesignError(PcpError):
    """A design the decomposer can be told about and correct (revisable, never fatal)."""


class DesignViolatesContract(DesignError):
    """The design moved something the contract froze, or smuggled an escape hatch."""


class DesignDoesNotCompile(DesignError):
    """The proposed design, or a child statement, is not well-formed Rocq."""


# ------------------------------------------------------------------ text surgery


def is_preamble_vernacular(text: str) -> bool:
    return first_word(text.strip()) in PREAMBLE_HEADS


def scan_fragment(text: str, label: str) -> None:
    """The gate's static scan over a non-proof fragment (ARCHITECTURE.md §4, design
    submissions): no escape hatch and no new axiom, wherever the fragment would land."""
    for sent in split_sentences(strip_comments(text)):
        code = sent.code
        if not code.strip():
            continue
        hatch = escape_hatch(code)
        if hatch:
            raise DesignViolatesContract(f"design {label!r} disables a kernel check ({hatch}): `{_short(code)}`")
        words = identifiers(code)
        i = 0
        while i < len(words) and words[i] in _MODIFIERS:
            i += 1
        head = words[i] if i < len(words) else first_word(code)
        if head in AXIOM_HEADS:
            raise DesignViolatesContract(f"design {label!r} adds an axiom ({head}): `{_short(code)}`; a design has no axioms")


def _short(code: str, width: int = 80) -> str:
    text = " ".join(code.split())
    return text if len(text) <= width else text[: width - 3] + "..."


def scan_child(statement: str, name: str) -> None:
    """A child statement is one sentence and nothing else.  It is frozen verbatim into
    every sibling's file, so ``Lemma foo : True. Unset Guard Checking.`` -- which Rocq
    accepts -- would hoist an escape hatch past every gate (review finding).  The
    proposal validator refuses it first; this is the check at the point of use."""
    scan_fragment(statement, name)
    sentences = [s for s in split_sentences(strip_comments(statement)) if s.code.strip()]
    if len(sentences) != 1:
        raise DesignViolatesContract(
            f"child {name!r} is not a single statement sentence ({len(sentences)} sentences): `{_short(statement)}`"
        )


def design_rounds_used(graph: Graph, root: Node) -> int:
    """Design rounds already spent on ``root``, across runs, from the decomposer's own
    attempt rows -- a crash-resume loop otherwise bought ``--design-rounds`` fresh
    revisions per invocation (the attempt budget is bounded the same way)."""
    return max(
        (int(r.get("round") or 0) for r in graph.attempts_for(root.id) if r.get("role") == "decomposer"),
        default=0,
    )


def add_imports(source: str, lines: Sequence[str]) -> str:
    """Append preamble lines after the last top-level ``Require``, deduplicated."""
    existing = {" ".join(s.code.split()) for s in split_sentences(source)}
    new = [line.strip() for line in lines if " ".join(line.split()) not in existing]
    return insert_preamble(source, "\n".join(new)) if new else source


def place_additions(text: str, additions: Sequence[str], *, anchor: str | None = None) -> str:
    """Insert each new declaration *before the first thing that uses it*.

    The consumer scan covers every sentence outside a proof body -- ``Context``,
    ``Notation``, ``Hint``, anonymous ``Instance`` lines included, not only named
    statements -- so a new ``Class fooG`` used only by ``Context \\`{!fooG Σ}`` lands
    above it.  Additions also use each other: each is pulled up to its earliest
    consumer, iterated to a fixpoint and bounded so a cycle terminates (the compile
    then reports it).  An orphan lands before the first proof block *in the anchor's
    own section*, so it can see the section's ``Σ``; the legacy fallback was the
    first proof block in the file, which could sit outside it.
    """
    if not additions:
        return text
    blocks = parse_blocks(text)
    spans = [(b.body_start, b.body_end) for b in blocks if b.body_start is not None and b.body_end is not None]

    def in_body(offset: int) -> bool:
        return any(start <= offset < end for start, end in spans)

    anchor_block = next((b for b in blocks if b.name == anchor), None) if anchor else None
    if anchor_block is not None:
        same_section = [
            b.statement_start for b in blocks
            if b.has_proof and b.sections == anchor_block.sections and b.statement_start <= anchor_block.statement_start
        ]
        fallback = min(same_section, default=anchor_block.statement_start)
    else:
        fallback = min((b.statement_start for b in blocks if b.has_proof), default=len(text))

    sentences = [
        (s.code_start, set(identifiers(s.code)))
        for s in split_sentences(text)
        if s.code.strip() and not in_body(s.code_start)
    ]
    names = [declared_name(a) for a in additions]
    anchors = [
        min((start for start, ids in sentences if name in ids), default=fallback) if name else fallback
        for name in names
    ]
    needs = {
        i: {j for j, nm in enumerate(names) if j != i and nm and nm in identifiers(strip_comments(body))}
        for i, body in enumerate(additions)
    }
    for _ in range(len(additions)):
        moved = False
        for i, deps in needs.items():
            for j in deps:
                if anchors[j] > anchors[i]:
                    anchors[j] = anchors[i]
                    moved = True
        if not moved:
            break
    depth = dict.fromkeys(needs, 0)
    for _ in range(len(additions)):
        moved = False
        for i, deps in needs.items():
            want = max((depth[j] + 1 for j in deps), default=0)
            if want > depth[i]:
                depth[i] = want
                moved = True
        if not moved:
            break
    out: list[str] = []
    cursor = 0
    for i in sorted(range(len(additions)), key=lambda i: (anchors[i], depth[i], i)):
        out.append(text[cursor : anchors[i]])
        out.append(additions[i].strip() + "\n\n")
        cursor = anchors[i]
    out.append(text[cursor:])
    return "".join(out)


def blame_child(detail: str, specs: Sequence[NodeSpec], *, text: str = "", line: int | None = None) -> str:
    """Name the offending child only when exactly one is identified -- by name in the
    compiler's message, or by the reported line falling inside its statement in the
    assembled ``text`` (Rocq usually reports a position, not a name)."""
    named = [s.name for s in specs if s.name and s.name in detail]
    if len(named) == 1:
        return f" (`{named[0]}`)"
    if line is not None and text:
        at_line: list[str] = []
        for s in specs:
            span = _statement_lines(text, s.statement)
            if span is not None and span[0] <= line <= span[1]:
                at_line.append(s.name)
        if len(at_line) == 1:
            return f" (`{at_line[0]}`)"
    return ""


def _statement_lines(text: str, statement: str) -> tuple[int, int] | None:
    start = text.find(statement.strip())
    if start < 0:
        return None
    first = text.count("\n", 0, start) + 1
    return first, first + statement.strip().count("\n")


def design_dir(workroot: str | Path, root_id: str, round_no: int) -> Path:
    """``<workroot>/<root.id>.designed[N]/``, fresh: an existing directory is never
    overwritten (it is what earlier packets and events point at)."""
    base = Path(workroot)
    n = round_no
    while True:
        candidate = base / f"{root_id}.designed{'' if n == 1 else n}"
        if not candidate.exists():
            return candidate
        n += 1


# ------------------------------------------------------------------ application


def apply_design(
    cfg: ProveConfig,
    graph: Graph,
    dev: Development,
    root: Node,
    proposal: PlanProposal,
    *,
    contract: Any,
    round_no: int,
    workroot: str | Path,
    preamble: str = "",
) -> Development:
    """Write the design into a working copy and check it (module docstring)."""
    blocks: dict[str, Any] = {}
    for b in dev.blocks:
        if b.name and b.name not in blocks:
            blocks[b.name] = b
    hoisted: list[str] = []
    edits: list[tuple[int, int, str]] = []
    additions: list[str] = []
    for line in proposal.imports:
        scan_fragment(line, "import")
        hoisted.append(line.strip())
    for child in proposal.children:
        scan_child(child.statement, child.name)
    for definition in proposal.definitions:
        text = definition.text.strip()
        scan_fragment(text, definition.name or "fragment")
        if is_preamble_vernacular(text):
            hoisted.append(text)
            continue
        block = blocks.get(definition.name) if definition.name else None
        if block is None:
            additions.append(text)
        else:
            edits.append((block.statement_start, block.statement_end, text))
    patched = _splice(dev.source, edits)
    if hoisted:
        patched = add_imports(patched, hoisted)
    if additions:
        patched = place_additions(patched, additions, anchor=root.name)

    check = contract.check(dev.source, patched)
    if not check.ok:
        raise DesignViolatesContract(
            "the design changed something the contract does not permit: " + check.detail
            + f"  --  contract: {contract.describe()}"
        )

    designed = dev
    target: Path | None = None
    if proposal.changes_design:
        target_dir = ensure_dir(design_dir(workroot, root.id, round_no))
        target = target_dir / dev.path.name
        atomic_write_text(target, patched)
        copy_if_exists(dev.path.parent / "_CoqProject", target_dir / "_CoqProject")
        if cfg.brief == "full":
            copy_if_exists(dev.path.parent / "DESIGN.md", target_dir / "DESIGN.md")
        designed = Development(target)
        _compile_or_raise(patched, designed, what="the design does not compile")
    if proposal.children:
        # A child's frozen statement is elaborated in every sibling's file, so one
        # bad statement poisons all of them; the stubbed per-node shape is what
        # makes this check cheap (5.4 s against 512 s on the cached rungs).
        specs = [NodeSpec(c.name, c.statement) for c in proposal.children]
        try:
            assembly = designed.assemble(root.name, specs, anchor_body=None, truncate=True, stub_prefix=True, extra_preamble=preamble)
        except UsageError as exc:
            raise DesignDoesNotCompile(str(exc)) from None
        _compile_or_raise(assembly.text, designed, what="a child statement does not typecheck", specs=specs)
    if target is not None:
        graph.emit("design.applied", root.id, round=round_no, definitions=proposal.definition_names(), file=str(target))
        graph.set_meta(DESIGNED_FILE_META, str(target))
    return designed


def _compile_or_raise(text: str, dev: Development, *, what: str, specs: Sequence[NodeSpec] = ()) -> None:
    cres = compile_text(text, filename=dev.path.name, root=dev.root, flags=coq_project_flags(dev.root))
    if cres.unavailable:
        raise ToolchainError(f"cannot check a design: {cres.unavailable}")
    if cres.timed_out:
        raise ToolchainError(f"cannot check a design: coqc timed out after {cres.elapsed_s:.0f}s")
    if not cres.ok:
        detail = cres.first_error() or cres.output[-1500:]
        where = cres.error_location()
        blame = blame_child(detail, specs, text=text, line=where.line if where else None) if specs else ""
        raise DesignDoesNotCompile(f"{what}{blame}: {detail}")


def _splice(text: str, edits: list[tuple[int, int, str]]) -> str:
    out: list[str] = []
    cursor = 0
    for start, end, replacement in sorted(edits):
        out.append(text[cursor:start])
        out.append(replacement)
        cursor = end
    out.append(text[cursor:])
    return "".join(out)


# ------------------------------------------------------------------ adoption


ADOPTED_PROPOSAL_META = "design_proposal"


def adopted_proposal(graph: Graph) -> PlanProposal | None:
    """The proposal the graph currently runs against, for revisions to complete from."""
    import json

    raw = graph.get_meta(ADOPTED_PROPOSAL_META)
    if not raw:
        return None
    try:
        return PlanProposal.from_json(json.loads(raw))
    except (ValueError, TypeError, ProofEngineeringAttempt):
        return None


def adopt_proposal(cfg: ProveConfig, graph: Graph, dev: Development, root: Node, proposal: PlanProposal, *, round_no: int = 1) -> list[Node]:
    """Turn a validated proposal into frozen, dispatchable nodes.

    Reconciled by statement hash like a plan: a child restated under an existing
    name gets the new statement at ``epoch+1`` with its body cleared (the legacy
    adoption kept the old frozen statement while the new one had been typechecked);
    a revived name comes back from the attic; unproved children the design no longer
    asks for are retired.  Nothing about a proof passes through here.
    """
    import json

    graph.set_meta(ADOPTED_PROPOSAL_META, json.dumps(proposal.to_json()))
    # The glue rationale IS the root's proof strategy (PLAN.md 8.2: a plan is children
    # plus a glue proof).  Without it the root prover's packet has no "why this lemma
    # exists" section at all -- the first spec-only seqlock_wf run contested the root
    # after registering its atomic update at the wrong program point.
    glue = " ".join((proposal.glue_rationale or proposal.rationale or "").split())
    if glue and glue[:400] != (root.intent or ""):
        graph.update(root.id, intent=glue[:400], role="human")
    budget = cfg.budget.split(max(1, len(proposal.children)))
    wanted = set(proposal.names())
    created: list[Node] = []
    for i, child in enumerate(proposal.children):
        existing = graph.by_name(child.name)
        new_hash = statement_hash(child.statement)
        if existing is None:
            node = graph.add_node(
                Node(
                    id=node_id(child.name), name=child.name, statement=child.statement.strip(),
                    rank="local", parent=root.id, depth=root.depth + 1, statement_status="frozen",
                    proof_status="open", owner="decomposer", intent=(child.rationale or proposal.rationale)[:400],
                    budget=budget, file=str(dev.path), ordering=i,
                )
            )
            graph.add_edge(root.id, node.id)
            created.append(node)
        elif existing.statement_hash != new_hash:
            # A restated obligation is a new one; the contest or proof was of the old.
            graph.update(
                existing.id, statement=child.statement.strip(), statement_hash=new_hash,
                epoch=existing.epoch + 1, proof_status="open", body=None, ordering=i,
                intent=(child.rationale or existing.intent)[:400], role="human",
            )
            graph.emit("plan.restated", existing.id, epoch=existing.epoch + 1, name=existing.name, round=round_no)
            ensure_edge(graph, root.id, existing.id)  # the root's pin stays where its proof was checked
        elif existing.proof_status == "attic":
            graph.set_proof_status(existing.id, "open", role="human")
            graph.emit("plan.revived", existing.id, round_of=root.id, round=round_no)
    retired: list[str] = []
    for node in graph.nodes(parent=root.id):
        if node.name in wanted or node.proof_status == "attic" or node.proof_status in PROVED_STATUSES:
            continue
        graph.set_proof_status(node.id, "attic", role="human")
        retired.append(node.name)
    if retired:
        graph.emit("plan.retired", root.id, retired=retired, round=round_no)
    graph.emit("plan.adopted", root.id, children=proposal.names(), retired=retired, round=round_no)
    return created


def revalidate(
    graph: Graph, dev: Development, gate: Gate, root: Node, *, preamble: str = "", only_stale: bool = False
) -> tuple[list[str], list[str]]:
    """Replay every proved body against the amended design (PLAN.md 8.5, replay-first).

    A proof that no longer gates is re-opened; the graph bumps its epoch and clears
    its body in the same transaction, so nothing stale is ever injected as a proved
    sibling.  A proof that holds has just been checked against its dependencies'
    current statements, so its demand edges are re-pinned there.  ``only_stale``
    replays just the proved nodes whose edges are stale (a dependency restated since
    the proof was checked): every run does this before dispatch, so a stale edge is
    examined rather than merely refused at integration.  Attic nodes are excluded
    from every replay assembly.
    """
    kept: list[str] = []
    reopened: list[str] = []
    for node in graph.nodes():
        if node.proof_status not in PROVED_STATUSES or not node.body or node.proof_status == "attic":
            continue
        if only_stale and not graph.stale_edges(node.id):
            continue
        is_anchor = dev.block(node.name) is not None
        # Siblings are STUBBED (Claim 1: a proof depends only on its siblings' statements),
        # so a sibling whose own body the amendment broke cannot get this sound proof
        # blamed and reopened (review finding).  Only non-mockable siblings keep a body.
        others = [
            NodeSpec(
                o.name, o.statement,
                o.body if (not o.mockable and o.proof_status in PROVED_STATUSES) else None,
                o.mockable, o.transparent,
            )
            for o in graph.nodes()
            if o.id != node.id and o.rank != "root" and o.proof_status != "attic" and dev.block(o.name) is None
        ]
        if is_anchor:
            result = gate.run(node.name, others, target=node.name, target_body=node.body, truncate=True, stub_prefix=True, extra_preamble=preamble)
        else:
            own = NodeSpec(node.name, node.statement, node.body, node.mockable, node.transparent)
            result = gate.run(root.name, [*others, own], target=node.name, target_body=None, truncate=True, stub_prefix=True, extra_preamble=preamble)
        if result.infrastructure:
            raise ToolchainError("cannot replay proofs against the revised design: " + result.render())
        if result.ok:
            repin_edges(graph, node.id)
            kept.append(node.name)
        else:
            graph.update(node.id, proof_status="open", role="human")
            reopened.append(node.name)
    return kept, reopened


def refresh_after_revision(graph: Graph, root: Node) -> list[str]:
    """The design changed under every unproved obligation: its closure is new, so it
    gets a new epoch and with it a fresh attempt budget -- otherwise the very
    failures that motivated the revision are the ones it cannot reach.  The
    statement itself is unchanged, so a proved dependent's pin follows the epoch:
    this bump is about budget, not about what was proved."""
    refreshed: list[str] = []
    for node in graph.nodes():
        if node.proof_status in PROVED_STATUSES or node.proof_status == "attic":
            continue
        graph.update(node.id, epoch=node.epoch + 1, role="human")
        for dependent in graph.dependents(node.id):
            repin_edges(graph, dependent)
        refreshed.append(node.name)
    if refreshed:
        graph.emit("design.refreshed", root.id, nodes=refreshed)
    return refreshed


# ------------------------------------------------------------------ staging (spec-only)


def staged_dir(cfg: ProveConfig) -> Path:
    return Path(cfg.workroot) / f"{node_id(cfg.target)}.staged"


def stage_spec_only(cfg: ProveConfig, root_id: str, *, contract: Any | None = None) -> Development:
    """The benchmark condition "each rung is given only the spec": a copy of the
    development holding only ``*.v`` and the project files, plus a ``design.json``
    that carries the contract and nothing else.  No ``DESIGN.md``, no ``bench.json``,
    no roles: nothing a worker or decomposer could read the brief from."""
    from pcp.orch.contract import DesignContract

    src_dir = Path(cfg.file).parent
    staged = ensure_dir(Path(cfg.workroot) / f"{root_id}.staged")
    for p in sorted(src_dir.glob("*.v")):
        atomic_write_text(staged / p.name, read_text(p))
    for name in STAGED_FILES:
        copy_if_exists(src_dir / name, staged / name)
    if contract is None:
        contract = DesignContract.from_corpus(src_dir)
    json_dump(staged / "design.json", contract.to_json())
    return Development(staged / Path(cfg.file).name)


def read_design_brief(cfg: ProveConfig) -> str:
    """The corpus ``DESIGN.md`` under ``--brief full``; nothing under ``spec-only``."""
    if cfg.brief != "full":
        return ""
    path = Path(cfg.file).parent / "DESIGN.md"
    return read_text(path) if path.exists() else ""


# ------------------------------------------------------------------ evidence


def standing_failures(graph: Graph, report: RunReport, *, max_attempts: int) -> RunReport:
    """The failures a resumed run inherited and this dispatch did not touch.

    ``design_failed`` used to read only the current dispatch, so a resume whose one
    dispatched node proved ended "not integrated" while a contested child and an
    attempt-exhausted child sat in the graph untouched (spec-only seqlock_wf,
    2026-09-05).  Those nodes are the design's business too.
    """
    from pcp.orch.schedule import NodeOutcome, attempts_spent

    seen = {o.node_id for o in report.outcomes}
    out = RunReport()
    for node in graph.nodes():
        if node.id in seen or node.proof_status == "attic":
            continue
        if node.proof_status == "contested" or (
            node.proof_status == "stuck" and attempts_spent(graph, node) >= max_attempts
        ):
            out.outcomes.append(NodeOutcome(
                node_id=node.id, name=node.name, status=node.proof_status,
                evidence=node.evidence or "", attempts=attempts_spent(graph, node),
            ))
    return out


def design_failed(report: RunReport) -> bool:
    """Did anything fail in a way the *design* could be responsible for?  Runner
    errors, protocol slips and permission blocks say nothing about the invariant."""
    from pcp.orch.failures import classify

    for outcome in report.outcomes:
        if outcome.status == "qed":
            continue
        if outcome.status == "contested":
            return True
        if outcome.status == "error":
            continue
        if classify(outcome.evidence, status=outcome.status).primary not in BLAMELESS:
            return True
    return False


def why_it_failed(outcome: NodeOutcome) -> str:
    from pcp.orch.failures import classify

    klass = classify(outcome.evidence or "", status=outcome.status).primary
    if outcome.status == "contested":
        return "the prover argues the statement itself is wrong -- read its reasoning before restating; it may be right"
    if klass in ("deadline", "no-progress"):
        return "ran out of clock without finishing: this obligation is too large. Split it"
    if outcome.requests:
        return "could not finish and named the lemmas it was missing (below) -- those names are where this obligation should be cut"
    if outcome.attempts > 1:
        return (
            f"{outcome.attempts} independent attempts failed. A second prover failing the same way "
            "is evidence about the obligation, not the prover"
        )
    return "did not finish"


def granularity_verdict(failed: Sequence[NodeOutcome], proved: Sequence[NodeOutcome]) -> str:
    return (
        f"=== {len(failed)} of {len(failed) + len(proved)} obligations were not proved ===\n"
        "Read this as a verdict on the decomposition before you read it as a verdict on "
        "the provers. Every obligation you state must be **tightly scoped proof "
        "engineering**: one self-contained step, provable without re-deriving your "
        "design. An obligation that no prover finishes was not that.\n"
        "Your first remedy is to **split the failing obligations further** -- more, "
        "smaller children, stated in the same vocabulary. Revising the design itself is "
        "the right move only when the evidence says the design is wrong (a prover "
        "contests a statement, or an invariant cannot be restored at a close site), not "
        "merely when a proof was hard."
    )


def design_evidence(report: RunReport, limit: int = EVIDENCE_LIMIT) -> str:
    """What the provers hit, in the decomposer's terms -- and what they asked for.
    Requests are quoted, never adopted: stating obligations is the decomposer's job."""
    failed = [o for o in report.outcomes if o.status != "qed"]
    proved = [o for o in report.outcomes if o.status == "qed"]
    parts: list[str] = []
    asked: list[str] = []
    if failed:
        parts.append(granularity_verdict(failed, proved))
    for outcome in failed:
        parts.append(
            f"--- {outcome.name} ({outcome.status}, {outcome.attempts} attempt(s), "
            f"{outcome.elapsed_s:.0f}s): {why_it_failed(outcome)}"
        )
        parts.append(outcome.evidence.strip()[:2000] or "(no evidence recorded)")
        for request in outcome.requests or []:
            statement = str(request.get("statement") or "").strip()
            rationale = str(request.get("rationale") or "").strip()
            if statement:
                asked.append(
                    f"--- {outcome.name} asked for:\n{statement[:1200]}" + (f"\n  why: {rationale[:400]}" if rationale else "")
                )
        for amendment in outcome.amendments or []:
            change = f"`{amendment.definition}` to also carry `{amendment.add}`" if amendment.kind == "add" else f"`{amendment.definition}` to be restated"
            asked.append(
                f"--- {outcome.name} asked for the design to change: {change}"
                + (f"\n  at: {amendment.at[:300]}" if amendment.at else "") + (f"\n  why: {amendment.why[:400]}" if amendment.why else "")
                + "\n  (a change that compiled was applied and replayed already; one listed here was refused or could not be checked)"
            )
    if asked:
        parts.append(
            "\n=== lemmas the provers asked to exist ===\n"
            "These are requests, not decisions: a prover cannot state its own "
            "obligations. Judge each one -- a request that merely restates the "
            "prover's own goal is a prover that wants the problem solved for it, but "
            "a request that names a genuinely separate fact is usually a signal that "
            "the obligation you gave it is too large, and should be split there."
        )
        parts.extend(asked)
    return "\n".join(parts)[:limit]


def design_problem(exc: Exception, *, revised: bool = False) -> str:
    which = "revised design" if revised else "design"
    if isinstance(exc, DesignViolatesContract):
        return (
            f"your {which} changed a definition the contract freezes: {exc} "
            "You may *add* definitions -- new ghost state, new resource algebras, new "
            "helper predicates -- and they are placed for you. You may not rewrite one "
            "that is already there."
        )
    return f"the {which} does not compile: {exc}"


# ------------------------------------------------------------------ the deadline ladder


async def decompose_with_retry(
    decomposer: Decomposer,
    root: Node,
    *,
    contract: Any | None,
    seconds: float,
    cap_seconds: float,
    elapsed_s: float = 0.0,
    graph: Graph,
    design_brief: str = "",
    library: Sequence[Path] = (),
    brief_mode: str = "full",
    round_no: int = 1,
) -> DecompositionResult:
    """Ask for the initial decomposition; a round killed by the clock is retried with
    a doubled clock, bounded by what remains of the run's own budget (map-speculative
    §5.6).  A deadline is not a judgement; an outage is not retried."""
    from pcp.orch.failures import classify

    spent = 0.0
    out: DecompositionResult | None = None
    for attempt in range(1, DECOMPOSE_DEADLINE_RETRIES + 2):
        out = await decomposer.propose(
            root, contract, budget_seconds=seconds, design_brief=design_brief, library=library,
            brief_mode=brief_mode, round_no=round_no,
        )
        if out.ok or out.infrastructure:
            return out
        if not (out.deadline or classify(out.violation or "").primary == "deadline"):
            return out
        if attempt > DECOMPOSE_DEADLINE_RETRIES:
            return out
        spent += seconds
        remaining = (cap_seconds - elapsed_s - spent) if cap_seconds > 0 else float("inf")
        nxt = min(seconds * 2, remaining)
        if nxt < seconds:
            graph.emit("decomposer.gave_up", root.id, reason="deadline", spent=spent, remaining=remaining)
            return out
        seconds = nxt
        graph.emit("decomposer.retried", root.id, reason="deadline", attempt=attempt, next_seconds=seconds)
    assert out is not None
    return out


# ------------------------------------------------------------------ the driver

Dispatch = Callable[[Development, int], Awaitable[RunReport]]
#: The cheap tier run after a revision's dispatch: ``(dev, report, dispatch) -> (dev, report)``.
CheapTier = Callable[[Development, RunReport, Dispatch], Awaitable[tuple[Development, RunReport]]]

#: Compile/typecheck/contract/shape repairs of a stated design per settle loop, by the
#: approver tier.  Bounded so a design that cannot be made to compile still ends up
#: back with the decomposer (which costs a round) rather than looping.
MAX_REPAIRS = 3


class DesignDriver:
    """One round counter, one evidence builder, one apply-adopt procedure -- for the
    initial design and for every revision (map-prove §7, smells 1-2)."""

    def __init__(
        self,
        cfg: ProveConfig,
        graph: Graph,
        root: Node,
        *,
        contract: Any,
        recorder: Any = None,
        preamble: str = "",
        design_brief: str = "",
        gate_factory: Callable[[Development], Gate] | None = None,
        pause: Any = None,
    ) -> None:
        self.cfg = cfg
        self.graph = graph
        self.root = root
        self.contract = contract
        self.recorder = recorder
        self.preamble = preamble
        self.design_brief = design_brief
        self.gate_factory = gate_factory or Gate
        #: The run's provider pause, handed to every ``Decomposer`` this driver builds.
        self.pause = pause
        #: Counted from the graph, so the bound holds across crash-resumes.
        self.rounds_used = design_rounds_used(graph, root)
        self.rounds: list[DecompositionResult] = []
        self.decomposition: DecompositionResult | None = None

    @property
    def active(self) -> bool:
        return self.cfg.decomposer_runner is not None and self.cfg.require_orchestration

    def decomposer(self, dev: Development) -> Decomposer:
        """The role object.  The approver (amendment verdicts, contest adjudication) is
        the decomposer's runner at a lower effort when the CLI built one; a run with
        only an approver configured still gets a ``Decomposer`` to adjudicate with."""
        approver = cast("Runner | None", self.cfg.approver_runner)  # typed `object` on ProveConfig by design
        runner = self.cfg.decomposer_runner or approver
        assert runner is not None, "no decomposer or approver runner configured"
        return Decomposer(
            runner, self.graph, dev, self.cfg.workroot, self.recorder,
            corpus=self.cfg.corpus, require_children=self.cfg.require_orchestration,
            approver=approver, pause=self.pause,
        )

    async def initial(self, dev: Development, *, elapsed_s: float = 0.0) -> Development:
        """Round 1: propose (with the deadline ladder), apply (with re-asks), adopt."""
        from pcp.orch.prove import DesignFailed, OrchestrationRequired

        if self.rounds_used >= self.cfg.max_design_rounds:
            raise OrchestrationRequired(
                f"no design was adopted and the design budget is spent ({self.rounds_used} of "
                f"{self.cfg.max_design_rounds} round(s) across runs); raise --design-rounds or start over with --fresh."
            )
        self.rounds_used += 1
        out = await decompose_with_retry(
            self.decomposer(dev), self.root, contract=self.contract, seconds=self.cfg.decomposer_seconds,
            cap_seconds=self.cfg.budget.seconds, elapsed_s=elapsed_s, graph=self.graph,
            design_brief=self.design_brief, library=self.cfg.library, brief_mode=self.cfg.brief,
            round_no=self.rounds_used,
        )
        self.decomposition = out
        if out.infrastructure or (not out.ok and self.rounds_used >= self.cfg.max_design_rounds):
            raise DesignFailed(
                "orchestration is required and no obligations were stated.\n" + out.render()
                + "\n\nSupply a plan with --plan, or configure a decomposer. A single "
                "prover taking the whole goal is not an orchestrated run."
            )
        settled = await self._settle(dev, out)
        if settled is None:
            last = self.rounds[-1] if self.rounds else out
            used = self.rounds_used
            raise DesignFailed(
                "no proposed design was usable, so nothing can be proved against one.\n" + last.render()
                + f"\n\nTried {used} of {self.cfg.max_design_rounds} design round(s)"
                + ("; raise --design-rounds to allow more." if used >= self.cfg.max_design_rounds
                   else ", stopping early because the decomposer could not run. The budget was not the limit.")
            )
        dev, proposal = settled
        adopt_proposal(self.cfg, self.graph, dev, self.root, proposal, round_no=self.rounds_used)
        return dev

    async def _settle(self, dev: Development, result: DecompositionResult) -> tuple[Development, PlanProposal] | None:
        """Apply ``result``; while it is rejected or fails to apply, re-ask with the
        checker's own words, each re-ask costing one design round.  ``None`` when the
        rounds ran out or the decomposer could not run."""
        current = result
        base: PlanProposal | None = None
        repairs = 0
        while True:
            if current.infrastructure:
                return None
            problem: str
            repairable = False
            if current.ok:
                assert current.proposal is not None
                proposal = current.proposal.merged_over(base)
                try:
                    new_dev = apply_design(
                        self.cfg, self.graph, dev, self.root, proposal, contract=self.contract,
                        round_no=current.round, workroot=self.cfg.workroot, preamble=self.preamble,
                    )
                    return new_dev, proposal
                except DesignError as exc:
                    problem = design_problem(exc, revised=current.round > 1)
                    current.problems.append(problem)
                    self.graph.emit("design.rejected", self.root.id, round=current.round, reason=str(exc)[:400])
                    base = proposal
                    repairable = True
            else:
                problem = current.render()
                if current.proposal is not None:
                    base = current.proposal.merged_over(base)
                # A shape problem (malformed entry, missing key, restated child, parse
                # violation) is a repair, not a redesign -- whether or not a proposal
                # could be read out of the reply.
                repairable = not current.deadline
            # The cheap tier: a design that was stated but does not compile / typecheck /
            # fit the contract, or arrived in the wrong shape, is REPAIRED by the approver
            # at medium effort without spending a design round (bounded).
            if repairable and repairs < MAX_REPAIRS and self.cfg.approver_runner is not None:
                repairs += 1
                self.graph.emit("design.repair", self.root.id, round=current.round, n=repairs, reason=problem[:300])
                current = await self.decomposer(dev).amend(
                    self.root, evidence=problem, round_no=current.round, budget_seconds=self.cfg.approver_seconds,
                    design=[d.text for d in base.definitions] if base is not None else None,
                    kind="design", contract=self.contract, base=base, repair=True,
                )
                self.rounds.append(current)
                continue
            if self.rounds_used >= self.cfg.max_design_rounds:
                return None
            self.rounds_used += 1
            current = await self.decomposer(dev).amend(
                self.root, evidence=problem, round_no=self.rounds_used, budget_seconds=self.cfg.decomposer_seconds,
                design=[d.text for d in base.definitions] if base is not None else None,
                kind="design", contract=self.contract, base=base,
            )
            self.rounds.append(current)
            if not current.ok:
                self.graph.emit("design.amendment_rejected", self.root.id, round=self.rounds_used, reason=current.render()[:400])

    async def revise(
        self, dev: Development, report: RunReport, dispatch: Dispatch, *, cheap_tier: CheapTier | None = None,
    ) -> tuple[Development, RunReport]:
        """Rounds 2..N while the proofs' failures could be the design's fault.

        ``cheap_tier`` runs after every revision's dispatch, before the next expensive
        round is considered: the amendment loop (requests applied, contests
        adjudicated, restatements adopted).  Without it a contest raised by a
        revision's own dispatch went straight to another decomposer round -- or, with
        the rounds spent, to the report unadjudicated (spec-only seqlock_wf, round 8).
        """
        reports = [report]
        view = RunReport.combined([report, standing_failures(self.graph, report, max_attempts=self.cfg.max_attempts)])
        while self.rounds_used < self.cfg.max_design_rounds and design_failed(view):
            self.rounds_used += 1
            amendment = await self.decomposer(dev).amend(
                self.root, evidence=design_evidence(view), round_no=self.rounds_used,
                budget_seconds=self.cfg.decomposer_seconds, kind="proofs", contract=self.contract,
                base=adopted_proposal(self.graph),
            )
            self.rounds.append(amendment)
            settled = await self._settle(dev, amendment)
            if settled is None:
                break
            dev, proposal = settled
            adopt_proposal(self.cfg, self.graph, dev, self.root, proposal, round_no=self.rounds_used)
            kept, reopened = revalidate(self.graph, dev, self.gate_factory(dev), self.root, preamble=self.preamble)
            refreshed = refresh_after_revision(self.graph, self.root)
            retried = reopen_incomplete(self.graph, max_attempts=self.cfg.max_attempts)
            self.graph.emit(
                "design.amended", self.root.id, round=self.rounds_used,
                kept=kept, reopened=reopened, refreshed=refreshed, retried=retried,
            )
            report = await dispatch(dev, self.rounds_used)
            if cheap_tier is not None:
                dev, report = await cheap_tier(dev, report, dispatch)
            reports.append(report)
            view = RunReport.combined([report, standing_failures(self.graph, report, max_attempts=self.cfg.max_attempts)])
        return dev, RunReport.combined(reports)


def elapsed_since(started: float) -> float:
    return time.perf_counter() - started


__all__ = [
    "DECOMPOSE_DEADLINE_RETRIES",
    "DesignDoesNotCompile",
    "DesignDriver",
    "DesignError",
    "DesignViolatesContract",
    "add_imports",
    "adopt_proposal",
    "apply_design",
    "blame_child",
    "decompose_with_retry",
    "design_dir",
    "design_evidence",
    "design_failed",
    "design_problem",
    "design_rounds_used",
    "granularity_verdict",
    "is_preamble_vernacular",
    "place_additions",
    "read_design_brief",
    "refresh_after_revision",
    "revalidate",
    "scan_child",
    "scan_fragment",
    "stage_spec_only",
    "staged_dir",
    "why_it_failed",
]
