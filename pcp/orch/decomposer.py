"""The decomposer role: states obligations, never proves them (PLAN.md 8.6, 8.2).

"Decomposers ... own the statements they created ... It proposes; sentinels and
auditors dispose."  And separately: "Provers ... return `qed / contested / stuck`:
never a partial edit, never a statement."

Those two sentences only mean something if the separation is *structural*.  Asking a
model to stay in its lane and then reading its output for tactics is not a
separation; it is a review, performed by the same kind of thing that would have
violated it.  So the split is enforced three ways, none of which is a prompt:

1. **Capability.**  The decomposer's runner is granted `Read`/`Glob`/`Grep` and
   nothing else -- no `Write`, no `Edit`, no `Bash`.  It cannot create a file, run
   `coqc`, or invoke `pcp check`, so it cannot do proof engineering even if asked.
2. **Type.**  Its answer is parsed into :class:`PlanProposal`, which has no field a
   proof body could travel in, and every statement passes ``assert_statement_only``.
3. **Store.**  ``Graph.record_proof`` refuses any role but ``prover``, so a proof
   that somehow reached this far still could not be written down.
"""

from __future__ import annotations

import json
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from pcp.orch.assemble import Development
from pcp.orch.decompose import (
    PlanProposal,
    ProofEngineeringAttempt,
    parse_proposal,
    validate_proposal,
)
from pcp.core.vernac import parse_blocks
from pcp.orch.graph import Graph, Node
from pcp.orch.runners.base import NodePayload

#: The decomposer's whole toolbox.  Read-only by construction.
DECOMPOSER_TOOLS = "Read,Glob,Grep"

TASK_FILE = "DECOMPOSE.md"
ANSWER_FILE = "plan.json"


@dataclass
class DecompositionResult:
    proposal: PlanProposal | None = None
    problems: list[str] = field(default_factory=list)
    violation: str = ""
    raw: str = ""
    elapsed_s: float = 0.0
    cost: dict[str, Any] = field(default_factory=dict)
    #: The model that actually produced this, resolved rather than labelled.
    model: str = ""
    trace: dict[str, Any] = field(default_factory=dict)
    #: The provider or its CLI failed -- an outage, a revoked credential, a missing
    #: binary. Not a decomposition failure, and not something a retry will fix.
    infrastructure: bool = False

    @property
    def ok(self) -> bool:
        return self.proposal is not None and not self.problems and not self.violation

    def render(self) -> str:
        if self.infrastructure:
            return (
                "the decomposer could not run at all -- this is a provider or CLI "
                f"failure, not a decomposition failure:\n  {self.violation}"
            )
        if self.violation:
            return f"decomposition rejected: {self.violation}"
        if self.problems:
            return "decomposition rejected:\n" + "\n".join(f"  · {p}" for p in self.problems)
        assert self.proposal is not None
        lines = [f"plan: {len(self.proposal.children)} obligation(s)"]
        for child in self.proposal.children:
            lines.append(f"  {child.name}: {' '.join(child.statement.split())[:100]}")
        return "\n".join(lines)


def blank_predicates(dev: Development) -> list[str]:
    """Definitions the corpus left as `True` -- the design that was withheld."""
    out: list[str] = []
    for block in parse_blocks(dev.source):
        if block.head != "Definition":
            continue
        line = dev.source[block.statement_start : block.statement_end]
        if line.rstrip().endswith(":= True%I.") or line.rstrip().endswith(":= True."):
            out.append(block.name)
    return out


def render_decomposition_task(
    node: Node, dev: Development, *, context: str = "", contract: object | None = None,
    library: list[Path] | None = None,
) -> str:
    """The decomposer's packet.  Notice what is absent: any way to check a proof."""
    blanks = blank_predicates(dev)
    parts: list[str] = []
    parts.append(f"# Decompose `{node.name}`\n")
    parts.append(
        "You are the **decomposer**. Your job is to state the obligations this goal "
        "should be broken into. You are not proving anything, and you have no tools "
        "for it: you can read files, and that is all.\n"
    )
    parts.append("## The goal\n")
    parts.append(f"```coq\n{node.statement.strip()}\n```\n")
    if node.intent:
        parts.append("## Why it exists\n")
        parts.append(node.intent.strip() + "\n")
    parts.append("## The development\n")
    parts.append(f"`{dev.path}` — read it. What is already defined and proved there is yours to use.\n")
    if context:
        parts.append(context.strip() + "\n")

    if blanks:
        parts.append("## The design is missing, and designing it is your job\n")
        parts.append(
            "These predicates are defined as `True`, which makes the specifications "
            "unprovable as they stand: "
            + ", ".join(f"`{b}`" for b in blanks)
            + ".\n\nDecide what the client owns, what invariant protects the data "
            "structure, and what ghost state connects them. Return them in "
            "`definitions` below. Anything that is not a proof is fair game there: "
            "resource algebras, typeclass fields, notations, scopes, and the "
            "`Require` lines your ghost state needs -- they are placed for you. You "
            "may not change the program or any specification: those are the "
            "theorem.\n"
        )
    else:
        # Saying nothing here read as permission.  On a rung whose design is given,
        # the decomposer's first move was to rewrite the invariant and the ghost
        # predicate -- reasonable-looking work that the contract then refused, at the
        # cost of the whole round.  The absence of a "design it" section is not the
        # same as the presence of a "it is already designed" one.
        parts.append("## The design is already there\n")
        parts.append(
            "The invariant, the ghost state and the client-facing predicates in this "
            "development are **given**, and they are frozen. Do not restate them and "
            "do not return them in `definitions` -- a design that rewrites one is "
            "rejected before any proof is attempted.\n\n"
            "What you may add is genuinely new: a helper predicate, a resource algebra, "
            "a `Require` line your obligations need. Additions are placed for you. Your "
            "actual job on this rung is the **decomposition** -- which obligations the "
            "proof of this goal breaks into, stated in the vocabulary that is already "
            "on the page.\n"
        )

    if contract is not None:
        parts.append("## What you may and may not change\n")
        parts.append(
            f"{contract.describe()}\n\nThis is checked mechanically before your "
            "design is accepted, so read it as a hard boundary rather than advice.\n"
        )

    if library:
        from pcp.orch.packet import render_library

        # The decomposer, not the prover, is the one that has to invent a design, so
        # it is the one a previous rung's design is worth most to.
        parts.append(render_library(library))

    parts.append("## What makes a good decomposition\n")
    parts.append(
        "- Every child must be **used** by the proof of the parent. A child nothing "
        "needs cannot enter the graph.\n"
        "- Children are dispatched **in parallel**, immediately, each to its own "
        "prover, with the others available as admitted stubs. So prefer several "
        "independent obligations to a deep chain.\n"
        "- State them in the development's own vocabulary, using the definitions "
        "that are already there.\n"
        "- **Every obligation must be tightly scoped proof engineering**: one "
        "self-contained step that a competent prover can carry out from the statement "
        "alone, without re-deriving your design and without discovering a second hard "
        "idea on the way. If stating an obligation requires you to explain a strategy "
        "for it, it is not one obligation.\n"
        "- **Prefer more, smaller obligations.** Measured across this ladder, the "
        "share of obligations that get proved falls off sharply with their size: at "
        "roughly a dozen tactics' worth of work each they nearly all land, at ~35 "
        "they still do, and by the time an obligation is worth a few hundred tactics "
        "only about half are proved. If you would expect an obligation to take more "
        "than about fifty tactics, it is probably two obligations. Splitting costs "
        "you one extra statement; not splitting costs a prover its whole budget.\n"
        "- A child that just restates the parent is not progress and is rejected "
        "automatically.\n"
    )

    parts.append("## Answer\n")
    parts.append(f"Write `{ANSWER_FILE}`… you cannot: you have no write tool. Reply with JSON:\n")
    parts.append(
        "```json\n"
        + json.dumps(
            {
                "rationale": "one or two lines on why this split",
                "definitions": [
                    {
                        "name": "",
                        "text": "From <library> Require Import <module>.",
                        "rationale": "an import your design needs -- an import has no name",
                    },
                    {
                        "name": "definition_name",
                        "text": "Definition definition_name (γ : gname) (P : iProp Σ) : iProp Σ := P.",
                        "rationale": "what this definition is for",
                    }
                ],
                "children": [
                    {
                        "name": "helper_lemma_name",
                        "statement": "Lemma helper_lemma_name (P : iProp Σ) : P -∗ P.",
                        "rationale": "what this buys the parent",
                    }
                ],
                "glue_rationale": "how the parent follows from the children",
            },
            indent=2,
        )
        + "\n```\n"
    )
    parts.append(
        "Each `definitions[].text` is one complete `Definition`/`Class`/`Notation` "
        "sentence. Each `statement` is exactly one `Lemma … .` sentence and "
        "**nothing else**. "
        "No `Proof.`, no tactics, no `Qed.` A statement carrying proof text is "
        "rejected outright and the decomposition is discarded — that is a role "
        "violation, not a formatting slip.\n"
    )
    return "\n".join(parts)


def render_amendment_task(
    node: Node, dev: Development, *, design: list[str], evidence: str, round_no: int
) -> str:
    """Ask for a *revision* of the design, given where it failed.

    An invariant fails in two directions and each looks different from the proof
    (`skills/invariants.md`): too strong and some step cannot restore it before
    closing, so the proof dies at an `iInv` close site; too weak and opening it does
    not yield what the use site needs, so it dies at the open site.  The evidence
    below is the only reliable way to tell which happened, which is why the design is
    revised *from* it rather than from first principles again.
    """
    parts: list[str] = []
    parts.append(f"# Revise the design for `{node.name}` (round {round_no})\n")
    parts.append(
        "Your previous design did not carry the proofs. You are still the "
        "decomposer: revise the design, do not attempt the proofs. You have no "
        "tools for them.\n"
    )
    parts.append("## Your current design\n")
    for text in design:
        parts.append("```coq\n" + text.strip() + "\n```\n")
    parts.append("## What happened\n")
    parts.append("```\n" + evidence.strip()[:6000] + "\n```\n")
    parts.append("## How to read that\n")
    parts.append(
        "- An obligation **no prover finished** is first evidence that it was not "
        "tightly scoped: split it into smaller obligations before you touch the "
        "design. A prover that ran out of clock, or two provers that failed the same "
        "way, are telling you about the statement you wrote, not about themselves.\n"
        "- A proof that dies **closing** an invariant usually means it is too "
        "**strong**: some step cannot restore it.\n"
        "- A proof that dies just after **opening** one usually means it is too "
        "**weak**: it does not yield what the use site needs.\n"
        "- A missing ghost resource means the ghost-state plan is incomplete, not "
        "that the invariant is wrong.\n"
    )
    if blank_predicates(dev):
        parts.append(
            "\nReturn the **same JSON shape as before**: `definitions` (the revised "
            "design, complete -- every definition you want, not a diff) and optionally "
            "`children`. A definition you omit keeps its current form. You may not "
            "change the program or any specification.\n"
        )
    else:
        # There is no design of yours to revise on this rung -- it was given. Asking
        # for one anyway spends a round of an expensive model producing something the
        # contract will refuse.
        parts.append(
            "\n**The invariant and the ghost state here are given and frozen**, so the "
            "revision cannot be to them. Return the same JSON shape as before, and put "
            "the work in `children`: different obligations, or additional ones, that "
            "reach the goal by another route. `definitions` is for genuinely new "
            "helpers only -- a definition already on the page may not be restated, and "
            "a design that restates one is rejected before any proof is attempted.\n"
        )
    return "\n".join(parts)


class Decomposer:
    """Runs one decomposition attempt under the statement-only contract."""

    role = "decomposer"

    def __init__(
        self,
        graph: Graph,
        dev: Development,
        runner: Any,
        *,
        workroot: Path,
        recorder: Any = None,
        corpus: str = "",
        library: Any = (),
    ) -> None:
        self.graph = graph
        self.dev = dev
        self.runner = runner
        self.workroot = Path(workroot)
        self.recorder = recorder
        self.corpus = corpus
        self.library = [Path(p) for p in library]

    def _already_proved(self, proposal: Any) -> list[str]:
        return _already_proved(self.dev, proposal)

    async def amend(
        self,
        node: Node,
        *,
        design: list[str],
        evidence: str,
        round_no: int,
        budget_seconds: float = 900.0,
    ) -> DecompositionResult:
        """One revision of the design, driven by the failure evidence."""
        return await self._run(
            node,
            render_amendment_task(node, self.dev, design=design, evidence=evidence, round_no=round_no),
            suffix=f"amend{round_no}",
            budget_seconds=budget_seconds,
        )

    async def propose(
        self, node: Node, *, budget_seconds: float = 900.0, context: str = "",
        contract: object | None = None,
    ) -> DecompositionResult:
        return await self._run(
            node,
            render_decomposition_task(node, self.dev, context=context, contract=contract,
                                      library=self.library),
            suffix="decompose",
            budget_seconds=budget_seconds,
        )

    async def _run(self, node: Node, task: str, *, suffix: str, budget_seconds: float) -> DecompositionResult:
        started = time.perf_counter()
        workdir = self.workroot / f"{node.id}.{suffix}"
        workdir.mkdir(parents=True, exist_ok=True)
        (workdir / TASK_FILE).write_text(task, encoding="utf-8")
        # The runner reads its prompt from TASK.md; give it the same name so no
        # runner needs to know this is a different kind of job.
        (workdir / "TASK.md").write_text(task, encoding="utf-8")

        attempt = self.graph.start_attempt(
            node.id, runner=getattr(self.runner, "name", "?"), owner="decomposer", role=self.role
        )
        payload = NodePayload(
            node_id=node.id,
            name=node.name,
            statement=node.statement,
            file=str(self.dev.path),
            workdir=workdir,
            budget_seconds=budget_seconds,
        )
        result = await self.runner.run_node(payload)
        text = (result.trace or {}).get("final_text") or result.raw or result.proof or ""

        out = DecompositionResult(
            raw=text[-8000:],
            elapsed_s=time.perf_counter() - started,
            cost=result.cost,
            model=str((result.trace or {}).get("model", "")),
            trace=result.trace or {},
        )
        # A runner that failed has already said why, and its reason outranks anything
        # the parser can infer from the silence that follows.  Parsing regardless
        # reported a decomposer killed at its deadline as "produced no JSON object to
        # read" -- which reads as the model ignoring the protocol, and sends you to
        # rewrite the prompt instead of raising the budget.
        if not text.strip() and result.status != "qed":
            out.violation = result.evidence or (
                f"the decomposer runner returned {result.status!r} and no output"
            )
            self.graph.emit("decomposer.failed", node.id, detail=out.violation[:400],
                            status=result.status, model=out.model)
            self.graph.finish_attempt(attempt, status="error", evidence=out.violation,
                                      model=out.model, cost=out.cost)
            self._record(node, out, workdir, suffix)
            return out
        # A revoked credential arrives as prose on stdout, so the JSON parser called it
        # "the decomposer produced no JSON object to read" -- true, and it sends you to
        # rewrite the prompt when the run could not reach the provider at all. Two
        # ladder rungs died this way in under a minute each, mid-run.
        broken = _infrastructure_failure(text, result)
        if broken:
            out.violation = broken
            out.infrastructure = True
            self.graph.emit("decomposer.failed", node.id, detail=broken[:400],
                            status=result.status, model=out.model, infrastructure=True)
            self.graph.finish_attempt(attempt, status="error", evidence=broken,
                                      model=out.model, cost=out.cost)
            self._record(node, out, workdir, suffix)
            return out
        try:
            proposal = parse_proposal(text)
        except ProofEngineeringAttempt as exc:
            out.violation = str(exc)
            self.graph.emit("decomposer.violation", node.id, detail=str(exc)[:400], model=out.model)
            self.graph.finish_attempt(attempt, status="error", evidence=str(exc), model=out.model)
            self._record(node, out, workdir, suffix)
            return out
        out.proposal = proposal
        out.problems = validate_proposal(proposal) + self._already_proved(proposal)
        self.graph.finish_attempt(
            attempt,
            status="qed" if out.ok else "stuck",
            evidence="; ".join(out.problems) or out.violation,
            model=out.model,
            cost=out.cost,
            # Deliberately no `body=`: a decomposition attempt has no proof to record.
        )
        self._record(node, out, workdir, suffix)
        return out

    def _record(self, node: Node, out: "DecompositionResult", workdir: Path, suffix: str) -> None:
        """Persist the decomposition next to the prover attempts.

        It was previously the only step in the pipeline that left no durable record,
        which is how a run reached the point of "which model designed this?" with no
        answer available.
        """
        if self.recorder is None:
            return
        from pcp.orch.record import AttemptRecord

        self.recorder.write(
            AttemptRecord(
                run_id=self.recorder.run_id,
                node=node.id,
                lemma=f"{node.name}.{suffix}",
                attempt=1,
                runner=f"{getattr(self.runner, 'name', '?')} [{out.model or 'unknown model'}]",
                status="qed" if out.ok else ("error" if out.violation else "stuck"),
                solved=out.ok,
                elapsed_s=out.elapsed_s,
                cost=out.cost,
                evidence=out.violation or "; ".join(out.problems),
                proof="",
                corpus=self.corpus,
                trace=out.trace,
            ),
            workdir=workdir,
            transcript=out.raw,
        )


def _already_proved(dev: Development, proposal: Any) -> list[str]:
    """Reject a child that names something the development already declares.

    The decomposer is told "what is already defined and proved there is yours to
    use", and naming such a lemma as an *obligation* is the opposite: the harness
    freezes a second declaration under the same name, dispatches a worker to prove
    what is already proved, and assembly then emits the name twice so the file stops
    compiling. One rwcas round did this three times over (`cd19`, `f17_update`,
    `bfd18_agree`); the worker sent to re-prove `cd19` spent two attempts working out
    that its lemma was sitting proved forty lines above the anchor.
    """
    existing = {b.name for b in parse_blocks(dev.source) if b.name}
    clashes = [c.name for c in getattr(proposal, "children", ()) if c.name in existing]
    return [
        f"child {name!r} is already declared in the development -- use it, do not "
        "restate it as an obligation"
        for name in clashes
    ]


def _infrastructure_failure(text: str, result: Any) -> str:
    """The provider's own failure text, when that is what came back instead of JSON.

    Only fires when there is no JSON at all to read: a design that happens to mention
    a rate limit in its prose is a design, not an outage.
    """
    from pcp.orch.decompose import _extract_json
    from pcp.orch.failures import classify

    if not text.strip() or _extract_json(text) is not None:
        return ""
    if classify(text, status=getattr(result, "status", "")).primary != "runner-error":
        return ""
    return " ".join(text.split())[:300]


def decomposer_runner(
    model: str | None = None, *, sandbox_factory: Any = None, effort: str | None = None
) -> Any:
    """A CLI runner that *cannot* write, edit, or execute anything."""
    from pcp.orch.runners.cli import claude_headless_runner

    runner = claude_headless_runner(model, allowed_tools=DECOMPOSER_TOOLS, effort=effort)
    if sandbox_factory is not None:
        from pcp.orch.runners.sandbox import SandboxedRunner

        return SandboxedRunner(inner=runner, sandbox_factory=sandbox_factory)
    return runner
