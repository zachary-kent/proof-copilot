"""The decomposer role: states obligations, never proves them (PLAN.md 8.2, 8.6).

"It proposes; sentinels and auditors dispose."  The separation is *structural*,
enforced three ways and none of them a prompt:

1. **Capability.**  Its runner is ``claude -p`` with ``Read Glob Grep`` and nothing
   else (:func:`pcp.orch.runners.base.decomposer_runner`): no ``Write``, no ``Edit``,
   no ``Bash``, so no ``coqc`` and no ``pcp check``.
2. **Type.**  Its answer is parsed into :class:`PlanProposal`, which has no field a
   proof body could travel in, and every child, definition and import passes
   :func:`assert_statement_only` at construction.
3. **Store.**  ``Graph.record_proof`` refuses any role but ``prover``; a decomposition
   attempt is finished without ``body=`` by construction.

The proposal parser is tolerant on purpose (each tolerance was bought with a lost
15-90 minute design round) and the *failure triage* is ordered: the runner's own
verdict outranks the parser's silence, an outage is detected before "no JSON", a
deadline is a deadline even when the stream carried text, and a protocol violation
is distinct from a structural problem.

The same role, at a lower effort, is the **approver** (PLAN.md 8.5, 8.9): a
prover's one-conjunct amendment request and a ``contested`` statement are each
adjudicated in one short round whose answer is a :class:`Verdict` -- a type with
room for a replacement *definition* and none for a proof, screened by the same
:func:`assert_statement_only`.  ``contested -> open`` is a human-only move in the
lattice; the approver is the human's delegate producing the verdict that move is
made on, and the graph still records the move under ``role="human"``.
"""

from __future__ import annotations

import asyncio
import json
import time
from collections.abc import Iterator, Sequence
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import TYPE_CHECKING, Any

from pcp.errors import ProtocolError
from pcp.orch.graph import Graph
from pcp.orch.model import Node
from pcp.orch.packet import render_library
from pcp.orch.protocol import NodePayload, NodeResult, Runner
from pcp.orch.runners.base import decomposer_runner
from pcp.orch.sentinels import SentinelReport, body_hash, run_free_sentinels
from pcp.rocq.assemble import Development
from pcp.rocq.body import ALLOWED_VERNAC, WRAPPERS
from pcp.rocq.decls import DECL_HEADS, PROOF_ENDERS, parse_blocks
from pcp.rocq.lexer import first_word, identifiers, split_sentences, strip_comments
from pcp.rocq.statement import statement_hash
from pcp.util.io import atomic_write_text, ensure_dir

if TYPE_CHECKING:
    from pcp.orch.protocol import AmendmentRequest

__all__ = [
    "AMENDMENT_VERDICTS",
    "ANSWER_FILE",
    "CONTEST_VERDICTS",
    "DECOMPOSE_FILE",
    "ChildStatement",
    "DecompositionResult",
    "Decomposer",
    "DesignDefinition",
    "PlanProposal",
    "ProofEngineeringAttempt",
    "Verdict",
    "already_declared",
    "assert_statement_only",
    "blank_predicates",
    "decomposer_runner",
    "extract_json",
    "json_in_stream",
    "parse_proposal",
    "parse_verdict",
    "render_amendment_adjudication",
    "render_amendment_task",
    "render_contest_adjudication",
    "render_decomposition_task",
    "validate_proposal",
]

DECOMPOSE_FILE = "DECOMPOSE.md"
ANSWER_FILE = "plan.json"
RAW_KEPT = 8000
EVIDENCE_SHOWN = 6000
#: Past the round's clock, a runner that has not returned is cancelled by the role
#: itself (the same backstop the scheduler keeps for provers).
DEADLINE_GRACE_S = 30.0

STATEMENT_HEADS: tuple[str, ...] = (
    "Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark", "Property", "Example",
)
#: Heads that declare an *obligation*; a design fragment may not contain one.
OBLIGATION_HEADS: tuple[str, ...] = ("Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark")
#: What an amendment prompt shows as "your current design".
DESIGN_HEADS: frozenset[str] = frozenset({
    "Definition", "Fixpoint", "CoFixpoint", "Class", "Record", "Structure", "Inductive",
    "CoInductive", "Variant", "Notation", "Instance", "Canonical", "Let", "Ltac",
})
_MODIFIERS = frozenset({
    "Local", "Global", "Program", "Polymorphic", "Monomorphic", "Cumulative", "NonCumulative",
    "Private", "Export",
})
_PROPOSAL_KEYS = ("children", "definitions", "imports", "rationale", "glue_rationale")
_VERDICT_KEYS = ("verdict",)


class ProofEngineeringAttempt(ProtocolError):
    """A decomposer tried to do proof engineering, or answered outside the protocol.

    Not a style violation -- a role violation: the moment a decomposer writes tactics,
    nothing downstream can tell a proved lemma from one whose "proof" was hallucinated
    by the model that stated it.  The whole proposal is discarded.
    """


# ------------------------------------------------------------------ the statement-only screen


def assert_statement_only(text: str, *, what: str = "proposal") -> None:
    """Reject anything that is a proof rather than a statement -- by construction.

    A statement is vernacular: every sentence begins with a capitalised command
    head.  A tactic sentence never does (``iIntros``, ``wp_load``, ``intros`` ...),
    a bullet or brace is not a sentence a statement has, and ``Proof``, the enders and
    ``Obligation`` are the proof's own vernacular.  Queries (``Check``, ``Search``)
    are not statements either.  ``admit``/``give_up`` anywhere are proof text.
    """
    code = strip_comments(text or "")
    for sent in split_sentences(code):
        c = sent.code
        if not c.strip():
            continue
        if sent.is_bullet or sent.is_brace:
            raise ProofEngineeringAttempt(_violation(what, "a proof bullet or brace", c))
        head = first_word(c)
        words = identifiers(c)
        if "admit" in words or "give_up" in words:
            raise ProofEngineeringAttempt(_violation(what, "proof text", c))
        if not head or not head[0].isupper():
            raise ProofEngineeringAttempt(_violation(what, "a tactic", c))
        i = 0
        while i < len(words) and words[i] in _MODIFIERS:
            i += 1
        bare = words[i] if i < len(words) else head
        if bare == "Proof" or bare in PROOF_ENDERS:
            raise ProofEngineeringAttempt(_violation(what, "proof text", c))
        if bare == "Obligation" or (bare == "Next" and i + 1 < len(words) and words[i + 1] == "Obligation"):
            raise ProofEngineeringAttempt(_violation(what, "an obligation script", c))
        if bare in ALLOWED_VERNAC or bare in WRAPPERS or bare == "Print":
            raise ProofEngineeringAttempt(_violation(what, "a query, not a statement", c))


def _violation(what: str, kind: str, code: str) -> str:
    shown = " ".join(code.split())[:60]
    return f"{what} contains {kind} ({shown!r}). A decomposer states obligations; it does not prove them."


# ------------------------------------------------------------------ the proposal type


@dataclass(frozen=True)
class ChildStatement:
    """One proposed obligation.  There is deliberately nowhere to put a proof."""

    name: str
    statement: str
    rationale: str = ""

    def __post_init__(self) -> None:
        assert_statement_only(self.statement, what=f"child {self.name!r}")

    def to_json(self) -> dict[str, str]:
        return {"name": self.name, "statement": self.statement, "rationale": self.rationale}


@dataclass(frozen=True)
class DesignDefinition:
    """A piece of design: any non-proof vernacular.  The contract decides what is allowed."""

    name: str = ""
    text: str = ""
    rationale: str = ""

    def __post_init__(self) -> None:
        assert_statement_only(self.text, what=f"design {self.name or 'fragment'!r}")

    def to_json(self) -> dict[str, str]:
        return {"name": self.name, "text": self.text, "rationale": self.rationale}


@dataclass(frozen=True)
class PlanProposal:
    """A decomposer's output.  The type is the enforcement: no proof-bearing field."""

    children: tuple[ChildStatement, ...] = ()
    definitions: tuple[DesignDefinition, ...] = ()
    imports: tuple[str, ...] = ()
    glue_rationale: str = ""
    rationale: str = ""

    def names(self) -> list[str]:
        return [c.name for c in self.children]

    def definition_names(self) -> list[str]:
        return [d.name for d in self.definitions if d.name]

    @property
    def changes_design(self) -> bool:
        return bool(self.definitions or self.imports)

    def to_json(self) -> dict[str, Any]:
        return {
            "rationale": self.rationale,
            "definitions": [d.to_json() for d in self.definitions],
            "imports": list(self.imports),
            "children": [c.to_json() for c in self.children],
            "glue_rationale": self.glue_rationale,
        }

    @classmethod
    def from_json(cls, data: dict[str, Any]) -> PlanProposal:
        return parse_payload(data)

    def merged_over(self, base: PlanProposal | None) -> PlanProposal:
        """This proposal on top of ``base``: a revision that omits a definition keeps
        the previous one (as the prompt promises), imports accumulate, and children
        are replaced only when the revision states any."""
        if base is None:
            return self
        defs: dict[str, DesignDefinition] = {}
        unnamed: list[DesignDefinition] = []
        for d in (*base.definitions, *self.definitions):
            if d.name:
                defs[d.name] = d
            elif all(" ".join(u.text.split()) != " ".join(d.text.split()) for u in unnamed):
                unnamed.append(d)
        imports = list(base.imports) + [i for i in self.imports if i not in base.imports]
        return PlanProposal(
            children=self.children or base.children,
            definitions=(*unnamed, *defs.values()),
            imports=tuple(imports),
            glue_rationale=self.glue_rationale or base.glue_rationale,
            rationale=self.rationale or base.rationale,
        )


# ------------------------------------------------------------------ parsing


def extract_json(text: str, *, keys: Sequence[str] = _PROPOSAL_KEYS) -> dict[str, Any] | None:
    """The answer object in a reply: a fenced ``json`` block first, else the first
    balanced ``{...}`` that parses *and looks like an answer* (carries one of
    ``keys`` -- a proposal's by default, ``("verdict",)`` for an adjudication).

    Braces inside strings are skipped, so an Iris triple ``{{{ P }}} e {{{ Q }}}``
    quoted in prose no longer desynchronises the scan; and a stream event or a
    stray object in prose is passed over because it carries none of the answer's
    keys.
    """
    text = text or ""
    for body in _fenced_json(text):
        found = _first_object(body, require_keys=False, keys=keys)
        if found is not None:
            return found
    return _first_object(text, require_keys=True, keys=keys)


def _fenced_json(text: str) -> list[str]:
    out: list[str] = []
    i = 0
    while True:
        start = text.find("```", i)
        if start < 0:
            return out
        nl = text.find("\n", start)
        if nl < 0:
            return out
        lang = text[start + 3 : nl].strip().lower()
        end = text.find("```", nl + 1)
        if end < 0:
            return out
        if lang in ("", "json"):
            out.append(text[nl + 1 : end])
        i = end + 3


def json_in_stream(raw: str, *, keys: Sequence[str] = _PROPOSAL_KEYS) -> dict[str, Any] | None:
    """A proposal stated in an *earlier* assistant turn of a stream-json transcript.

    The stream parser keeps only the final text, so a decomposer that stated its
    plan and then said "Done." was rejected as "produced no JSON object" and lost
    the round.  Only assistant text is searched -- never tool results, which quote
    the packet's own JSON template -- and the newest plan wins.
    """
    found: dict[str, Any] | None = None
    for line in (raw or "").splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(event, dict):
            continue
        for text in _assistant_texts(event):
            candidate = extract_json(text, keys=keys)
            if candidate is not None:
                found = candidate
    return found


def _assistant_texts(event: dict[str, Any]) -> Iterator[str]:
    """The model's own words in one stream event (claude ``assistant`` / codex ``agent_message``)."""
    if event.get("type") == "assistant":
        for block in (event.get("message") or {}).get("content") or []:
            if isinstance(block, dict) and block.get("type") == "text":
                yield str(block.get("text") or "")
    elif event.get("type") == "item.completed":
        item = event.get("item") or {}
        if isinstance(item, dict) and item.get("type") == "agent_message":
            yield str(item.get("text") or "")


def _first_object(text: str, *, require_keys: bool, keys: Sequence[str] = _PROPOSAL_KEYS) -> dict[str, Any] | None:
    pos = 0
    while True:
        start = text.find("{", pos)
        if start < 0:
            return None
        end = _balanced_end(text, start)
        if end is None:
            return None
        candidate = text[start : end + 1]
        try:
            value = json.loads(candidate)
        except json.JSONDecodeError:
            pos = start + 1
            continue
        if isinstance(value, dict) and (not require_keys or any(k in value for k in keys)):
            return value
        pos = end + 1


def _balanced_end(text: str, start: int) -> int | None:
    depth = 0
    in_string = False
    i, n = start, len(text)
    while i < n:
        ch = text[i]
        if in_string:
            if ch == "\\":
                i += 2
                continue
            if ch == '"':
                in_string = False
        elif ch == '"':
            in_string = True
        elif ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return None


def _is_identifier(name: str) -> bool:
    return bool(name) and (name[0].isalpha() or name[0] == "_") and all(c.isalnum() or c in "_'" for c in name)


def declared_name(text: str) -> str:
    """The name a sentence declares, or ``""`` (imports and ``Context`` are nameless)."""
    try:
        return next((b.name for b in parse_blocks(text) if b.name), "") or ""
    except Exception:  # noqa: BLE001 -- unparseable text declares nothing
        return ""


def as_declaration(name: str, statement: str) -> str:
    """Give a child's statement its ``Lemma <name> : ... .`` header if it lacks one, and
    its terminating ``.`` if it lacks that.  Never renames: a statement that declares
    something else is left for :func:`validate_proposal` to refuse."""
    text = (statement or "").strip()
    if not text:
        return text
    if declared_name(text):
        return text if text.endswith(".") else text + "."
    body = text[:-1].rstrip() if text.endswith(".") else text
    return f"Lemma {name} :\n  {body}."


CHILD_STATEMENT_KEYS: tuple[str, ...] = ("statement", "text", "lemma", "declaration", "coq", "code", "rocq")
#: `text` is the documented key; round 4 of the spec-only seqlock_wf run wrote `coq` and
#: lost the round to it.  Synonyms are cheaper than a 20-minute design round.
DEFINITION_TEXT_KEYS: tuple[str, ...] = ("text", "definition", "statement", "coq", "code", "rocq", "sentence", "body")
#: Keys that never hold the Rocq text of an entry.
_ENTRY_META_KEYS: frozenset[str] = frozenset({"name", "rationale", "why", "notes", "note", "reason", "comment", "kind"})


def _entry_text(entry: dict[str, Any], keys: tuple[str, ...]) -> str:
    """The Rocq sentence of a proposal entry: a documented key first, else any other
    string field that reads as vernacular (round 7 of the spec-only seqlock_wf run wrote
    `statement` for a definition; a synonym must never cost a 17-minute round)."""
    for k in keys:
        value = entry.get(k)
        if isinstance(value, str) and value.strip():
            return value.strip()
    for k, value in entry.items():
        if k in _ENTRY_META_KEYS or not isinstance(value, str) or not value.strip():
            continue
        head = first_word(value.strip())
        if head and head[0].isupper() and head in DECL_HEADS | {"From", "Require", "Import", "Export", "Open", "Close", "Set", "Unset", "Declare", "Global", "Local"}:
            return value.strip()
    return ""


def parse_payload(payload: dict[str, Any]) -> PlanProposal:
    raw_children = payload.get("children") or []
    if not isinstance(raw_children, list):
        raise ProofEngineeringAttempt("`children` must be a list of statements")
    children: list[ChildStatement] = []
    for entry in raw_children:
        if not isinstance(entry, dict):
            raise ProofEngineeringAttempt("each child must be an object with name and statement")
        name = str(entry.get("name", "")).strip()
        # `statement` is the documented key; a model that wrote `text` for its
        # definitions tends to write `text` here too, and a whole design round is
        # too expensive to lose to a synonym.
        statement = _entry_text(entry, CHILD_STATEMENT_KEYS)
        if not _is_identifier(name):
            raise ProofEngineeringAttempt(f"child name {name!r} is not a Rocq identifier")
        if not statement:
            raise ProofEngineeringAttempt(
                f"child {name!r} has no statement (expected a `statement` key holding one `Lemma … .` sentence)"
            )
        children.append(ChildStatement(name, as_declaration(name, statement), str(entry.get("rationale", "") or "")))
    raw_defs = payload.get("definitions") or []
    if not isinstance(raw_defs, list):
        raise ProofEngineeringAttempt("`definitions` must be a list")
    definitions: list[DesignDefinition] = []
    for entry in raw_defs:
        if isinstance(entry, str):
            entry = {"text": entry}  # a bare sentence is the same design said less carefully
        if not isinstance(entry, dict):
            raise ProofEngineeringAttempt("each definition must be an object, or a single Rocq sentence")
        name = str(entry.get("name", "") or "").strip()
        text = _entry_text(entry, DEFINITION_TEXT_KEYS)
        if not text:
            raise ProofEngineeringAttempt(
                f"design entry {name or '<unnamed>'!r} has no text (expected a `text` key holding one complete sentence)"
            )
        if not name:
            name = declared_name(text)
        if name and not _is_identifier(name):
            raise ProofEngineeringAttempt(f"design name {name!r} is not an identifier")
        definitions.append(DesignDefinition(name, text, str(entry.get("rationale", "") or "")))
    raw_imports = payload.get("imports") or []
    if isinstance(raw_imports, str):
        raw_imports = [raw_imports]
    if not isinstance(raw_imports, list):
        raise ProofEngineeringAttempt("`imports` must be a list of Require lines")
    imports: list[str] = []
    for entry in raw_imports:
        line = str(entry).strip()
        if not line:
            continue
        words = identifiers(line)
        if not (first_word(line) == "Require" or (first_word(line) == "From" and "Require" in words)):
            raise ProofEngineeringAttempt(f"import {line!r} is not a Require line")
        assert_statement_only(line, what="import")
        imports.append(line if line.endswith(".") else line + ".")
    return PlanProposal(
        children=tuple(children),
        definitions=tuple(definitions),
        imports=tuple(imports),
        glue_rationale=str(payload.get("glue_rationale", "") or ""),
        rationale=str(payload.get("rationale", "") or ""),
    )


def parse_proposal(text: str) -> PlanProposal:
    """Read a decomposer's reply, rejecting proof content deterministically."""
    payload = extract_json(text)
    if payload is None:
        raise ProofEngineeringAttempt("the decomposer produced no JSON object to read")
    return parse_payload(payload)


def validate_proposal(proposal: PlanProposal, *, require_children: bool = True) -> list[str]:
    """Structural checks beyond "it is not a proof" (map-speculative §5.4).

    A definitions-only proposal is refused when orchestration is required: with no
    children a single prover takes the whole goal, which is exactly the
    unorchestrated run the flag forbids.
    """
    problems: list[str] = []
    for definition in proposal.definitions:
        label = definition.name or " ".join(definition.text.split())[:40]
        blocks = parse_blocks(definition.text + "\n")
        if any(b.has_proof for b in blocks):
            problems.append(f"design {label!r} carries a proof")
        offending = [b.head for b in blocks if b.head in OBLIGATION_HEADS]
        if offending:
            problems.append(
                f"design {label!r} declares a {offending[0]}; a new obligation goes in "
                "`children`, so it can be stated, frozen and dispatched like any other"
            )
        if definition.name and blocks and all(b.name != definition.name for b in blocks):
            problems.append(f"design {definition.name!r} does not declare {definition.name}")
    if not proposal.children and not proposal.definitions:
        problems.append(
            "the plan has no children: orchestration is required, so a decomposer must "
            "state at least one obligation rather than hand the whole goal to a single prover"
        )
    elif require_children and not proposal.children:
        problems.append(
            "the plan states definitions but no children: orchestration is required, so a "
            "design alone is not a plan -- state the obligations the goal breaks into"
        )
    seen: set[str] = set()
    for child in proposal.children:
        if child.name in seen:
            problems.append(f"duplicate child name {child.name!r}")
        seen.add(child.name)
        blocks = parse_blocks(child.statement + "\n")
        if len(blocks) != 1 or blocks[0].name != child.name:
            problems.append(
                f"child {child.name!r} must be exactly one declaration named {child.name}. "
                "Give it as either a bare proposition (the header is added for you) or "
                f"one `Lemma {child.name} ... .` -- not several declarations, and not one "
                "under a different name."
            )
            continue
        if blocks[0].head not in STATEMENT_HEADS:
            problems.append(f"child {child.name!r} is a {blocks[0].head}; children must be lemmas")
        if blocks[0].has_proof:
            problems.append(f"child {child.name!r} carries a proof")
        # One declaration is not enough: `Lemma foo : True. Unset Guard Checking.` is
        # one block and two sentences, and Rocq accepts it.
        sentences = [s for s in split_sentences(strip_comments(child.statement)) if s.code.strip()]
        if len(sentences) != 1:
            problems.append(
                f"child {child.name!r} must be exactly one sentence; the statement ends at its first `.` "
                f"and what follows (`{' '.join(sentences[1].code.split())[:60]}`) is not part of an obligation"
                if len(sentences) > 1 else f"child {child.name!r} has no statement sentence"
            )
    return problems


def drop_redundant_children(dev: Development, root: Node, proposal: PlanProposal) -> tuple[PlanProposal, list[str]]:
    """Remove children that merely restate the root or an existing declaration.

    Round 5 of the spec-only seqlock_wf run listed the (already proved) root among its
    children and the whole 17-minute revision was rejected for it.  A redundant child
    is a no-op, not a violation: drop it, say so, keep the rest.
    """
    existing = set(dev.names())
    root_hash = statement_hash(root.statement)
    kept: list[ChildStatement] = []
    notes: list[str] = []
    for c in proposal.children:
        if c.name == root.name or c.name in existing:
            notes.append(f"dropped child {c.name!r}: already declared in the development (use it, do not restate it)")
        elif statement_hash(c.statement) == root_hash or body_hash(c.statement) == body_hash(root.statement):
            notes.append(f"dropped child {c.name!r}: it restates the root")
        else:
            kept.append(c)
    if len(kept) == len(proposal.children):
        return proposal, []
    return replace(proposal, children=tuple(kept)), notes


def already_declared(dev: Development, proposal: PlanProposal) -> list[str]:
    """A child that names an existing declaration duplicates it at assembly and sends a
    worker to re-prove a proved lemma: "use it, do not restate it"."""
    existing = set(dev.names())
    return [
        f"child {c.name!r} is already declared in the development -- use it, do not restate it as an obligation"
        for c in proposal.children
        if c.name in existing
    ]


def blank_predicates(dev: Development) -> list[str]:
    """Definitions the corpus left as ``True`` -- the design that was withheld."""
    out: list[str] = []
    for block in dev.blocks:
        if block.head != "Definition" or not block.name:
            continue
        line = " ".join(block.statement.split())
        if line.endswith(":= True%I.") or line.endswith(":= True."):
            out.append(block.name)
    return out


def current_design(dev: Development) -> list[str]:
    """Every design-shaped declaration's text, for "Your current design"."""
    return [
        dev.source[b.statement_start : b.statement_end]
        for b in dev.blocks
        if b.head in DESIGN_HEADS and b.name
    ]


# ------------------------------------------------------------------ prompts


def render_decomposition_task(
    node: Node,
    dev: Development,
    *,
    contract: Any | None = None,
    library: Sequence[Path] = (),
    design_brief: str = "",
    brief_mode: str = "full",
) -> str:
    """The decomposer's packet.  Notice what is absent: any way to check a proof.

    Under ``brief_mode="spec-only"`` only what is derivable from the file is shown:
    the blank predicates, the statements, the contract.  The brief text is never
    passed, and the template leaks no design of its own.
    """
    blanks = blank_predicates(dev)
    parts: list[str] = []
    parts.append(f"# Decompose `{node.name}`\n")
    parts.append(
        "You are the **decomposer**. Your job is to state the obligations this goal "
        "should be broken into; you are not proving anything, and you have no tools "
        "for it: you can read files, and that is all.\n"
    )
    parts.append("## The goal\n")
    parts.append(f"```coq\n{node.statement.strip()}\n```\n")
    if node.intent:
        parts.append("## Why it exists\n")
        parts.append(node.intent.strip() + "\n")
    parts.append("## The development\n")
    parts.append(f"`{dev.path}` — read it. What is already defined and proved there is yours to use.\n")
    if design_brief.strip() and brief_mode == "full":
        parts.append(design_brief.strip() + "\n")
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
            "may not change the program or any specification: those are the theorem.\n"
        )
    else:
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
        "automatically; so is one that duplicates an obligation already stated.\n"
    )
    parts.append("## Answer\n")
    parts.append(f"Write `{ANSWER_FILE}`… you cannot: you have no write tool. Reply with JSON:\n")
    parts.append("```json\n" + json.dumps(_TEMPLATE, indent=2) + "\n```\n")
    parts.append(
        "Keep every `rationale` to one or two sentences: the answer is read by a "
        "program, and a reply that overruns the CLI's output limit is lost entirely, "
        "round included. Say the design in Rocq, not in prose.\n"
        "Each `definitions[].text` is one complete `Definition`/`Class`/`Notation` "
        "sentence. Each `statement` is exactly one `Lemma … .` sentence and "
        "**nothing else**. "
        "No `Proof.`, no tactics, no `Qed.` A statement carrying proof text is "
        "rejected outright and the decomposition is discarded — that is a role "
        "violation, not a formatting slip.\n"
    )
    return "\n".join(parts)


_TEMPLATE = {
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
        },
    ],
    "children": [
        {
            "name": "helper_lemma_name",
            "statement": "Lemma helper_lemma_name (P : iProp Σ) : P -∗ P.",
            "rationale": "what this buys the parent",
        }
    ],
    "glue_rationale": "how the parent follows from the children",
}


def render_amendment_task(
    node: Node,
    dev: Development,
    *,
    design: Sequence[str],
    evidence: str,
    round_no: int,
    kind: str = "proofs",
    contract: Any | None = None,
) -> str:
    """Ask for a *revision*, given where it failed.

    ``kind="proofs"``: the provers failed and the evidence is theirs, read with the
    two-direction invariant rubric (``skills/invariants.md``).  ``kind="design"``:
    the design itself was rejected before any proof (it did not compile, or it moved
    something the contract froze, or the answer was unreadable) -- the checker's
    own words are the evidence and no granularity verdict is pretended.
    """
    parts: list[str] = []
    parts.append(f"# Revise the design for `{node.name}` (round {round_no})\n")
    parts.append("## The development\n")
    parts.append(
        f"`{dev.path}` -- read it before revising (Read/Glob/Grep reach it); the definitions "
        "below are quoted from it, and a revision written from memory of the design page "
        "alone lost a round. List only the obligations you add or restate under `children`: "
        "never the root, and never a lemma the development already declares or has proved.\n"
    )
    if kind == "design":
        parts.append(
            "Your previous answer could not be applied. You are still the decomposer: "
            "correct the design, do not attempt the proofs. You have no tools for them.\n"
        )
    else:
        parts.append(
            "Your previous design did not carry the proofs. You are still the "
            "decomposer: revise the design, do not attempt the proofs. You have no "
            "tools for them.\n"
        )
    parts.append("## Your current design\n")
    if design:
        for text in design:
            parts.append("```coq\n" + text.strip() + "\n```\n")
    else:
        parts.append("(no design of yours is on the page yet)\n")
    parts.append("## What happened\n")
    parts.append("```\n" + evidence.strip()[:EVIDENCE_SHOWN] + "\n```\n")
    parts.append("## How to read that\n")
    if kind == "design":
        parts.append(
            "- The message above is the checker's, verbatim: a compiler error names the "
            "line, a contract refusal names the definition, a rejected answer names the "
            "field. Fix exactly that.\n"
            "- Return the whole design again, corrected. Every entry in `definitions` "
            "needs both a `name` and a `text`; a definition you do not intend to change "
            "may be left out and keeps its current form.\n"
        )
    else:
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
    if contract is not None:
        parts.append("## What you may and may not change\n")
        parts.append(f"{contract.describe()}\n")
    if blank_predicates(dev) or kind == "design":
        parts.append(
            "\nReturn the **same JSON shape as before**: `definitions` (the revised "
            "design, complete -- every definition you want, not a diff) and optionally "
            "`children`. A definition you omit keeps its current form. You may not "
            "change the program or any specification.\n"
        )
    else:
        parts.append(
            "\n**The invariant and the ghost state here are given and frozen**, so the "
            "revision cannot be to them. Return the same JSON shape as before, and put "
            "the work in `children`: different obligations, or additional ones, that "
            "reach the goal by another route. `definitions` is for genuinely new "
            "helpers only -- a definition already on the page may not be restated, and "
            "a design that restates one is rejected before any proof is attempted.\n"
        )
    return "\n".join(parts)


# ------------------------------------------------------------------ adjudication (PLAN.md 8.5, 8.9)

AMENDMENT_VERDICTS: tuple[str, ...] = ("accept", "adjust", "reject")
CONTEST_VERDICTS: tuple[str, ...] = ("statement", "strategy")
#: Words a model reaches for instead of the protocol's.  A round is cheap here, but
#: the prover waiting on it is not.
_VERDICT_SYNONYMS: dict[str, str] = {
    "approve": "accept", "approved": "accept", "accepted": "accept", "ok": "accept", "yes": "accept",
    "adjusted": "adjust", "amend": "adjust", "modify": "adjust", "revise": "adjust",
    "rejected": "reject", "refuse": "reject", "refused": "reject", "no": "reject",
    "design": "statement", "invariant": "statement", "definition": "statement",
    "prover": "strategy", "proof": "strategy", "tactic": "strategy", "tactics": "strategy",
}
#: The answer is a yes/no on one conjunct, not a design: the prompt says so in tokens.
VERDICT_TOKENS = 300


@dataclass
class Verdict:
    """An approver's answer on one amendment or one contest.

    PLAN.md 8.5 names two event-driven audits -- the ``weaken``-shaped change and the
    ``contested`` adjudication -- and both are one short round here, at a lower
    effort than a design.  For an amendment: ``accept`` | ``adjust`` (``definition``
    + ``text``, the complete replacement sentence) | ``reject`` (``hint`` says why,
    naming the close site).  For a contest: ``statement`` (optionally a one-definition
    fix as ``definition`` + ``text``) | ``strategy`` (``hint`` is what to tell the
    prover).

    The type has room for a *definition* and none for a proof: ``text`` is screened by
    :func:`assert_statement_only` before it is kept, and a verdict whose text carries
    proof text is discarded whole (``ok`` false, ``violation`` set), exactly as a
    proposal would be.
    """

    verdict: str
    definition: str = ""
    text: str = ""
    hint: str = ""
    #: ``statement`` on a contest only: the corrected obligation itself (one sentence
    #: under the contested node's own name), applied without a design round.
    restatement: str = ""
    raw: str = ""
    cost: dict[str, Any] = field(default_factory=dict)
    model: str = ""
    infrastructure: bool = False
    attempt_id: int = 0
    #: ``amendment`` or ``contest``.
    kind: str = ""
    #: Why no verdict could be read; empty when one was.
    violation: str = ""
    deadline: bool = False
    elapsed_s: float = 0.0
    transcript: str = ""
    trace: dict[str, Any] = field(default_factory=dict)
    round: int = 1

    @property
    def ok(self) -> bool:
        """A usable verdict was read (and nothing in it was proof text)."""
        return bool(self.verdict) and not self.violation

    def summary(self) -> str:
        if not self.ok:
            return self.violation or "no verdict"
        if self.verdict == "statement" and self.restatement:
            return f"statement, restated: {' '.join(self.restatement.split())[:120]}"
        if self.verdict == "adjust" or (self.verdict == "statement" and self.text):
            return f"{self.verdict} `{self.definition}`: {' '.join(self.text.split())[:100]}"
        return f"{self.verdict}: {' '.join(self.hint.split())[:200]}" if self.hint else self.verdict

    def render(self) -> str:
        if self.infrastructure:
            return f"the approver could not run at all -- a provider or CLI failure, not a verdict:\n  {self.violation}"
        if not self.ok:
            return f"no verdict: {self.violation}"
        return f"{self.kind or 'verdict'}: {self.summary()}"

    def to_json(self) -> dict[str, Any]:
        return {
            "ok": self.ok, "kind": self.kind, "verdict": self.verdict, "definition": self.definition,
            "text": self.text, "hint": self.hint, "restatement": self.restatement, "violation": self.violation, "model": self.model,
            "cost": dict(self.cost), "infrastructure": self.infrastructure, "deadline": self.deadline,
            "elapsed_s": self.elapsed_s, "attempt_id": self.attempt_id, "round": self.round,
        }

    @classmethod
    def from_json(cls, data: dict[str, Any]) -> Verdict:
        return cls(
            verdict=str(data.get("verdict", "") or ""), definition=str(data.get("definition", "") or ""),
            text=str(data.get("text", "") or ""), hint=str(data.get("hint", "") or ""),
            restatement=str(data.get("restatement", "") or ""),
            kind=str(data.get("kind", "") or ""), violation=str(data.get("violation", "") or ""),
            model=str(data.get("model", "") or ""), cost=dict(data.get("cost") or {}),
            infrastructure=bool(data.get("infrastructure", False)), deadline=bool(data.get("deadline", False)),
            elapsed_s=float(data.get("elapsed_s", 0.0) or 0.0), attempt_id=int(data.get("attempt_id", 0) or 0),
            round=int(data.get("round", 1) or 1),
        )


#: Keys a model reaches for when it corrects the obligation itself.
_RESTATEMENT_KEYS: tuple[str, ...] = (
    "restatement", "restated", "new_statement", "corrected_statement", "corrected", "lemma", "obligation", "statement_text",
)


def _is_one_obligation(text: str) -> bool:
    """Exactly one `Lemma`/`Theorem`/... sentence and nothing else."""
    try:
        blocks = parse_blocks(text.rstrip() + ("" if strip_comments(text).rstrip().endswith(".") else ".") + "\n")
    except Exception:  # noqa: BLE001 -- unreadable text is not an obligation
        return False
    return len(blocks) == 1 and blocks[0].head in OBLIGATION_HEADS


def parse_verdict(payload: dict[str, Any], *, kind: str, definition: str = "", node_name: str = "") -> Verdict:
    """Read one verdict object under the statement-only contract.

    :class:`ProofEngineeringAttempt` for proof text or an obligation in ``text`` (a
    role violation: the round is discarded); plain :class:`ProtocolError` for a
    verdict outside the protocol (an unknown word, an ``adjust`` with no sentence,
    a sentence that fixes a different definition than the one asked about).
    """
    allowed = AMENDMENT_VERDICTS if kind == "amendment" else CONTEST_VERDICTS
    word = str(payload.get("verdict", "") or "").strip().lower().rstrip(".")
    word = _VERDICT_SYNONYMS.get(word, word)
    if word not in allowed:
        raise ProtocolError(f"verdict {word!r} is not one of {', '.join(allowed)}")
    name = str(payload.get("definition", "") or "").strip()
    text = str(payload.get("text", "") or payload.get("replacement", "") or "").strip()
    hint = str(payload.get("hint", "") or payload.get("why", "") or payload.get("rationale", "") or "").strip()
    restatement = next(
        (str(payload.get(k) or "").strip() for k in _RESTATEMENT_KEYS if str(payload.get(k) or "").strip()), ""
    )
    if restatement and not _is_one_obligation(restatement):
        if kind == "contest" and word == "statement":
            raise ProtocolError("a restatement is exactly one obligation sentence: `Lemma <same name> … .`")
        restatement = ""  # a stray name or echo under `lemma`/`obligation`/... on another verdict
    if text:
        assert_statement_only(text, what=f"the {kind} verdict's text")
        blocks = parse_blocks(text + "\n")
        offending = [b.head for b in blocks if b.head in OBLIGATION_HEADS]
        if offending and kind == "contest" and not restatement and (not node_name or declared_name(text) == node_name):
            restatement, text = text, ""  # the corrected obligation arrived under `text`
        elif offending:
            raise ProofEngineeringAttempt(
                f"the verdict's text declares a {offending[0]}; a fix is a definition -- an obligation "
                "goes through the statement pipeline"
            )
    if text:
        declared = declared_name(text)
        name = name or declared
        if declared and name and declared != name:
            raise ProtocolError(f"the verdict's text declares {declared!r}, not {name!r}")
        if definition and name and name != definition:
            raise ProtocolError(f"the verdict fixes {name!r}; the request was about {definition!r}")
        if not strip_comments(text).rstrip().endswith("."):
            text += "."
    if word == "adjust" and not text:
        raise ProtocolError("an `adjust` verdict needs the complete replacement definition in `text`")
    if restatement:
        if kind != "contest" or word != "statement":
            raise ProtocolError("a restatement goes only with a contest's `statement` verdict")
        assert_statement_only(restatement, what="the contest verdict's restatement")
        declared = declared_name(restatement)
        if node_name and declared != node_name:
            raise ProtocolError(f"the restatement declares {declared!r}; the contested obligation is {node_name!r}")
        if not strip_comments(restatement).rstrip().endswith("."):
            restatement += "."
    return Verdict(verdict=word, definition=name or definition, text=text, hint=hint, restatement=restatement, kind=kind)


_AMENDMENT_VERDICT_TEMPLATE = {
    "verdict": "accept | adjust | reject",
    "definition": "adjust only: the definition's name",
    "text": "adjust only: the complete replacement sentence, `Definition <name> … := … .`",
    "why": "one or two sentences; for reject, the program step or close site that breaks",
}
_CONTEST_VERDICT_TEMPLATE = {
    "verdict": "statement | strategy",
    "definition": "statement only, when one definition fixes it: its name",
    "text": "statement only, when one definition fixes it: the complete replacement sentence",
    "restatement": "statement only, when the obligation's own statement is wrong and the design is not: "
                   "the complete corrected sentence, `Lemma <same name> … .`",
    "hint": "strategy only: at most three sentences telling the prover what to do differently",
}
_NO_PROOF_TEXT = (
    "`text` is one `Definition` sentence and **nothing else**: no `Lemma`, no "
    "`Proof.`, no tactics, no `Qed.` A verdict carrying proof text is discarded "
    "whole -- that is a role violation, not a formatting slip.\n"
)


def _design_section(dev: Development, design: Sequence[str]) -> list[str]:
    parts = ["## The current design\n"]
    shown = [t for t in design if t.strip()] or current_design(dev)
    if shown:
        parts.extend("```coq\n" + text.strip() + "\n```\n" for text in shown)
    else:
        parts.append("(no design of yours is on the page yet)\n")
    return parts


def _contract_section(contract: Any | None) -> list[str]:
    if contract is None:
        return []
    return [
        "## What you may and may not change\n",
        f"{contract.describe()}\n\nChecked mechanically after your answer: a fix outside it is refused.\n",
    ]


def render_amendment_adjudication(
    root: Node,
    dev: Development,
    amendment: AmendmentRequest,
    *,
    evidence: str,
    contract: Any | None = None,
    design: Sequence[str] = (),
) -> str:
    """The approver's packet for a prover's amendment request (PLAN.md 8.5).

    Short and decisive on purpose: a design round is 30-45 minutes at ``xhigh``;
    this is a yes/no on one conjunct at ``medium``.  The default answer is *accept*
    -- a strengthening that compiled is already machine-checked for form and every
    affected proof is replayed after it -- so a rejection is asked for only when the
    fact is false or unmaintainable, with the close site that breaks.
    """
    name = amendment.definition
    parts: list[str] = [f"# Approve, adjust or reject a change to `{name}`\n"]
    parts.append(
        "You are the **approver**: the decomposer's delegate for one small change a "
        "prover asked for mid-proof. Decide; do not redesign and do not prove -- you "
        "have no tools for either.\n"
    )
    parts.append("## The goal\n")
    parts.append(f"```coq\n{root.statement.strip()}\n```\n")
    parts.extend(_design_section(dev, design))
    parts.append("## The requested change\n")
    block = dev.block(name)
    if block is not None:
        parts.append(f"`{name}` today:\n\n```coq\n{block.statement.strip()}\n```\n")
    if amendment.kind == "add":
        parts.append(f"The prover asks that `{name}` **also carry** this conjunct:\n\n```coq\n{amendment.add.strip()}\n```\n")
    else:
        parts.append(f"The prover asks that `{name}` **become**:\n\n```coq\n{amendment.replace.strip()}\n```\n")
    who = amendment.requester or "a prover"
    if amendment.at.strip():
        parts.append(f"Needed by `{who}` at: {amendment.at.strip()}\n")
    if amendment.why.strip():
        parts.append(f"Its reason: {amendment.why.strip()}\n")
    parts.append("## The prover's evidence\n")
    parts.append("```\n" + (evidence.strip()[:EVIDENCE_SHOWN] or "(none given)") + "\n```\n")
    parts.extend(_contract_section(contract))
    parts.append("## How to decide\n")
    parts.append(
        "- **accept** when the added fact holds in every state the invariant describes "
        "and every close site can re-establish it. This is the expected answer: the "
        "change is machine-checked for form and every affected proof is replayed.\n"
        "- **adjust** when the fact is right but its form is wrong -- a missing later "
        "modality `▷`, a fraction, a binder that should be existential, a conjunct "
        "that belongs under the existential. Give the **complete** replacement "
        f"`Definition {name} … := … .` sentence in `text`.\n"
        "- **reject** only when the fact is false or unmaintainable, and say in `why` "
        "which program step or close site cannot restore it.\n"
        "- A conjunct that makes the definition **unsatisfiable** is unmaintainable by "
        "definition: `False`, `⌜0 = 1⌝`, a contradiction with the body, two exclusive "
        "tokens of one ghost name. A predicate nothing can establish proves every "
        "specification that assumes it, so the prover asking for one is asking for its "
        "goal to become vacuous. Reject it and name what cannot be established.\n"
        "- Do not reject because the change is inelegant, and do not redesign around it.\n"
    )
    parts.append("## Answer\n")
    parts.append(f"Reply with JSON only, in under {VERDICT_TOKENS} tokens:\n")
    parts.append("```json\n" + json.dumps(_AMENDMENT_VERDICT_TEMPLATE, indent=2, ensure_ascii=False) + "\n```\n")
    parts.append(_NO_PROOF_TEXT)
    return "\n".join(parts)


def render_contest_adjudication(
    root: Node,
    dev: Development,
    node: Node,
    *,
    evidence: str,
    contract: Any | None = None,
    design: Sequence[str] = (),
    failed_attempts: int = 0,
) -> str:
    """A prover contests ``node`` -- or, with ``failed_attempts``, nobody contested it
    and that many attempts failed: is the statement (or the design above it) wrong, or
    the prover's strategy?  PLAN.md 8.9: a node escalated twice is a statement
    problem; 9.2: an invariant fails in two directions and each has a signature.

    ``contested -> open`` is a human-only move in the lattice.  This packet is the
    human's delegate deciding; the move itself is still made under ``role="human"``
    by :func:`pcp.orch.amend.reopen_for_amendment`.
    """
    if failed_attempts:
        parts: list[str] = [f"# Review `{node.name}` after {failed_attempts} failed attempt(s)\n"]
        parts.append(
            f"You are the **approver**. No prover contested this obligation, but {failed_attempts} "
            "attempt(s) at it failed and budget remains. Decide whether the statement (or the "
            "design it rests on) is wrong, or the provers' strategy is. Do not prove it yourself; "
            "you have no tools for it.\n"
        )
    else:
        parts = [f"# Adjudicate the contest on `{node.name}`\n"]
        parts.append(
            "You are the **approver**. A prover says this obligation cannot be proved as "
            "stated. Decide whether the statement (or the design it rests on) is wrong, "
            "or the prover's strategy is. Do not prove it yourself; you have no tools for it.\n"
        )
    parts.append("## The contested obligation\n")
    parts.append(f"```coq\n{node.statement.strip()}\n```\n")
    if node.intent:
        parts.append("## Why it exists\n")
        parts.append(node.intent.strip() + "\n")
    parts.append("## The goal it serves\n")
    parts.append(f"```coq\n{root.statement.strip()}\n```\n")
    parts.extend(_design_section(dev, design))
    parts.append("## The last attempt's evidence\n" if failed_attempts else "## The prover's case\n")
    parts.append("```\n" + (evidence.strip()[:EVIDENCE_SHOWN] or "(no evidence was given)") + "\n```\n")
    parts.extend(_contract_section(contract))
    parts.append("## How to decide\n")
    parts.append(
        "- A proof that dies **closing** an invariant many steps after opening it "
        "usually means the invariant is too **strong**; one that dies just after "
        "**opening** it means too **weak**. Either is a `statement` verdict.\n"
        "- If one definition fixes it -- a missing conjunct, a `▷`, a fraction -- give "
        "it as `definition` + `text` (the complete sentence). If the statement is wrong "
        "in a way one definition does not fix, answer `statement` with no `text`; the "
        "design is then revised.\n"
        "- If the obligation's **own statement** is wrong and the design is not -- a "
        "non-persistent resource stated as a `-∗` premise before a `□`-boxed `{{{ }}}` "
        "triple, a missing hypothesis, a wrong postcondition -- answer `statement` with "
        "`restatement`: the complete corrected sentence under the same name. It is compiled, "
        "checked and adopted at once, without a design round, and every proof that used the "
        "old statement is replayed.\n"
        "- If the obligation is provable and the prover missed the route, answer "
        "`strategy` with a `hint` of at most three sentences: where to register or "
        "commit the atomic update, which lemma to use, which hypothesis to keep.\n"
        "- The prover's transcript is a claim, not a proof. Audit the claim, not the rhetoric.\n"
    )
    parts.append("## Answer\n")
    parts.append(f"Reply with JSON only, in under {VERDICT_TOKENS} tokens:\n")
    parts.append("```json\n" + json.dumps(_CONTEST_VERDICT_TEMPLATE, indent=2, ensure_ascii=False) + "\n```\n")
    parts.append(_NO_PROOF_TEXT)
    return "\n".join(parts)


# ------------------------------------------------------------------ the result


@dataclass
class DecompositionResult:
    proposal: PlanProposal | None = None
    problems: list[str] = field(default_factory=list)
    violation: str = ""
    #: The tail of the reply text the proposal was read from.
    raw: str = ""
    #: The runner's full output stream -- what the record's ``transcript.txt`` keeps
    #: (ARCHITECTURE.md 5: the event stream, not the final text).
    transcript: str = ""
    elapsed_s: float = 0.0
    cost: dict[str, Any] = field(default_factory=dict)
    #: The model that actually produced this, resolved rather than labelled.
    model: str = ""
    trace: dict[str, Any] = field(default_factory=dict)
    #: The provider or its CLI failed: not a decomposition failure, never retried.
    infrastructure: bool = False
    #: The runner killed the decomposer at its deadline: retried with more clock.
    deadline: bool = False
    sentinels: SentinelReport | None = None
    attempt_id: int = 0
    round: int = 1
    #: Non-blocking observations about an accepted proposal (e.g. a redundant child that
    #: was dropped rather than costing the round).
    notes: list[str] = field(default_factory=list)

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
        lines.extend(f"  note: {n}" for n in self.notes)
        return "\n".join(lines)

    def to_json(self) -> dict[str, Any]:
        return {
            "ok": self.ok,
            "proposal": self.proposal.to_json() if self.proposal else None,
            "problems": list(self.problems),
            "violation": self.violation,
            "elapsed_s": self.elapsed_s,
            "cost": dict(self.cost),
            "model": self.model,
            "infrastructure": self.infrastructure,
            "deadline": self.deadline,
            "sentinels": self.sentinels.to_json() if self.sentinels else None,
            "attempt_id": self.attempt_id,
            "round": self.round,
        }


# ------------------------------------------------------------------ the role


class Decomposer:
    """Runs decomposition attempts under the statement-only contract."""

    role = "decomposer"

    def __init__(
        self,
        runner: Runner,
        graph: Graph,
        dev: Development,
        workroot: str | Path,
        recorder: Any = None,
        *,
        corpus: str = "",
        require_children: bool = True,
        deadline_grace_s: float = DEADLINE_GRACE_S,
        approver: Runner | None = None,
        pause: Any = None,
    ) -> None:
        self.runner = runner
        self.graph = graph
        self.dev = dev
        self.workroot = Path(workroot)
        self.recorder = recorder
        self.corpus = corpus
        self.require_children = require_children
        self.deadline_grace_s = float(deadline_grace_s)
        #: The adjudicating runner (same model and tools, lower effort); the design
        #: runner when none is configured.
        self.approver = approver
        #: The run's provider pause (:class:`pcp.orch.outage.ProviderPause`), shared
        #: with the scheduler; ``None`` means an outage is filed as today.
        self.pause = pause

    async def propose(
        self,
        root: Node,
        contract: Any | None,
        *,
        budget_seconds: float,
        design_brief: str = "",
        library: Sequence[Path] = (),
        brief_mode: str = "full",
        round_no: int = 1,
    ) -> DecompositionResult:
        task = render_decomposition_task(
            root, self.dev, contract=contract, library=library, design_brief=design_brief, brief_mode=brief_mode,
        )
        return await self._run(root, task, suffix="decompose", budget_seconds=budget_seconds, round_no=round_no)

    async def amend(
        self,
        root: Node,
        *,
        evidence: str,
        round_no: int,
        budget_seconds: float,
        design: Sequence[str] | None = None,
        kind: str = "proofs",
        contract: Any | None = None,
        base: PlanProposal | None = None,
        repair: bool = False,
    ) -> DecompositionResult:
        """Re-ask.  ``base`` is the proposal being revised: an answer that omits its
        children (a definitions-only compile repair) or its definitions (a
        children-only restatement) is completed from ``base`` *before* validation --
        the prompt promises that an omitted part keeps its current form, so such a
        repair is never rejected as "no children".

        ``repair=True`` is the cheap tier: a compile, typecheck or contract failure of an
        otherwise accepted design is fixed by the approver runner (medium effort) and
        recorded under role ``repairer``, so it never counts as a design round --
        round 6 of the spec-only seqlock_wf run was a whole 16-minute redesign spent on
        one syntax error in one child statement."""
        task = render_amendment_task(
            root, self.dev, design=current_design(self.dev) if design is None else design,
            evidence=evidence, round_no=round_no, kind=kind, contract=contract,
        )
        runner = self.approver if (repair and self.approver is not None) else None
        return await self._run(
            root, task, suffix=f"amend{round_no}", budget_seconds=budget_seconds, round_no=round_no, base=base,
            runner=runner, who="repairer" if repair else "decomposer",
        )

    # -- adjudication (the approver) ------------------------------------------

    async def adjudicate_amendment(
        self,
        root: Node,
        amendment: AmendmentRequest,
        *,
        evidence: str,
        budget_seconds: float,
        contract: Any | None = None,
        design: Sequence[str] = (),
    ) -> Verdict:
        """Approve, adjust or reject a prover's amendment request (PLAN.md 8.5).
        Recorded on the root, as a design round is: the definition is the root's."""
        task = render_amendment_adjudication(
            root, self.dev, amendment, evidence=evidence, contract=contract, design=design,
        )
        return await self._adjudicate(
            root, task, kind="amendment", budget_seconds=budget_seconds, definition=amendment.definition,
        )

    async def adjudicate_contest(
        self,
        root: Node,
        node: Node,
        *,
        evidence: str,
        budget_seconds: float,
        contract: Any | None = None,
        design: Sequence[str] = (),
        failed_attempts: int = 0,
    ) -> Verdict:
        """``statement`` or ``strategy`` for a contested node, or for one that failed
        ``failed_attempts`` times without contesting (PLAN.md 8.9).  Recorded on the
        node: the verdict is about it."""
        task = render_contest_adjudication(
            root, self.dev, node, evidence=evidence, contract=contract, design=design, failed_attempts=failed_attempts,
        )
        return await self._adjudicate(node, task, kind="contest", budget_seconds=budget_seconds)

    async def _adjudicate(
        self, node: Node, task: str, *, kind: str, budget_seconds: float, definition: str = ""
    ) -> Verdict:
        runner = self.approver or self.runner
        n = self._adjudication_no(node)
        suffix = f"adjudicate{n}"
        result, attempt_id, workdir, started = await self._invoke(
            node, task, suffix=suffix, budget_seconds=budget_seconds, round_no=n, runner=runner, who="approver",
        )
        out = self._triage_verdict(node, result, kind=kind, attempt_id=attempt_id, round_no=n, definition=definition)
        out.elapsed_s = time.perf_counter() - started
        self._record_safely(node, out, workdir, suffix, runner=runner, evidence=out.summary())
        return out

    def _adjudication_no(self, node: Node) -> int:
        """``adjudicate<N>``: one directory per verdict, never overwritten (the same
        rule the design directories follow)."""
        return 1 + sum(1 for p in self.workroot.glob(f"{node.id}.adjudicate*") if p.is_dir())

    # -- the shared machinery ---------------------------------------------------

    async def _run(
        self, node: Node, task: str, *, suffix: str, budget_seconds: float, round_no: int,
        base: PlanProposal | None = None, runner: Runner | None = None, who: str = "decomposer",
    ) -> DecompositionResult:
        result, attempt_id, workdir, started = await self._invoke(
            node, task, suffix=suffix, budget_seconds=budget_seconds, round_no=round_no, runner=runner, who=who,
        )
        out = self._triage(node, result, attempt_id=attempt_id, round_no=round_no, base=base)
        out.elapsed_s = time.perf_counter() - started
        self._record_safely(
            node, out, workdir, suffix, runner=runner or self.runner, evidence=out.violation or "; ".join(out.problems)
        )
        return out

    async def _invoke(
        self, node: Node, task: str, *, suffix: str, budget_seconds: float, round_no: int,
        runner: Runner | None = None, who: str = "decomposer",
    ) -> tuple[NodeResult, int, Path, float]:
        """Start the attempt row, write the packet, run the runner under the clock.
        Returns the raw result, the attempt id, the workdir and the start time.

        An ``error`` that is a provider outage (:func:`pcp.orch.outage.detect_outage`)
        closes its row as ``error``, holds the run's pause and, once the provider
        answers, runs the round *again* under the same clock and round number: a
        deadline is what the doubling ladder in :mod:`pcp.orch.prove.design` is for,
        an outage is not a deadline, and no design round is spent
        (``design_rounds_used`` is the maximum round, which the retry does not move).
        """
        runner = runner or self.runner
        started = time.perf_counter()
        attempt_id, workdir, payload = self._begin(node, task, suffix=suffix, round_no=round_no, runner=runner, who=who, budget_seconds=budget_seconds)
        result = await self._under_clock(runner, payload, budget_seconds=budget_seconds, who=who)
        outage = self._outage_of(result)
        if outage is not None:
            self.graph.finish_attempt(attempt_id, status="error", evidence=result.evidence, model=result.model, cost=dict(result.cost))
            self.graph.emit(f"{who}.outage", node.id, kind=outage.kind, detail=outage.detail[:400], attempt=attempt_id, round=round_no)
            if await self.pause.hold(outage):
                attempt_id, workdir, payload = self._begin(node, task, suffix=suffix, round_no=round_no, runner=runner, who=who, budget_seconds=budget_seconds)
                result = await self._under_clock(runner, payload, budget_seconds=budget_seconds, who=who)
        return result, attempt_id, workdir, started

    def _begin(
        self, node: Node, task: str, *, suffix: str, round_no: int, runner: Runner, who: str, budget_seconds: float,
    ) -> tuple[int, Path, NodePayload]:
        """One attempt row and one fresh directory for it (never reused: the directory
        name is the row id)."""
        attempt_id = self.graph.start_attempt(
            node.id, runner=getattr(runner, "name", "?"), owner=node.owner, role=who, round=round_no
        )
        workdir = ensure_dir(self.workroot / f"{node.id}.{suffix}" / f"a{attempt_id}")
        atomic_write_text(workdir / DECOMPOSE_FILE, task)
        atomic_write_text(workdir / "TASK.md", task)  # runners always read TASK.md
        payload = NodePayload(
            node_id=node.id, name=node.name, statement=node.statement, file=str(self.dev.path),
            workdir=workdir, scratch_file=self.dev.path.name, budget_seconds=budget_seconds,
        )
        return attempt_id, workdir, payload

    async def _under_clock(self, runner: Runner, payload: NodePayload, *, budget_seconds: float, who: str) -> NodeResult:
        try:
            return await asyncio.wait_for(runner.run_node(payload), timeout=budget_seconds + self.deadline_grace_s)
        except TimeoutError:
            # The runner did not honour the clock: a deadline all the same (retried
            # with more clock by the ladder), never a wedged design round.
            return NodeResult(
                status="stuck", timed_out=True,
                evidence=f"the {who} exceeded its {budget_seconds:.0f}s deadline and the runner did not stop it; killed",
            )
        except Exception as exc:  # noqa: BLE001 -- a raising runner is infrastructure, filed as such
            return NodeResult(status="error", evidence=f"the {who} runner raised {type(exc).__name__}: {exc}")

    def _outage_of(self, result: NodeResult) -> Any:
        """The outage a round's ``error`` reports, when the run has a pause to hold."""
        if self.pause is None or not getattr(self.pause, "enabled", False):
            return None
        from pcp.orch.outage import detect_outage

        outage = detect_outage(result)
        return outage if outage is not None and outage.retryable else None

    def _record_safely(self, node: Node, out: Any, workdir: Path, suffix: str, *, runner: Runner, evidence: str) -> None:
        try:
            self._record(node, out, workdir, suffix, runner=runner, evidence=evidence)
        except Exception as exc:  # noqa: BLE001 -- a record is about the round; it never ends the run
            self.graph.emit("record.failed", node.id, attempt_id=out.attempt_id, error=f"{type(exc).__name__}: {exc}")

    def _file_failure(
        self, node: Node, result: NodeResult, *, attempt_id: int, violation: str, model: str,
        cost: dict[str, Any], infrastructure: bool, deadline: bool, event: str,
    ) -> None:
        """A round that produced no answer: the event, and the attempt row closed.
        ``error`` is the infrastructure verdict everywhere else in the store; a
        deadline or a reply outside the protocol is the round's own failure."""
        self.graph.emit(
            f"decomposer.{event}", node.id, detail=violation[:400], status=result.status,
            model=model, infrastructure=infrastructure, deadline=deadline, attempt=attempt_id,
        )
        self.graph.finish_attempt(
            attempt_id, status="error" if infrastructure else "stuck", evidence=violation, model=model, cost=cost,
        )

    def _triage_verdict(
        self, node: Node, result: NodeResult, *, kind: str, attempt_id: int, round_no: int, definition: str = "",
    ) -> Verdict:
        """The same ordered triage as :meth:`_triage`, for a verdict: runner verdict >
        outage > deadline > no JSON > proof text (violation) > protocol shape."""
        from pcp.orch.failures import classify

        text = str(result.trace.get("final_text") or "") or result.raw or result.proof or ""
        out = Verdict(
            verdict="", kind=kind, raw=text[-RAW_KEPT:], transcript=result.raw, cost=dict(result.cost),
            model=result.model, trace=dict(result.trace), attempt_id=attempt_id, round=round_no,
        )
        payload = extract_json(text, keys=_VERDICT_KEYS)
        if payload is None and result.raw and result.raw != text:
            payload = json_in_stream(result.raw, keys=_VERDICT_KEYS)

        def fail(violation: str, *, infrastructure: bool = False, deadline: bool = False, event: str = "failed") -> Verdict:
            out.violation, out.infrastructure, out.deadline = violation, infrastructure, deadline
            self._file_failure(
                node, result, attempt_id=attempt_id, violation=violation, model=out.model, cost=out.cost,
                infrastructure=infrastructure, deadline=deadline, event=event,
            )
            return out

        if result.status == "error":
            return fail(result.evidence or "the approver runner returned 'error' and no reason", infrastructure=True)
        if result.timed_out and payload is None:
            return fail(result.evidence or f"the approver exceeded its {payload_seconds(result)} deadline", deadline=True)
        if not text.strip():
            violation = result.evidence or f"the approver runner returned {result.status!r} and no output"
            klass = classify(violation, status=result.status, exit_code=result.exit_code).primary
            return fail(violation, infrastructure=klass == "runner-error", deadline=klass == "deadline")
        if payload is None:
            if classify(text, status=result.status, exit_code=result.exit_code).primary == "runner-error":
                return fail(" ".join(text.split())[:300], infrastructure=True)
            return fail("the approver produced no JSON verdict to read")
        try:
            read = parse_verdict(
                payload, kind=kind, definition=definition, node_name=node.name if kind == "contest" else "",
            )
        except ProofEngineeringAttempt as exc:
            return fail(str(exc), event="violation")
        except ProtocolError as exc:
            return fail(str(exc))
        out.verdict, out.definition, out.text, out.hint = read.verdict, read.definition, read.text, read.hint
        out.restatement = read.restatement
        self.graph.emit(
            "approver.verdict", node.id, kind=kind, verdict=out.verdict, definition=out.definition,
            attempt=attempt_id, model=out.model,
        )
        self.graph.finish_attempt(attempt_id, status="qed", evidence=out.summary(), model=out.model, cost=out.cost)
        return out

    def _triage(
        self, node: Node, result: NodeResult, *, attempt_id: int, round_no: int, base: PlanProposal | None = None
    ) -> DecompositionResult:
        """Runner verdict > outage > deadline-with-text > parse > validate (map-speculative §5.5)."""
        from pcp.orch.failures import classify

        text = str(result.trace.get("final_text") or "") or result.raw or result.proof or ""
        out = DecompositionResult(
            raw=text[-RAW_KEPT:], transcript=result.raw, cost=dict(result.cost), model=result.model,
            trace=dict(result.trace), attempt_id=attempt_id, round=round_no,
        )
        payload = extract_json(text)
        if payload is None and result.raw and result.raw != text:
            payload = json_in_stream(result.raw)  # the plan was stated in an earlier turn

        def fail(violation: str, *, infrastructure: bool = False, deadline: bool = False, kind: str = "failed") -> DecompositionResult:
            out.violation, out.infrastructure, out.deadline = violation, infrastructure, deadline
            self._file_failure(
                node, result, attempt_id=attempt_id, violation=violation, model=out.model, cost=out.cost,
                infrastructure=infrastructure, deadline=deadline, event=kind,
            )
            return out

        if result.status == "error":
            return fail(result.evidence or "the decomposer runner returned 'error' and no reason", infrastructure=True)
        if result.timed_out and payload is None:
            # A deadline is not a judgement -- and it is one whether or not the
            # stream carried text: finding no JSON in a killed stream is not the
            # model ignoring the protocol.
            return fail(result.evidence or f"the decomposer exceeded its {payload_seconds(result)} deadline", deadline=True)
        if not text.strip():
            violation = result.evidence or f"the decomposer runner returned {result.status!r} and no output"
            klass = classify(violation, status=result.status, exit_code=result.exit_code).primary
            return fail(violation, infrastructure=klass == "runner-error", deadline=klass == "deadline")
        if payload is None:
            broken = classify(text, status=result.status, exit_code=result.exit_code).primary == "runner-error"
            if broken:
                return fail(" ".join(text.split())[:300], infrastructure=True)
        try:
            proposal = parse_payload(payload) if payload is not None else parse_proposal(text)
        except ProofEngineeringAttempt as exc:
            return fail(str(exc), kind="violation")
        if base is not None:
            proposal = proposal.merged_over(base)
        proposal, out.notes = drop_redundant_children(self.dev, node, proposal)
        out.proposal = proposal
        out.problems = validate_proposal(proposal, require_children=self.require_children)
        out.problems += already_declared(self.dev, proposal)
        out.sentinels = self._sentinels(node, proposal)
        out.problems += [f"sentinel: {h.node}: {h.sentinel} -- {h.detail}" for h in out.sentinels.blocking]
        self.graph.finish_attempt(
            attempt_id,
            status="qed" if out.ok else "stuck",
            evidence="; ".join(out.problems),
            model=out.model,
            cost=out.cost,
            # Deliberately no `body=`: a decomposition attempt has no proof to record.
        )
        return out

    def _sentinels(self, root: Node, proposal: PlanProposal) -> SentinelReport:
        """Free sentinels over the proposal (PLAN.md 8.4), against everything already
        stated: the root, the file's declarations, and graph nodes the proposal does
        not itself restate (a revision may re-propose a child under its own name)."""
        proposed = set(proposal.names())
        known: dict[str, str] = {}
        stuck: dict[str, str] = {}
        for b in self.dev.blocks:
            if b.name and b.head in STATEMENT_HEADS:
                known[statement_hash(b.statement)] = b.name
                known[body_hash(b.statement)] = b.name
        for n in self.graph.nodes():
            if n.id == root.id or n.name in proposed or n.proof_status == "attic":
                continue
            known[n.statement_hash] = n.name
            known[body_hash(n.statement)] = n.name
            if n.proof_status in ("stuck", "contested"):
                stuck[n.name] = n.statement
        known[root.statement_hash or statement_hash(root.statement)] = root.name
        children: Any = proposal.children  # frozen dataclasses satisfy the sentinel protocol at runtime
        definitions = {d.name: d.text for d in proposal.definitions if d.name}
        return run_free_sentinels(
            children, existing_hashes=known, root_statement=root.statement, stuck_statements=stuck,
            definitions=definitions,
        )

    def _record(
        self, node: Node, out: DecompositionResult | Verdict, workdir: Path, suffix: str, *, runner: Runner, evidence: str,
    ) -> None:
        if self.recorder is None:
            return
        from pcp.orch.record import AttemptRecord

        self.recorder.write(
            AttemptRecord(
                run_id=self.recorder.run_id,
                node=node.id,
                lemma=node.name,
                attempt=out.round,
                runner=f"{getattr(runner, 'name', '?')} [{out.model or 'unknown model'}]",
                status="qed" if out.ok else ("error" if out.violation else "stuck"),
                solved=out.ok,
                elapsed_s=out.elapsed_s,
                cost=out.cost,
                evidence=evidence,
                corpus=self.corpus,
                trace=out.trace,
                attempt_id=out.attempt_id,
                round=out.round,
            ),
            workdir=workdir,
            transcript=out.transcript or out.raw,
            suffix=suffix,
        )


def payload_seconds(result: NodeResult) -> str:
    seconds = result.cost.get("seconds") if isinstance(result.cost, dict) else None
    return f"{float(seconds):.0f}s" if seconds else "clock"
