"""The recursive control flow (PLAN.md 8.2).

Everything the orchestrator does is one procedure::

    prove(stmt frozen@e, budget B):
        if estimate_simple(stmt):
            r ← dispatch(stmt, small b ⊂ B)      # optimistic probe
            if r = qed: return                    # cheap models are cheap
        plan ← decompose(stmt)                    # children + GLUE PROOF
        freeze children  (sentinels always; audit only if triggered)
        for c in plan.children, in parallel: prove(c, share of B)

Three things keep it from running away, and none of them is vigilance:

* **Budget flows down, failure flows up.**  Children inherit fractions of the
  parent's budget; exhaustion propagates upward as ``stuck``.  Runaway recursion is
  bounded by construction.
* **Depth is a smell.**  A depth cap (default 2) means that at the cap a decomposer
  may not decompose further -- dispatch or return ``stuck``, forcing a re-plan one
  level up instead of another layer down.
* **Probe-then-decompose.**  Ex-ante difficulty judgement is not reliable enough to
  gate on; a failed probe returns the trace of where it got stuck, which is exactly
  the evidence that makes the next decomposition better.

Phase 7 material, feature-flagged off: the daily loop is depth-1 with a human root
decomposer, and this must not be on its critical path.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field

from pcp.core.vernac import parse_blocks, split_sentences, strip_comments
from pcp.orch.graph import Budget, Graph, Node

#: Roles that are allowed to put a proof into the graph.  Exactly one.
PROOF_BEARING_ROLES = ("prover",)

DEFAULT_DEPTH_CAP = 2


@dataclass
class Difficulty:
    """A cheap heuristic, deliberately.

    A learned estimator is not built unless traffic ever justifies it; until then
    this exists to pick a probe budget, not to make a decision -- the decision is
    ``probe-then-decompose``, which is cheap to be wrong about.
    """

    size: int
    quantifiers: int
    modalities: int
    invariants: int

    @property
    def score(self) -> float:
        return (
            self.size / 200.0
            + 0.5 * self.quantifiers
            + 0.7 * self.modalities
            + 1.2 * self.invariants
        )

    def simple(self, threshold: float = 2.5) -> bool:
        return self.score < threshold


_QUANT = re.compile(r"[∀∃]")
_MODAL = re.compile(r"▷|□|\|==>|\|=\{|◇|<pers>")
_INV = re.compile(r"\binv\b|\bna_inv\b|\bcinv\b|\binv_alloc\b")


def estimate(statement: str) -> Difficulty:
    return Difficulty(
        size=len(statement),
        quantifiers=len(_QUANT.findall(statement)),
        modalities=len(_MODAL.findall(statement)),
        invariants=len(_INV.findall(statement)),
    )


@dataclass
class Plan:
    """A decomposition: children **plus the glue proof**.

    A plan is not prose -- it is a machine-checked proof of the parent from its
    children.  That is what kills the classic decomposition failure, where the
    children are individually plausible, jointly insufficient, and the gap is
    discovered only at assembly after the leaf budget is spent.
    """

    parent: str
    children: list[tuple[str, str]] = field(default_factory=list)
    glue: str = ""
    rationale: str = ""

    def has_gap(self) -> bool:
        """Strong no-gap: every child must be *used* by the glue.

        The demand edge is the glue referencing the child (PLAN.md 8.8): a child the
        glue never mentions is a node nothing demands, and it cannot enter the graph.
        """
        return any(name not in self.glue for name, _ in self.children)

    def unused_children(self) -> list[str]:
        return [name for name, _ in self.children if name not in self.glue]


@dataclass
class DecompositionPolicy:
    depth_cap: int = DEFAULT_DEPTH_CAP
    #: Relaxed no-gap is the default for all plans: children freeze and dispatch
    #: immediately and the glue is a concurrent node.  Blocking dispatch on glue-Qed
    #: would idle the flat-rate window and put frontier tokens on the tactic path.
    strict_no_gap: bool = False
    probe_first: bool = True
    probe_share: float = 0.15


def may_decompose(node: Node, policy: DecompositionPolicy) -> tuple[bool, str]:
    """At the cap, a decomposer may not decompose: dispatch or return ``stuck``."""
    if node.depth >= policy.depth_cap:
        return False, (
            f"depth cap {policy.depth_cap} reached; re-plan one level up rather than "
            "adding another layer -- depth usually signals a missing abstraction"
        )
    if node.budget.exhausted():
        return False, "budget exhausted; this propagates upward as stuck"
    return True, ""


def probe_budget(node: Node, policy: DecompositionPolicy) -> Budget:
    return node.budget.split(1, share=policy.probe_share)


def child_budgets(node: Node, n_children: int) -> Budget:
    """Geometric split, so depth is bounded and the cheap direction is width --
    which the scheduling invariant already rewards."""
    return node.budget.split(max(1, n_children))


def accept_plan(
    graph: Graph,
    parent: Node,
    plan: Plan,
    policy: DecompositionPolicy,
    *,
    glue_gated: bool | None = None,
) -> tuple[bool, str]:
    """Decide whether a plan may enter the graph.

    Under the relaxed rule the plan is accepted and the glue becomes a concurrent
    node; a gap then surfaces as an ordinary ``stuck`` on the glue rather than as
    up-front ceremony.  Under ``strict_no_gap`` the glue must already have `Qed`'d
    against admitted children before any child is dispatched.
    """
    allowed, why = may_decompose(parent, policy)
    if not allowed:
        return False, why
    unused = plan.unused_children()
    if unused:
        return False, (
            "pull-only node creation: the glue never references "
            + ", ".join(unused)
            + " -- a node nothing demands cannot enter the graph"
        )
    if policy.strict_no_gap and not glue_gated:
        return False, "strict no-gap: the glue proof must Qed against the admitted children first"
    return True, ""


def intent_brief(root_goal: str, parent_rationale: str) -> str:
    """Two lines, carried in every context packet.

    Deep nodes otherwise get stated in the local idiom rather than the root's, and
    the development slowly loses its vocabulary.
    """
    return (
        f"root goal: {' '.join(root_goal.split())[:200]}\n"
        f"why this node: {' '.join(parent_rationale.split())[:200]}"
    )


# ------------------------------------------------- the statement-only contract

class ProofEngineeringAttempt(ValueError):
    """A decomposer tried to do proof engineering.

    Not a style violation -- a role violation.  The decomposer's job is to state
    obligations; the moment it also writes tactics, the separation the whole pipeline
    rests on is gone, and nothing downstream can tell a proved lemma from one whose
    "proof" was hallucinated by the same model that stated it.
    """


#: Anything that makes a sentence a *proof* rather than a statement.
_PROOF_MARKERS = (
    re.compile(r"^\s*Proof\b", re.M),
    re.compile(r"^\s*(?:Qed|Defined|Admitted|Abort|Save)\s*\.", re.M),
    re.compile(r"^\s*(?:Next\s+Obligation|Obligation)\b", re.M),
    re.compile(r"\badmit\b"),
)

#: Tactic vocabulary.  A statement never contains these at the head of a sentence.
_TACTIC_HEAD = re.compile(
    r"^\s*(i[A-Z]\w*|wp_\w+|intros?\b|apply\b|exact\b|refine\b|destruct\b|induction\b|"
    r"rewrite\b|simpl\b|unfold\b|split\b|left\b|right\b|exists\b|eauto\b|auto\b|lia\b|"
    r"done\b|reflexivity\b|assumption\b|constructor\b|inversion\b|by\b|set\b|pose\b)",
    re.M,
)

#: Vernacular a *statement* may legitimately be.
_STATEMENT_HEADS = (
    "Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark", "Property", "Example",
)


def assert_statement_only(text: str, *, what: str = "proposal") -> None:
    """Reject anything that is a proof rather than a statement.

    Deterministic: no model judges this, and the check runs on the decomposer's
    output before it can reach the graph.
    """
    code = strip_comments(text or "")
    for pattern in _PROOF_MARKERS:
        m = pattern.search(code)
        if m:
            raise ProofEngineeringAttempt(
                f"{what} contains proof text ({m.group(0).strip()!r}). "
                "A decomposer states obligations; it does not prove them."
            )
    for sentence in split_sentences(code):
        if _TACTIC_HEAD.match(sentence.code):
            raise ProofEngineeringAttempt(
                f"{what} contains a tactic ({' '.join(sentence.code.split())[:60]!r}). "
                "A decomposer states obligations; it does not prove them."
            )


@dataclass(frozen=True)
class ChildStatement:
    """One proposed obligation.  There is deliberately nowhere to put a proof."""

    name: str
    statement: str
    rationale: str = ""

    def __post_init__(self) -> None:
        assert_statement_only(self.statement, what=f"child {self.name!r}")


#: Vernacular that declares an *obligation* rather than design.  These are the only
#: heads a design fragment may not contain: an obligation needs stating, freezing and
#: dispatching, which is what `children` is for.
_OBLIGATION_HEADS = ("Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark")


@dataclass(frozen=True)
class DesignDefinition:
    """A piece of design the decomposer proposes.

    PLAN.md 9.3: the sketch -- the invariant catalog and the ghost-state plan -- is a
    *design* artifact, decided before tactic work.  Deciding it is the decomposer's
    job, and it is still not proof engineering.

    The text may be **any non-proof vernacular**: a `Definition`, a `Class`, a
    `Notation`, an `Open Scope`, a `Require`.  Restricting it to named definitions is
    what broke the first orchestrated run -- the design needed `ghost_var` and had no
    permitted way to import it, so it compiled to "The reference ghost_varG was not
    found".  The screen that matters is that it contains no proof; the *contract*
    decides what is permissible, not this schema.
    """

    name: str = ""
    text: str = ""
    rationale: str = ""

    def __post_init__(self) -> None:
        assert_statement_only(self.text, what=f"design {self.name or 'fragment'!r}")


@dataclass(frozen=True)
class PlanProposal:
    """A decomposer's output.

    The type is the enforcement: it has no field a proof body could travel in, so a
    decomposer cannot smuggle one through even if it tries.  Everything that reaches
    the graph from a decomposer passes through here.
    """

    children: tuple[ChildStatement, ...] = ()
    definitions: tuple[DesignDefinition, ...] = ()
    #: `From … Require Import …` lines the design needs.  A designer that picks
    #: `ghost_var` for its ghost state must be able to import it; without this the
    #: design compiles to "The reference ghost_varG was not found".
    imports: tuple[str, ...] = ()
    glue_rationale: str = ""
    rationale: str = ""

    def names(self) -> list[str]:
        return [c.name for c in self.children]

    def definition_names(self) -> list[str]:
        return [d.name for d in self.definitions]


_IDENT = re.compile(r"^[A-Za-z_][\w']*$")


def _as_declaration(name: str, statement: str) -> str:
    """Give a child's statement its `Lemma <name> : … .` header if it lacks one.

    The decomposer is asked for `{name, statement}` and quite reasonably reads
    "statement" as the proposition -- `∀ Φ γ, inv N (I Φ γ) -∗ …` -- rather than a
    whole vernacular declaration. Rejecting that spelling threw away a *correct*
    revision: one rwcas round proposed three well-reasoned obligations this way, was
    refused for "must be exactly one declaration", and the run lost the one repair
    that would have integrated it.

    The name is already given separately, so the header is derivable rather than
    guessed. A statement that already declares something is left exactly as it is --
    this only fills in what is missing, and it never renames.
    """
    text = (statement or "").strip()
    if not text or _declared_name(text):
        return statement
    body = text.rstrip()
    if body.endswith("."):
        body = body[:-1].rstrip()
    return f"Lemma {name} :\n  {body}."


def _declared_name(text: str) -> str:
    """The name a design sentence declares, or `""` for one that declares none.

    Imports and `Context` lines are legitimately nameless; so is anything the
    parser does not recognise, and those all end up placed as additions.
    """
    from pcp.core.vernac import parse_blocks

    try:
        return next((b.name for b in parse_blocks(text) if b.name), "")
    except Exception:
        return ""



def parse_proposal(text: str) -> PlanProposal:
    """Read a decomposer's JSON answer, rejecting proof content deterministically."""
    payload = _extract_json(text)
    if payload is None:
        raise ProofEngineeringAttempt("the decomposer produced no JSON object to read")
    raw_children = payload.get("children") or []
    if not isinstance(raw_children, list):
        raise ProofEngineeringAttempt("`children` must be a list of statements")
    children: list[ChildStatement] = []
    for entry in raw_children:
        if not isinstance(entry, dict):
            raise ProofEngineeringAttempt("each child must be an object with name and statement")
        name = str(entry.get("name", "")).strip()
        statement = str(entry.get("statement", "")).strip()
        if not _IDENT.match(name):
            raise ProofEngineeringAttempt(f"child name {name!r} is not a Rocq identifier")
        if not statement:
            raise ProofEngineeringAttempt(f"child {name!r} has no statement")
        children.append(
            ChildStatement(name=name, statement=_as_declaration(name, statement),
                           rationale=str(entry.get("rationale", "")))
        )
    raw_defs = payload.get("definitions") or []
    if not isinstance(raw_defs, list):
        raise ProofEngineeringAttempt("`definitions` must be a list")
    definitions: list[DesignDefinition] = []
    for entry in raw_defs:
        # A bare sentence is the same design said less carefully -- no role is
        # crossed and no proof text is smuggled, so it is a formatting slip rather
        # than a violation, and `imports` has always been read this way. Rejecting
        # it threw away a fifteen-minute xhigh design round over a pair of braces.
        if isinstance(entry, str):
            entry = {"text": entry}
        if not isinstance(entry, dict):
            raise ProofEngineeringAttempt(
                "each definition must be an object, or a single Rocq sentence"
            )
        name = str(entry.get("name", "")).strip()
        text = str(entry.get("text", "") or entry.get("definition", "")).strip()
        if not text:
            raise ProofEngineeringAttempt(f"design entry {name or '<unnamed>'!r} has no text")
        # The name is what decides whether this fills a blank or is a new
        # declaration, so an omitted one has to be recovered from the sentence:
        # left empty, a redefinition of `value` would be appended beside the stub
        # instead of replacing it, and the file would not compile.
        if not name:
            name = _declared_name(text)
        if name and not _IDENT.match(name):
            raise ProofEngineeringAttempt(f"design name {name!r} is not an identifier")
        definitions.append(
            DesignDefinition(name=name, text=text, rationale=str(entry.get("rationale", "")))
        )
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
        if not re.match(r"^(?:From\s+\S+\s+)?Require\b", line):
            raise ProofEngineeringAttempt(
                f"import {line!r} is not a Require line"
            )
        assert_statement_only(line, what="import")
        imports.append(line if line.endswith(".") else line + ".")

    return PlanProposal(
        children=tuple(children),
        definitions=tuple(definitions),
        imports=tuple(imports),
        glue_rationale=str(payload.get("glue_rationale", "")),
        rationale=str(payload.get("rationale", "")),
    )


def _extract_json(text: str) -> dict | None:
    text = text or ""
    fence = re.search(r"```(?:json)?\s*\n(.*?)```", text, re.S)
    candidates = [fence.group(1)] if fence else []
    start = text.find("{")
    if start >= 0:
        candidates.append(text[start:])
    for candidate in candidates:
        try:
            value = json.loads(candidate)
        except json.JSONDecodeError:
            depth = 0
            for i, ch in enumerate(candidate):
                if ch == "{":
                    depth += 1
                elif ch == "}":
                    depth -= 1
                    if depth == 0:
                        try:
                            value = json.loads(candidate[: i + 1])
                        except json.JSONDecodeError:
                            break
                        return value if isinstance(value, dict) else None
            continue
        if isinstance(value, dict):
            return value
    return None


def validate_proposal(proposal: PlanProposal) -> list[str]:
    """Structural checks on a proposal, beyond "it is not a proof"."""
    problems: list[str] = []
    for definition in proposal.definitions:
        label = definition.name or " ".join(definition.text.split())[:40]
        blocks = parse_blocks(definition.text + "\n")
        # Only two things are wrong here: a proof, or a new *obligation*.  Everything
        # else -- imports, scopes, notations, typeclass instances -- is design, and
        # whether it is allowed is the contract's call, not this function's.
        if any(b.has_proof for b in blocks):
            problems.append(f"design {label!r} carries a proof")
        offending = [b.head for b in blocks if b.head in _OBLIGATION_HEADS]
        if offending:
            problems.append(
                f"design {label!r} declares a {offending[0]}; a new obligation goes in "
                "`children`, so it can be stated, frozen and dispatched like any other"
            )
        if definition.name and blocks and all(b.name != definition.name for b in blocks):
            problems.append(
                f"design {definition.name!r} does not declare {definition.name}"
            )
    if not proposal.children and not proposal.definitions:
        problems.append(
            "the plan has no children: orchestration is required, so a decomposer "
            "must state at least one obligation rather than hand the whole goal to "
            "a single prover"
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
        if blocks[0].head not in _STATEMENT_HEADS:
            problems.append(
                f"child {child.name!r} is a {blocks[0].head}; children must be lemmas"
            )
        if blocks[0].has_proof:
            problems.append(f"child {child.name!r} carries a proof")
    return problems
