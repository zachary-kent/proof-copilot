"""Statement sentinels: deterministic checks at freeze time (PLAN.md 8.4).

Deterministic before model.  Every check here is a program, and a model is the last
resort -- audits are *event-driven*, and one of the events is a sentinel hit.

Only the *free* sentinels live here (no compile): duplicates by hash, the "no
lateral moves" reduction check, converging failures, the partial-correctness flag
and the hypothesis-hygiene comparison.  The costed vacuity probe is not built.

Every text scan goes through :mod:`pcp.rocq.lexer`/:mod:`pcp.rocq.statement`, so
comments, newlines and Texan triples cannot fool a check.
"""

from __future__ import annotations

import re
from collections.abc import Iterable, Mapping
from dataclasses import dataclass, field
from typing import Any, Protocol, cast

from pcp.rocq.lexer import identifiers, strip_comments
from pcp.rocq.statement import (
    normalize_statement,
    split_head,
    statement_binders,
    statement_hash,
    statement_name,
)
from pcp.util.hashing import content_hash


class _Stated(Protocol):
    name: str
    statement: str


@dataclass(frozen=True)
class SentinelHit:
    sentinel: str
    node: str
    detail: str
    #: Blocking hits stop a freeze; advisory ones are recorded and reported.
    blocking: bool = False

    def render(self) -> str:
        mark = "BLOCK" if self.blocking else "note "
        return f"  [{mark}] {self.node}: {self.sentinel} -- {self.detail}"

    def to_json(self) -> dict[str, Any]:
        return {"sentinel": self.sentinel, "node": self.node, "detail": self.detail, "blocking": self.blocking}


@dataclass
class SentinelReport:
    hits: list[SentinelHit] = field(default_factory=list)

    @property
    def blocking(self) -> list[SentinelHit]:
        return [h for h in self.hits if h.blocking]

    @property
    def ok(self) -> bool:
        return not self.blocking

    def render(self) -> str:
        if not self.hits:
            return "sentinels: clean"
        return "sentinels:\n" + "\n".join(h.render() for h in self.hits)

    def to_json(self) -> dict[str, Any]:
        return {"ok": self.ok, "hits": [h.to_json() for h in self.hits]}


# ------------------------------------------------------------------ hashing

def statement_body(statement: str) -> str:
    """The proposition without ``[attrs] [modifiers] Lemma name`` -- a rename is not a new lemma."""
    head, binders, ty = split_head(statement)
    if not head:
        return normalize_statement(statement)
    name = statement_name(statement)
    prefix = f"{head} {binders}".split()
    if name and name in prefix:
        # Modifiers (``Polymorphic Lemma b ...``) push the name into the binder text.
        binders = " ".join(prefix[prefix.index(name) + 1 :])
    return normalize_statement(f"{binders} : {ty}")


def body_hash(statement: str) -> str:
    """Name-insensitive statement hash (prefix ``s:``, like :func:`statement_hash`)."""
    return content_hash(statement_body(statement), prefix="s:")


def is_lateral(request: str, goal: str) -> bool:
    """No lateral moves (PLAN.md 8.4): a request that restates the goal is not progress."""
    return body_hash(request) == body_hash(goal)


# ------------------------------------------------------------------ the checks

def partial_correctness(name: str, statement: str) -> list[SentinelHit]:
    """Iris ``WP`` and Texan triples are partial: divergence satisfies every spec.

    Flagged iff the statement (comments stripped) mentions ``WP``/``wp`` or a
    ``{{{ P }}} e {{{ Q }}}`` triple and neither ``twp`` nor a total postcondition
    ``[{ ... }]`` / ``[[{ ... }]]``.  The sentinel does not decide -- it makes the
    auditor decide deliberately rather than by default.
    """
    code = strip_comments(statement)
    words = set(identifiers(code))
    partial = bool(words & {"WP", "wp"}) or "{{{" in code
    total = bool(words & {"twp", "TWP"}) or "[{" in code
    if partial and not total:
        return [
            SentinelHit(
                "partial-correctness flag",
                name,
                "uses partial `WP`/`{{{ }}}`: divergence satisfies this spec. Use `twp` / `[{ }]` "
                "or carry an explicit termination side condition if that is not intended",
            )
        ]
    return []


#: Resource forms that are never persistent: exclusive-auth fragments, exclusive
#: elements, auth/points-to/ghost-map at an owned fraction, weakest preconditions, lock
#: tokens, ghost variables, later credits, non-atomic tokens, cancellable-invariant
#: tokens, mono-nat / ghost-map authorities, saved props at an owned fraction.  The
#: discarded forms (``↦□``, ``↦{DfracDiscarded}``, ``●□``) are persistent and excluded;
#: ``inv``, ``⌜ ⌝``, ``□`` never match.
_DISCARDED = r"(?!\s*(?:□|\{\s*DfracDiscarded\s*\}))"
_NON_PERSISTENT = re.compile(
    r"◯E|●E|\bExcl\b|↦" + _DISCARDED + r"|↪\[[^\]]*\]" + _DISCARDED + r"|●" + _DISCARDED
    + r"|\bWP\b|\bwp\b|\bghost_var\b|\blocked\b|£|\bna_own\b|\bcinv_own\b|\bmono_nat_auth_own\b|\bghost_map_auth\b"
    + r"|saved_\w+_own\s+\S+\s+\(?\s*DfracOwn\b"
)
#: One argument of an invariant or a persistent predicate: a parenthesised term (one
#: level of nesting) or a bare token that is not a connective.
_ARG = r"(?:\((?:[^()]|\([^()]*\))*\)|[^\s()⌜∗∧∨→⊢-]+)"
#: Sub-terms that are persistent whatever they hold, masked before the search: a boxed
#: term (a box before a quantifier scopes over the rest of the premise), an invariant
#: application (namespace, ghost names, the body: up to six arguments), and a pure
#: embedding ``⌜ ⌝``.
_MASKED = re.compile(
    r"(?:(?<![↦\]●◯])□|■|<pers>)\s*(?:(?:∀|∃|forall\b|exists\b).*$|" + _ARG + r")"
    r"|\b(?:inv|na_inv|cinv)\b(?:\s+" + _ARG + r"){2,6}"
    r"|⌜[^⌝]*⌝",
    re.S,
)  # the □ of a discarded fraction (`↦□`, `↪[γ]□`, `●□`) belongs to the resource, not to a box
#: A quantifier or later prefix before a premise's head: ``∀ vs, p16 γ vs Q``, ``▷ inv …``.
_BINDER_PREFIX = re.compile(r"^\s*(?:(?:∀|∃|forall\s|exists\s)[^,]*,|▷)\s*")
#: A declared persistence instance in a design definition: ``Instance ... : Persistent (p ...)``.
_PERSISTENT_INSTANCE = re.compile(r"\bPersistent\s*\(\s*([A-Za-z_][\w']*)")
#: A conjunct of a design definition's body that is persistent by its own head.
_PERSISTENT_HEADS = ("□", "■", "<pers>", "inv ", "na_inv ", "cinv ", "⌜", "meta ", "True", "emp")
#: Saved propositions/predicates are persistent only at the discarded fraction.
_SAVED_DISCARDED = re.compile(r"saved_(?:prop|pred|anything)_own\s+\S+\s+DfracDiscarded\b")
#: Library predicates that are persistent by convention and take spatial arguments.
_LIBRARY_PERSISTENT: frozenset[str] = frozenset({"is_lock", "is_rw_lock", "is_barrier"})
_OPEN, _CLOSE = "([{", ")]}"


def _skip_string(text: str, i: int) -> int:
    """Index just past the string literal opening at ``text[i]``."""
    j = i + 1
    while j < len(text):
        if text[j] == '"':
            if text[j + 1 : j + 2] == '"':  # Coq escapes a quote by doubling it
                j += 2
                continue
            return j + 1
        j += 1
    return j


def _split_depth0(text: str, tokens: tuple[str, ...]) -> list[str]:
    """Split ``text`` at any of ``tokens`` occurring at bracket depth 0, outside strings."""
    parts: list[str] = []
    depth = start = i = 0
    while i < len(text):
        ch = text[i]
        if ch == '"':
            i = _skip_string(text, i)
            continue
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth -= 1
        elif depth == 0:
            hit = next((t for t in tokens if text.startswith(t, i)), None)
            if hit is not None and not (hit == "⊢" and text[i - 1 : i] == "⊣"):
                parts.append(text[start:i])
                i += len(hit)
                start = i
                continue
        i += 1
    parts.append(text[start:])
    return parts


def _depth0_text(text: str) -> str:
    """``text`` with every bracketed sub-term blanked, whatever its nesting."""
    out: list[str] = []
    depth = 0
    for ch in text:
        if ch in _OPEN:
            depth += 1
            out.append(" ")
        elif ch in _CLOSE:
            depth = max(0, depth - 1)
            out.append(" ")
        elif depth == 0:
            out.append(ch)
        else:
            out.append(" ")
    return "".join(out)


def _top_conjuncts(body: str) -> list[str]:
    """Split at ``∗``, ``∧``, ``∨`` at bracket depth 0 (the wand is excluded on purpose:
    an unboxed wand is not persistent, and the caller rejects it)."""
    return _split_depth0(body, ("∗", "∧", "∨"))


def _normalise_conjunct(text: str) -> str:
    """Whitespace-normalised, quantifier/later prefix and outer parentheses stripped."""
    c = " ".join(text.split()).strip()
    while True:
        m = _BINDER_PREFIX.match(c)
        if m and m.end() > 0:
            c = c[m.end():].strip()
            continue
        if c.startswith("(") and c.endswith(")"):
            c = c[1:-1].strip()
            continue
        if c.startswith("("):
            c = c[1:].strip()
            continue
        return c


def _visibly_persistent(definition_text: str) -> bool:
    """Whether a `Definition p ... : iProp Σ := body.` is persistent by its own shape:
    every top-level part (under any quantifier, later, or parentheses) is boxed, pure,
    an invariant, or a discarded saved prop, and no unboxed wand, implication or update
    sits at the top.  Unknown shapes count as not persistent: the repairer can box the
    body or move the premise, and either is a cheap fix -- the alternative is a prover
    attempt spent discovering the triple is unprovable."""
    _, sep, body = strip_comments(definition_text).partition(":=")
    if not sep:
        return True  # not a definition with a body (a Notation, an Instance): trust it
    body = " ".join(body.split()).strip().rstrip(".").strip()
    if body.endswith("%I"):
        body = body[:-2].strip()
    body = _normalise_conjunct(body)
    if any(tok in _depth0_text(body) for tok in ("-∗", "→", "={")):
        return False  # an unboxed wand, implication or update at the top is not persistent
    for part in _top_conjuncts(body):
        c = _normalise_conjunct(part)
        if not (c.startswith(_PERSISTENT_HEADS) or _SAVED_DISCARDED.match(c) or c == ""):
            return False
    return True


def _declared_persistent(definitions: Mapping[str, str]) -> set[str]:
    """Names given a ``Persistent`` instance anywhere in the design."""
    out: set[str] = set()
    for text in definitions.values():
        code = strip_comments(text)
        if "Instance" in identifiers(code):
            out.update(m.group(1) for m in _PERSISTENT_INSTANCE.finditer(code))
    return out


def _top_level_triple(code: str) -> int:
    """Index of the statement's own ``{{{`` / ``[[{`` (bracket depth 0, outside strings),
    else -1: a triple nested in a WP postcondition or a parenthesised premise is not the
    boxed goal."""
    depth = 0
    i = 0
    while i < len(code):
        ch = code[i]
        if ch == '"':
            i = _skip_string(code, i)
            continue
        if depth == 0 and (code.startswith("{{{", i) or code.startswith("[[{", i)):
            return i
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth -= 1
        i += 1
    return -1


def _split_wands(text: str) -> list[str]:
    """Split on ``-∗`` (and the entailment ``⊢``) at bracket depth 0 only: a boxed
    premise may itself contain a wand.  ``P ⊢ {{{ … }}}`` states P outside the boxed
    triple exactly as ``P -∗ {{{ … }}}`` does."""
    return _split_depth0(text, ("-∗", "⊢"))


def _after_header(first_premise: str) -> str:
    """The first wand premise still carries `Lemma name (binders) :`; return what follows
    the statement's top-level colon (binder colons sit one level down)."""
    depth = 0
    for i, ch in enumerate(first_premise):
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth -= 1
        elif ch == ":" and depth == 0 and first_premise[i + 1 : i + 2] != "=" and first_premise[i - 1 : i] != ":":
            return first_premise[i + 1 :]
    return first_premise


def _head_identifier(premise: str) -> str:
    lead = premise.strip().lstrip("(").strip()
    while (m := _BINDER_PREFIX.match(lead)) and m.end() > 0:
        lead = lead[m.end():].lstrip("(").strip()
    return next(iter(identifiers(lead)), "")


def _mask_persistent_applications(premise: str, heads: set[str]) -> str:
    """Blank an application headed by a known-persistent predicate, arguments included
    (``is_lock γ lk (l ↦ v)``: the points-to is the lock's, not the caller's)."""
    if not heads:
        return premise
    pattern = re.compile(r"\b(?:" + "|".join(re.escape(h) for h in sorted(heads)) + r")\b(?:\s+" + _ARG + r")*")
    return pattern.sub(" ", premise)


def resources_outside_triple(
    name: str, statement: str, *, definitions: Mapping[str, str] | None = None
) -> list[SentinelHit]:
    """A Texan triple ``{{{ P }}} e {{{ Q }}}`` (or the total ``[[{ P }]] e [[{ Q }]]``) is
    ``□``-boxed: everything its proof needs that is not persistent must be in ``P``, not
    a wand premise before the triple, because introducing the ``□`` discards the spatial
    context.  A statement of the shape ``own γ (◯E _) -∗ {{{ True }}} e {{{ Q }}}`` is
    unprovable by construction, and a prover would spend an attempt discovering it
    (spec-only seqlock_wf, round 8, ``c4_close``).  Blocking: a repair, not a redesign.

    Only the statement's own triple counts (bracket depth 0, outside strings); premises
    are split at depth-0 wands and entailments; boxed terms, invariant applications,
    pure embeddings and applications of known-persistent predicates are masked; a
    design-defined predicate heading a premise is non-persistent unless its body is
    visibly persistent or the design declares a ``Persistent`` instance for it.
    """
    code = strip_comments(statement)
    cut = _top_level_triple(code)
    if cut < 0:
        return []
    premises = _split_wands(code[:cut])[:-1]  # every wand antecedent stated before the triple
    if premises:
        premises[0] = _after_header(premises[0])
    texts = definitions or {}
    declared = _declared_persistent(texts)
    persistent_heads = declared | {k for k, v in texts.items() if _visibly_persistent(v)} | _LIBRARY_PERSISTENT
    designed = {k for k, v in texts.items() if k not in persistent_heads}
    bad: list[str] = []
    for premise in premises:
        unboxed = _mask_persistent_applications(_MASKED.sub(" ", premise), persistent_heads)
        if _NON_PERSISTENT.search(unboxed):
            bad.append(premise.strip())
            continue
        # A design-defined predicate *heading* a premise (`p16 γ ws Q`) is persistent only
        # if its body says so.  As an argument (`inv N (d15 ...)`) it is whatever wraps it.
        if _head_identifier(unboxed) in designed:
            bad.append(premise.strip())
    if not bad:
        return []
    return [
        SentinelHit(
            "resource outside triple", name,
            "a non-persistent resource is a wand premise before the `{{{ }}}` triple "
            f"({bad[0][-80:]}); the triple is □-boxed, so move it into the precondition "
            "(or make the definition visibly persistent by boxing its body)",
            blocking=True,
        )
    ]


def hygiene_sentinel(parent_statement: str, child_statement: str, name: str, *, slack: int = 3) -> list[SentinelHit]:
    """A child carrying many more explicit binders than its parent is accumulating (PLAN.md 8.2)."""
    parent = len(statement_binders(parent_statement))
    child = len(statement_binders(child_statement))
    if child > parent + slack:
        return [
            SentinelHit(
                "hygiene sentinel",
                name,
                f"carries {child} explicit binders against the parent's {parent}; check for incidental accumulation",
            )
        ]
    return []


def _pairs(stuck: Mapping[str, str] | Iterable[Any]) -> list[tuple[str, str]]:
    if isinstance(stuck, Mapping):
        return list(stuck.items())
    out: list[tuple[str, str]] = []
    for item in stuck:
        if isinstance(item, tuple):
            out.append((str(item[0]), str(item[1])))
        else:
            stated = cast(Any, item)
            out.append((str(stated.name), str(stated.statement)))
    return out


def _existing(existing: Mapping[str, str] | Iterable[str]) -> dict[str, str]:
    if isinstance(existing, Mapping):
        return dict(existing)
    return {h: "" for h in existing}


def run_free_sentinels(
    specs: Iterable[_Stated],
    *,
    existing_hashes: Mapping[str, str] | Iterable[str] = (),
    root_statement: str = "",
    stuck_statements: Mapping[str, str] | Iterable[Any] = (),
    definitions: Mapping[str, str] | None = None,
) -> SentinelReport:
    """Everything that costs nothing, over a plan's children (or a decomposer's).

    ``existing_hashes`` are hashes of statements already in the graph (either
    :func:`statement_hash` or :func:`body_hash`; both are compared), optionally
    mapped to the node name for the message.  ``root_statement`` is the parent whose
    plan this is: a child restating it is a lateral move, and it is the hygiene
    baseline.  ``stuck_statements`` are nodes already ``stuck``/``contested``: a new
    statement equal to one of them is a converging failure -- a design signal, not
    work.
    """
    report = SentinelReport()
    known = _existing(existing_hashes)
    root_hash = body_hash(root_statement) if root_statement else None
    stuck = [(n, body_hash(s)) for n, s in _pairs(stuck_statements)]
    seen: dict[str, str] = {}
    for spec in specs:
        name, statement = spec.name, spec.statement
        h_body = body_hash(statement)
        h_text = statement_hash(statement)
        if root_hash is not None and h_body == root_hash:
            report.hits.append(
                SentinelHit(
                    "reduction sentinel", name,
                    "restates the root it is meant to prove; that is not progress",
                    blocking=True,
                )
            )
        elif h_body in seen:
            report.hits.append(
                SentinelHit("duplicate statement", name, f"same statement as {seen[h_body]}", blocking=True)
            )
        elif h_body in known or h_text in known:
            other = known.get(h_body) or known.get(h_text) or "an existing node"
            report.hits.append(
                SentinelHit("duplicate statement", name, f"same statement as {other}", blocking=True)
            )
        else:
            seen[h_body] = name
        for stuck_name, stuck_hash in stuck:
            if stuck_hash == h_body:
                report.hits.append(
                    SentinelHit(
                        "converging failure", name,
                        f"duplicates `{stuck_name}`, which is already stuck or contested; "
                        "route this to its decomposer as a re-plan",
                        blocking=True,
                    )
                )
                break
        report.hits.extend(partial_correctness(name, statement))
        report.hits.extend(resources_outside_triple(name, statement, definitions=definitions))
        if root_statement:
            report.hits.extend(hygiene_sentinel(root_statement, statement, name))
    return report
