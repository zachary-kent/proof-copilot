"""The integrity gate: deterministic, model-free, immutable (PLAN.md 8.7; ARCHITECTURE.md §4).

A pure function of (frozen development, worker body).  No model is involved at any
point -- not to check the proof, and above all not to review a success.

Order of the checks, cheapest first, and why each exists:

1. **static body checks** -- the body is validated *as a proof body by construction*
   (:func:`pcp.rocq.body.validate_body`: tactic sentences only, an allowlist of
   harmless queries) and each violation is filed under the legacy check name it
   belongs to.  No denylist: ``Qed.``/``Abort.`` in a body, ``Set Nested Proofs
   Allowed``, ``Unset Guard Checking``, a global ``Notation`` -- all rejected
   whether or not they start a line, and comments are stripped by the real lexer;
2. **statement pinning** and **``Proof using`` discipline** -- asserted on the
   assembly, as regression guards on span arithmetic;
3. **structural recheck** -- the assembly is re-lexed: the target block must carry
   exactly the frozen statement, exactly the submitted body and the expected ender,
   and the assembly's declaration list must equal that of the same assembly with the
   body replaced by ``admit.``.  A body cannot define, redefine or re-open anything;
4. **compile** in a fresh directory (``pcp.rocq.project.compile_text``); a compiler
   that is missing or times out is *infrastructure* (``GateResult.infrastructure``)
   and never the worker's fault;
5. **axiom hygiene** -- ``Print Assumptions`` on the module-qualified name, parsed by
   grammar (wrapped types, ``assumed guarded`` entries, injected output), whitelist
   and stubs matched by suffix;
6. advisory: which stubs the proof rests on; the opt-in unused-premise removal probe.

:class:`Gate` is a frozen dataclass: two threads gating two nodes share nothing.
"""

from __future__ import annotations

import time
from collections import Counter
from collections.abc import Iterable
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Protocol

from pcp.errors import GateError, UsageError
from pcp.orch.failures import GATE_COULD_NOT_RUN
from pcp.rocq.assemble import Development, NodeSpec, has_proof_using_directive
from pcp.rocq.assumptions import classify_assumptions, parse_assumptions, trailer
from pcp.rocq.body import Violation, validate_body
from pcp.rocq.decls import ProofBlock, parse_blocks
from pcp.rocq.lexer import first_word, identifiers, split_sentences
from pcp.rocq.project import compile_text, coq_project_flags
from pcp.rocq.statement import normalize_statement, remove_binder, statement_binders
from pcp.util.text import tail_lines

#: Axioms Rocq/Iris developments legitimately rest on.  Anything else is an event.
DEFAULT_AXIOM_WHITELIST: tuple[str, ...] = (
    "functional_extensionality_dep",
    "propositional_extensionality",
    "proof_irrelevance",
    "Classical_Prop.classic",
    "ClassicalEpsilon.constructive_indefinite_description",
    "Eqdep.Eq_rect_eq.eq_rect_eq",
    "JMeq_eq",
)

# Check names are part of the external contract (§1.2): `pcp failures` and the
# advice table key on them.
CHECK_NO_ADMIT = "no new Admitted / admit / Axiom / Parameter"
CHECK_ESCAPE = "no escape hatches"
CHECK_AMBIENT = "ambient-state hygiene (no global Instance/Hint/Notation/Ltac)"
CHECK_PINNING = "statement pinning by construction"
CHECK_PROOF_USING = "`Proof using` discipline"
CHECK_STRUCTURE = "body is a single proof (structural recheck)"
CHECK_COMPILES = "compiles (coqc)"
CHECK_AXIOMS = "axiom hygiene (Print Assumptions ⊆ whitelist + open stubs)"
CHECK_AXIOMS_DESIGN = "axiom hygiene (Print Assumptions ⊆ whitelist)"
CHECK_STUBS = "rests on open stubs"
CHECK_UNUSED = "unused-premise report"
CHECK_CONTRACT = "design contract (only declared-mutable definitions changed)"

#: Heads whose registration changes how *future* statements elaborate (item 7).
_AMBIENT_HEADS = frozenset({
    "Instance", "Hint", "Notation", "Ltac", "Ltac2", "Canonical", "Coercion", "Existing",
    "Reserved", "Tactic", "Infix", "Arguments", "Opaque", "Transparent", "Strategy", "Typeclasses",
})
_MODIFIER_WORDS = frozenset({
    "Local", "Global", "Export", "Program", "Polymorphic", "Monomorphic", "Cumulative",
    "NonCumulative", "Private",
})
#: ``Set``/``Unset`` option prefixes that turn the kernel off or change proof structure.
_HATCH_OPTIONS = (
    ("Universe", "Checking"), ("Guard", "Checking"), ("Positivity", "Checking"),
    ("Elimination", "Schemes"), ("Nested", "Proofs"),
)


@dataclass(frozen=True)
class Check:
    name: str
    ok: bool
    detail: str = ""
    #: Advisory checks report but do not fail the gate.
    advisory: bool = False

    def render(self) -> str:
        mark = "ok " if self.ok else ("warn" if self.advisory else "FAIL")
        line = f"  [{mark}] {self.name}"
        if self.detail:
            line += f": {self.detail}"
        return line

    def to_json(self) -> dict[str, Any]:
        return {"name": self.name, "ok": self.ok, "detail": self.detail, "advisory": self.advisory}

    @classmethod
    def from_json(cls, d: dict[str, Any]) -> Check:
        return cls(str(d.get("name", "")), bool(d.get("ok")), str(d.get("detail", "")), bool(d.get("advisory")))


@dataclass
class GateResult:
    """Self-contained verdict: the :class:`Gate` keeps nothing per run."""

    ok: bool
    checks: list[Check] = field(default_factory=list)
    assumptions: dict[str, list[str]] = field(default_factory=dict)
    compile_output: str = ""
    elapsed_s: float = 0.0
    assembled: str = ""
    unused_premises: list[str] = field(default_factory=list)
    #: The gate itself could not run (no coqc, compile timeout): never blame the worker.
    infrastructure: bool = False

    @property
    def failures(self) -> list[Check]:
        return [c for c in self.checks if not c.ok and not c.advisory]

    def render(self) -> str:
        head = "gate: PASS" if self.ok else "gate: FAIL"
        lines = [f"{head} ({self.elapsed_s:.1f}s)"]
        lines += [c.render() for c in self.checks]
        if not self.ok and self.compile_output:
            lines.append("")
            lines.append(tail_lines(self.compile_output, 40))
        return "\n".join(lines)

    def to_json(self) -> dict[str, Any]:
        return {
            "ok": self.ok,
            "elapsed_s": self.elapsed_s,
            "checks": [c.to_json() for c in self.checks],
            "assumptions": self.assumptions,
            "unused_premises": list(self.unused_premises),
        }

    @classmethod
    def from_json(cls, d: dict[str, Any]) -> GateResult:
        checks = [Check.from_json(c) for c in d.get("checks", [])]
        infra = any(c.name == CHECK_COMPILES and c.detail.startswith(GATE_COULD_NOT_RUN) for c in checks)
        return cls(
            ok=bool(d.get("ok")),
            checks=checks,
            assumptions={k: list(v) for k, v in (d.get("assumptions") or {}).items()},
            elapsed_s=float(d.get("elapsed_s", 0.0)),
            unused_premises=list(d.get("unused_premises") or []),
            infrastructure=infra,
        )


class _Contract(Protocol):
    results: frozenset[str]

    def check(self, original: str, candidate: str) -> Check: ...


# ------------------------------------------------------------------ static checks

def _strip_attributes(code: str) -> str:
    text = code.lstrip()
    while text.startswith("#["):
        close = text.find("]")
        if close < 0:
            break
        text = text[close + 1 :].lstrip()
    return text


def _command_words(code: str) -> list[str]:
    """The identifiers of a vernacular sentence with attributes and modifiers skipped."""
    words = identifiers(_strip_attributes(code))
    i = 0
    while i < len(words) and words[i] in _MODIFIER_WORDS:
        i += 1
    return words[i:]


def _declaration_head(code: str) -> tuple[str, str]:
    """``(head, next word)`` of a vernacular sentence, modifiers and attributes skipped."""
    words = _command_words(code)
    head = words[0] if words else first_word(code)
    nxt = words[1] if len(words) > 1 else ""
    return head, nxt


def _has_bypass_attribute(code: str) -> bool:
    text = code.lstrip()
    while text.startswith("#["):
        close = text.find("]")
        if close < 0:
            return False
        if "bypass_check" in text[: close + 1]:
            return True
        text = text[close + 1 :].lstrip()
    return False


def escape_hatch(code: str) -> str | None:
    """Why a vernacular sentence is an escape hatch (item 6), or ``None``.

    Modifiers are skipped first: ``Local Unset Guard Checking.`` is the same hatch as
    ``Unset Guard Checking.``, and looking at the first word alone let it through the
    design-mode fragment scan (review finding).
    """
    head, nxt = _declaration_head(code)
    if head in ("Set", "Unset"):
        words = _command_words(code)[1:]
        for option in _HATCH_OPTIONS:
            if tuple(words[: len(option)]) == option:
                return f"{head} {' '.join(option)}"
        return None
    if head == "Obligation" and nxt == "Tactic":
        return "Obligation Tactic override"
    if _has_bypass_attribute(code):
        return "bypass_check attribute"
    return None


def _check_for(v: Violation) -> str:
    """Which legacy check a body violation belongs to."""
    if v.reason.startswith("`Set`/`Unset`"):
        return CHECK_ESCAPE if escape_hatch(v.sentence) else CHECK_NO_ADMIT
    if v.reason.startswith("vernacular command"):
        if escape_hatch(v.sentence):
            return CHECK_ESCAPE
        head, _nxt = _declaration_head(v.sentence)
        if head in _AMBIENT_HEADS:
            return CHECK_AMBIENT
    return CHECK_NO_ADMIT


def static_checks(bodies: dict[str, str], *, admitted: Iterable[str] = ()) -> list[Check]:
    """Checks 1-3 over ``{node: body}``, decided by reading the bodies alone.

    Built on :func:`validate_body`, so the names are the legacy ones but the
    decision is structural: anything that is not a tactic sentence is rejected.
    ``admitted`` names bodies that end in ``Admitted`` (design mode): ``admit`` is
    not an offence there, but every vernacular sentence still is.
    """
    offenders: dict[str, list[str]] = {CHECK_NO_ADMIT: [], CHECK_ESCAPE: [], CHECK_AMBIENT: []}
    tolerated = set(admitted)
    for node, body in bodies.items():
        for v in validate_body(body):
            if node in tolerated and v.reason.startswith("forbidden tactic"):
                continue
            offenders[_check_for(v)].append(f"{node}: {v.render()}")
    return [Check(name, not found, "; ".join(found)) for name, found in offenders.items()]


# ------------------------------------------------------------------ the gate

@dataclass(frozen=True)
class Gate:
    """Immutable: every run is a pure function of its arguments (bug class "gate cross-contamination")."""

    dev: Development
    axiom_whitelist: tuple[str, ...] = DEFAULT_AXIOM_WHITELIST
    extra_whitelist: tuple[str, ...] = ()
    timeout: float = 600.0
    scratch_root: Path | None = None

    def __init__(
        self,
        dev: Development,
        *,
        axiom_whitelist: Iterable[str] = DEFAULT_AXIOM_WHITELIST,
        extra_whitelist: Iterable[str] = (),
        timeout: float = 600.0,
        scratch_root: str | Path | None = None,
    ) -> None:
        object.__setattr__(self, "dev", dev)
        object.__setattr__(self, "axiom_whitelist", tuple(axiom_whitelist))
        object.__setattr__(self, "extra_whitelist", tuple(extra_whitelist))
        object.__setattr__(self, "timeout", float(timeout))
        object.__setattr__(self, "scratch_root", Path(scratch_root) if scratch_root is not None else None)

    @property
    def whitelist(self) -> frozenset[str]:
        return frozenset(self.axiom_whitelist) | frozenset(self.extra_whitelist)

    @property
    def flags(self) -> list[str]:
        return coq_project_flags(self.dev.root)

    @staticmethod
    def static_checks(bodies: dict[str, str]) -> list[Check]:
        return static_checks(bodies)

    # -- per-node / integration --------------------------------------------
    def run(
        self,
        anchor: str,
        nodes: list[NodeSpec],
        *,
        target: str | None = None,
        target_body: str | None = None,
        truncate: bool = True,
        check_assumptions: bool = True,
        extra_preamble: str = "",
        unused_premise_report: bool = False,
        stub_prefix: bool = False,
    ) -> GateResult:
        """Gate one node (``target``, default the anchor) against the frozen development.

        Sibling nodes still stubbed with ``Admitted`` are legitimate assumptions for a
        *per-node* gate (Claim 1); refusing them would serialise the frontier.
        Integration (``truncate=False`` over a fully proved set) has no stubs.
        """
        started = time.perf_counter()
        target = target or anchor
        block = self.dev.block(anchor)
        if block is None:
            raise GateError(f"{self.dev.path}: no declaration named {anchor!r} to anchor the assembly")
        if any(spec.name == anchor for spec in nodes):
            raise GateError(f"the anchor {anchor!r} may not also appear in the node list")
        target_spec = next((s for s in nodes if s.name == target), None)
        if target != anchor and (target_spec is None or target_spec.body is None):
            raise GateError(f"target {target!r} is not among the nodes with a body")
        body = target_body if target == anchor else (target_spec.body if target_spec else None)

        bodies = {spec.name: spec.body for spec in nodes if spec.body is not None}
        if target_body is not None:
            bodies[anchor] = target_body
        checks = static_checks(bodies)

        modules = tuple(s.name for s in self.dev.scopes_at(block.statement_start) if s.kind == "module")
        qualify = _qualifier(modules)
        proved = [spec.name for spec in nodes if spec.body is not None] + ([anchor] if target_body is not None else [])
        stubs = {qualify(spec.name) for spec in nodes if spec.body is None}
        if target_body is None:
            stubs.add(qualify(anchor))
        trailer_text = trailer([qualify(n) for n in proved]) if check_assumptions and proved else ""

        try:
            assembly = self.dev.assemble(
                anchor, nodes, anchor_body=target_body, truncate=truncate,
                extra_preamble=extra_preamble, trailer=trailer_text, stub_prefix=stub_prefix,
            )
        except UsageError as exc:
            raise GateError(str(exc)) from None
        stubs |= set(assembly.stubbed)

        frozen = block.statement if target == anchor else (target_spec.statement if target_spec else "")
        checks.append(_pinning_check(assembly.text, frozen))
        checks.append(_proof_using_check(assembly.text))
        reference = self.dev.assemble(
            anchor, _with_body(nodes, target, "admit."),
            anchor_body="admit." if target == anchor else target_body,
            truncate=truncate, extra_preamble=extra_preamble, trailer=trailer_text, stub_prefix=stub_prefix,
        )
        transparent = block.ender == "Defined" if target == anchor else bool(target_spec and target_spec.transparent)
        checks.append(structural_recheck(assembly.text, reference.text, target, frozen, body or "", transparent))

        result = GateResult(ok=False, checks=checks, assembled=assembly.text)
        if any(not c.ok and not c.advisory for c in checks):
            result.checks.append(Check(CHECK_COMPILES, False, "skipped: static checks failed"))
            result.elapsed_s = time.perf_counter() - started
            return result

        compiled = self._compile(assembly.text, result)
        if compiled and check_assumptions and proved:
            self._assumption_checks(result, proved, qualify, stubs, CHECK_AXIOMS)
        if compiled and unused_premise_report and body is not None:
            unused, note = self._unused_premises(anchor, nodes, target, target_body, extra_preamble, stub_prefix)
            result.unused_premises = unused
            result.checks.append(
                Check(CHECK_UNUSED, not unused, ("the proof does not need: " + ", ".join(unused)) if unused else note, advisory=True)
            )
        result.ok = all(c.ok or c.advisory for c in result.checks)
        result.elapsed_s = time.perf_counter() - started
        return result

    def _compile(self, text: str, result: GateResult) -> bool:
        cres = compile_text(
            text, filename=self.dev.path.name, root=self.dev.root, flags=self.flags,
            timeout=self.timeout, scratch_root=self.scratch_root,
        )
        result.compile_output = cres.output
        if cres.unavailable or cres.timed_out:
            reason = cres.unavailable or f"coqc timed out after {self.timeout:.0f}s"
            result.checks.append(Check(CHECK_COMPILES, False, f"{GATE_COULD_NOT_RUN} {reason}"))
            result.infrastructure = True
            return False
        result.checks.append(Check(CHECK_COMPILES, cres.ok, "" if cres.ok else cres.first_error()))
        result._stdout = cres.stdout  # type: ignore[attr-defined]
        return cres.ok

    def _assumption_checks(
        self, result: GateResult, proved: list[str], qualify: Any, stubs: set[str], check_name: str
    ) -> None:
        qualified = [qualify(n) for n in proved]
        report = parse_assumptions(getattr(result, "_stdout", ""), qualified)
        bare = dict(zip(qualified, proved, strict=True))
        result.assumptions = {bare[q]: axioms for q, axioms in report.to_json().items()}
        bad: list[str] = []
        leaning: list[str] = []
        for q, axioms in report.by_name.items():
            _ok, on_stubs, offending = classify_assumptions(axioms, whitelist=set(self.whitelist), stubs=stubs)
            if offending:
                bad.append(f"{bare[q]}: {', '.join(a.render() for a in offending)}")
            leaning.extend(a.name for a in on_stubs)
        if report.failed:
            bad.append(
                "could not read Print Assumptions output for " + ", ".join(bare[q] for q in report.failed)
                + "; treat as unverified"
            )
        result.checks.append(Check(check_name, not bad, "; ".join(bad)))
        if leaning:
            result.checks.append(
                Check(CHECK_STUBS, True, ", ".join(sorted(set(leaning))) + " (expected until they are discharged)", advisory=True)
            )

    def _unused_premises(
        self, anchor: str, nodes: list[NodeSpec], target: str, target_body: str | None,
        extra_preamble: str, stub_prefix: bool, *, max_probes: int = 8,
    ) -> tuple[list[str], str]:
        """Premises the proof does not need -- by removal probe, not by term inspection.

        ``Qed`` is opaque and even ``Defined`` elides implicits, so reading the term is
        unsound; asking the kernel (restate without the binder, recompile) is ground
        truth at one compile per candidate.  Bounded, advisory, and nothing it compiles
        ever reaches the development.
        """
        if target == anchor:
            statement = self.dev.require_block(anchor).statement
        else:
            statement = next(s.statement for s in nodes if s.name == target)
        candidates = statement_binders(statement)
        if not candidates:
            return [], "no explicit binders to probe"
        if len(candidates) > max_probes:
            return [], f"{len(candidates)} binders exceeds the probe budget of {max_probes}"
        unused: list[str] = []
        for name in candidates:
            weaker = remove_binder(statement, name)
            if weaker is None:
                continue
            if target == anchor:
                assembly = self.dev.assemble(
                    anchor, nodes, anchor_body=target_body, truncate=True, extra_preamble=extra_preamble,
                    statement_override=weaker, stub_prefix=stub_prefix,
                )
            else:
                probe_nodes = [s if s.name != target else NodeSpec(s.name, weaker, s.body, s.mockable, s.transparent) for s in nodes]
                assembly = self.dev.assemble(
                    anchor, probe_nodes, anchor_body=target_body, truncate=True, extra_preamble=extra_preamble,
                    stub_prefix=stub_prefix,
                )
            cres = compile_text(
                assembly.text, filename=self.dev.path.name, root=self.dev.root, flags=self.flags,
                timeout=self.timeout, scratch_root=self.scratch_root,
            )
            if cres.ok:
                unused.append(name)
        return unused, ""

    # -- design submissions ------------------------------------------------
    def run_design(
        self,
        candidate_text: str,
        contract: _Contract,
        *,
        proved: list[str] | None = None,
        check_assumptions: bool = True,
    ) -> GateResult:
        """Gate a whole-file design submission against a :class:`DesignContract`.

        The submitter supplies definitions *and* proofs; what it may not supply is a
        different specification, an escape hatch anywhere in the file, or an
        ``Admitted`` result.  ``proved`` defaults to every result the contract names
        plus every ``Qed`` lemma; ``Admitted`` lemmas that are not results are stubs.
        """
        started = time.perf_counter()
        blocks = parse_blocks(candidate_text)
        # Every script body, Admitted ones included: an ``Unset Universe Checking``
        # inside an admitted helper is global state, not a proof (review finding).
        bodies = {_block_key(b): b.body(candidate_text) for b in blocks if b.kind == "script"}
        admitted = [_block_key(b) for b in blocks if b.kind == "script" and b.ender not in ("Qed", "Defined")]
        checks = static_checks(bodies, admitted=admitted)
        checks = _merge(checks, _fragment_checks(candidate_text, blocks, self.dev.source))
        results = set(getattr(contract, "results", frozenset()))
        checks = _merge(checks, [_results_proved_check(blocks, results)])
        checks.append(contract.check(self.dev.source, candidate_text))

        by_name: dict[str, ProofBlock] = {}
        for b in blocks:
            if b.name and b.name not in by_name:
                by_name[b.name] = b
        if proved is None:
            proved = [b.name for b in blocks if b.name and b.kind == "script" and b.ender == "Qed"]
            proved += [r for r in results if r in by_name and r not in proved]
        stubs = {
            b.qualified_name or "" for b in blocks
            if b.name and b.ender == "Admitted" and b.name not in results
        }

        def qualify(name: str) -> str:
            b = by_name.get(name)
            return (b.qualified_name or name) if b else name

        result = GateResult(ok=False, checks=checks, assembled=candidate_text)
        if any(not c.ok and not c.advisory for c in checks):
            result.checks.append(Check(CHECK_COMPILES, False, "skipped: static checks failed"))
            result.elapsed_s = time.perf_counter() - started
            return result
        text = candidate_text
        if check_assumptions and proved:
            text = candidate_text.rstrip() + "\n\n" + trailer([qualify(n) for n in proved]) + "\n"
        compiled = self._compile(text, result)
        if compiled and check_assumptions and proved:
            self._assumption_checks(result, proved, qualify, stubs, CHECK_AXIOMS_DESIGN)
        result.ok = all(c.ok or c.advisory for c in result.checks)
        result.elapsed_s = time.perf_counter() - started
        return result


# ------------------------------------------------------------------ helpers

def _qualifier(modules: tuple[str, ...]) -> Any:
    def qualify(name: str) -> str:
        return ".".join((*modules, name))

    return qualify


def _with_body(nodes: list[NodeSpec], target: str, body: str) -> list[NodeSpec]:
    return [NodeSpec(s.name, s.statement, body, s.mockable, s.transparent) if s.name == target else s for s in nodes]


def _pinning_check(text: str, frozen: str) -> Check:
    present = bool(frozen.strip()) and frozen.strip() in text
    return Check(CHECK_PINNING, present, "" if present else "the frozen statement text is not present verbatim in the assembly")


def _proof_using_check(text: str) -> Check:
    ok = has_proof_using_directive(text)
    return Check(CHECK_PROOF_USING, ok, "" if ok else "missing Set Default Proof Using")


def _names(text: str) -> list[str]:
    return [b.qualified_name or f"<anonymous {b.head}>" for b in parse_blocks(text)]


def structural_recheck(text: str, reference: str, target: str, frozen: str, body: str, transparent: bool) -> Check:
    """Re-lex the assembly and compare it with the same assembly carrying ``admit.``.

    Equal declaration lists mean the body introduced, redefined or re-opened nothing;
    the target block then must be exactly (frozen statement, submitted body, expected
    ender).  This is what makes ``Abort. Definition target := ...`` and
    ``exact I. Qed. Notation ...`` impossible even if a static rule missed them.
    """
    if not body.strip():
        return Check(CHECK_STRUCTURE, False, "empty proof body")
    actual, expected = _names(text), _names(reference)
    if actual != expected:
        extra = sorted((Counter(actual) - Counter(expected)).elements())
        missing = sorted((Counter(expected) - Counter(actual)).elements())
        detail = "the body changes the declaration list"
        if extra:
            detail += f"; introduces {', '.join(extra)}"
        if missing:
            detail += f"; loses {', '.join(missing)}"
        return Check(CHECK_STRUCTURE, False, detail)
    ref_blocks = parse_blocks(reference)
    blocks = parse_blocks(text)
    index = next((i for i, b in enumerate(ref_blocks) if b.name == target and " ".join(b.body(reference).split()) == "admit."), None)
    if index is None or index >= len(blocks):
        return Check(CHECK_STRUCTURE, False, f"the target {target!r} is not a single proof block in the assembly")
    block = blocks[index]
    ender = "Defined" if transparent else "Qed"
    problems: list[str] = []
    if normalize_statement(block.statement) != normalize_statement(frozen):
        problems.append("its statement is not the frozen statement")
    if " ".join(block.body(text).split()) != " ".join(body.split()):
        problems.append("its body is not the submitted body")
    if block.ender != ender:
        problems.append(f"it ends with {block.ender or 'nothing'} rather than {ender}")
    return Check(CHECK_STRUCTURE, not problems, "; ".join(problems))


def _block_key(b: ProofBlock) -> str:
    return b.qualified_name or f"<anonymous {b.head} @{b.statement_start}>"


def _fragment_checks(candidate: str, blocks: list[ProofBlock], original: str) -> list[Check]:
    """Static scan over every sentence *outside* a proof body (design mode)."""
    spans = [(b.body_start, b.body_end) for b in blocks if b.body_start is not None and b.body_end is not None]
    known = {normalize_statement(s.code) for s in split_sentences(original)}
    hatches: list[str] = []
    axioms: list[str] = []
    for sent in split_sentences(candidate):
        if any(start <= sent.code_start < end for start, end in spans):
            continue
        code = sent.code
        if not code.strip():
            continue
        hatch = escape_hatch(code)
        if hatch:
            hatches.append(f"<fragment>: {hatch}: `{_short(code)}`")
        head, _nxt = _declaration_head(code)
        if head in ("Axiom", "Axioms", "Parameter", "Parameters", "Conjecture") and normalize_statement(code) not in known:
            axioms.append(f"<fragment>: new {head}: `{_short(code)}`")
    return [Check(CHECK_NO_ADMIT, not axioms, "; ".join(axioms)), Check(CHECK_ESCAPE, not hatches, "; ".join(hatches))]


def _results_proved_check(blocks: list[ProofBlock], results: set[str]) -> Check:
    problems: list[str] = []
    seen: set[str] = set()
    for b in blocks:
        if b.name not in results or b.name in seen:
            continue
        seen.add(b.name)
        if b.kind == "term":
            continue
        if b.kind != "script" or b.ender not in ("Qed", "Defined"):
            what = b.ender or ("no proof" if b.kind == "none" else "an unterminated proof")
            problems.append(f"{b.name}: {what} (a result must be proved)")
    return Check(CHECK_NO_ADMIT, not problems, "; ".join(problems))


def _merge(checks: list[Check], extra: list[Check]) -> list[Check]:
    """Combine same-named checks: ok iff both, details joined."""
    by_name = {c.name: c for c in checks}
    out: list[Check] = []
    for c in checks:
        e = next((x for x in extra if x.name == c.name), None)
        if e is None:
            out.append(c)
        else:
            detail = "; ".join(d for d in (c.detail, e.detail) if d)
            out.append(Check(c.name, c.ok and e.ok, detail, c.advisory))
    out += [x for x in extra if x.name not in by_name]
    return out


def _short(code: str, width: int = 80) -> str:
    text = " ".join(code.split())
    return text if len(text) <= width else text[: width - 3] + "..."
