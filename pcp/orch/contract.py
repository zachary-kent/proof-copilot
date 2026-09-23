"""The design contract: which definitions may change, declared by the developer (PLAN.md 9.1).

A design task needs *some* definitions to be mutable -- you cannot invent an
invariant without writing one -- but "mutable" must not mean "whatever the model
decided to rewrite".  So the set is declared up front and enforced by comparison:

* a declaration whose text changed must be in the **mutable** set;
* a declaration that disappeared is a violation regardless;
* new declarations are allowed by default (ghost state has to come from somewhere)
  and can be switched off; a new *lemma* is never a design edit -- an obligation
  goes through the statement pipeline;
* imports are additive: an existing ``Require`` may not go (it changes what the
  surrounding code means); new ones may be forbidden per task.

Intermediate lemma statements are not trust-critical, so by default they are not
frozen: the **results** are frozen by name, the development must compile with no
axioms, and every result must be proved from what remains -- the compiler checks
that a restated helper still serves its callers.  With no results named nothing is
"intermediate" and every lemma stays frozen (fail closed).

Comparison is by declaration *identity* (module-qualified name) and *normalised
statement* (comments removed by the nesting-aware lexer, whitespace collapsed), so a
moved comment is not a change and ``A.x``/``B.x`` are two declarations.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Any

from pcp.errors import UsageError
from pcp.orch.gate import CHECK_CONTRACT, Check
from pcp.rocq.decls import ProofBlock, parse_blocks
from pcp.rocq.lexer import first_word, split_sentences
from pcp.rocq.statement import normalize_statement
from pcp.util.io import json_load

CONTRACT_FILE = "design.json"
BENCH_FILE = "bench.json"


@dataclass(frozen=True)
class ContractViolation:
    name: str
    kind: str  # changed | deleted | added | import removed | import added
    detail: str = ""

    def render(self) -> str:
        return f"{self.name}: {self.kind}" + (f" — {self.detail}" if self.detail else "")

    def to_json(self) -> dict[str, str]:
        return {"name": self.name, "kind": self.kind, "detail": self.detail}


def corpus_declaration_names(corpus: Path, file: str | None = None) -> frozenset[str]:
    """Every declaration name in the corpus's development file (``bench.json:file``, else
    the single ``.v``); empty when there is none to read."""
    from pcp.rocq.decls import parse_blocks
    from pcp.util.io import read_text

    candidates = [corpus / file] if file else sorted(p for p in corpus.glob("*.v") if "__pcp" not in p.stem)
    names: set[str] = set()
    for path in candidates:
        if path.is_file():
            names.update(b.name for b in parse_blocks(read_text(path)) if b.name)
    return frozenset(names)


@dataclass(frozen=True)
class DesignContract:
    """What a design task is allowed to touch."""

    #: Declarations whose bodies may be rewritten.  Everything else is frozen.
    mutable: frozenset[str] = field(default_factory=frozenset)
    #: The results: statements the developer asked to have proved.  Never change,
    #: never disappear; a name here overrides ``mutable`` and ``mutable_lemmas``.
    results: frozenset[str] = field(default_factory=frozenset)
    mutable_lemmas: bool = True
    allow_additions: bool = True
    allow_imports: bool = True
    #: Every declaration name of the ORIGINAL corpus file.  A name absent from it was
    #: introduced by a design, is design-owned, and stays amendable (a definition the
    #: design itself added is never refused as "not declared mutable").  Empty = unknown,
    #: which fails closed to the `mutable` list.
    frozen_names: frozenset[str] = field(default_factory=frozenset)
    #: Heads a new declaration may have, when additions are allowed.
    addable_heads: tuple[str, ...] = (
        "Definition", "Notation", "Class", "Instance", "Record", "Inductive",
        "Canonical", "Local", "Context", "Variable", "Fixpoint", "Ltac",
    )

    LEMMA_HEADS = ("Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark", "Property", "Example")

    # -- construction ------------------------------------------------------
    @classmethod
    def everything_frozen(cls) -> DesignContract:
        return cls(mutable=frozenset(), allow_additions=False, allow_imports=False, mutable_lemmas=False)

    @classmethod
    def from_names(cls, names: Iterable[str], **kw: Any) -> DesignContract:
        return cls(mutable=frozenset(names), **kw)

    @classmethod
    def from_json(cls, data: dict[str, Any], *, results: Iterable[str] = ()) -> DesignContract:
        """The ``design.json`` shape (contract §5.6); ``results`` adds held-out names."""
        return cls(
            mutable=frozenset(data.get("mutable", []) or []),
            results=frozenset(results) | frozenset(data.get("results", []) or []),
            mutable_lemmas=bool(data.get("mutable_lemmas", True)),
            allow_additions=bool(data.get("allow_additions", True)),
            allow_imports=bool(data.get("allow_imports", True)),
            frozen_names=frozenset(data.get("frozen_names", []) or []),
        )

    @classmethod
    def from_corpus(cls, corpus: str | Path) -> DesignContract:
        """``design.json`` > ``bench.json`` > everything frozen; results ∪= held-out names.

        A corpus directory that does not exist is an error, not "nothing mutable":
        a silent fallback would produce a contract that refuses every design.
        """
        corpus = Path(corpus)
        if not corpus.is_dir():
            raise UsageError(f"no corpus directory at {corpus}")
        bench = corpus / BENCH_FILE
        bench_data = json_load(bench) if bench.exists() else {}
        held_out = frozenset(h.get("anonymised") or h["name"] for h in bench_data.get("holdout", []))
        frozen_names = corpus_declaration_names(corpus, bench_data.get("file"))
        explicit = corpus / CONTRACT_FILE
        if explicit.exists():
            contract = cls.from_json(json_load(explicit), results=held_out)
            if not contract.frozen_names and frozen_names:
                contract = replace(contract, frozen_names=frozen_names)
            return contract
        if bench_data:
            declared = bench_data.get("mutable")
            if declared is None:
                declared = [s.get("anonymised") or s["name"] for s in bench_data.get("stubbed", [])]
            return cls(
                mutable=frozenset(declared),
                results=held_out,
                allow_additions=bool(bench_data.get("allow_additions", True)),
                frozen_names=frozen_names,
            )
        return cls.everything_frozen()

    def to_json(self) -> dict[str, Any]:
        return {
            "mutable": sorted(self.mutable),
            "frozen_names": sorted(self.frozen_names),
            "results": sorted(self.results),
            "mutable_lemmas": self.mutable_lemmas,
            "allow_additions": self.allow_additions,
            "allow_imports": self.allow_imports,
        }

    # -- semantics ---------------------------------------------------------
    @property
    def lemmas_are_mutable(self) -> bool:
        """The intermediate-lemma relaxation is licensed only by named results."""
        return self.mutable_lemmas and bool(self.results)

    def is_design_addition(self, name: str) -> bool:
        """``name`` was introduced by a design, not by the corpus (known only when the
        original's names were recorded)."""
        return bool(self.frozen_names) and name not in self.frozen_names

    def may_amend(self, name: str) -> bool:
        """May a design (or an amendment) rewrite this definition?  Results never;
        declared-mutable names and the design's own additions yes."""
        if name in self.results:
            return False
        return name in self.mutable or self.is_design_addition(name)

    def _may_change(self, name: str, head: str) -> bool:
        if name in self.results:
            return False
        if name in self.mutable or self.is_design_addition(name):
            return True
        return self.lemmas_are_mutable and head in self.LEMMA_HEADS

    def _why_frozen(self, name: str) -> str:
        if name in self.results:
            return "this is a result to be proved, not a statement to be rewritten"
        mutable = ", ".join(sorted(self.mutable)) or "nothing"
        return f"not declared mutable; mutable here: {mutable}"

    def violations(self, original: str, candidate: str) -> list[ContractViolation]:
        """Every way ``candidate`` exceeds what this contract permits."""
        out = self._import_violations(original, candidate)
        before = _declarations(original)
        after = _declarations(candidate)
        for key, block in before.items():
            name = block.name or key
            if key not in after:
                out.append(ContractViolation(
                    name, "deleted",
                    "a result may not be dropped" if name in self.results else "the contract permits no deletions",
                ))
                continue
            other = after[key]
            if normalize_statement(block.statement) != normalize_statement(other.statement) and not self._may_change(name, block.head):
                out.append(ContractViolation(name, "changed", self._why_frozen(name)))
        for key, block in after.items():
            if key in before:
                continue
            name = block.name or key
            if not self.allow_additions:
                out.append(ContractViolation(name, "added", "this contract permits no additions"))
            elif block.head not in self.addable_heads:
                out.append(ContractViolation(
                    name, "added",
                    f"a new {block.head} is not a design edit; an obligation goes through the statement pipeline",
                ))
        return out

    def _import_violations(self, original: str, candidate: str) -> list[ContractViolation]:
        old, new = _require_lines(original), _require_lines(candidate)
        out = [ContractViolation(gone, "import removed", "imports may only be added") for gone in sorted(old - new)]
        if not self.allow_imports:
            out += [ContractViolation(added, "import added", "this contract permits no imports") for added in sorted(new - old)]
        return out

    def check(self, before_source: str, after_source: str) -> Check:
        """As a gate :class:`Check`, so it reads the same as every other rule."""
        problems = self.violations(before_source, after_source)
        return Check(CHECK_CONTRACT, not problems, "; ".join(p.render() for p in problems[:6]))

    def describe(self) -> str:
        parts = []
        if self.mutable:
            parts.append("may change: " + ", ".join(f"`{n}`" for n in sorted(self.mutable)))
        if self.lemmas_are_mutable:
            parts.append(
                "intermediate lemma statements may be restated (a caller must then "
                "supply the hypotheses, and the compiler checks it)"
            )
        if self.results:
            parts.append("frozen results: " + ", ".join(f"`{n}`" for n in sorted(self.results)))
        if not parts:
            return "nothing may change"
        parts.append("additions " + ("allowed" if self.allow_additions else "not allowed"))
        parts.append("imports " + ("addable" if self.allow_imports else "fixed"))
        return "; ".join(parts)


def _declarations(source: str) -> dict[str, ProofBlock]:
    """Named declarations keyed by module-qualified name (first occurrence wins)."""
    out: dict[str, ProofBlock] = {}
    for b in parse_blocks(source):
        if b.name and b.qualified_name and b.qualified_name not in out:
            out[b.qualified_name] = b
    return out


def _require_lines(source: str) -> set[str]:
    """Every ``Require`` sentence, whitespace-normalised, from the lexer (not a regex)."""
    out: set[str] = set()
    for sent in split_sentences(source):
        code = sent.code
        fw = first_word(code)
        if fw == "Require" or (fw == "From" and " Require" in " ".join(code.split())):
            out.add(" ".join(code.split()))
    return out
