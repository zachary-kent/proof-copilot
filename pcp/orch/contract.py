"""The design contract: which definitions may change, declared by the developer.

A design task needs *some* definitions to be mutable -- you cannot invent an
invariant without writing one -- but "mutable" must not mean "whatever the model
decided to rewrite".  So the set is declared up front, by the person who built the
benchmark or the development, and enforced by comparison:

* a declaration whose text changed must be in the **mutable** set;
* a declaration that disappeared is a violation regardless;
* new declarations are allowed by default, because ghost state has to come from
  somewhere, and can be switched off for a task where it should not.

One exception, and it is the important one.  *Intermediate lemma statements are not
trust-critical*, so by default they are not frozen.  The reason is that the freeze
that matters is enforced elsewhere and more strongly: the **results** -- the
specifications the developer actually asked for -- are frozen by name, the whole
development must compile with no axioms, and every result must be proved from what
remains.  A helper lemma that acquires a new hypothesis is therefore only useful if
every call site can discharge it, and *the compiler checks that*, not us.  Weakening a
helper into uselessness is possible and harmless: the result that needed it stops
being provable.  So `mutable_lemmas` defaults to true, and `results` carries the names
that may never move.

This is the same principle as PLAN.md 8.3's two-zone assembly, applied one level up:
the freeze is enforced by construction where it can be (a prover only ever returns a
proof body) and by comparison where it cannot (a designer must edit definitions).
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

from pcp.core.vernac import parse_blocks
from pcp.orch.hashing import normalize_statement

import re

#: `From X Require Import a b.` / `Require Import c.`
_REQUIRE_LINE = re.compile(r"^\s*(?:From\s+\S+\s+)?Require\b[^.]*\.", re.M)

CONTRACT_FILE = "design.json"


@dataclass(frozen=True)
class ContractViolation:
    name: str
    kind: str          # changed | deleted | added
    detail: str = ""

    def render(self) -> str:
        return f"{self.name}: {self.kind}" + (f" — {self.detail}" if self.detail else "")


@dataclass(frozen=True)
class DesignContract:
    """What a design task is allowed to touch."""

    #: Declarations whose bodies may be rewritten.  Everything else is frozen.
    mutable: frozenset[str] = field(default_factory=frozenset)
    #: The top-level results: the statements the developer asked to have proved.
    #: These may never change or disappear, whatever else the contract permits --
    #: they are the whole point of the run, and a run that restates its own goal has
    #: proved nothing.  A name here overrides `mutable` and `mutable_lemmas`.
    results: frozenset[str] = field(default_factory=frozenset)
    #: May *intermediate* lemma statements be restated?  Yes, by default: a helper is
    #: an internal step, and a caller that cannot supply the hypotheses a restated
    #: helper demands simply fails to compile.  See the module docstring.
    mutable_lemmas: bool = True
    #: May the designer introduce new declarations (resource algebras, helper
    #: definitions, notations)?  Usually yes: ghost state has to come from somewhere.
    allow_additions: bool = True
    #: May the designer add `Require` lines?  Choosing ghost state means choosing the
    #: library it comes from, so a design task that forbids this is unsatisfiable.
    #: Removing an existing import is never allowed: it changes what the surrounding
    #: code means.
    allow_imports: bool = True
    #: Heads a new declaration may have, when additions are allowed.  Lemmas are
    #: excluded on purpose -- a new *obligation* goes through the statement pipeline,
    #: not through a design edit.
    addable_heads: tuple[str, ...] = (
        "Definition", "Notation", "Class", "Instance", "Record", "Inductive",
        "Canonical", "Local", "Context", "Variable",
    )

    #: Heads whose statements `mutable_lemmas` governs.  A `Definition` is *not* one
    #: of these: it can be unfolded by its users, so changing one silently changes
    #: what a frozen result means.  A lemma cannot -- `Qed` makes it opaque.
    LEMMA_HEADS = (
        "Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark", "Property",
        "Example",
    )

    @classmethod
    def everything_frozen(cls) -> "DesignContract":
        return cls(
            mutable=frozenset(), allow_additions=False, allow_imports=False,
            mutable_lemmas=False,
        )

    def _may_change(self, name: str, head: str) -> bool:
        if name in self.results:
            return False
        if name in self.mutable:
            return True
        # The relaxation is *licensed by* the freeze: an intermediate lemma is safe to
        # restate only because some other, named statement is not.  With no results
        # declared we cannot tell an intermediate from the goal, so nothing is
        # intermediate and every lemma stays frozen.  A contract that forgets to name
        # its results must fail closed, not open.
        return self.mutable_lemmas and bool(self.results) and head in self.LEMMA_HEADS

    @classmethod
    def from_names(cls, names: Iterable[str], **kw) -> "DesignContract":
        return cls(mutable=frozenset(names), **kw)

    @classmethod
    def from_corpus(cls, corpus: Path) -> "DesignContract":
        """Read the contract a benchmark declares.

        Falls back to the stubbed definitions: if a corpus blanked a predicate, it
        plainly intends the designer to fill it in.
        """
        corpus = Path(corpus)
        bench = corpus / "bench.json"
        bench_data = (
            json.loads(bench.read_text(encoding="utf-8")) if bench.exists() else {}
        )
        # The held-out specifications *are* the results, so a benchmark never has to
        # say so twice; design.json may still name more.
        held_out = frozenset(
            h.get("anonymised") or h["name"] for h in bench_data.get("holdout", [])
        )

        explicit = corpus / CONTRACT_FILE
        if explicit.exists():
            data = json.loads(explicit.read_text(encoding="utf-8"))
            return cls(
                mutable=frozenset(data.get("mutable", [])),
                results=held_out | frozenset(data.get("results", [])),
                mutable_lemmas=bool(data.get("mutable_lemmas", True)),
                allow_additions=bool(data.get("allow_additions", True)),
                allow_imports=bool(data.get("allow_imports", True)),
            )
        if bench_data:
            declared = bench_data.get("mutable")
            if declared is None:
                declared = [s["anonymised"] for s in bench_data.get("stubbed", [])]
            return cls(
                mutable=frozenset(declared),
                results=held_out,
                allow_additions=bool(bench_data.get("allow_additions", True)),
            )
        return cls.everything_frozen()

    # -- enforcement -------------------------------------------------------
    def violations(self, original: str, candidate: str) -> list[ContractViolation]:
        """Every way ``candidate`` exceeds what this contract permits."""
        out: list[ContractViolation] = []
        out += self._import_violations(original, candidate)
        before = {b.name: (b, original) for b in parse_blocks(original) if b.name}
        after = {b.name: (b, candidate) for b in parse_blocks(candidate) if b.name}

        for name, (block, src) in before.items():
            if name not in after:
                # Deletion stays forbidden even for a lemma the design may *restate*.
                # Restating is checked by the compiler -- the callers must still work.
                # Vanishing is not checked by anything, and no design needs it.
                out.append(ContractViolation(
                    name, "deleted",
                    "a result may not be dropped" if name in self.results
                    else "the contract permits no deletions",
                ))
                continue
            other, osrc = after[name]
            old = normalize_statement(src[block.statement_start : block.statement_end])
            new = normalize_statement(osrc[other.statement_start : other.statement_end])
            if old != new and not self._may_change(name, block.head):
                out.append(ContractViolation(name, "changed", self._why_frozen(name)))

        for name, (block, _src) in after.items():
            if name in before:
                continue
            if not self.allow_additions:
                out.append(ContractViolation(name, "added", "this contract permits no additions"))
            elif block.head not in self.addable_heads:
                out.append(
                    ContractViolation(
                        name, "added",
                        f"a new {block.head} is not a design edit; an obligation goes "
                        "through the statement pipeline",
                    )
                )
        return out

    def _why_frozen(self, name: str) -> str:
        if name in self.results:
            return "this is a result to be proved, not a statement to be rewritten"
        mutable = ", ".join(sorted(self.mutable)) or "nothing"
        return f"not declared mutable; mutable here: {mutable}"

    def _import_violations(self, original: str, candidate: str) -> list[ContractViolation]:
        """Imports are *additive*: new ones are fine, existing ones may not go.

        They are not declarations, so the block-level comparison never saw them --
        which meant a design could silently delete `Require Import invariants` and
        change what every surrounding definition meant.
        """
        def lines(text: str) -> set[str]:
            return {" ".join(m.group(0).split()) for m in _REQUIRE_LINE.finditer(text)}

        old, new = lines(original), lines(candidate)
        out: list[ContractViolation] = []
        for gone in sorted(old - new):
            out.append(ContractViolation(gone, "import removed", "imports may only be added"))
        if not self.allow_imports:
            for added in sorted(new - old):
                out.append(ContractViolation(added, "import added", "this contract permits no imports"))
        return out

    def check(self, original: str, candidate: str):
        """As a gate :class:`Check`, so it reads the same as every other rule."""
        from pcp.orch.gate import Check

        problems = self.violations(original, candidate)
        return Check(
            "design contract (only declared-mutable definitions changed)",
            not problems,
            "; ".join(p.render() for p in problems[:6]),
        )

    @property
    def lemmas_are_mutable(self) -> bool:
        """Is the intermediate-lemma relaxation actually in force?"""
        return self.mutable_lemmas and bool(self.results)

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
            parts.append(
                "frozen results: " + ", ".join(f"`{n}`" for n in sorted(self.results))
            )
        if not parts:
            return "nothing may change"
        parts.append("additions " + ("allowed" if self.allow_additions else "not allowed"))
        parts.append("imports " + ("addable" if self.allow_imports else "fixed"))
        return "; ".join(parts)

    def to_json(self) -> dict:
        return {
            "mutable": sorted(self.mutable),
            "results": sorted(self.results),
            "mutable_lemmas": self.mutable_lemmas,
            "allow_additions": self.allow_additions,
            "allow_imports": self.allow_imports,
        }
