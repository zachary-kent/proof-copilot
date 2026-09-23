#!/usr/bin/env python3
"""Build a contamination-controlled benchmark from a real Rocq development.

PLAN.md 13 asks for held-out lemmas: replace bodies with ``Admitted``, ask an agent to
reprove them.  For a *public* development that is not enough on its own -- the answer
is on the internet, and may be in the model's weights -- so the builder does three
things (docs/BENCHMARKS.md "Contamination control"):

1. **holds out** the named proofs and nothing else: the design is given, the tactic
   work is not;
2. **anonymises** the file-local identifiers (role suffixes kept) and strips prose,
   so neither a grep nor a memorised lemma name is a shortcut;
3. **keeps the answer key out of the corpus directory** -- in ``--reference``, which
   the worker sandbox never binds and which may not lie inside ``--out``.

A *design rung* (BENCHMARKS.md "Design rungs: the invariant is the task") additionally
blanks the client-facing predicates to ``True``, drops the ghost-state scaffolding,
minimises the typeclass, replaces the imports and inserts a proved *persistence
guard*; ``design.json`` then records the contract that
``pcp.orch.contract.DesignContract`` enforces (PLAN.md 9.1, 9.3).

The pipeline is a fixed sequence of text stages over the lexer's byte offsets
(``pcp.rocq.decls``), in an order that is load-bearing (see :func:`build`): the guard
is inserted and checked against the *original*; signatures are read while the
original imports and bodies still exist; scrubbing, stubbing, stripping and renaming
follow; the result is **verified by compiling**, and nothing is written on failure.

    python eval/make_benchmark.py /tmp/bench/build/rwcas.v \\
        --holdout read_spec write_spec new_rwcas_spec \\
        --out eval/corpus/bench/rwcas --reference .pcp/reference/rwcas

Honest limitation: this defeats lookup and name matching; it does not prove a model
has not memorised the *proof structure* of a public development.  Treat a solve on an
anonymised public corpus as an upper bound.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
import tempfile
from collections.abc import Callable, Iterator
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pcp.config import env as penv  # noqa: E402
from pcp.errors import PcpError, ToolchainError, UsageError  # noqa: E402
from pcp.rocq.decls import ProofBlock, parse_blocks  # noqa: E402
from pcp.rocq.lexer import (  # noqa: E402
    first_word,
    identifiers,
    iter_comments,
    skip_comment,
    skip_string,
    split_sentences,
    strip_comments,
)
from pcp.rocq.project import CompileResult, compile_text  # noqa: E402
from pcp.util.io import atomic_write_text, ensure_dir, json_dump, json_load, read_text, rm_tree  # noqa: E402

#: Suffixes that carry the *role* of a name.  Keeping them keeps the development
#: legible without keeping it searchable.
ROLE_SUFFIXES: tuple[str, ...] = (
    "_spec", "_inv", "_alloc", "_agree", "_update", "_own", "_valid", "_op",
    "_lookup", "_insert", "_snoc", "_cons", "_nil", "_wf", "_closed", "_ne",
    "_proper", "_persistent", "_timeless", "_G", "_pre", "_post",
)

#: Heads whose declared names are file-local and therefore safe to rename.
RENAMEABLE_HEADS: tuple[str, ...] = (
    "Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark", "Property",
    "Definition", "Fixpoint", "CoFixpoint", "Inductive", "Record", "Class",
    "Instance", "Example", "Variant", "Structure",
)

#: Heads whose ``{ ... }`` body declares instance fields (``f :: C``).
CLASS_HEADS: tuple[str, ...] = ("Class", "Record", "Structure")

PROJECT = "-Q . bench\n"
PROJECT_FLAGS: tuple[str, ...] = ("-Q", ".", "bench")
#: The cached rungs take minutes to compile; the gate's default is far too short here.
COMPILE_TIMEOUT = 7200.0
#: ``:= True`` alone elaborates in ``Prop`` and every use site then fails to typecheck.
DEFAULT_STUB_TYPE = "iProp Σ"
DESIGN_NOTE = "DESIGN.md carries the given design; it is included in every worker packet"

BENCH_FILE = "bench.json"
DESIGN_FILE = "design.json"
BRIEF_FILE = "DESIGN.md"
PROJECT_FILE = "_CoqProject"
REFERENCE_FILE = "reference.json"
DESIGN_NOTE_LEVELS = ("none", "glossary", "full")


class CorpusError(PcpError):
    """The corpus (or the reference with its guards) does not compile: nothing is emitted."""

    exit_code = 1


# ------------------------------------------------------------------------ records

@dataclass
class HeldOut:
    """A held-out proof.  ``reference_body`` is the answer key and never enters the corpus."""

    name: str
    anonymised: str
    statement: str
    reference_body: str
    reference_sha256: str
    lines: int
    tactics: int

    def to_json(self, *, with_reference: bool = False) -> dict[str, Any]:
        d: dict[str, Any] = {"name": self.name, "anonymised": self.anonymised, "statement": self.statement}
        if with_reference:
            d["reference_body"] = self.reference_body
        d.update(reference_sha256=self.reference_sha256, lines=self.lines, tactics=self.tactics)
        return d

    @classmethod
    def from_json(cls, d: dict[str, Any]) -> HeldOut:
        return cls(
            name=d["name"],
            anonymised=d.get("anonymised") or d["name"],
            statement=d.get("statement", ""),
            reference_body=d.get("reference_body", ""),
            reference_sha256=d.get("reference_sha256", ""),
            lines=int(d.get("lines", 0)),
            tactics=int(d.get("tactics", 0)),
        )


@dataclass
class StubbedDefinition:
    """A design artifact the worker has to invent.  ``original`` is recorded by hash only."""

    name: str
    anonymised: str
    original: str
    stub: str
    original_sha256: str

    def to_json(self, *, with_original: bool = False) -> dict[str, Any]:
        d: dict[str, Any] = {"name": self.name, "anonymised": self.anonymised}
        if with_original:
            d["original"] = self.original
        d.update(stub=self.stub, original_sha256=self.original_sha256)
        return d

    @classmethod
    def from_json(cls, d: dict[str, Any]) -> StubbedDefinition:
        return cls(
            name=d["name"],
            anonymised=d.get("anonymised") or d["name"],
            original=d.get("original", ""),
            stub=d.get("stub", ""),
            original_sha256=d.get("original_sha256", ""),
        )


@dataclass
class Benchmark:
    """Everything the builder knows about a rung.  Two views leave this object:

    * :meth:`to_json` is ``bench.json`` -- what a worker is allowed to read.  The
      sandbox binds the rung under test, this file included, so no reference body, no
      stubbed original, no upstream path and no *name* of a dropped declaration is in
      it: naming ``registry_inv`` after scrubbing it is not scrubbing.  ``dropped`` is
      a count.
    * :meth:`reference_json` is the answer key, written under ``--reference``.
    """

    source: str
    file: str
    anonymised: bool
    holdout: list[HeldOut] = field(default_factory=list)
    stubbed: list[StubbedDefinition] = field(default_factory=list)
    dropped: list[str] = field(default_factory=list)
    #: Declarations the design process may rewrite (``DesignContract.mutable``).
    mutable: list[str] = field(default_factory=list)
    #: Statements given *proved* that must stay exactly as they are: design guards.
    results: list[str] = field(default_factory=list)
    allow_additions: bool = True
    rename_map: dict[str, str] = field(default_factory=dict)
    notes: list[str] = field(default_factory=list)

    def to_json(self) -> dict[str, Any]:
        return {
            "file": self.file,
            "anonymised": self.anonymised,
            "holdout": [h.to_json() for h in self.holdout],
            "stubbed": [s.to_json() for s in self.stubbed],
            "dropped": len(self.dropped),
            "mutable": list(self.mutable),
            "results": list(self.results),
            "allow_additions": self.allow_additions,
            "rename_map": dict(self.rename_map),
            "notes": list(self.notes),
        }

    def reference_json(self) -> dict[str, Any]:
        return {
            "source": self.source,
            "file": self.file,
            "holdout": [h.to_json(with_reference=True) for h in self.holdout],
            "dropped": list(self.dropped),
            "rename_map": dict(self.rename_map),
        }

    def contract_json(self) -> dict[str, Any]:
        """``design.json``: exactly the fields ``DesignContract.from_json`` reads."""
        return {"mutable": list(self.mutable), "results": list(self.results), "allow_additions": self.allow_additions}

    @classmethod
    def from_json(cls, d: dict[str, Any]) -> Benchmark:
        """Read either view.  From the corpus view the answer-key fields come back empty
        and ``dropped`` is ``[]`` -- that lossiness is the contamination control."""
        dropped = d.get("dropped", [])
        return cls(
            source=d.get("source", ""),
            file=d["file"],
            anonymised=bool(d.get("anonymised", False)),
            holdout=[HeldOut.from_json(h) for h in d.get("holdout", [])],
            stubbed=[StubbedDefinition.from_json(s) for s in d.get("stubbed", [])],
            dropped=list(dropped) if isinstance(dropped, list) else [],
            mutable=list(d.get("mutable", [])),
            results=list(d.get("results", [])),
            allow_additions=bool(d.get("allow_additions", True)),
            rename_map=dict(d.get("rename_map", {})),
            notes=list(d.get("notes", [])),
        )


# ------------------------------------------------------- depth-aware text scanning
#
# Every regex attempt at these failed on a real file (nested parens, annotated
# binders, dotted module names, braces inside a field's type), so the scanning is
# explicit: bracket depth, with comments and strings skipped by the lexer's own
# helpers.  Nothing here is a regex over Rocq text (ARCHITECTURE.md §3 rule 2).

_OPENERS = "([{"
_CLOSERS = ")]}"


def _code_positions(text: str, start: int = 0, end: int | None = None) -> Iterator[tuple[int, int]]:
    """``(i, depth)`` for each character outside comments and strings; ``depth`` is before ``i``."""
    n = len(text) if end is None else end
    depth = 0
    i = start
    while i < n:
        if text.startswith("(*", i):
            i = skip_comment(text, i)
            continue
        if text[i] == '"':
            i = skip_string(text, i)
            continue
        yield i, depth
        ch = text[i]
        if ch in _OPENERS:
            depth += 1
        elif ch in _CLOSERS:
            depth -= 1
        i += 1


def _top_level_find(text: str, token: str, start: int = 0, end: int | None = None) -> int:
    for i, depth in _code_positions(text, start, end):
        if depth == 0 and text.startswith(token, i):
            return i
    return -1


def _annotation_colon(text: str, start: int = 0, end: int | None = None) -> int:
    """The first top-level ``:`` that is an annotation (not ``:=``, ``::`` or ``:>``)."""
    skip_until = -1
    for i, depth in _code_positions(text, start, end):
        if i < skip_until or depth != 0 or text[i] != ":":
            continue
        if text.startswith("::", i) or text.startswith(":=", i) or text.startswith(":>", i):
            skip_until = i + 2
            continue
        return i
    return -1


def _matching(text: str, i: int) -> int:
    """Index of the closer matching the opener at ``i``, or ``-1``."""
    for j, depth in _code_positions(text, i):
        if j > i and depth == 1 and text[j] in _CLOSERS:
            return j
    return -1


def _split_top_level(text: str, seps: tuple[str, ...]) -> list[str]:
    parts: list[str] = []
    last = 0
    skip_until = -1
    for i, depth in _code_positions(text):
        if i < skip_until or depth != 0:
            continue
        for sep in seps:
            if text.startswith(sep, i) and not (sep == "->" and i > 0 and text[i - 1] == "<"):
                parts.append(text[last:i])
                last = skip_until = i + len(sep)
                break
    parts.append(text[last:])
    return [p.strip() for p in parts if p.strip()]


def _split_arrows(ty: str) -> list[str]:
    """Top-level arrow-separated components of a type."""
    return _split_top_level(ty, ("→", "->"))


def _strip_forall_prefix(ty: str) -> str:
    """Drop a leading ``∀ {Σ : gFunctors} ...,`` -- the section variables Rocq discharged."""
    ty = ty.strip()
    if not (ty.startswith("∀") or ty.startswith("forall")):
        return ty
    comma = _top_level_find(ty, ",")
    return ty[comma + 1 :].strip() if comma >= 0 else ty


def _return_type(signature: str | None) -> str | None:
    if not signature:
        return None
    parts = _split_arrows(_strip_forall_prefix(signature))
    return parts[-1] if parts else None


# ------------------------------------------------------------ declarations and binders

@dataclass(frozen=True)
class Binder:
    """One binder of a declaration head.

    ``explicit`` ``(x y : T)``, ``implicit`` ``{x : T}``, ``generalising`` `` `{!C} ``,
    ``bare`` ``x`` (a pattern binder ``'x`` is bare with the quote dropped: it cannot
    carry an annotation, and every call site is positional).
    """

    kind: str
    names: tuple[str, ...]
    text: str
    annotation: str | None = None


def parse_binders(text: str) -> list[Binder]:
    """The binder list of a declaration head, groups respected."""
    out: list[Binder] = []
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        if ch.isspace():
            i += 1
            continue
        if text.startswith("(*", i):
            i = skip_comment(text, i)
            continue
        if ch == "`":
            if i + 1 >= n or text[i + 1] not in "({":
                raise UsageError(f"unsupported binder syntax: {text[i:i + 24]!r}")
            close = _matching(text, i + 1)
            if close < 0:
                raise UsageError(f"unbalanced binder list: {text.strip()!r}")
            out.append(Binder("generalising", (), text[i : close + 1]))
            i = close + 1
            continue
        if ch in "({":
            close = _matching(text, i)
            if close < 0:
                raise UsageError(f"unbalanced binder list: {text.strip()!r}")
            inner = text[i + 1 : close]
            colon = _annotation_colon(inner)
            names = tuple(_binder_name(t) for t in (inner[:colon] if colon >= 0 else inner).split())
            annotation = inner[colon + 1 :].strip() if colon >= 0 else None
            out.append(Binder("explicit" if ch == "(" else "implicit", names, text[i : close + 1], annotation))
            i = close + 1
            continue
        if ch in "[)}]":
            raise UsageError(f"unsupported binder syntax: {text[i:i + 24]!r}")
        j = i
        while j < n and not text[j].isspace() and text[j] not in "({[`":
            j += 1
        out.append(Binder("bare", (_binder_name(text[i:j]),), text[i:j]))
        i = j
    return out


def _binder_name(token: str) -> str:
    return token.lstrip("'")


def binder_names(text: str) -> list[str]:
    """Binder names in ``a (b : T) 'c`` -- in order, groups flattened."""
    return [n for b in parse_binders(text) for n in b.names]


@dataclass(frozen=True)
class Declaration:
    """``<prefix><name><binders> : <annotation> := <body>.`` taken apart at top level."""

    prefix: str
    name: str
    binders: str
    annotation: str | None
    body: str | None

    @property
    def head_text(self) -> str:
        binders = self.binders.strip()
        return f"{self.prefix}{self.name}" + (f" {binders}" if binders else "")


def split_declaration(block: ProofBlock) -> Declaration:
    """Take a declaration statement apart without ever matching the name as a substring.

    A ``head.split(name, 1)`` would find ``fin`` inside the keyword ``Definition``;
    the name is located *after* the head keyword the parser already identified.
    """
    if block.name is None:
        raise UsageError("an anonymous declaration cannot be taken apart by name")
    code = strip_comments(block.statement).rstrip()
    if code.endswith("."):
        code = code[:-1].rstrip()
    p = _name_offset(code, block.head, block.name)
    name_end = p + len(block.name)
    assign = _top_level_find(code, ":=", name_end)
    colon = _annotation_colon(code, name_end, assign if assign >= 0 else None)
    head_end = assign if assign >= 0 else len(code)
    binders_end = colon if colon >= 0 else head_end
    return Declaration(
        prefix=code[:p],
        name=block.name,
        binders=code[name_end:binders_end],
        annotation=code[colon + 1 : head_end].strip() if colon >= 0 else None,
        body=code[assign + 2 :].strip() if assign >= 0 else None,
    )


def _name_offset(code: str, head: str, name: str) -> int:
    pos = 0
    while True:
        hp = code.find(head, pos)
        if hp < 0:
            raise UsageError(f"cannot locate {head} {name!r} in: {code[:80]!r}")
        p = hp + len(head)
        while p < len(code) and code[p].isspace():
            p += 1
        if p > hp + len(head) and code.startswith(name, p) and not _ident_char(code[p + len(name) : p + len(name) + 1]):
            return p
        pos = hp + 1


def _ident_char(ch: str) -> bool:
    return bool(ch) and (ch.isalnum() or ch in "_'")


def _named_blocks(source: str, *, heads: tuple[str, ...] | None = None) -> dict[str, ProofBlock]:
    """Named declarations by bare name (first occurrence wins)."""
    out: dict[str, ProofBlock] = {}
    for b in parse_blocks(source):
        if b.name and (heads is None or b.head in heads):
            out.setdefault(b.name, b)
    return out


# ------------------------------------------------------------------ anonymisation

def local_names(source: str) -> list[str]:
    """Identifiers this file declares: renameable heads, instance fields, sections.

    Library names are never touched because only *declared* names are listed.  The
    order is the file order and is what indexes the pseudonyms, so it must stay
    stable across rebuilds (``build.sh`` names the design rungs' inputs by it).
    """
    blocks = parse_blocks(source)
    names = [b.name for b in blocks if b.head in RENAMEABLE_HEADS and b.name]
    for b in blocks:
        if b.head in CLASS_HEADS:
            names += _instance_fields(b.statement)
    names += [_section_name(s.code) for s in split_sentences(source) if first_word(s.code) == "Section"]
    seen: set[str] = set()
    out: list[str] = []
    for n in names:
        if n and n not in seen and len(n) > 2:
            seen.add(n)
            out.append(n)
    return out


def _instance_fields(statement: str) -> list[str]:
    """``f`` for every ``f :: C`` field of a ``Class``/``Record`` body."""
    code = strip_comments(statement)
    assign = _top_level_find(code, ":=")
    open_ = _top_level_find(code, "{", assign + 2) if assign >= 0 else -1
    close = _matching(code, open_) if open_ >= 0 else -1
    if close < 0:
        return []
    out: list[str] = []
    for item in _split_top_level(code[open_ + 1 : close], (";",)):
        while item.startswith("#["):
            item = item[item.find("]") + 1 :].lstrip()
        head, sep, _ = item.partition("::")
        if sep and len(head.split()) == 1:
            out.append(head.strip())
    return out


def _section_name(code: str) -> str:
    parts = code.split()
    return parts[1].rstrip(".") if len(parts) > 1 else ""


def pseudonym(name: str, index: int, salt: str) -> str:
    """A stable, unguessable-but-readable replacement.

    The role suffix survives (``write_spec`` -> ``fc23_spec``) so a reader can still
    tell a spec from an invariant; the searchable part does not.
    """
    for suffix in ROLE_SUFFIXES:
        if name.endswith(suffix) and len(name) > len(suffix):
            return f"{_tag(name, salt)}{index}{suffix}"
    return f"{_tag(name, salt)}{index}"


def _tag(name: str, salt: str) -> str:
    digest = hashlib.blake2b(f"{salt}:{name}".encode(), digest_size=2).hexdigest()
    return "".join(c for c in digest if c.isalpha()) or "x"


def rename_text(text: str, mapping: dict[str, str]) -> str:
    """Rename whole identifiers, in one pass, longest name first.

    The boundary treats ``'`` as part of an identifier: ``\\bread'\\b`` never matches
    ``read'`` (no word character follows a prime) while ``read`` matches *inside* it,
    so primed names would survive with their prefix renamed.  ``\\w`` is
    Unicode-aware, so ``γₕ`` and ``γᵥ`` are identifiers too.  One alternation pass
    means a pseudonym produced for one name can never be renamed again as another.
    """
    if not mapping:
        return text
    names = sorted(mapping, key=len, reverse=True)
    pattern = re.compile(r"(?<![\w'])(?:" + "|".join(re.escape(n) for n in names) + r")(?![\w'])")
    return pattern.sub(lambda m: mapping[m.group(0)], text)


def tidy(text: str) -> str:
    """Trailing whitespace off every line; runs of blank lines collapsed to one."""
    text = "\n".join(line.rstrip() for line in text.split("\n"))
    while "\n\n\n" in text:
        text = text.replace("\n\n\n", "\n\n")
    return text


def anonymise(source: str, *, salt: str, drop_comments: bool = True) -> tuple[str, dict[str, str]]:
    names = local_names(source)
    mapping = {n: pseudonym(n, i, salt) for i, n in enumerate(names)}
    out = rename_text(source, mapping)
    if drop_comments:
        out = tidy(strip_comments(out))
    return out, mapping


# ------------------------------------------------------------------------ holdout

def hold_out(source: str, names: list[str]) -> tuple[str, list[HeldOut]]:
    """Replace the named proofs with ``Admitted.``, keeping their statements exactly.

    The corpus shape is always ``Proof.\\nAdmitted.`` -- a lemma written without a
    ``Proof.`` sentence gets one -- which is what ``assemble.stub_proof_bodies`` and
    ``NodeSpec.render`` produce, so the gate and the corpus agree on what a stub is.
    """
    blocks = {
        n: b for n, b in _named_blocks(source).items()
        if b.kind == "script" and b.ender in ("Qed", "Defined") and b.body_start is not None and b.ender_end is not None
    }
    missing = [n for n in names if n not in blocks]
    if missing:
        raise UsageError(f"no proof block named: {', '.join(missing)}")
    held: list[HeldOut] = []
    edits: list[tuple[int, int, str]] = []
    for name in names:
        b = blocks[name]
        assert b.body_start is not None and b.ender_end is not None
        body = b.body(source)
        held.append(HeldOut(
            name=name,
            anonymised=name,
            statement=b.statement,
            reference_body=body,
            reference_sha256=_sha256(body),
            lines=len(body.strip().splitlines()),
            tactics=len(b.tactics()),
        ))
        stub = "\nAdmitted." if b.proof_start is not None else "\nProof.\nAdmitted."
        edits.append((b.body_start, b.ender_end, stub))
    return _apply_edits(source, edits), held


def _apply_edits(source: str, edits: list[tuple[int, int, str]]) -> str:
    out: list[str] = []
    cursor = 0
    for start, end, text in sorted(edits):
        out.append(source[cursor:start])
        out.append(text)
        cursor = end
    out.append(source[cursor:])
    return "".join(out)


def _sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


# ------------------------------------------------------------------ signatures

def definition_types(source: str, names: list[str], *, timeout: float = COMPILE_TIMEOUT) -> dict[str, str]:
    """Ask Rocq for each definition's full type, in one compile.

    Blanking a body also destroys type inference: ``value γ n`` had ``γ : gname`` only
    because the body applied ``ghost_var`` to it, so the stub must carry the signature
    the original never wrote down.  A failed probe is an error, not an empty answer:
    returning ``{}`` would surface the failure later as an unrelated type error in
    the final verify.
    """
    blocks = _named_blocks(source)
    qualified = {(blocks[n].qualified_name or n) if n in blocks else n: n for n in names}
    probe = source.rstrip() + "\n\n" + "\n".join(f"About {q}." for q in qualified) + "\n"
    result = compile_source(probe, "About_probe.v", timeout=timeout)
    if not result.ok:
        raise UsageError("the signature probe did not compile: " + result.first_error())
    return parse_about(result.output, qualified)


_PROVENANCE = (" is not universe polymorphic", " is universe polymorphic", "Arguments ", "Expands to",
               " is transparent", " is opaque", "Declared in")


def parse_about(output: str, names: dict[str, str] | list[str]) -> dict[str, str]:
    """``{bare name: type}`` from ``About`` answers (``name : type``, possibly wrapped).

    An answer runs from a column-0 ``name :`` line to the next blank line; wrapped
    types continue on indented lines (or, when the type starts on its own line,
    immediately after the ``name :`` line).  The provenance Rocq appends is cut.
    """
    wanted = dict(names) if isinstance(names, dict) else {n: n for n in names}
    wanted.update({bare: bare for bare in list(wanted.values())})
    lines = output.splitlines()
    found: dict[str, str] = {}
    i = 0
    while i < len(lines):
        line = lines[i]
        i += 1
        if not line or line[0].isspace():
            continue
        key, sep, rest = line.partition(" :")
        if not sep or key not in wanted or wanted[key] in found or rest.startswith(":") or rest.startswith("="):
            continue
        parts = [rest.strip()] if rest.strip() else []
        while i < len(lines) and lines[i].strip() and (lines[i][0].isspace() or not parts):
            parts.append(lines[i].strip())
            i += 1
        ty = " ".join(" ".join(parts).split())
        for marker in _PROVENANCE:
            cut = ty.find(marker)
            if cut >= 0:
                ty = ty[:cut]
        found[wanted[key]] = ty.strip().rstrip(".").strip()
    return found


# ---------------------------------------------------------------------- stubbing

def stub_definitions(
    source: str,
    specs: list[str],
    *,
    default_type: str = DEFAULT_STUB_TYPE,
    types: dict[str, str] | None = None,
) -> tuple[str, list[StubbedDefinition]]:
    """Replace the named definitions' bodies with ``True``.

    This is the difference between "prove this, given the design" and "design it and
    prove it": for a CSL development the invariant and the abstract state predicate
    *are* the problem.  ``specs`` entries are ``name`` or ``name=TYPE``.  Bare binders
    are annotated from the discharged signature (right-aligned: the leading arrows are
    the section's ``Context``); explicit, implicit and generalising binders are kept
    verbatim; the return type is the original annotation, else the signature's last
    component, else ``default_type``.
    """
    wanted: dict[str, str | None] = {}
    for entry in specs:
        name, _, ty = entry.partition("=")
        wanted[name.strip()] = ty.strip() or None
    blocks = _named_blocks(source, heads=("Definition",))
    missing = [n for n in wanted if n not in blocks]
    if missing:
        raise UsageError(f"no Definition named: {', '.join(missing)}")
    edits: list[tuple[int, int, str]] = []
    stubbed: list[StubbedDefinition] = []
    for name in sorted(wanted, key=lambda n: blocks[n].statement_start):
        block = blocks[name]
        original = source[block.statement_start : block.statement_end]
        decl = split_declaration(block)
        if decl.body is None:
            raise UsageError(f"cannot parse the definition of {name!r} to stub it:\n{original[:200]}")
        signature = wanted[name] or (types or {}).get(name)
        ret = decl.annotation or _return_type(signature) or default_type
        annotated = _annotate_binders(parse_binders(decl.binders), signature)
        head = decl.head_text if annotated is None else f"{decl.prefix}{name}{annotated}"
        replacement = f"{head} : {ret} := True%I."
        edits.append((block.statement_start, block.statement_end, replacement))
        stubbed.append(StubbedDefinition(name, name, original, replacement, _sha256(original)))
    return _apply_edits(source, edits), stubbed


def _annotate_binders(binders: list[Binder], signature: str | None) -> str | None:
    """The binder list with every bare binder typed, or ``None`` when that is not possible.

    Rocq reports a section definition's type *after* discharge, so the leading
    arguments are the section's own ``Context`` variables and the definition's
    positional binders are the trailing ones -- hence the zip from the right.
    """
    if not any(b.kind == "bare" for b in binders):
        return "".join(" " + b.text for b in binders)
    if not signature:
        return None
    args = _split_arrows(_strip_forall_prefix(signature))[:-1]
    positional = sum(len(b.names) for b in binders if b.kind in ("explicit", "bare"))
    if len(args) < positional:
        return None
    tail = args[len(args) - positional :]
    out: list[str] = []
    k = 0
    for b in binders:
        if b.kind == "bare":
            out.append(f" ({b.names[0]} : {tail[k]})")
            k += 1
        else:
            out.append(" " + b.text)
            if b.kind == "explicit":
                k += len(b.names)
    return "".join(out)


# --------------------------------------------------------------------- scrubbing

def drop_declarations(source: str, names: list[str]) -> tuple[str, list[str]]:
    """Delete named declarations outright, with every comment stacked above them.

    Stubbing a definition to ``True`` still tells the worker that *something* of that
    shape exists; for design a worker is supposed to invent, the honest scrub is
    deletion -- and the comments above it go too: a comment explaining an invariant
    describes the answer as surely as the invariant does.  The whole stacked block is
    taken, not only the last comment of a stack.
    """
    blocks = _named_blocks(source)
    missing = [n for n in names if n not in blocks]
    if missing:
        raise UsageError(f"nothing named: {', '.join(missing)}")
    spans = sorted((comment_block_start(source, blocks[n].statement_start), blocks[n].end) for n in names)
    parts: list[str] = []
    cursor = 0
    for begin, finish in spans:
        chunk = source[cursor : max(begin, cursor)].rstrip()
        parts.append(chunk + ("\n\n" if chunk else ""))
        cursor = max(cursor, finish)
        while cursor < len(source) and source[cursor] == "\n":
            cursor += 1
    parts.append(source[cursor:])
    return "".join(parts), list(names)


def comment_block_start(source: str, offset: int) -> int:
    """Start of the comment block introducing the declaration at ``offset``.

    The nearest comment above counts when only whitespace separates it from the
    declaration; comments stacked above *it* chain as long as no blank line
    intervenes.  A header paragraph set off by a blank line is the file's, not the
    declaration's, and ``--strip-comments`` is the tool for that.
    """
    comments = [(s, e) for s, e, _ in iter_comments(source) if e <= offset]
    start = offset
    for s, e in reversed(comments):
        gap = source[e:start]
        if gap.strip() or (start != offset and gap.count("\n") > 1):
            break
        start = s
    return start


def set_imports(source: str, imports: list[str]) -> str:
    """Replace every ``Require`` *sentence* with a given, minimal set.

    ``From iris.base_logic.lib Require Import token ghost_var`` names three quarters
    of the ghost-state plan.  Sentences come from the lexer, so a ``Require`` wrapped
    over several lines and one with
    dotted module names go too.
    """
    lines = [ln if ln.strip().endswith(".") else ln.strip() + "." for ln in imports]
    replacement = "\n".join(lines)
    requires = [s for s in split_sentences(source) if _is_require(s.code)]
    if not requires:
        return replacement + "\n\n" + source
    parts: list[str] = []
    cursor = 0
    for k, sent in enumerate(requires):
        parts.append(source[cursor : sent.code_start])
        if k == 0:
            parts.append(replacement + "\n")
        cursor = sent.end
        if cursor < len(source) and source[cursor] == "\n":
            cursor += 1
    parts.append(source[cursor:])
    return "".join(parts)


def _is_require(code: str) -> bool:
    fw = first_word(code)
    return fw == "Require" or (fw == "From" and "Require" in identifiers(code))


def minimize_class(source: str, name: str, fields: list[str]) -> str:
    """Reduce a typeclass to the listed fields.

    A ``Class rwcasG Σ`` listing ``inG Σ requestRegUR``, ``tokenG Σ`` and two
    ``ghost_varG`` instances *is* the ghost-state design.  The body is found by
    bracket matching, so a field whose type contains braces (``{[ ... ]}``) does not
    end it early and no old field survives the reduction.
    """
    block = _named_blocks(source, heads=("Class",)).get(name)
    if block is None:
        raise UsageError(f"no Class named {name!r}")
    region = source[block.statement_start : block.statement_end]
    assign = _top_level_find(region, ":=")
    open_ = _top_level_find(region, "{", assign + 2) if assign >= 0 else -1
    close = _matching(region, open_) if open_ >= 0 else -1
    if close < 0:
        raise UsageError(f"cannot minimise Class {name!r}: no `:= {{ ... }}` body")
    body = "\n" + "\n".join(f"  {f.strip()};" for f in fields if f.strip()) + "\n"
    return source[: block.statement_start] + region[: open_ + 1] + body + region[close:] + source[block.statement_end :]


# ------------------------------------------------------------ the persistence guard

def add_persistence_obligation(source: str, name: str) -> str:
    """Insert ``Lemma <name>_persistent .. : Persistent (<name> ..)`` after ``<name>``.

    A design rung that stubs the client-facing predicate has a degenerate solution:
    define it as *exclusive* ownership of the location.  Every specification still
    goes through -- with no interference the CmpXchg cannot fail, so the prophecy and
    the helping protocol are never needed.  Requiring persistence forces sharing, and
    sharing brings the hard case back (BENCHMARKS.md "The degenerate solution").

    The obligation is inserted **proved** (``apply _.``) and is *not* held out: held
    out it would be inert (``True`` is persistent).  Left proved, every compile
    enforces it, so a degenerate design is rejected at adoption.  Implicit binders are
    made explicit and the application uses ``@``; a generalising binder is refused
    loudly rather than turned into a plausible wrong goal.
    """
    block = _named_blocks(source).get(name)
    if block is None:
        raise UsageError(f"--persistent {name}: no such declaration")
    decl = split_declaration(block)
    if decl.body is None:
        raise UsageError(f"--persistent {name}: not a definition with a body")
    binders: list[str] = []
    args: list[str] = []
    implicit = False
    for b in parse_binders(decl.binders):
        if b.kind == "generalising":
            raise UsageError(
                f"--persistent {name}: generalising binder `(..) is not supported; "
                "state the obligation in the source instead"
            )
        args += b.names
        if b.kind == "implicit":
            implicit = True
            binders.append(f"({b.text[1:-1]})" if b.annotation is not None else " ".join(b.names))
        elif b.kind == "explicit":
            binders.append(b.text)
        else:
            binders.append(b.names[0])
    application = " ".join([("@" if implicit else "") + name, *args])
    line_start = source.rfind("\n", 0, block.statement_start) + 1
    indent = source[line_start : block.statement_start]
    if indent.strip():
        indent = ""
    sep = " " if binders else ""
    lemma = (
        f"\n\n{indent}Lemma {name}_persistent{sep}{' '.join(binders)} : "
        f"Persistent ({application}).\n{indent}Proof. apply _. Qed."
    )
    end = block.end
    return source[:end] + lemma + source[end:]


# ------------------------------------------------------------------ verification

def compile_source(text: str, filename: str, *, timeout: float = COMPILE_TIMEOUT) -> CompileResult:
    """``coqc -Q <dir> bench <filename>`` in a fresh scratch directory (``pcp.rocq.project``)."""
    scratch = Path(tempfile.mkdtemp(prefix="pcp-bench-"))
    try:
        result = compile_text(
            text,
            filename=filename,
            root=ensure_dir(scratch / "root"),
            flags=list(PROJECT_FLAGS),
            timeout=timeout,
            scratch_root=scratch / "work",
        )
    finally:
        rm_tree(scratch)
    if result.unavailable:
        raise ToolchainError(result.unavailable)
    return result


def _tail(result: CompileResult, limit: int = 3000) -> str:
    return result.output[-limit:]


# ------------------------------------------------------------------- the brief

def _brief_header(file: str) -> list[str]:
    return [f"# Design brief: `{file}`", ""]


def _specs_section(holdouts: list[HeldOut]) -> list[str]:
    lines = ["## What you must prove", ""]
    for h in holdouts:
        lines += [f"### `{h.anonymised}`", "", "```coq", h.statement.strip(), "```", ""]
    return lines


def spec_only_brief(corpus_dir: str | Path) -> str:
    """Just the held-out statements of a corpus, from its ``bench.json``.

    The orchestrator's ``--brief spec-only`` hands workers this instead of
    ``DESIGN.md``: no glossary, no roles, no author prose -- the theorem and nothing
    else.  Pure: the only I/O is reading the corpus.
    """
    data = json_load(Path(corpus_dir) / BENCH_FILE)
    holdouts = [HeldOut.from_json(h) for h in data.get("holdout", [])]
    return "\n".join(_brief_header(data["file"]) + _specs_section(holdouts)).rstrip("\n") + "\n"


def render_design(
    original: str,
    stubbed: str,
    bench: Benchmark,
    roles: dict[str, str],
    *,
    notes: str = "full",
) -> str:
    """The design brief handed to every worker (``DESIGN.md``).

    Anonymisation removes the *search key*, not the design: the invariant, the
    abstract predicate and the ghost-state plan are given exactly as PLAN.md 9.3 says
    (the sketch is frozen first, the tactic work is dispatched).  ``notes`` sets how
    much beyond the code is said: ``none`` is the spec-only brief (structure only, no
    role descriptions, no author prose), ``glossary`` adds the roles, ``full`` adds
    the author's longer comments as well.
    """
    if notes not in DESIGN_NOTE_LEVELS:
        raise UsageError(f"--design-notes must be one of {', '.join(DESIGN_NOTE_LEVELS)}")
    roles = roles if notes != "none" else {}
    lines = _brief_header(bench.file)
    lines += _intro(bench) + [""]
    lines += _specs_section(bench.holdout)
    lines += _definitions_section(stubbed, bench, roles)
    lines += _lemmas_section(stubbed, bench, roles)
    if notes == "full":
        lines += _prose_section(original, bench.rename_map)
    return "\n".join(lines) + "\n"


def _intro(bench: Benchmark) -> list[str]:
    if bench.stubbed or bench.dropped:
        blanked = ", ".join(f"`{d.anonymised}`" for d in bench.stubbed)
        return [
            "You are given **the implementation and the specifications, and nothing "
            "else**. The predicates the specifications are stated in terms of"
            + (f" ({blanked})" if blanked else "")
            + " are present but **empty** -- defined as `True`, which makes the "
            "specifications unprovable as they stand.",
            "",
            "Designing them is the task. Decide what the client owns, what invariant "
            "protects the cell, and what ghost state connects the two, then fill the "
            "definitions in and prove the specifications against them. You may add "
            "definitions, resource algebras, typeclass fields, imports and helper "
            "lemmas. You may **not** change the program or any specification: those "
            "are the theorem.",
        ]
    return [
        "This development's design is **given**: the implementation, the invariants, "
        "the ghost state and the helper lemmas are all present and correct. What is "
        "held out is the tactic work for the specifications below."
    ]


def _definitions_section(stubbed: str, bench: Benchmark, roles: dict[str, str]) -> list[str]:
    blanked = {d.anonymised for d in bench.stubbed}
    lines = ["## Given definitions", ""]
    if blanked:
        lines.append("The program is frozen. The predicates marked **(blank)** are yours to define; everything else is read-only.")
    else:
        lines.append("These are frozen. Read them; do not change them.")
    lines.append("")
    inverse = {v: k for k, v in bench.rename_map.items()}
    for block in parse_blocks(stubbed):
        if block.head not in ("Definition", "Class", "Record", "Inductive", "Instance") or not block.name:
            continue
        note = roles.get(inverse.get(block.name, block.name), "")
        mark = " **(blank -- yours to define)**" if block.name in blanked else ""
        lines.append(f"- `{block.name}`{mark}" + (f" -- {note}" if note else ""))
    return lines


def _lemmas_section(stubbed: str, bench: Benchmark, roles: dict[str, str]) -> list[str]:
    given = [b.name for b in parse_blocks(stubbed) if b.head in ("Lemma", "Theorem") and b.has_proof and b.ender == "Qed" and b.name]
    if not given:
        return []
    inverse = {v: k for k, v in bench.rename_map.items()}
    lines = ["", "## Given lemmas (already proved -- use them)", ""]
    for n in given:
        note = roles.get(inverse.get(n, n), "")
        lines.append(f"- `{n}`" + (f" -- {note}" if note else ""))
    return lines


def _prose_section(original: str, mapping: dict[str, str]) -> list[str]:
    """The author's longer comments, quoted; only ``[...]`` doc spans are renamed.

    Applying the map to running prose turns "the failing write" into "the failing
    c2": unreadable, and it withholds design rather than a search key.
    """
    notes = [text.strip("(*) ").strip() for _s, _e, text in iter_comments(original)]
    notes = [_rename_bracketed(n, mapping) for n in notes if len(n) > 150]
    if not notes:
        return []
    lines = ["", "## Design notes from the author", ""]
    for n in notes[:4]:
        lines += ["> " + line.strip().lstrip("*").strip() for line in n.splitlines()]
        lines.append("")
    return lines


def _rename_bracketed(text: str, mapping: dict[str, str]) -> str:
    out: list[str] = []
    i = 0
    while True:
        a = text.find("[", i)
        b = text.find("]", a + 1) if a >= 0 else -1
        if a < 0 or b < 0:
            out.append(text[i:])
            return "".join(out)
        out += [text[i : a + 1], rename_text(text[a + 1 : b], mapping), "]"]
        i = b + 1


# ---------------------------------------------------------------------- pipeline

@dataclass(frozen=True)
class Options:
    """The CLI, resolved.  Paths are absolute by the time they get here (rule 4)."""

    source: Path
    holdout: tuple[str, ...]
    out: Path
    reference: Path
    name: str | None = None
    salt: str = "pcp"
    anonymise: bool = True
    keep_comments: bool = False
    mutable: tuple[str, ...] = ()
    allow_additions: bool = True
    strip_comments: bool = False
    persistent: tuple[str, ...] = ()
    verify: bool = True
    drop: tuple[str, ...] = ()
    imports: tuple[str, ...] = ()
    class_fields: tuple[tuple[str, tuple[str, ...]], ...] = ()
    roles: dict[str, str] = field(default_factory=dict)
    design_notes: str = "full"
    stub_definitions: tuple[str, ...] = ()

    @classmethod
    def from_args(cls, args: argparse.Namespace) -> Options:
        class_fields = []
        for spec in args.class_fields:
            cname, _, fields = spec.partition("=")
            class_fields.append((cname.strip(), tuple(f for f in fields.split(";") if f.strip())))
        return cls(
            source=Path(args.source).resolve(),
            holdout=tuple(args.holdout),
            out=Path(args.out).resolve(),
            reference=Path(args.reference).resolve(),
            name=args.name,
            salt=args.salt,
            anonymise=not args.no_anonymise,
            keep_comments=args.keep_comments,
            mutable=tuple(args.mutable),
            allow_additions=not args.no_additions,
            strip_comments=args.strip_comments,
            persistent=tuple(args.persistent),
            verify=not args.skip_verify,
            drop=tuple(args.drop),
            imports=tuple(args.imports),
            class_fields=tuple(class_fields),
            roles=dict(r.split("=", 1) for r in args.role if "=" in r),
            design_notes=args.design_notes,
            stub_definitions=tuple(args.stub_definition),
        )


@dataclass
class Built:
    """A rung ready to be written: the corpus and the answer key, still in memory."""

    name: str
    bench: Benchmark
    corpus_text: str
    reference_text: str
    design_md: str
    out: Path
    reference: Path


Log = Callable[[str], None]


def refuse_key_inside_corpus(out: Path, reference: Path) -> None:
    out, reference = Path(out).resolve(), Path(reference).resolve()
    if reference == out or out in reference.parents:
        raise UsageError("--reference must not live inside --out: that is the answer key")


def module_name(source: Path, salt: str, anonymised: bool) -> str:
    stem = Path(source).stem
    if not anonymised:
        return stem[0].upper() + stem[1:]
    return "M" + hashlib.blake2b(f"{salt}:{stem}".encode(), digest_size=3).hexdigest()


def build(opts: Options, *, log: Log = print, warn: Log | None = None) -> Built:
    """Run the stages in the one order that works (map-eval §5.4).

    1. guards on the **original**, compiled to prove the reference satisfies them;
    2. hold out;
    3. signatures, while the original imports and bodies still exist -- blanking a
       body destroys the inference that gave ``γ : gname``, scrubbing the imports
       destroys the compile;
    4. drop, minimise the class, replace imports, stub, strip comments, anonymise;
    5. verify by compiling; refuse to emit otherwise.
    """
    warn = warn or (lambda m: print(m, file=sys.stderr))
    refuse_key_inside_corpus(opts.out, opts.reference)
    source = read_text(opts.source)
    guards: list[str] = []
    for target in opts.persistent:
        source = add_persistence_obligation(source, target)
        guards.append(f"{target}_persistent")
    if guards and opts.verify:
        result = compile_source(source, f"{opts.name or 'Reference'}.v")
        if not result.ok:
            raise CorpusError("the persistence obligation is not provable by the reference design:\n" + _tail(result))
        log(f"verified: reference proves {len(guards)} persistence obligation(s)")

    text, held = hold_out(source, list(opts.holdout))
    types = _signatures(text, opts, warn)

    dropped: list[str] = []
    if opts.drop:
        text, dropped = drop_declarations(text, list(opts.drop))
    for cname, fields in opts.class_fields:
        text = minimize_class(text, cname, list(fields))
    if opts.imports:
        text = set_imports(text, list(opts.imports))
    stub_defs: list[StubbedDefinition] = []
    if opts.stub_definitions:
        text, stub_defs = stub_definitions(text, list(opts.stub_definitions), types=types)
    if opts.strip_comments:
        text = tidy(strip_comments(text))
    mapping: dict[str, str] = {}
    if opts.anonymise:
        text, mapping = anonymise(text, salt=opts.salt, drop_comments=not opts.keep_comments)
    for h in held:
        h.anonymised = mapping.get(h.name, h.name)
        h.statement = rename_text(h.statement, mapping)
    for sd in stub_defs:
        sd.anonymised = mapping.get(sd.name, sd.name)
        sd.stub = rename_text(sd.stub, mapping)

    name = opts.name or module_name(opts.source, opts.salt, opts.anonymise)
    bench = Benchmark(
        source=str(opts.source),
        file=f"{name}.v",
        anonymised=opts.anonymise,
        holdout=held,
        stubbed=stub_defs,
        dropped=dropped,
        mutable=sorted({*opts.mutable, *(sd.anonymised for sd in stub_defs)}),
        results=sorted(mapping.get(g, g) for g in guards),
        allow_additions=opts.allow_additions,
        rename_map=mapping,
        notes=[DESIGN_NOTE],
    )
    if opts.verify:
        result = compile_source(text, bench.file)
        if not result.ok:
            raise CorpusError("the held-out development does not compile:\n" + _tail(result))
        log(f"verified: {bench.file} compiles with {len(held)} proof(s) held out")
    return Built(
        name=name,
        bench=bench,
        corpus_text=text,
        reference_text=rename_text(source, mapping),
        design_md=render_design(source, text, bench, opts.roles, notes=opts.design_notes),
        out=opts.out,
        reference=opts.reference,
    )


def _signatures(text: str, opts: Options, warn: Log) -> dict[str, str]:
    names = [s.partition("=")[0].strip() for s in opts.stub_definitions]
    if not names:
        return {}
    if not opts.verify and penv.coqc_binary() is None:
        warn("no coqc on PATH: stub signatures are not resolved (--skip-verify)")
        return {}
    try:
        types = definition_types(text, names)
    except UsageError as exc:
        if opts.verify:
            raise
        warn(f"{exc}; stubs keep their binders as written (--skip-verify)")
        return {}
    if types:
        warn("resolved signatures: " + "; ".join(f"{k} : {v}" for k, v in types.items()))
    return types


def emit(built: Built) -> None:
    """Write the corpus, then the answer key -- atomically, so a reader never sees half a rung."""
    out = ensure_dir(built.out)
    bench = built.bench
    atomic_write_text(out / bench.file, built.corpus_text)
    json_dump(out / DESIGN_FILE, bench.contract_json())
    atomic_write_text(out / BRIEF_FILE, built.design_md)
    atomic_write_text(out / PROJECT_FILE, PROJECT)
    json_dump(out / BENCH_FILE, bench.to_json())
    ref = ensure_dir(built.reference)
    json_dump(ref / REFERENCE_FILE, bench.reference_json())
    atomic_write_text(ref / f"{built.name}_reference.v", built.reference_text)


def report(built: Built, log: Log = print) -> None:
    bench = built.bench
    log(f"corpus     {built.out}/{bench.file}")
    log(f"answer key {built.reference}/  (keep this out of every worker sandbox)")
    for h in bench.holdout:
        log(f"  held out {h.anonymised:<28} {h.lines:>4} lines, {h.tactics:>3} tactics")
    for sd in bench.stubbed:
        log(f"  stubbed  {sd.anonymised:<28} definition body blanked to True")
    for g in bench.results:
        log(f"  guard    {g:<28} given proved; frozen, enforced by every compile")
    for n in bench.dropped:
        log(f"  dropped  {n:<28} removed entirely")
    log(
        f"  contract may change: {', '.join(bench.mutable) or 'nothing'}"
        f"; additions {'allowed' if bench.allow_additions else 'forbidden'}"
    )


# --------------------------------------------------------------------------- CLI

def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description="Build a contamination-controlled benchmark rung from a Rocq development.")
    ap.add_argument("source", type=Path)
    ap.add_argument("--holdout", nargs="+", required=True, metavar="NAME")
    ap.add_argument(
        "--stub-definition", action="append", default=[], metavar="NAME[=TYPE]",
        help="blank a definition's body to `True`, so the worker must invent it: "
        "--stub-definition value --stub-definition rwcas_inv",
    )
    ap.add_argument("--out", type=Path, required=True, help="corpus directory (goes in the repo)")
    ap.add_argument("--reference", type=Path, required=True, help="where the answer key goes -- must NOT be inside --out")
    ap.add_argument("--name", default=None, help="module name in the corpus (default: derived)")
    ap.add_argument("--salt", default="pcp", help="anonymisation salt; change it to re-anonymise")
    ap.add_argument("--no-anonymise", action="store_true")
    ap.add_argument("--keep-comments", action="store_true")
    ap.add_argument(
        "--mutable", action="append", default=[], metavar="NAME",
        help="declare a definition the design process may rewrite (the stubbed ones always are)",
    )
    ap.add_argument("--no-additions", action="store_true", help="forbid introducing new declarations")
    ap.add_argument(
        "--strip-comments", action="store_true",
        help="remove every comment, independently of anonymisation (the header narrates the strategy)",
    )
    ap.add_argument(
        "--persistent", action="append", default=[], metavar="NAME",
        help="require NAME to be persistent, as a guard given proved (see docs/BENCHMARKS.md)",
    )
    ap.add_argument("--skip-verify", action="store_true", help="do not compile-check the result")
    ap.add_argument("--drop", action="append", default=[], metavar="NAME", help="delete a declaration outright, with its comments")
    ap.add_argument("--imports", action="append", default=[], metavar="LINE", help="replace every Require sentence with these")
    ap.add_argument("--class-fields", action="append", default=[], metavar="NAME=F1;F2", help="reduce a typeclass to the listed fields")
    ap.add_argument("--role", action="append", default=[], metavar="NAME=DESCRIPTION", help="annotate a given definition for the brief")
    ap.add_argument(
        "--design-notes", choices=list(DESIGN_NOTE_LEVELS), default="full",
        help="what DESIGN.md says beyond the code: nothing (spec-only), the glossary, or the glossary plus the original prose",
    )
    return ap


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        built = build(Options.from_args(args))
        emit(built)
        report(built)
    except PcpError as exc:
        print(str(exc), file=sys.stderr)
        return exc.exit_code
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
