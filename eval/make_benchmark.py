#!/usr/bin/env python3
"""Build a contamination-controlled benchmark from a real Rocq development.

PLAN.md 13 asks for held-out lemmas: replace bodies with `Admitted`, ask an agent to
reprove them.  For a *public* development that is not enough on its own — the answer
is on the internet, and may be in the model's weights.  So this does three things:

1. **Holds out** the named proofs, leaving every definition, invariant and helper the
   original had.  The design is given; the tactic work is not.
2. **Anonymises** file-local identifiers and strips prose comments, so neither a
   local grep nor a memorised lemma name is a shortcut.  Role suffixes (`_inv`,
   `_spec`, `_alloc`) are preserved so the task stays readable.
3. **Keeps the reference proofs out of the corpus directory entirely**, in a separate
   location the worker sandbox never binds.

Anonymisation is *verified*: the rewritten file must still compile, or the tool
refuses to emit it.  A benchmark that does not build is worse than no benchmark.

    python eval/make_benchmark.py /tmp/bench/build/rwcas.v \\
        --holdout read_spec write_spec new_rwcas_spec \\
        --out eval/corpus/bench/rwcas --reference .pcp/reference/rwcas

Honest limitation, recorded here because it bounds what the numbers mean: this
defeats lookup and name-matching. It does not prove the model has not memorised the
*proof structure* of a public development. Treat a solve on an anonymised public
corpus as an upper bound, and compare against a private one before believing it.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pcp.core.vernac import iter_comments, parse_blocks, strip_comments  # noqa: E402
from pcp.orch.gate import coqc_binary  # noqa: E402

#: Suffixes that carry the *role* of a name.  Keeping them keeps the development
#: legible without keeping it searchable.
ROLE_SUFFIXES = (
    "_spec", "_inv", "_alloc", "_agree", "_update", "_own", "_valid", "_op",
    "_lookup", "_insert", "_snoc", "_cons", "_nil", "_wf", "_closed", "_ne",
    "_proper", "_persistent", "_timeless", "_G", "_pre", "_post",
)

#: Heads whose declared names are file-local and therefore safe to rename.
RENAMEABLE_HEADS = (
    "Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark", "Property",
    "Definition", "Fixpoint", "CoFixpoint", "Inductive", "Record", "Class",
    "Instance", "Example", "Variant", "Structure",
)

_COMMENT = re.compile(r"\(\*.*?\*\)", re.S)
_CLASS_FIELD = re.compile(r"^\s*([A-Za-z_][\w']*)\s*::", re.M)
_SECTION = re.compile(r"^\s*Section\s+([A-Za-z_][\w']*)\s*\.", re.M)


@dataclass
class StubbedDefinition:
    """A design artifact the worker has to invent, not one it is handed."""

    name: str
    anonymised: str
    original: str
    stub: str
    original_sha256: str


@dataclass
class HeldOut:
    name: str
    anonymised: str
    statement: str
    reference_body: str
    reference_sha256: str
    lines: int
    tactics: int


@dataclass
class Benchmark:
    source: str
    file: str
    anonymised: bool
    holdout: list[HeldOut] = field(default_factory=list)
    stubbed: list[StubbedDefinition] = field(default_factory=list)
    dropped: list[str] = field(default_factory=list)
    #: Declarations the design process may rewrite.  Everything else is frozen, and
    #: the freeze is checked rather than trusted.
    mutable: list[str] = field(default_factory=list)
    #: Statements that are given *proved* and must stay exactly as they are: design
    #: guards.  Unlike the holdout there is no work to do on them -- their whole
    #: function is that a design which breaks one stops compiling.
    results: list[str] = field(default_factory=list)
    allow_additions: bool = True
    rename_map: dict[str, str] = field(default_factory=dict)
    notes: list[str] = field(default_factory=list)

    def to_json(self) -> dict:
        """What ships *inside the corpus* -- so, what a worker is allowed to read.

        The sandbox binds the rung under test, this file included, so anything left
        here is handed over. Two fields were handing over a great deal:

        * ``dropped`` listed the scrubbed declarations **by name** --
          `requestReg`, `AU_write`, `write_inv`, `registry_inv`, `linearize_writes`
          -- which is the ghost-state architecture and the helping protocol, named.
          Scrubbing the declarations and then naming them is not scrubbing.
        * ``source`` was the absolute path of the upstream file, so it named the
          development: a search key, which is the one thing anonymisation exists to
          remove.

        Both stay in ``reference.json``, which is masked.
        """
        d = asdict(self)
        # The reference bodies are the answer key. They never go in the corpus.
        for h in d["holdout"]:
            h.pop("reference_body", None)
        for st in d["stubbed"]:
            # The original body of a stubbed invariant is as much of an answer as a
            # proof is; it is recorded by hash only.
            st.pop("original", None)
        d.pop("source", None)
        d["dropped"] = len(self.dropped)
        return d


# ------------------------------------------------------------------ anonymisation

def local_names(source: str) -> list[str]:
    """Identifiers this file declares.  Library names are never touched."""
    names: list[str] = []
    for block in parse_blocks(source):
        if block.head in RENAMEABLE_HEADS and block.name:
            names.append(block.name)
    names += _CLASS_FIELD.findall(source)
    names += _SECTION.findall(source)
    seen: set[str] = set()
    out = []
    for n in names:
        if n not in seen and len(n) > 2:
            seen.add(n)
            out.append(n)
    return out


def pseudonym(name: str, index: int, salt: str) -> str:
    """A stable, unguessable-but-readable replacement.

    The role suffix survives (`write_spec` -> `q3a_spec`), so a reader can still tell
    a spec from an invariant; the searchable part does not.
    """
    for suffix in ROLE_SUFFIXES:
        if name.endswith(suffix) and len(name) > len(suffix):
            return f"{_tag(name, salt)}{index}{suffix}"
    return f"{_tag(name, salt)}{index}"


def _tag(name: str, salt: str) -> str:
    digest = hashlib.blake2b(f"{salt}:{name}".encode(), digest_size=2).hexdigest()
    return "".join(c for c in digest if c.isalpha()) or "x"


def anonymise(source: str, *, salt: str, drop_comments: bool = True) -> tuple[str, dict[str, str]]:
    names = local_names(source)
    mapping = {n: pseudonym(n, i, salt) for i, n in enumerate(names)}
    # Longest first, so `write_spec` is rewritten before `write`.
    out = source
    for name in sorted(mapping, key=len, reverse=True):
        out = re.sub(rf"\b{re.escape(name)}\b", mapping[name], out)
    if drop_comments:
        # Nesting-aware: Rocq comments nest, and a regex leaves dangling `*)`.
        out = strip_comments(out)
        out = re.sub(r"[ \t]+\n", "\n", out)
        out = re.sub(r"\n{3,}", "\n\n", out)
    return out, mapping


# ----------------------------------------------------------------------- holdout

def _split_definition(text: str) -> tuple[str, str | None] | None:
    """Split ``Definition f (n : Z) : T := body.`` into (head, annotation).

    Depth-aware rather than regex-based: binders contain colons (``(n : Z)``) and
    bodies contain ``:=``, so the top-level occurrences are the only ones that mean
    what they look like.
    """
    depth = 0
    assign = -1
    for i, ch in enumerate(text):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and text.startswith(":=", i):
            assign = i
            break
    if assign < 0:
        return None
    head = text[:assign].rstrip()
    depth = 0
    colon = -1
    for i, ch in enumerate(head):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and ch == ":" and not head.startswith(":=", i):
            colon = i
            break
    if colon < 0:
        return head, None
    return head[:colon].rstrip(), head[colon + 1 :].strip()


_ABOUT = re.compile(r"^(?P<name>[\w']+)\s*:\s*(?P<type>.+?)(?=\n\S|\n\s*\n|\Z)", re.M | re.S)


def definition_types(source: str, names: list[str], *, project: str = "-Q . bench\n") -> dict[str, str]:
    """Ask Rocq for each definition's full type, in one compile.

    Needed because blanking a body also destroys type inference: `value γ n` had
    `γ : gname` only because the body applied `ghost_var` to it, so the stub has to
    carry the signature the original never had to write down.
    """
    probe = source.rstrip() + "\n\n" + "\n".join(f"About {n}." for n in names) + "\n"
    coqc = coqc_binary()
    if coqc is None:
        return {}
    work = Path(tempfile.mkdtemp(prefix="pcp-about-"))
    try:
        (work / "About_probe.v").write_text(probe, encoding="utf-8")
        (work / "_CoqProject").write_text(project, encoding="utf-8")
        proc = subprocess.run(
            [coqc, "-Q", str(work), "bench", "-w", "-notation-overridden", "About_probe.v"],
            cwd=str(work), capture_output=True, text=True, timeout=7200,
        )
        out = proc.stdout + proc.stderr
    finally:
        shutil.rmtree(work, ignore_errors=True)
    found: dict[str, str] = {}
    for m in _ABOUT.finditer(out):
        name = m.group("name")
        if name in names and name not in found:
            ty = " ".join(m.group("type").split())
            # `About` appends provenance after the type; keep only the type itself.
            ty = re.split(r"\s*\(\S+ is (?:not )?universe|\s*Arguments |\s*Expands to", ty)[0]
            found[name] = ty.rstrip(".").strip()
    return found


def stub_definitions(
    source: str,
    specs: list[str],
    *,
    default_type: str = "iProp Σ",
    types: dict[str, str] | None = None,
) -> tuple[str, list[StubbedDefinition]]:
    """Replace named definitions' bodies with ``True``.

    This is the difference between "prove this, given the design" and "design it and
    prove it".  For a CSL development the invariant and the abstract state predicate
    *are* the problem: with them supplied, the remaining work is tactic bookkeeping;
    with them blanked, the worker has to invent the ghost state, decide what the
    client owns, and make the frozen specifications come out true.

    ``specs`` entries are ``name`` or ``name=TYPE``.  A definition with no return
    annotation gets ``default_type``, because ``:= True`` alone elaborates in ``Prop``
    and every use site then fails to typecheck.
    """
    wanted: dict[str, str | None] = {}
    for entry in specs:
        name, _, ty = entry.partition("=")
        wanted[name.strip()] = ty.strip() or None

    blocks = {b.name: b for b in parse_blocks(source) if b.head == "Definition"}
    missing = [n for n in wanted if n not in blocks]
    if missing:
        raise SystemExit(f"no Definition named: {', '.join(missing)}")

    out: list[str] = []
    cursor = 0
    stubbed: list[StubbedDefinition] = []
    for name in sorted(wanted, key=lambda n: blocks[n].statement_start):
        block = blocks[name]
        text = source[block.statement_start : block.statement_end]
        split = _split_definition(text)
        if split is None:
            raise SystemExit(f"cannot parse the definition of {name!r} to stub it:\n{text[:200]}")
        head, ann = split
        binders = _binder_names_of(head, name)
        signature = wanted[name] or (types or {}).get(name)
        annotated = _annotate_binders(name, binders, signature)
        ret = ann or (_return_type(signature) if signature else None) or default_type
        if annotated is None:
            # No signature available: keep the head as written and hope the binders
            # were already annotated.  Verification will catch it if they were not.
            replacement = f"{head} : {ret} := True%I."
        else:
            replacement = f"Definition {name}{annotated} : {ret} := True%I."
        out.append(source[cursor : block.statement_start])
        out.append(replacement)
        cursor = block.statement_end
        stubbed.append(
            StubbedDefinition(
                name=name,
                anonymised=name,
                original=text,
                stub=replacement,
                original_sha256=hashlib.sha256(text.encode()).hexdigest(),
            )
        )
    out.append(source[cursor:])
    return "".join(out), stubbed


def _split_arrows(ty: str) -> list[str]:
    """Top-level `→`-separated components of a type."""
    parts: list[str] = []
    depth = 0
    buf = ""
    i = 0
    while i < len(ty):
        ch = ty[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if depth == 0 and ty.startswith("→", i):
            parts.append(buf.strip())
            buf = ""
            i += 1
            continue
        buf += ch
        i += 1
    parts.append(buf.strip())
    return [p for p in parts if p]


def _strip_implicit_prefix(ty: str) -> str:
    """Drop a leading `∀ {Σ : gFunctors},` -- section variables Rocq discharged."""
    m = re.match(r"\s*(?:∀|forall)\s*(?:\{[^}]*\}|\([^)]*\)|[^,])*,\s*(.*)", ty, re.S)
    return m.group(1).strip() if m else ty.strip()


def _return_type(signature: str | None) -> str | None:
    if not signature:
        return None
    parts = _split_arrows(_strip_implicit_prefix(signature))
    return parts[-1] if parts else None


def _binder_groups(rest: str) -> list[str]:
    """Split a binder list into groups, respecting nesting.

    A regex cannot do this: `(requests : list (gname * Z))` closes twice, and
    stopping at the first `)` invents a phantom binder that shifts every subsequent
    type by one.
    """
    groups: list[str] = []
    depth = 0
    buf = ""
    for ch in rest:
        if ch in "([{":
            depth += 1
            if depth == 1 and ch == "(":
                if buf.strip():
                    groups.extend(buf.split())
                buf = ""
                continue
        elif ch in ")]}":
            depth -= 1
            if depth == 0:
                groups.append(buf)
                buf = ""
                continue
        if depth == 0 and ch.isspace():
            if buf.strip():
                groups.extend(buf.split())
            buf = ""
            continue
        buf += ch
    if buf.strip():
        groups.extend(buf.split())
    return [g for g in groups if g.strip()]


def _binder_names_of(head: str, name: str) -> list[str]:
    """Binder names in `Definition f a (b : T) c` -- in order, groups flattened."""
    rest = head.split(name, 1)[-1]
    out: list[str] = []
    for group in _binder_groups(rest):
        head_part = group.split(":")[0]
        for t in head_part.split():
            t = t.strip("{}")
            if not t:
                continue
            # `'γ` is a *pattern* binder; it cannot carry a type annotation. The stub
            # body references nothing and every call site is positional, so the name
            # is free to normalise.
            out.append(t.lstrip("'"))
    return out


def _annotate_binders(name: str, binders: list[str], signature: str | None) -> str | None:
    """Give each original binder an explicit type, taken from the discharged signature.

    Rocq reports a section definition's type *after* discharge, so the leading
    arguments are the section's own `Context` variables.  The definition's own
    binders are the trailing ones, which is why this zips from the right.
    """
    if not signature or not binders:
        return None
    args = _split_arrows(_strip_implicit_prefix(signature))[:-1]
    if len(args) < len(binders):
        return None
    tail = args[len(args) - len(binders) :]
    return "".join(f" ({b} : {t})" for b, t in zip(binders, tail))


def _arrow_arity(ty: str) -> int:
    """Top-level arrows in a type -- how many arguments the stub must abstract."""
    depth = 0
    n = 0
    i = 0
    while i < len(ty):
        ch = ty[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and ty.startswith("→", i):
            n += 1
        elif depth == 0 and ty.startswith("forall", i):
            return 0  # dependent: fall back to keeping the original binders
        i += 1
    return n


#: `[^.]*\.` cannot cross a dot *inside* the import list, so
#: `From iris.algebra Require Import auth gmap list lib.mono_nat.` never matched and
#: survived `--imports` -- leaving `auth`, `gmap` and `mono_nat` named in a benchmark
#: whose whole point is that the ghost-state plan is not given. The one design rung
#: that existed was clean only because its imports happen to contain no dotted module
#: names. Match to the final `.` at end of line instead.
_REQUIRE = re.compile(
    r"^[ \t]*(?:From\s+\S+\s+)?Require\s+(?:Import|Export)?[^\n]*?\.[ \t]*$", re.M
)
# Named groups throughout: a bare `(...)` next to a `(?P<name>...)` shifts every
# subsequent index, and picking the wrong one silently emits the old body and drops
# the closing brace.
#: `[^:=]*` for the binders looked right and silently excluded every class written
#: `Class seqlockG (Σ : gFunctors) := {` -- the `:` inside the annotated binder ends
#: the match before the `:=` ever arrives. Only `Class rwcasG Σ := {` worked, which
#: is why the one design rung that existed was the one that happened to be spelled
#: that way. Consume anything up to the `:=` that opens the body instead.
_CLASS_BODY = re.compile(
    r"(?P<open>Class\s+(?P<name>[\w']+)\b[^{]*?:=\s*\{)(?P<body>.*?)(?P<close>\})", re.S
)


def drop_declarations(source: str, names: list[str]) -> tuple[str, list[str]]:
    """Delete named declarations outright, with the comment that introduces them.

    Stubbing a definition to `True` still tells the worker that *something* of that
    shape exists.  For design a worker is supposed to invent -- the resource algebra
    behind a registry, a helper lemma that only makes sense inside one proof -- the
    honest scrub is deletion, and the comment above it goes too: a comment explaining
    an invariant describes the answer as surely as the invariant does.
    """
    blocks = {b.name: b for b in parse_blocks(source)}
    missing = [n for n in names if n not in blocks]
    if missing:
        raise SystemExit(f"nothing named: {', '.join(missing)}")

    spans: list[tuple[int, int]] = []
    for name in names:
        block = blocks[name]
        end = block.ender_end or block.statement_end
        spans.append((_comment_start_before(source, block.statement_start), end))

    # Highest offset first, so earlier offsets stay valid as the text shrinks.
    out = source
    for begin, finish in sorted(spans, reverse=True):
        out = out[:begin].rstrip() + "\n\n" + out[finish:].lstrip("\n")
    return out, list(names)


def _comment_start_before(source: str, offset: int) -> int:
    """Start of the comment block immediately preceding ``offset``, else ``offset``.

    Uses the lexer's own nesting-aware scan rather than a backwards search: a
    hand-rolled reverse walk mis-nests on `(** … *)` headers and, in one case here,
    swallowed the entire file preamble.
    """
    best = offset
    for cstart, cend, _text in iter_comments(source):
        if cend > offset:
            break
        if not source[cend:offset].strip():
            best = min(best, cstart)
    return best


def set_imports(source: str, imports: list[str]) -> str:
    """Replace every `Require` line with a given, minimal set.

    `From iris.base_logic.lib Require Import token ghost_var` names three quarters of
    the intended ghost-state plan. A benchmark that leaves it in is measuring
    something other than design.
    """
    lines = [ln if ln.strip().endswith(".") else ln.strip() + "." for ln in imports]
    replacement = "\n".join(lines)
    first = _REQUIRE.search(source)
    if first is None:
        return replacement + "\n\n" + source
    out = _REQUIRE.sub("", source)
    return out[: first.start()] + replacement + "\n" + out[first.start() :].lstrip("\n")


def minimize_class(source: str, name: str, fields: list[str]) -> str:
    """Reduce a typeclass to the listed fields.

    A `Class rwcasG Σ` listing `inG Σ requestRegUR`, `tokenG Σ` and two `ghost_varG`
    instances *is* the ghost-state design. Left in, the worker only has to guess how
    to assemble parts it has already been handed.
    """

    def rewrite(m: re.Match[str]) -> str:
        if m.group("name") != name:
            return m.group(0)
        body = "\n" + "\n".join(f"  {f.strip()};" for f in fields if f.strip()) + "\n"
        return m.group("open") + body + m.group("close")

    out, n = _CLASS_BODY.subn(rewrite, source)
    if n == 0:
        raise SystemExit(f"no Class named {name!r}")
    return out


def _binder_signature(head: str, name: str) -> tuple[str, str]:
    """`Definition f {a : A} (b c : B)` -> ("(a : A) (b c : B)", "@f a b c").

    Reconstructing the application is the fiddly half.  An *implicit* binder cannot be
    passed positionally, so `Persistent (f a b c)` would not typecheck; making every
    binder explicit and applying with `@` is the one form that is right whether the
    original binder was implicit or not.  `@` is only reached for when it is needed,
    so the common all-explicit case keeps the plain application.
    """
    rest = head.split(name, 1)[-1].strip()
    groups: list[tuple[str, str]] = []
    i = 0
    while i < len(rest):
        ch = rest[i]
        if ch.isspace():
            i += 1
            continue
        if ch == "`":
            # A generalising binder discharges into the statement in a way this
            # cannot reproduce.  Fail loudly rather than emit a plausible wrong goal.
            raise SystemExit(
                f"--persistent {name}: generalising binder `(..) is not supported; "
                "state the obligation in the source instead"
            )
        if ch in "({":
            depth, j = 0, i
            while j < len(rest):
                if rest[j] in "([{":
                    depth += 1
                elif rest[j] in ")]}":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            groups.append((ch, rest[i + 1 : j]))
            i = j + 1
            continue
        j = i
        while j < len(rest) and not rest[j].isspace():
            j += 1
        groups.append(("", rest[i:j]))
        i = j

    binders: list[str] = []
    argv: list[str] = []
    implicit = False
    for opener, inner in groups:
        implicit = implicit or opener == "{"
        binders.append(f"({inner})")
        argv += [t.lstrip("'") for t in inner.split(":")[0].split()]
    application = " ".join([("@" if implicit else "") + name, *argv])
    return " ".join(binders), application


def add_persistence_obligation(source: str, name: str) -> str:
    """Insert `Lemma <name>_persistent .. : Persistent (<name> ..)` after `<name>`.

    A design rung that stubs the client-facing predicate has a degenerate solution:
    define it as *exclusive* ownership of the location rather than as an invariant.
    Every specification still goes through -- with no interference, the CmpXchg cannot
    fail, so the prophecy and the helping protocol that the development exists to
    demonstrate are never needed, and `Print Assumptions` is clean.  Requiring the
    predicate to be persistent is what forces it to be shared, and sharing is what
    brings the hard case back.

    The obligation is inserted **proved** (`apply _.`) and is *not* held out. Holding
    it out would be worse than useless: the stub makes it trivial (`True` is
    persistent), so it would sit there as an `Admitted.` proving nothing, inert until
    some worker bothered to discharge it. Left proved, every compile enforces it --
    including the design-compile check -- so a design that makes the predicate
    exclusive is rejected at adoption time, before a single worker is dispatched. It
    is registered as a frozen *result* so no design may restate it away.
    """
    block = next((b for b in parse_blocks(source) if b.name == name), None)
    if block is None:
        raise SystemExit(f"--persistent {name}: no such declaration")
    head_ann = _split_definition(block.statement)
    if head_ann is None:
        raise SystemExit(f"--persistent {name}: not a definition with a body")
    head, _ = head_ann
    binders, argv = _binder_signature(head, name)
    line_start = source.rfind("\n", 0, block.statement_start) + 1
    indent = source[line_start : block.statement_start]
    if indent.strip():
        indent = ""
    sep = " " if binders else ""
    lemma = (
        f"\n\n{indent}Lemma {name}_persistent{sep}{binders} : "
        f"Persistent ({argv}).\n{indent}Proof. apply _. Qed."
    )
    end = block.statement_end
    return source[:end] + lemma + source[end:]


def hold_out(source: str, names: list[str]) -> tuple[str, list[HeldOut]]:
    """Replace the named proofs with `Admitted.`, keeping their statements exactly."""
    blocks = {b.name: b for b in parse_blocks(source) if b.has_proof}
    missing = [n for n in names if n not in blocks]
    if missing:
        raise SystemExit(f"no proof block named: {', '.join(missing)}")
    held: list[HeldOut] = []
    edits: list[tuple[int, int, str]] = []
    for name in names:
        b = blocks[name]
        assert b.body_start is not None and b.ender_end is not None
        body = b.body(source)
        held.append(
            HeldOut(
                name=name,
                anonymised=name,
                statement=b.statement,
                reference_body=body,
                reference_sha256=hashlib.sha256(body.encode()).hexdigest(),
                lines=len(body.strip().splitlines()),
                tactics=len(b.tactics()),
            )
        )
        edits.append((b.body_start, b.ender_end, "\nAdmitted."))
    out: list[str] = []
    cursor = 0
    for start, end, text in sorted(edits):
        out.append(source[cursor:start])
        out.append(text)
        cursor = end
    out.append(source[cursor:])
    return "".join(out), held


# ------------------------------------------------------------------ verification

def compiles(text: str, name: str, project: str, extra_root: Path | None = None) -> tuple[bool, str]:
    coqc = coqc_binary()
    if coqc is None:
        return False, "no coqc on PATH"
    work = Path(tempfile.mkdtemp(prefix="pcp-bench-"))
    try:
        (work / f"{name}.v").write_text(text, encoding="utf-8")
        (work / "_CoqProject").write_text(project, encoding="utf-8")
        proc = subprocess.run(
            [coqc, "-Q", str(work), "bench", "-w", "-notation-overridden", f"{name}.v"],
            cwd=str(work),
            capture_output=True,
            text=True,
            timeout=7200,
        )
        return proc.returncode == 0, (proc.stdout + proc.stderr)[-3000:]
    finally:
        shutil.rmtree(work, ignore_errors=True)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("source", type=Path)
    ap.add_argument("--holdout", nargs="+", required=True)
    ap.add_argument(
        "--stub-definition", action="append", default=[], metavar="NAME[=TYPE]",
        help="blank a definition's body to `True`, so the worker must invent it. "
        "For a CSL development this is where the difficulty lives: "
        "--stub-definition value --stub-definition rwcas_inv",
    )
    ap.add_argument("--out", type=Path, required=True, help="corpus directory (goes in the repo)")
    ap.add_argument("--reference", type=Path, required=True,
                    help="where the answer key goes -- must NOT be inside --out")
    ap.add_argument("--name", default=None, help="module name in the corpus (default: derived)")
    ap.add_argument("--salt", default="pcp", help="anonymisation salt; change it to re-anonymise")
    ap.add_argument("--no-anonymise", action="store_true")
    ap.add_argument("--keep-comments", action="store_true")
    ap.add_argument(
        "--mutable", action="append", default=[], metavar="NAME",
        help="declare a definition the design process may rewrite. Defaults to the "
        "stubbed ones. Enforced deterministically: anything else that changes is a "
        "contract violation, whoever changed it.",
    )
    ap.add_argument(
        "--no-additions", action="store_true",
        help="forbid introducing new declarations (ghost state, helper definitions)",
    )
    ap.add_argument(
        "--strip-comments", action="store_true",
        help="remove every comment, independently of anonymisation. The upstream "
        "header for a CSL development typically narrates the whole proof strategy; "
        "leaving it in hands over the design in prose after removing it in code.",
    )
    ap.add_argument(
        "--persistent", action="append", default=[], metavar="NAME",
        help="require NAME to be persistent, as a held-out obligation. Without it a "
        "design rung has a degenerate solution: define the client-facing predicate as "
        "exclusive ownership, and every spec goes through with no interference and so "
        "no need for the protocol the development demonstrates.",
    )
    ap.add_argument("--skip-verify", action="store_true", help="do not compile-check the result")
    ap.add_argument(
        "--drop", action="append", default=[], metavar="NAME",
        help="delete a declaration outright, with any comment introducing it. For "
        "design a worker must invent, deletion is honest where stubbing still hints.",
    )
    ap.add_argument(
        "--imports", action="append", default=[], metavar="LINE",
        help="replace every Require line with these. The default imports name the "
        "ghost-state plan (token, ghost_var, auth); a design benchmark must not.",
    )
    ap.add_argument(
        "--class-fields", action="append", default=[], metavar="NAME=F1;F2",
        help="reduce a typeclass to the listed fields, e.g. --class-fields "
        "'rwcasG=heapGS Σ'",
    )
    ap.add_argument(
        "--role", action="append", default=[], metavar="NAME=DESCRIPTION",
        help="annotate a given definition for the design brief, e.g. "
        "--role rwcas_inv='the main invariant' --role value='the abstract state'",
    )
    ap.add_argument(
        "--design-notes", choices=["none", "glossary", "full"], default="full",
        help="what goes in DESIGN.md: nothing, the glossary of given definitions, or "
        "the glossary plus the original prose. The design is meant to be *given* -- "
        "anonymisation is about the search key, not about withholding the design.",
    )
    args = ap.parse_args()

    if args.reference.resolve() == args.out.resolve() or args.out.resolve() in args.reference.resolve().parents:
        raise SystemExit("--reference must not live inside --out: that is the answer key")

    source = args.source.read_text(encoding="utf-8")
    bench = Benchmark(source=str(args.source), file="", anonymised=not args.no_anonymise)

    # Order matters.  Signatures must be read while the original imports and bodies
    # are still present -- blanking `value` destroys the very inference that told us
    # `γ : gname`, and scrubbing `ghost_var` out of the imports destroys the compile
    # that would have told us anything at all.
    guards: list[str] = []
    for target in args.persistent:
        source = add_persistence_obligation(source, target)
        guards.append(f"{target}_persistent")
    if args.persistent and not args.skip_verify:
        # The guard must be satisfiable by the design it is guarding, or the rung
        # ships an impossible goal.  The reference is the only thing that can say so.
        ok, output = compiles(source, args.name or "Reference", "-Q . bench\n")
        if not ok:
            print("the persistence obligation is not provable by the reference "
                  "design:\n" + output, file=sys.stderr)
            return 1
        print(f"verified: reference proves {len(args.persistent)} persistence obligation(s)")

    stubbed, held = hold_out(source, args.holdout)

    stub_names = [e.split("=")[0].strip() for e in args.stub_definition]
    types: dict[str, str] = {}
    if stub_names:
        types = definition_types(stubbed, stub_names)
        if types:
            print("resolved signatures: " + "; ".join(f"{k} : {v}" for k, v in types.items()),
                  file=sys.stderr)

    dropped: list[str] = []
    if args.drop:
        stubbed, dropped = drop_declarations(stubbed, args.drop)
    for spec in args.class_fields:
        cname, _, fields = spec.partition("=")
        stubbed = minimize_class(stubbed, cname.strip(), fields.split(";"))
    if args.imports:
        stubbed = set_imports(stubbed, args.imports)

    stub_defs: list[StubbedDefinition] = []
    if args.stub_definition:
        stubbed, stub_defs = stub_definitions(stubbed, args.stub_definition, types=types)

    if args.strip_comments:
        stubbed = strip_comments(stubbed)
        stubbed = re.sub(r"[ \t]+\n", "\n", stubbed)
        stubbed = re.sub(r"\n{3,}", "\n\n", stubbed)
    if not args.no_anonymise:
        stubbed, mapping = anonymise(stubbed, salt=args.salt, drop_comments=not args.keep_comments)
        bench.rename_map = mapping
        for h in held:
            h.anonymised = mapping.get(h.name, h.name)
            h.statement = _rename_text(h.statement, mapping)
    bench.holdout = held
    for sd in stub_defs:
        sd.anonymised = bench.rename_map.get(sd.name, sd.name)
    bench.stubbed = stub_defs
    bench.dropped = dropped
    bench.mutable = sorted({*(args.mutable or []), *(sd.anonymised for sd in stub_defs)})
    bench.results = sorted(bench.rename_map.get(g, g) for g in guards)
    bench.allow_additions = not args.no_additions

    name = args.name or _module_name(args.source, args.salt, not args.no_anonymise)
    bench.file = f"{name}.v"
    project = "-Q . bench\n"

    if not args.skip_verify:
        ok, output = compiles(stubbed, name, project)
        if not ok:
            print("the held-out development does not compile:\n" + output, file=sys.stderr)
            return 1
        print(f"verified: {name}.v compiles with {len(held)} proof(s) held out")

    roles = dict(r.split("=", 1) for r in args.role if "=" in r)
    mutable = sorted({*(args.mutable or []), *(sd.anonymised for sd in stub_defs)})
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / f"{name}.v").write_text(stubbed, encoding="utf-8")
    (args.out / "design.json").write_text(
        json.dumps(
            {
                "mutable": mutable,
                # The held-out specifications are results already; these are the
                # extra ones that are given proved and must stay that way.
                "results": bench.results,
                "allow_additions": not args.no_additions,
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    if args.design_notes != "none":
        (args.out / "DESIGN.md").write_text(
            render_design(source, stubbed, bench, roles, prose=args.design_notes == "full"),
            encoding="utf-8",
        )
        bench.notes.append("DESIGN.md carries the given design; it is included in every worker packet")
    (args.out / "_CoqProject").write_text(project, encoding="utf-8")
    (args.out / "bench.json").write_text(json.dumps(bench.to_json(), indent=2), encoding="utf-8")

    args.reference.mkdir(parents=True, exist_ok=True)
    (args.reference / "reference.json").write_text(
        json.dumps({"source": str(args.source), "file": bench.file,
                    "holdout": [asdict(h) for h in held],
                    "dropped": dropped,
                    "rename_map": bench.rename_map}, indent=2),
        encoding="utf-8",
    )
    (args.reference / f"{name}_reference.v").write_text(
        _rename_text(source, bench.rename_map) if bench.rename_map else source, encoding="utf-8"
    )
    print(f"corpus     {args.out}/{name}.v")
    print(f"answer key {args.reference}/  (keep this out of every worker sandbox)")
    for h in held:
        print(f"  held out {h.anonymised:<28} {h.lines:>4} lines, {h.tactics:>3} tactics")
    for sd in stub_defs:
        print(f"  stubbed  {sd.anonymised:<28} definition body blanked to True")
    for g in bench.results:
        print(f"  guard    {g:<28} given proved; frozen, enforced by every compile")
    for name in dropped:
        print(f"  dropped  {name:<28} removed entirely")
    print(f"  contract may change: {', '.join(mutable) or 'nothing'}"
          f"; additions {'allowed' if not args.no_additions else 'forbidden'}")
    return 0


def render_design(original: str, stubbed: str, bench: "Benchmark", roles: dict, *, prose: bool) -> str:
    """The design brief handed to every worker.

    The point of anonymisation is to remove the *search key*, not to withhold the
    design: the invariant, the abstract predicate and the ghost-state plan are given,
    exactly as PLAN.md 9.3 says they should be -- the sketch is frozen first and the
    tactic work is what gets dispatched.  What the worker does not get is a name it
    could look up, nor (with the sandbox) any way to look one up.
    """
    lines = [f"# Design brief: `{bench.file}`", ""]
    if bench.stubbed or bench.dropped:
        blanked = ", ".join(f"`{d.anonymised}`" for d in bench.stubbed)
        lines.append(
            "You are given **the implementation and the specifications, and nothing "
            "else**. The predicates the specifications are stated in terms of"
            + (f" ({blanked})" if blanked else "")
            + " are present but **empty** -- defined as `True`, which makes the "
            "specifications unprovable as they stand."
        )
        lines.append("")
        lines.append(
            "Designing them is the task. Decide what the client owns, what invariant "
            "protects the cell, and what ghost state connects the two, then fill the "
            "definitions in and prove the specifications against them. You may add "
            "definitions, resource algebras, typeclass fields, imports and helper "
            "lemmas. You may **not** change the program or any specification: those "
            "are the theorem."
        )
    else:
        lines.append(
            "This development's design is **given**: the implementation, the invariants, "
            "the ghost state and the helper lemmas are all present and correct. What is "
            "held out is the tactic work for the specifications below."
        )
    lines.append("")
    lines.append("## What you must prove")
    lines.append("")
    for h in bench.holdout:
        lines.append(f"### `{h.anonymised}`")
        lines.append("")
        lines.append("```coq")
        lines.append(h.statement.strip())
        lines.append("```")
        lines.append("")

    lines.append("## Given definitions")
    lines.append("")
    blanked_names = {d.anonymised for d in bench.stubbed}
    if blanked_names:
        lines.append(
            "The program is frozen. The predicates marked **(blank)** are yours to "
            "define; everything else is read-only."
        )
    else:
        lines.append("These are frozen. Read them; do not change them.")
    lines.append("")
    inverse = {v: k for k, v in bench.rename_map.items()}
    for block in parse_blocks(stubbed):
        if block.head not in ("Definition", "Class", "Record", "Inductive", "Instance"):
            continue
        original_name = inverse.get(block.name, block.name)
        note = roles.get(original_name, "")
        mark = " **(blank -- yours to define)**" if block.name in blanked_names else ""
        lines.append(f"- `{block.name}`{mark}" + (f" -- {note}" if note else ""))

    given = [
        b.name for b in parse_blocks(stubbed)
        if b.head in ("Lemma", "Theorem") and b.has_proof and b.ender == "Qed"
    ]
    if given:
        lines.append("")
        lines.append("## Given lemmas (already proved -- use them)")
        lines.append("")
        for n in given:
            original_name = inverse.get(n, n)
            lines.append(f"- `{n}`" + (f" -- {roles[original_name]}" if original_name in roles else ""))

    if prose:
        notes = [text.strip("(*) ").strip() for _s, _e, text in iter_comments(original)]
        # Rename only inside Coq's `[...]` doc spans. Applying the map to running
        # prose turns "the failing write" into "the failing c2" -- unreadable, and
        # it withholds design rather than withholding a search key.
        notes = [_rename_bracketed(n, bench.rename_map) for n in notes if len(n) > 150]
        if notes:
            lines.append("")
            lines.append("## Design notes from the author")
            lines.append("")
            for n in notes[:4]:
                for line in n.splitlines():
                    lines.append("> " + line.strip().lstrip("*").strip())
                lines.append("")
    return "\n".join(lines) + "\n"


def _rename_bracketed(text: str, mapping: dict[str, str]) -> str:
    return re.sub(
        r"\[([^\]]*)\]",
        lambda m: "[" + _rename_text(m.group(1), mapping) + "]",
        text,
    )


def _rename_text(text: str, mapping: dict[str, str]) -> str:
    for name in sorted(mapping, key=len, reverse=True):
        text = re.sub(rf"\b{re.escape(name)}\b", mapping[name], text)
    return text


def _module_name(source: Path, salt: str, anonymised: bool) -> str:
    stem = source.stem
    if not anonymised:
        return stem[0].upper() + stem[1:]
    return "M" + hashlib.blake2b(f"{salt}:{stem}".encode(), digest_size=3).hexdigest()


if __name__ == "__main__":
    raise SystemExit(main())
