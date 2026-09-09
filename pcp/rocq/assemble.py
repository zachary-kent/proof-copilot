"""Two-zone assembly: frozen spec + worker bodies (PLAN.md 8.3, 8.7).

A worker never edits a file; it returns a *proof body*, and assembly rebuilds the
development from the frozen source plus that body.  Anything the worker did to a
statement, a definition, or another node is discarded because there is nowhere for it
to go.  The one thing assembly must get right is span arithmetic, which is why it is
built on the lexer's byte offsets rather than on regexes.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

from pcp.errors import UsageError
from pcp.rocq.decls import ProofBlock, Scope, parse_blocks, scopes_at
from pcp.rocq.lexer import Sentence, first_word, split_sentences
from pcp.util.io import atomic_write_text, read_text

#: Iris itself sets this, and the gate requires it: without a fixed `Proof using`
#: discipline a `Qed`'d constant's discharged arity can differ from the admitted stub's.
PROOF_USING_DIRECTIVE = 'Set Default Proof Using "Type".'

PLAN_HEADS = ("Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark", "Property", "Example")


@dataclass(frozen=True)
class NodeSpec:
    """One obligation as it appears in an assembled file."""

    name: str
    statement: str
    #: ``None`` means "admit it" -- a type-checked stub (PLAN.md Claim 1).
    body: str | None = None
    #: Non-mockable obligations cannot be stubbed; they genuinely block.
    mockable: bool = True
    transparent: bool = False
    #: The sentence that opens the script.  The anchor keeps the frozen file's own
    #: (``Proof using Hn.``): under ``Set Default Proof Using "Type"`` a proof that
    #: needs a section hypothesis outside its type is valid only with that clause, and
    #: re-emitting a bare ``Proof.`` rejected every such proof (review finding).
    opener: str = "Proof."

    @property
    def proved(self) -> bool:
        return self.body is not None

    def render(self) -> str:
        statement = self.statement.strip()
        opener = self.opener.strip() or "Proof."
        if self.body is None:
            if not self.mockable:
                raise UsageError(f"{self.name} is non-mockable and has no body; it cannot be stubbed")
            return f"{statement}\n{opener}\nAdmitted.\n"
        ender = "Defined." if self.transparent else "Qed."
        return f"{statement}\n{opener}\n{self.body.strip()}\n{ender}\n"

    def with_body(self, body: str | None) -> NodeSpec:
        return NodeSpec(self.name, self.statement, body, self.mockable, self.transparent, self.opener)


@dataclass
class Assembly:
    text: str
    #: Byte span of each rendered node's *body* in ``text``, for error mapping.
    spans: dict[str, tuple[int, int]] = field(default_factory=dict)
    #: Scopes that were open at the anchor (outermost first).
    open_scopes: list[Scope] = field(default_factory=list)
    #: Module-qualified names whose proofs were replaced by ``Admitted.`` for speed.
    stubbed: list[str] = field(default_factory=list)
    #: Module path (outermost first) that qualifies names declared at the anchor.
    modules: tuple[str, ...] = ()

    def qualified(self, name: str) -> str:
        return ".".join((*self.modules, name))


class Development:
    """A source file plus the obligations layered onto it."""

    def __init__(self, path: str | Path, source: str | None = None) -> None:
        self.path = Path(path)
        self.source = source if source is not None else read_text(self.path)
        self.sentences: list[Sentence] = split_sentences(self.source)
        self.blocks: list[ProofBlock] = parse_blocks(self.source, sentences=self.sentences)

    @property
    def root(self) -> Path:
        return self.path.parent

    def block(self, name: str) -> ProofBlock | None:
        for b in self.blocks:
            if b.name == name:
                return b
        return None

    def require_block(self, name: str) -> ProofBlock:
        block = self.block(name)
        if block is None:
            raise UsageError(f"{self.path}: no declaration named {name!r}")
        return block

    def names(self) -> list[str]:
        return [b.name for b in self.blocks if b.name]

    def scopes_at(self, offset: int) -> list[Scope]:
        return scopes_at(self.sentences, offset)

    def assemble(
        self,
        anchor: str,
        nodes: list[NodeSpec],
        *,
        anchor_body: str | None = None,
        truncate: bool = True,
        with_proof_using: bool = True,
        extra_preamble: str = "",
        trailer: str = "",
        statement_override: str | None = None,
        stub_prefix: bool = False,
    ) -> Assembly:
        """Rebuild the development from frozen source plus proof bodies.

        ``anchor`` is the declaration *in the file* that fixes the insertion point --
        in the daily loop, the user's root lemma.  ``nodes`` are inserted before it, in
        order, each proved or stubbed.  ``anchor_body`` is the anchor's own body,
        ``None`` to admit it (or to leave a non-proof anchor as it is).

        ``truncate`` cuts the file after the anchor and closes the open scopes -- the
        fast per-node check.  ``stub_prefix`` additionally replaces every *other* proof
        with ``Admitted.``: sound for a per-node check by Claim 1, never used for
        integration.
        """
        block = self.require_block(anchor)
        preamble = self.source[: block.statement_start]
        stubbed: list[str] = []
        if stub_prefix:
            preamble, stubbed = stub_proof_bodies(preamble)
        if with_proof_using and not has_proof_using_directive(preamble):
            preamble = insert_preamble(preamble, PROOF_USING_DIRECTIVE)
        if extra_preamble.strip():
            preamble = insert_preamble(preamble, extra_preamble.strip())
        if not preamble.endswith("\n"):
            preamble += "\n"

        parts: list[str] = [preamble]
        spans: dict[str, tuple[int, int]] = {}
        cursor = len(preamble)

        def push(chunk: str, name: str | None = None, body_offset: tuple[int, int] | None = None) -> None:
            nonlocal cursor
            parts.append(chunk)
            if name is not None and body_offset is not None:
                spans[name] = (cursor + body_offset[0], cursor + body_offset[1])
            cursor += len(chunk)

        for spec in nodes:
            rendered = spec.render() + "\n"
            push(rendered, spec.name, _body_span(rendered))

        statement = statement_override if statement_override is not None else block.statement
        if block.kind == "none" and anchor_body is None and statement_override is None:
            # A definition-style anchor: keep it exactly as written.
            push(self.source[block.statement_start : block.end].rstrip() + "\n")
        else:
            anchor_spec = NodeSpec(
                anchor, statement, anchor_body, transparent=block.ender == "Defined",
                opener=block.proof_opener or "Proof.",
            )
            rendered = anchor_spec.render()
            push(rendered, anchor, _body_span(rendered))

        open_scopes = self.scopes_at(block.statement_start)
        tail_stubbed: list[str] = []
        if truncate:
            for scope in reversed(open_scopes):
                push(f"End {scope.name}.\n")
        else:
            tail = self.source[block.end :]
            if stub_prefix:
                tail, tail_stubbed = stub_proof_bodies(tail)
            push(tail)
        if trailer.strip():
            push("\n" + trailer.strip() + "\n")
        return Assembly(
            text="".join(parts),
            spans=spans,
            open_scopes=open_scopes,
            stubbed=stubbed + tail_stubbed,
            modules=tuple(s.name for s in open_scopes if s.kind == "module"),
        )


def _body_span(rendered: str) -> tuple[int, int] | None:
    blocks = parse_blocks(rendered)
    if not blocks or blocks[0].body_start is None or blocks[0].body_end is None:
        return None
    return blocks[0].body_start, blocks[0].body_end


# ------------------------------------------------------------------ preamble edits

_PREAMBLE_WORDS = ("Require", "From", "Import", "Export")


def insert_preamble(source: str, extra: str) -> str:
    """Insert ``extra`` after the last top-level ``Require``/``Import`` line.

    "Top-level" means before any ``Section``/``Module`` opens: a ``Require`` is not legal
    inside a section, so the insertion point is never allowed to drift there.
    """
    sentences = split_sentences(source)
    last = 0
    for sent in sentences:
        fw = first_word(sent.code)
        if fw in ("Section", "Module"):
            break
        if fw in _PREAMBLE_WORDS:
            last = sent.end
    if last == 0 and sentences:
        # No Require at all: put it before the first sentence, after leading comments.
        first = sentences[0]
        last = first.code_start
        return source[:last] + extra.strip() + "\n" + source[last:]
    return source[:last] + "\n" + extra.strip() + "\n" + source[last:]


def has_proof_using_directive(source: str) -> bool:
    """Whether a ``Set Default Proof Using`` *sentence* is present.

    A substring test was fooled both ways: a commented-out directive suppressed the
    insertion, and the gate's identical substring check then passed vacuously.
    """
    for sent in split_sentences(source):
        code = sent.code
        if first_word(code) == "Set" and " ".join(code.split()).startswith("Set Default Proof Using"):
            return True
    return False


def ensure_proof_using(source: str) -> str:
    return source if has_proof_using_directive(source) else insert_preamble(source, PROOF_USING_DIRECTIVE)


# ------------------------------------------------------------------- stubbing

def stub_proof_bodies(source: str, *, keep: set[str] | None = None) -> tuple[str, list[str]]:
    """Replace every ``Qed``-terminated proof body with ``Admitted.``

    Returns the rewritten source and the **module-qualified** names that were stubbed,
    so the gate can admit them as expected assumptions.  ``Defined``/``Abort``/
    ``Admitted`` blocks and anonymous blocks are left untouched: a transparent proof may
    be computed with, and an anonymous one cannot be whitelisted by name.
    """
    keep = keep or set()
    blocks = [
        b
        for b in parse_blocks(source)
        if b.kind == "script" and b.ender == "Qed" and b.name and b.name not in keep
        and b.body_start is not None and b.ender_start is not None
    ]
    if not blocks:
        return source, []
    out: list[str] = []
    cursor = 0
    stubbed: list[str] = []
    for b in blocks:
        assert b.body_start is not None and b.ender_start is not None
        out.append(source[cursor : b.body_start])
        out.append("\nAdmitted.")
        cursor = b.ender_end if b.ender_end is not None else b.ender_start
        stubbed.append(b.qualified_name or b.name or "")
    out.append(source[cursor:])
    return "".join(out), stubbed


def stubbed_twin(path: str | Path, *, keep: str) -> Path:
    """A statements-only twin of ``path`` beside it (``<stem>__pcpfast.v``).

    Same directory so the project's ``-Q``/``-R`` flags apply unchanged; a distinct name
    so nothing ``Require``s it.  Sound for the same reason as ``stub_prefix``.
    """
    src = Path(path)
    stubbed, _ = stub_proof_bodies(read_text(src), keep={keep})
    twin = src.with_name(f"{src.stem}__pcpfast.v")
    if not twin.exists() or read_text(twin) != stubbed:
        atomic_write_text(twin, stubbed)
    return twin


# ---------------------------------------------------------------------- plans

def parse_plan(source: str) -> list[NodeSpec]:
    """Read a plan file: a ``.v`` of child statements, admitted or proved.

    Anything that is not a named lemma-like statement is refused rather than
    dropped: a ``Definition`` a plan silently lost left every child failing to
    elaborate with no hint why (review finding).
    """
    specs: list[NodeSpec] = []
    for block in parse_blocks(source):
        if block.head not in PLAN_HEADS or not block.name:
            what = f"{block.head} {block.name}" if block.name else f"an anonymous {block.head}"
            raise UsageError(
                f"plan: `{what}` is not an obligation; a plan holds lemma statements only "
                "(definitions and instances belong in the development)"
            )
        body = block.body(source).strip() if block.kind == "script" else ""
        proved = bool(body) and block.ender in ("Qed", "Defined")
        specs.append(
            NodeSpec(
                name=block.name,
                statement=block.statement.strip(),
                body=body if proved else None,
                transparent=block.ender == "Defined",
            )
        )
    return specs


def plan_preamble(source: str) -> str:
    """Everything in a plan file before its first declaration -- extra Requires etc.

    A scope opener there (``Section``, ``Module``, ``Context``) is refused: the
    preamble is spliced into every assembly, and an unclosed section broke each
    of them far from the plan (review finding).
    """
    blocks = parse_blocks(source)
    text = source if not blocks else source[: blocks[0].statement_start]
    lines: list[str] = []
    for sent in split_sentences(text):
        code = sent.code.strip()
        if not code:
            continue  # only vernacular survives: comments would clutter the packet
        if first_word(code) in _PREAMBLE_FORBIDDEN:
            raise UsageError(f"plan preamble: `{' '.join(code.split())[:60]}` opens a scope; only Require/Import/option lines belong before the first statement")
        lines.append(code)
    return "\n".join(lines).strip()


_PREAMBLE_FORBIDDEN = frozenset({"Section", "Module", "Context", "End"})
