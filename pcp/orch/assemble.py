"""Two-zone assembly: frozen spec + worker patch (PLAN.md 8.3, 8.7).

The freeze is enforced **by construction, not by trust**.  A worker never edits a
file; it returns a *proof body*, and assembly rebuilds the development from the
frozen source plus that body.  Anything the worker did to a statement, a definition,
or another node is discarded because there is nowhere for it to go -- not detected by
review, which a model could talk its way past.

The one thing assembly must get right is span arithmetic, which is why
``pcp.core.vernac`` is a lexer with byte offsets rather than a regex.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path

from pcp.core.vernac import ProofBlock, parse_blocks, split_sentences

#: Iris itself sets this, and the gate requires it: without a fixed `Proof using`
#: discipline a `Qed`'d constant's discharged arity can differ from the admitted
#: stub's, and dependents compiled against the stub break (PLAN.md 8.7 item 3).
PROOF_USING_DIRECTIVE = 'Set Default Proof Using "Type".'

_SECTION_OPEN = re.compile(r"^\s*(?:Section|Module(?!\s+Type)|Module\s+Type)\s+([A-Za-z_][\w']*)")
_SECTION_CLOSE = re.compile(r"^\s*End\s+([A-Za-z_][\w']*)\s*\.")


@dataclass
class NodeSpec:
    """One obligation as it appears in an assembled file."""

    name: str
    statement: str
    #: ``None`` means "admit it" -- a type-checked stub, which is exactly what makes
    #: the whole frontier dispatchable in parallel (PLAN.md 0, Claim 1).
    body: str | None = None
    #: Non-mockable obligations (``Defined``, definitions dependents must compute
    #: with) cannot be stubbed by an admit; they genuinely block.
    mockable: bool = True
    transparent: bool = False

    def render(self) -> str:
        statement = self.statement.strip()
        if self.body is None:
            if not self.mockable:
                raise ValueError(f"{self.name} is non-mockable and has no body; it cannot be stubbed")
            return f"{statement}\nProof.\nAdmitted.\n"
        ender = "Defined." if self.transparent else "Qed."
        body = self.body.strip()
        return f"{statement}\nProof.\n{body}\n{ender}\n"


@dataclass
class Assembly:
    text: str
    #: Byte offset of each node's proof body in ``text`` -- for error mapping.
    spans: dict[str, tuple[int, int]] = field(default_factory=dict)
    open_sections: list[str] = field(default_factory=list)
    #: Names whose proofs were replaced by ``Admitted.`` for speed.  They are
    #: legitimate assumptions for this check and the gate must allow them.
    stubbed: list[str] = field(default_factory=list)


class Development:
    """A source file plus the obligations layered onto it."""

    def __init__(self, path: str | Path, source: str | None = None) -> None:
        self.path = Path(path)
        self.source = source if source is not None else self.path.read_text(encoding="utf-8")
        self.blocks = parse_blocks(self.source)
        self.sentences = split_sentences(self.source)

    # -- lookup ------------------------------------------------------------
    def block(self, name: str) -> ProofBlock | None:
        for b in self.blocks:
            if b.name == name:
                return b
        return None

    def preamble_end(self, name: str) -> int:
        """Offset just before ``name``'s statement -- the insertion point for children."""
        block = self.block(name)
        if block is None:
            raise KeyError(f"{self.path}: no declaration named {name!r}")
        return block.statement_start

    def open_sections_at(self, offset: int) -> list[str]:
        """Sections/modules still open at ``offset``, innermost last."""
        stack: list[str] = []
        for sent in self.sentences:
            if sent.start >= offset:
                break
            m = _SECTION_OPEN.match(sent.code)
            if m:
                stack.append(m.group(1))
                continue
            m = _SECTION_CLOSE.match(sent.code)
            if m and stack and stack[-1] == m.group(1):
                stack.pop()
        return stack

    # -- assembly ----------------------------------------------------------
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

        ``anchor`` is the declaration *in the file* that fixes the insertion point and
        the preamble -- in the daily loop, the user's root lemma.  ``nodes`` are the
        obligations inserted before it, in order; each carries its proved body or is
        rendered as an ``Admitted`` stub.  ``anchor_body`` is the body for the anchor
        itself, ``None`` to admit it.

        Children come from the plan and do not exist in the file, so they can only be
        addressed this way: the anchor is what the file knows about.

        ``truncate=True`` cuts the file after the anchor and closes any sections that
        were still open -- the fast per-node check.  ``truncate=False`` keeps the rest
        of the file, which is what the integration gate compiles.

        ``stub_prefix=True`` additionally replaces every *other* proof in the file with
        ``Admitted.``  On a real development this is the difference between a check
        that takes minutes and one that takes seconds: these files are slow because of
        proof automation, and none of that automation has anything to do with whether
        *this* node's proof works.  It is sound for a per-node check by the same
        argument as Claim 1 -- a proof against a type-checked stub is exactly the work
        that survives -- and it is never used for integration, where every proof is
        real.  Transparent (``Defined``) proofs are left alone: dependents may need to
        compute with them, which is what ``non-mockable`` means.
        """
        block = self.block(anchor)
        if block is None:
            raise KeyError(f"{self.path}: no declaration named {anchor!r}")

        preamble = self.source[: block.statement_start]
        stubbed: list[str] = []
        if stub_prefix:
            preamble, stubbed = stub_proof_bodies(preamble)
        if with_proof_using and PROOF_USING_DIRECTIVE not in preamble:
            preamble = _insert_proof_using(preamble)
        if extra_preamble:
            preamble = _insert_after_requires(preamble, extra_preamble)

        if not preamble.endswith("\n"):
            preamble += "\n"
        parts: list[str] = [preamble]
        spans: dict[str, tuple[int, int]] = {}
        cursor = len(preamble)

        def push(chunk: str, name: str | None = None) -> None:
            nonlocal cursor
            parts.append(chunk)
            if name is not None:
                spans[name] = (cursor, cursor + len(chunk))
            cursor += len(chunk)

        for spec in nodes:
            push(spec.render() + "\n", spec.name)

        anchor_spec = NodeSpec(
            name=anchor,
            statement=statement_override if statement_override is not None else block.statement,
            body=anchor_body,
            transparent=block.ender == "Defined",
        )
        push(anchor_spec.render(), anchor)

        open_sections = self.open_sections_at(block.statement_start)
        tail_stubbed: list[str] = []
        if truncate:
            for section in reversed(open_sections):
                push(f"End {section}.\n")
        else:
            tail = self.source[block.ender_end if block.ender_end else block.statement_end :]
            if stub_prefix:
                tail, tail_stubbed = stub_proof_bodies(tail)
            push(tail)
        if trailer:
            push("\n" + trailer.strip() + "\n")
        return Assembly(
            text="".join(parts),
            spans=spans,
            open_sections=open_sections,
            stubbed=stubbed + tail_stubbed,
        )


def _insert_proof_using(preamble: str) -> str:
    """Put the directive after the last `From ... Require ...`, before any content."""
    sentences = split_sentences(preamble)
    last_require = 0
    for sent in sentences:
        if re.match(r"^\s*(?:From\s+\S+\s+)?Require\b", sent.code) or re.match(r"^\s*Import\b", sent.code):
            last_require = sent.end
    return preamble[:last_require] + f"\n{PROOF_USING_DIRECTIVE}\n" + preamble[last_require:]


def _insert_after_requires(preamble: str, extra: str) -> str:
    sentences = split_sentences(preamble)
    last_require = 0
    for sent in sentences:
        if re.match(r"^\s*(?:From\s+\S+\s+)?Require\b", sent.code):
            last_require = sent.end
    return preamble[:last_require] + f"\n{extra.strip()}\n" + preamble[last_require:]


def parse_plan(source: str) -> list[NodeSpec]:
    """Read a plan file: a `.v` of child statements, admitted or proved.

    A plan is not prose -- it is Rocq.  That is the whole point of PLAN.md 8.2's
    no-gap rule: the plan's glue must eventually `Qed` against these children, and a
    plan you cannot compile is a plan you cannot check.
    """
    specs: list[NodeSpec] = []
    for block in parse_blocks(source):
        if block.head not in ("Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark", "Example"):
            continue
        body = block.body(source).strip() if block.has_proof else ""
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
    """Everything in a plan file before its first declaration -- extra Requires etc."""
    blocks = parse_blocks(source)
    if not blocks:
        return source
    return source[: blocks[0].statement_start]


# --------------------------------------------------------------- binder surgery

_BINDER_GROUP = re.compile(r"\(([^():]*?)\s*:\s*([^()]*(?:\([^()]*\)[^()]*)*)\)")


def statement_binders(statement: str) -> list[str]:
    """Names bound by explicit `(x y : T)` groups in a statement.

    Implicit `{x : T}` and typeclass `` `{...} `` binders are deliberately excluded:
    they are plumbing, not premises, and probing them produces noise.
    """
    head = statement.split(":=")[0]
    names: list[str] = []
    for group, _ty in _BINDER_GROUP.findall(head):
        names.extend(n for n in group.split() if n and n != "_")
    return names


def remove_binder(statement: str, name: str) -> str | None:
    """Return ``statement`` with binder ``name`` dropped, or ``None`` if not found.

    Used only by the unused-premise probe, which compiles the result in a scratch
    directory and throws it away.  Nothing this produces is ever integrated -- the
    freeze is about what reaches the development, and this never does.
    """
    for m in _BINDER_GROUP.finditer(statement):
        names = m.group(1).split()
        if name not in names:
            continue
        rest = [n for n in names if n != name]
        if rest:
            replacement = f"({' '.join(rest)} : {m.group(2)})"
        else:
            replacement = ""
        out = statement[: m.start()] + replacement + statement[m.end() :]
        return re.sub(r"[ \t]{2,}", " ", out)
    return None


def stub_proof_bodies(source: str, *, keep: set[str] | None = None) -> tuple[str, list[str]]:
    """Replace every ``Qed``-terminated proof body with ``Admitted.``

    Returns the rewritten source and the names that were stubbed, so the gate can
    admit them as expected assumptions rather than flagging them.

    ``Defined``/``Abort``/``Admitted`` blocks are left untouched: a transparent proof
    may be something a dependent computes with, and stubbing it changes meaning
    rather than just cost.
    """
    keep = keep or set()
    blocks = [
        b
        for b in parse_blocks(source)
        if b.has_proof and b.ender == "Qed" and b.name not in keep
        and b.body_start is not None and b.ender_end is not None
    ]
    if not blocks:
        return source, []
    out: list[str] = []
    cursor = 0
    stubbed: list[str] = []
    for b in sorted(blocks, key=lambda x: x.body_start or 0):
        assert b.body_start is not None and b.ender_end is not None
        out.append(source[cursor : b.body_start])
        out.append("\nAdmitted.")
        cursor = b.ender_end
        stubbed.append(b.name)
    out.append(source[cursor:])
    return "".join(out), stubbed
