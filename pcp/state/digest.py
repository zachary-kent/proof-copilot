"""Content-addressed prop store, selection, head symbols and folding (PLAN.md 3.2, 5).

Three jobs, all pure functions over printed props:

* **Store props once.**  A 300-step proof stores a large invariant once and references
  it by hash; the trace header's ``props`` map is this store.
* **Select.**  The ``select`` grammar of ``pcp state`` / ``proof_state`` (contract 1.8):
  id globs, classes, ``mentions:<tok>``, ``head:<sym>``.  A hypothesis named
  *explicitly* (glob / mentions / head) is reported as such so the renderer can let an
  explicit request beat every demotion (legacy bug: ``select="Hinv"`` under
  ``diff_only`` rendered nothing).
* **Fold.**  ``render_prop`` folds only in the modes whose point is folding.  ``full``
  never folds: the legacy renderer folded every 5-line prop in every mode, so a wrapped
  invariant could never be displayed at all.

Hashes are the full 128-bit ``props.prop_hash`` (the legacy 32-bit truncation merged
distinct props silently); ``fold_id`` shortens them for display only.
"""

from __future__ import annotations

import re
from collections.abc import Iterable, Iterator, Mapping
from dataclasses import dataclass
from fnmatch import fnmatchcase
from typing import Literal

from pcp.state.ipm.model import IrisGoal
from pcp.state.ipm.skeleton import parse_skeleton
from pcp.state.props import prop_hash

Mode = Literal["full", "folded", "summary", "hash-only"]
MODES: tuple[str, ...] = ("full", "folded", "summary", "hash-only")

#: Chars per token.  Deterministic and dependency-free; stability matters more than accuracy.
CHARS_PER_TOKEN = 4


# ------------------------------------------------------------------------- store


class PropStore:
    """Hash -> first printed spelling.  Deduplicating, append-only, JSON-shaped."""

    def __init__(self, props: Mapping[str, str] | None = None) -> None:
        self._by_hash: dict[str, str] = dict(props or {})

    def put(self, prop: str, *, prefix: str = "h") -> str:
        h = prop_hash(prop, prefix=prefix)
        # First spelling wins: normalisation is lossy (evar names, wrapping) and a stable
        # spelling keeps diffs readable.
        self._by_hash.setdefault(h, prop)
        return h

    def get(self, h: str) -> str | None:
        return self._by_hash.get(h)

    def __contains__(self, h: object) -> bool:
        return h in self._by_hash

    def __len__(self) -> int:
        return len(self._by_hash)

    def items(self) -> Iterator[tuple[str, str]]:
        return iter(self._by_hash.items())

    def update(self, source: Mapping[str, str] | PropStore | IrisGoal | Iterable[IrisGoal]) -> None:
        """Intern everything in ``source``: a hash map, another store, or goals.

        Interning every prop of every goal of every step is what makes the trace
        header's ``props`` cover every hash that appears in the steps.
        """
        if isinstance(source, PropStore):
            for h, p in source.items():
                self._by_hash.setdefault(h, p)
        elif isinstance(source, Mapping):
            for h, p in source.items():
                self._by_hash.setdefault(str(h), str(p))
        elif isinstance(source, IrisGoal):
            self._intern_goal(source)
        else:
            for g in source:
                self._intern_goal(g)

    def _intern_goal(self, goal: IrisGoal) -> None:
        for h in goal.pure:
            self._by_hash.setdefault(h.hash, h.prop)
        for h in goal.intuitionistic + goal.spatial:
            self._by_hash.setdefault(h.hash, h.prop)
        if goal.goal:
            self._by_hash.setdefault(goal.goal_hash or prop_hash(goal.goal, prefix="g"), goal.goal)

    def to_json(self) -> dict[str, str]:
        return dict(self._by_hash)

    @classmethod
    def from_json(cls, data: Mapping[str, str] | None) -> PropStore:
        return cls(data or {})


# ------------------------------------------------------------------------ tokens


def estimate_tokens(text: str) -> int:
    """``len / 4``, at least 1 for non-empty text."""
    if not text:
        return 0
    return max(1, round(len(text) / CHARS_PER_TOKEN))


def fold_id(h: str) -> str:
    """Short display id of a hash: the first 8 hex chars after the prefix."""
    return h.rsplit(":", maxsplit=1)[-1][:8]


# ----------------------------------------------------------------------- folding


@dataclass(frozen=True)
class FoldedProp:
    hash: str
    head: str
    lines: int

    def render(self) -> str:
        return f"⟨fold:{fold_id(self.hash)} · {self.head} · {self.lines} lines⟩"


def head_summary(prop: str, width: int = 40) -> str:
    """First line, truncated: enough to recognise a prop, not to read it."""
    first = prop.strip().splitlines()[0] if prop.strip() else ""
    if len(first) <= width:
        return first
    return first[: width - 1].rstrip() + "…"


def line_count(prop: str) -> int:
    return len(prop.splitlines()) or 1


def fold(prop: str, h: str) -> FoldedProp:
    return FoldedProp(hash=h, head=head_summary(prop), lines=line_count(prop))


def render_prop(prop: str, mode: str = "full", *, fold_over_lines: int = 4, hash: str = "") -> str:
    """Render one prop under ``mode``.

    ``full`` **never** folds -- it is the one mode whose contract is "show me the
    text".  ``folded`` auto-folds props longer than ``fold_over_lines``; ``summary`` and
    ``hash-only`` are strictly shorter.
    """
    h = hash or prop_hash(prop)
    if mode == "hash-only":
        return h
    if mode == "summary":
        return head_summary(prop)
    if mode == "folded" and line_count(prop) > fold_over_lines:
        return fold(prop, h).render()
    return prop


# ---------------------------------------------------------------------- selector

CLASS_SELECTORS: frozenset[str] = frozenset({"pure", "intuitionistic", "spatial", "all", "changed", "unchanged"})


@dataclass(frozen=True)
class Selector:
    """A parsed ``select`` expression (contract 1.8).

    Comma-separated union of: ``H*`` (id glob), a class name, ``mentions:<tok>``,
    ``head:<sym>``.  Empty selects everything.  Unknown tokens are id globs.
    """

    globs: tuple[str, ...] = ()
    classes: frozenset[str] = frozenset()
    mentions: tuple[str, ...] = ()
    heads: tuple[str, ...] = ()

    @classmethod
    def parse(cls, text: str | None) -> Selector:
        globs: list[str] = []
        classes: set[str] = set()
        mentions: list[str] = []
        heads: list[str] = []
        for raw in (text or "").split(","):
            token = raw.strip()
            if not token:
                continue
            if token.startswith("mentions:"):
                mentions.append(token[len("mentions:") :].strip())
            elif token.startswith("head:"):
                heads.append(token[len("head:") :].strip())
            elif token in CLASS_SELECTORS:
                classes.add(token)
            else:
                globs.append(token)
        if not (globs or classes or mentions or heads):
            classes.add("all")
        return cls(tuple(globs), frozenset(classes), tuple(mentions), tuple(heads))

    @property
    def everything(self) -> bool:
        return "all" in self.classes

    def explicit(self, ident: str, prop: str, *, names: Iterable[str] = ()) -> bool:
        """Named by id, by ``mentions:`` or by ``head:`` -- not merely by class."""
        idents = {ident, *names}
        if any(fnmatchcase(i, g) for i in idents for g in self.globs):
            return True
        if any(tok and tok in prop for tok in self.mentions):
            return True
        if self.heads:
            head = head_symbol(prop)
            if any(head == h or (h and head.startswith(h)) for h in self.heads):
                return True
        return False

    def matches(self, ident: str, prop: str, klass: str, *, names: Iterable[str] = (), changed: bool = False) -> bool:
        if self.everything or klass in self.classes:
            return True
        if "changed" in self.classes and changed:
            return True
        if "unchanged" in self.classes and not changed:
            return True
        return self.explicit(ident, prop, names=names)


# ------------------------------------------------------------------ head symbols

_CONNECTIVE_HEAD: dict[str, str] = {
    "sep": "∗", "and": "∧", "or": "∨", "wand": "-∗", "wand_iff": "∗-∗", "iff": "↔", "impl": "→",
    "exists": "∃", "forall": "∀", "pure": "⌜⌝", "credit": "£", "entails": "⊢", "equiv": "≡",
}
#: Modality nodes are looked through: ``▷ □ WP e {{ Φ }}`` heads ``WP``.
_MODALITY_KINDS: frozenset[str] = frozenset({
    "box", "intuitionistically", "persistently", "plainly", "later", "except0", "bupd", "fupd",
    "fupd_step", "affinely", "absorbingly", "pers", "affine", "absorb",
})
_MODALITY_PREFIXES = ("▷", "□", "■", "◇", "|==>", "<pers>", "<affine>", "<absorb>", "<obj>", "<subj>")
_LATER_POWER = re.compile(r"^\^\s*\d+")
#: Relational symbols that head an atom when they occur space-delimited at the top level.
_INFIX_HEADS = ("↦", "⤳", "≡", "≼", "≠", "=", "∈", "∉", "⊆", "⊑", "≤", "<", "≥", ">")
_IDENT = re.compile(r"[^\W\d][\w'.]*")


def _strip_modalities(text: str) -> str:
    text = text.strip()
    while True:
        if text.startswith("|={"):
            close = text.find("=>")
            if close < 0:
                return text
            text = text[close + 2 :].lstrip()
            continue
        for p in _MODALITY_PREFIXES:
            if text.startswith(p):
                text = text[len(p) :].lstrip()
                m = _LATER_POWER.match(text)
                if p == "▷" and m:
                    text = text[m.end() :].lstrip()
                break
        else:
            return text


def _top_level_tokens(text: str) -> list[str]:
    out: list[str] = []
    depth = 0
    buf = ""
    for ch in text:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        if ch.isspace() and depth == 0:
            if buf:
                out.append(buf)
            buf = ""
        else:
            buf += ch
    if buf:
        out.append(buf)
    return out


def _atom_head(text: str) -> str:
    text = _strip_modalities(text)
    if not text:
        return ""
    if text.startswith("⌜"):
        return "⌜⌝"
    tokens = _top_level_tokens(text)
    if tokens and tokens[0] in ("WP", "TWP"):
        return "WP"
    for tok in tokens[1:]:
        for sym in _INFIX_HEADS:
            if tok.startswith(sym):
                return sym
    stripped = text.lstrip("( ")
    m = _IDENT.match(stripped)
    if m:
        return m.group(0)
    return stripped.split()[0] if stripped.split() else ""


def _skel_head(node: object) -> str:
    kind = getattr(node, "kind", "atom")
    while kind in _MODALITY_KINDS and getattr(node, "children", None):
        node = getattr(node, "children")[0]  # noqa: B009 -- `node` is typed `object` on purpose
        kind = getattr(node, "kind", "atom")
    if kind == "atom":
        return _atom_head(getattr(node, "text", ""))
    return _CONNECTIVE_HEAD.get(kind, kind)


def head_symbol(prop: str) -> str:
    """The head symbol of a printed prop: ``WP`` for a WP goal, ``↦`` for ``l ↦ v``,
    ``own`` for ``own γ x``, ``∗`` for a separating conjunction.

    The legacy heuristic headed ``l ↦ v`` as ``l`` and a whole WP goal as one atom, so
    the relevance filter demoted every spatial hypothesis of every WP goal.
    """
    text = prop.strip()
    if not text:
        return ""
    return _skel_head(parse_skeleton(text))


def _walk(node: object) -> Iterator[object]:
    yield node
    for c in getattr(node, "children", None) or []:
        yield from _walk(c)


def _wp_postcondition(text: str) -> str:
    """The postcondition prop of ``WP e @ E {{ v, Φ v }}`` (or ``[{ }]``), else ``""``."""
    depth = 0
    i, n = 0, len(text)
    while i < n:
        if depth == 0 and (text.startswith("{{", i) or text.startswith("[{", i)):
            close = "}}" if text.startswith("{{", i) else "}]"
            j = i + 2
            d = 0
            while j < n:
                if text.startswith(close, j) and d == 0:
                    inner = text[i + 2 : j].strip()
                    # `v, Φ v` -- drop the value binder.
                    m = re.match(r"^([^\W\d][\w']*)\s*,\s*", inner)
                    return inner[m.end() :] if m else inner
                if text[j] in "([{":
                    d += 1
                elif text[j] in ")]}":
                    d = max(0, d - 1)
                j += 1
            return ""
        if text[i] in "([{":
            depth += 1
        elif text[i] in ")]}":
            depth = max(0, depth - 1)
        i += 1
    return ""


def heads(prop: str, *, _depth: int = 0) -> set[str]:
    """Every head symbol in a prop: the root's, each atom's, and a WP's postcondition's."""
    text = prop.strip()
    if not text or _depth > 3:
        return set()
    skel = parse_skeleton(text)
    out = {_skel_head(skel)}
    for node in _walk(skel):
        if getattr(node, "kind", "") != "atom":
            continue
        atom = getattr(node, "text", "")
        h = _atom_head(atom)
        if h:
            out.add(h)
        if h == "WP":
            post = _wp_postcondition(atom)
            if post:
                out |= heads(post, _depth=_depth + 1)
    out.discard("")
    return out
