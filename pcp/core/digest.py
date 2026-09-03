"""Content-addressed prop store, elision and render budgets (PLAN.md 3.2, 5).

Two jobs:

* **Store props once.**  In a 300-step proof a large invariant that no tactic touches
  is stored once and referenced 300 times by hash.  Rendering can then say
  "unchanged since step 4" instead of reprinting it.
* **Spend a token budget deliberately.**  Every render passes through a budget and
  every render *says* how much it elided.  A model that knows it is looking at a
  partial view asks for more; a model that does not, hallucinates.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass, field
from typing import Callable, Iterable, Iterator, Literal

Mode = Literal["full", "folded", "summary", "hash-only"]

# Iris proofs are evar-dense.  Instantiating an evar reprints hypotheses no tactic
# touched, so hashing must be modulo evar names or every such step looks like a mass
# consume/produce (PLAN.md 4.1).
_EVAR = re.compile(r"\?(?:Goal)?[A-Za-z_][A-Za-z0-9_']*")
_WS = re.compile(r"\s+")


def normalize(prop: str) -> str:
    """Canonical form of a printed prop: whitespace-collapsed, evar names erased."""
    return _WS.sub(" ", _EVAR.sub("?_", prop)).strip()


def prop_hash(prop: str, *, prefix: str = "h") -> str:
    """Content hash of a printed prop, modulo evar names and whitespace."""
    digest = hashlib.blake2b(normalize(prop).encode("utf-8"), digest_size=8).hexdigest()
    return f"{prefix}:{digest[:8]}"


def blob_hash(data: str | bytes, *, prefix: str = "b") -> str:
    """Exact content hash (no normalization).  Used for source text and patches."""
    raw = data.encode("utf-8") if isinstance(data, str) else data
    return f"{prefix}:{hashlib.blake2b(raw, digest_size=16).hexdigest()}"


class PropStore:
    """Hash -> printed prop.  Deduplicating, append-only, cheap to serialize."""

    def __init__(self) -> None:
        self._by_hash: dict[str, str] = {}

    def put(self, prop: str, *, prefix: str = "h") -> str:
        h = prop_hash(prop, prefix=prefix)
        # Keep the first spelling seen: normalization is lossy, the store is a display
        # cache, and a stable spelling makes diffs readable.
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

    def to_json(self) -> dict[str, str]:
        return dict(self._by_hash)

    @classmethod
    def from_json(cls, data: dict[str, str]) -> "PropStore":
        store = cls()
        store._by_hash.update(data)
        return store


# --------------------------------------------------------------------------- tokens

def estimate_tokens(text: str) -> int:
    """Cheap, deterministic token estimate.

    Deliberately not a real tokenizer: the budget only has to be stable and roughly
    right, and a tokenizer dependency for this would be absurd.  ~3.6 chars/token is
    a decent fit for Rocq/Iris source with heavy unicode notation.
    """
    if not text:
        return 0
    return max(1, round(len(text) / 3.6))


@dataclass
class RenderBudget:
    """A token budget that is spent, reported, and never silently exceeded."""

    limit: int = 4000
    spent: int = 0
    elided: int = 0

    def can_afford(self, text: str) -> bool:
        return self.spent + estimate_tokens(text) <= self.limit

    def charge(self, text: str) -> int:
        n = estimate_tokens(text)
        self.spent += n
        return n

    def skip(self, text: str) -> int:
        n = estimate_tokens(text)
        self.elided += n
        return n

    @property
    def remaining(self) -> int:
        return max(0, self.limit - self.spent)


# --------------------------------------------------------------------------- folding

@dataclass
class FoldedProp:
    """A prop rendered as a one-line stub, expandable by id in one call."""

    hash: str
    head: str
    lines: int

    def render(self) -> str:
        return f"⟨fold:{self.hash.split(':')[-1]} · {self.head} · {self.lines} lines⟩"


def head_summary(prop: str, width: int = 40) -> str:
    """First line of a prop, truncated -- enough to recognise it, not to read it."""
    first = prop.strip().splitlines()[0] if prop.strip() else ""
    if len(first) <= width:
        return first
    return first[: width - 1].rstrip() + "…"


def fold(prop: str, h: str) -> FoldedProp:
    return FoldedProp(hash=h, head=head_summary(prop), lines=len(prop.splitlines()) or 1)


def render_prop(prop: str, h: str, mode: Mode, *, fold_over_lines: int = 4) -> str:
    """Render one prop under a mode.  ``full`` still auto-folds oversized props."""
    if mode == "hash-only":
        return h
    if mode == "summary":
        return head_summary(prop)
    if mode == "folded":
        return fold(prop, h).render()
    if len(prop.splitlines()) > fold_over_lines:
        return fold(prop, h).render()
    return prop


# --------------------------------------------------------------------------- select

_CLASS_SELECTORS = {"spatial", "intuitionistic", "pure", "changed", "unchanged", "all", "goal"}


@dataclass
class Selector:
    """Parsed ``select`` expression (PLAN.md 5).

    Grammar, comma-separated, any mix of:
      ``H*``            id glob
      ``spatial``       class
      ``mentions:γ``    predicate -- prop text contains the token
      ``head:WP``       predicate -- prop's head symbol
    """

    globs: list[str] = field(default_factory=list)
    classes: set[str] = field(default_factory=set)
    mentions: list[str] = field(default_factory=list)
    heads: list[str] = field(default_factory=list)

    @classmethod
    def parse(cls, spec: str | None) -> "Selector":
        sel = cls()
        if not spec:
            sel.classes.add("all")
            return sel
        for raw in spec.split(","):
            token = raw.strip()
            if not token:
                continue
            if token.startswith("mentions:"):
                sel.mentions.append(token[len("mentions:") :])
            elif token.startswith("head:"):
                sel.heads.append(token[len("head:") :])
            elif token in _CLASS_SELECTORS:
                sel.classes.add(token)
            else:
                sel.globs.append(token)
        if not (sel.globs or sel.classes or sel.mentions or sel.heads):
            sel.classes.add("all")
        return sel

    def selects_everything(self) -> bool:
        return "all" in self.classes and not (self.globs or self.mentions or self.heads)


def head_symbol(prop: str) -> str:
    """Best-effort head symbol of a printed prop.  Used by the relevance filter."""
    text = prop.strip()
    # Strip leading binders/modalities so `▷ ▷ WP e {{ Φ }}` heads as `WP`.
    while True:
        m = re.match(r"^\s*(?:▷|□|■|\|==>|\|=\{[^}]*\}=>|◇|<pers>)\s*", text)
        if not m or not m.group(0):
            break
        text = text[m.end() :]
    m = re.match(r"^[(\s]*([A-Za-z_][A-Za-z0-9_.']*)", text)
    if m:
        return m.group(1)
    m = re.match(r"^\s*(\S+)", text)
    return m.group(1) if m else ""


def matches(
    ident: str,
    prop: str,
    klass: str,
    sel: Selector,
    *,
    changed: bool = False,
) -> bool:
    from fnmatch import fnmatchcase

    if sel.selects_everything():
        return True
    if "all" in sel.classes:
        return True
    if klass in sel.classes:
        return True
    if "changed" in sel.classes and changed:
        return True
    if "unchanged" in sel.classes and not changed:
        return True
    if any(fnmatchcase(ident, g) for g in sel.globs):
        return True
    if any(token in prop for token in sel.mentions):
        return True
    if sel.heads:
        head = head_symbol(prop)
        if any(head == h or head.startswith(h) for h in sel.heads):
            return True
    return False


def budgeted(
    items: Iterable[tuple[str, str]],
    budget: RenderBudget,
    render: Callable[[str, str], str],
) -> tuple[list[str], list[str]]:
    """Render ``(id, prop)`` pairs until the budget runs out.

    Returns ``(rendered_lines, elided_ids)``.  Elision is *visible*: the caller is
    expected to print the manifest of what did not fit.
    """
    rendered: list[str] = []
    elided: list[str] = []
    for ident, prop in items:
        line = render(ident, prop)
        if budget.can_afford(line):
            budget.charge(line)
            rendered.append(line)
        else:
            budget.skip(line)
            elided.append(ident)
    return rendered, elided
