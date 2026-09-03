"""The Iris proof-state data model (PLAN.md 3.2).

Everything else in ``pcp.core`` is a view over these types.  They are deliberately
JSON-shaped and versioned: a trace is a durable artifact (the eval corpus, the
regression suite, later training data), not an in-memory convenience.
"""

from __future__ import annotations

import re
from dataclasses import asdict, dataclass, field
from typing import Any, Literal

from pcp.core.digest import prop_hash

SCHEMA_VERSION = 1

HypClass = Literal["pure", "intuitionistic", "spatial"]


@dataclass
class Hyp:
    """One hypothesis in an IPM context (or one ordinary Coq hypothesis)."""

    id: str
    prop: str
    hash: str = ""
    klass: HypClass = "spatial"
    #: ``True`` / ``False`` once the persistence oracle (PLAN.md 4.3) has run,
    #: ``None`` while unknown.  Never guessed.
    persistent: bool | None = None
    affine: bool | None = None
    #: Extra names when several pure binders share a type (``names`` in petanque).
    names: list[str] = field(default_factory=list)

    def __post_init__(self) -> None:
        if not self.hash:
            self.hash = prop_hash(self.prop)
        if not self.names:
            self.names = [self.id]

    def to_json(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_json(cls, d: dict[str, Any]) -> "Hyp":
        return cls(**d)


@dataclass
class WPInfo:
    """The program-term part of a weakest-precondition goal, kept out of the blob."""

    expr_hash: str
    expr_summary: str
    total: bool = False  # `twp` rather than `wp` -- PLAN.md 8.4 partial-correctness flag

    def to_json(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class Modality:
    """First-class modality block (PLAN.md 3.2).

    Mask arithmetic is failure mode #3 and it is entirely mechanical.  Once mask and
    later-depth are *fields*, they can be diffed and asserted on: "you are under mask
    ``⊤ ∖ ↑N`` but ``wp_store`` needs ``↑N ⊆ E``".
    """

    mask: str | None = None
    laters: int = 0
    fupd: bool = False
    bupd: bool = False
    except0: bool = False
    wp: WPInfo | None = None

    def to_json(self) -> dict[str, Any]:
        d = asdict(self)
        d["wp"] = self.wp.to_json() if self.wp else None
        return d

    @classmethod
    def from_json(cls, d: dict[str, Any]) -> "Modality":
        wp = d.get("wp")
        return cls(
            mask=d.get("mask"),
            laters=d.get("laters", 0),
            fupd=d.get("fupd", False),
            bupd=d.get("bupd", False),
            except0=d.get("except0", False),
            wp=WPInfo(**wp) if wp else None,
        )

    def describe(self) -> str:
        bits = []
        if self.mask:
            bits.append(f"mask {self.mask}")
        if self.laters:
            bits.append(f"▷^{self.laters}")
        if self.fupd:
            bits.append("fupd")
        if self.bupd:
            bits.append("bupd")
        if self.except0:
            bits.append("◇")
        if self.wp:
            bits.append(("twp " if self.wp.total else "wp ") + self.wp.expr_summary)
        return " · ".join(bits) if bits else "—"


@dataclass
class IrisGoal:
    """One goal: ordinary Coq context + the two IPM contexts + the conclusion."""

    goal_id: str = "g0"
    pure: list[Hyp] = field(default_factory=list)
    intuitionistic: list[Hyp] = field(default_factory=list)
    spatial: list[Hyp] = field(default_factory=list)
    goal: str = ""
    goal_hash: str = ""
    modality: Modality = field(default_factory=Modality)
    #: ``False`` when the printed goal had no IPM separators at all -- an ordinary
    #: Coq goal.  The ledger's guarantees only apply to IPM goals.
    is_ipm: bool = True
    #: Raw printed goal, kept as an untrusted display fallback (PLAN.md 3.1).
    raw: str = ""

    def __post_init__(self) -> None:
        if not self.goal_hash and self.goal:
            self.goal_hash = prop_hash(self.goal)

    # -- accessors ---------------------------------------------------------
    @property
    def ipm_hyps(self) -> list[Hyp]:
        return self.intuitionistic + self.spatial

    def by_id(self, ident: str) -> Hyp | None:
        for h in self.pure + self.intuitionistic + self.spatial:
            if h.id == ident or ident in h.names:
                return h
        return None

    def context(self, klass: HypClass) -> list[Hyp]:
        return {"pure": self.pure, "intuitionistic": self.intuitionistic, "spatial": self.spatial}[klass]

    def to_json(self) -> dict[str, Any]:
        return {
            "goal_id": self.goal_id,
            "pure": [h.to_json() for h in self.pure],
            "intuitionistic": [h.to_json() for h in self.intuitionistic],
            "spatial": [h.to_json() for h in self.spatial],
            "goal": {"prop": self.goal, "hash": self.goal_hash},
            "modality": self.modality.to_json(),
            "is_ipm": self.is_ipm,
        }

    @classmethod
    def from_json(cls, d: dict[str, Any]) -> "IrisGoal":
        goal = d.get("goal") or {}
        return cls(
            goal_id=d.get("goal_id", "g0"),
            pure=[Hyp.from_json(h) for h in d.get("pure", [])],
            intuitionistic=[Hyp.from_json(h) for h in d.get("intuitionistic", [])],
            spatial=[Hyp.from_json(h) for h in d.get("spatial", [])],
            goal=goal.get("prop", ""),
            goal_hash=goal.get("hash", ""),
            modality=Modality.from_json(d.get("modality", {})),
            is_ipm=d.get("is_ipm", True),
        )


@dataclass
class Step:
    """One tactic application and the state it produced (PLAN.md 3.2)."""

    step: int
    state_id: int
    tactic: str
    goals: list[IrisGoal] = field(default_factory=list)
    #: Parent goal id, when this step's goals were spawned by a splitting tactic.
    parent_goal: str | None = None
    ok: bool = True
    error: str | None = None
    state_hash: int | None = None
    elapsed_ms: int = 0
    messages: list[str] = field(default_factory=list)

    def to_json(self) -> dict[str, Any]:
        return {
            "v": SCHEMA_VERSION,
            "step": self.step,
            "state_id": self.state_id,
            "state_hash": self.state_hash,
            "tactic": self.tactic,
            "ok": self.ok,
            "error": self.error,
            "elapsed_ms": self.elapsed_ms,
            "parent_goal": self.parent_goal,
            "goals": [g.to_json() for g in self.goals],
        }

    @classmethod
    def from_json(cls, d: dict[str, Any]) -> "Step":
        return cls(
            step=d["step"],
            state_id=d["state_id"],
            tactic=d["tactic"],
            goals=[IrisGoal.from_json(g) for g in d.get("goals", [])],
            parent_goal=d.get("parent_goal"),
            ok=d.get("ok", True),
            error=d.get("error"),
            state_hash=d.get("state_hash"),
            elapsed_ms=d.get("elapsed_ms", 0),
        )


# --------------------------------------------------------------------- modality bits

_MASK_FUPD = re.compile(r"\|=\{([^}]*)\}=(?:\{([^}]*)\})?=?>")


def scan_modality(prop: str) -> Modality:
    """Extract the modality block from a printed conclusion.

    Conservative by construction: anything not recognised is simply absent from the
    block, never guessed at.  The printed text remains available as ``raw``.
    """
    m = Modality()
    text = prop.strip()

    # Leading later depth: `▷ ▷ P`, `▷^2 P`.
    while True:
        mm = re.match(r"^\s*▷\s*(?:\^\s*(\d+))?\s*", text)
        if not mm or not mm.group(0).strip():
            break
        m.laters += int(mm.group(1)) if mm.group(1) else 1
        text = text[mm.end() :]

    fupd = _MASK_FUPD.search(prop)
    if fupd:
        m.fupd = True
        left = (fupd.group(1) or "").strip()
        right = (fupd.group(2) or "").strip()
        if not right:
            # `|={E1,E2}=>` puts both masks in one brace group, comma-separated.
            parts = split_masks(left)
            if len(parts) == 2:
                left, right = parts
        # `⇝` is the fupd's *own* mask change; `→` is reserved for a change between
        # two steps, so a MaskChange event never reads ambiguously.
        m.mask = f"{left} ⇝ {right}" if right and right != left else left or None
    if "|==>" in prop:
        m.bupd = True
    if re.search(r"(^|\s)◇(\s|$)", prop):
        m.except0 = True

    wpm = re.search(r"\b(twp|WP|wp)\b", prop)
    if wpm:
        total = wpm.group(1) == "twp"
        expr = _extract_wp_expr(prop[wpm.end() :])
        m.wp = WPInfo(expr_hash=prop_hash(expr, prefix="e"), expr_summary=_summarise(expr), total=total)
        # `WP e @ E {{ Φ }}` -- the mask sits after `@`.
        at = re.search(r"@\s*(?:E\s*;\s*)?([^{]+?)\s*\{\{", prop[wpm.end() :])
        if at and not m.mask:
            m.mask = at.group(1).strip()
    return m


def split_masks(text: str) -> list[str]:
    """Split `E1,E2` at the top level -- `⊤ ∖ ↑N` and `{[x]}` contain no bare comma,
    but set-builder and application syntax can, so respect nesting."""
    out, depth, buf = [], 0, ""
    for ch in text:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(buf.strip())
            buf = ""
        else:
            buf += ch
    out.append(buf.strip())
    return [p for p in out if p]


def canonical_mask(mask: str | None) -> str:
    """`None` (no modality) and `⊤` are the same ambient mask for diffing."""
    if mask is None:
        return "⊤"
    return " ".join(mask.split()) or "⊤"


def _extract_wp_expr(rest: str) -> str:
    """The program term of a WP goal: everything up to `@` or the postcondition."""
    cut = len(rest)
    depth = 0
    for i, ch in enumerate(rest):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and (rest.startswith("{{", i) or ch == "@"):
            cut = i
            break
    return rest[:cut].strip()


def _summarise(expr: str, width: int = 48) -> str:
    one = " ".join(expr.split())
    return one if len(one) <= width else one[: width - 1] + "…"
