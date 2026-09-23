"""The Iris proof-state data model (PLAN.md 3.2).

Everything else in ``pcp.state`` is a view over these types.  They are JSON-shaped and
versioned: a trace is a durable artifact (the eval corpus, the regression suite, later
training data), and the on-disk shape is ``schema v=1``.
"""

from __future__ import annotations

import re
from dataclasses import asdict, dataclass, field
from typing import Any, Literal

from pcp.state.props import prop_hash

SCHEMA_VERSION = 1

HypClass = Literal["pure", "intuitionistic", "spatial"]


@dataclass
class Hyp:
    """One hypothesis in an IPM context (or one ordinary Coq hypothesis).

    Anonymous IPM hypotheses print as ``_ : P``; they get a synthetic id ``_1``, ``_2``
    ... per context so they stay addressable, with ``anonymous=True``.
    """

    id: str
    prop: str
    hash: str = ""
    klass: HypClass = "spatial"
    #: ``True``/``False`` once the persistence oracle has run; ``None`` while unknown.
    persistent: bool | None = None
    affine: bool | None = None
    #: Extra names when several pure binders share a type (``names`` in petanque).
    names: list[str] = field(default_factory=list)
    anonymous: bool = False

    def __post_init__(self) -> None:
        if not self.hash:
            self.hash = prop_hash(self.prop, prefix="p" if self.klass == "pure" else "h")
        if not self.names:
            self.names = [self.id]

    def to_json(self) -> dict[str, Any]:
        d = asdict(self)
        if not self.anonymous:
            d.pop("anonymous")
        return d

    @classmethod
    def from_json(cls, d: dict[str, Any]) -> Hyp:
        return cls(
            id=d["id"],
            prop=d.get("prop", ""),
            hash=d.get("hash", ""),
            klass=d.get("klass", "spatial"),
            persistent=d.get("persistent"),
            affine=d.get("affine"),
            names=list(d.get("names") or []),
            anonymous=bool(d.get("anonymous", False)),
        )


@dataclass
class WPInfo:
    """The program-term part of a weakest-precondition goal, kept out of the blob."""

    expr_hash: str
    expr_summary: str
    #: Total weakest precondition.  Iris prints it as ``WP e [{ Φ }]`` (square braces),
    #: never as the token ``twp`` (PLAN.md 8.4 partial-correctness flag).
    total: bool = False

    def to_json(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class Modality:
    """First-class modality block (PLAN.md 3.2).

    Mask and later-depth are *fields* so they can be diffed and asserted on: "you are
    under mask ``⊤ ∖ ↑N`` but ``wp_store`` needs ``↑N ⊆ E``".  The block describes the
    **head** of the conclusion only: a wand whose conclusion contains a fupd is not
    itself under that fupd.
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
    def from_json(cls, d: dict[str, Any]) -> Modality:
        wp = d.get("wp")
        return cls(
            mask=d.get("mask"),
            laters=int(d.get("laters", 0) or 0),
            fupd=bool(d.get("fupd", False)),
            bupd=bool(d.get("bupd", False)),
            except0=bool(d.get("except0", False)),
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
    #: ``False`` when the printed goal had no IPM separators at all.
    is_ipm: bool = True
    #: Raw printed goal, kept as an untrusted display fallback (PLAN.md 3.1).
    raw: str = ""

    def __post_init__(self) -> None:
        if not self.goal_hash and self.goal:
            self.goal_hash = prop_hash(self.goal, prefix="g")

    @property
    def ipm_hyps(self) -> list[Hyp]:
        return self.intuitionistic + self.spatial

    @property
    def all_hyps(self) -> list[Hyp]:
        return self.pure + self.intuitionistic + self.spatial

    def by_id(self, ident: str) -> Hyp | None:
        for h in self.all_hyps:
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
    def from_json(cls, d: dict[str, Any]) -> IrisGoal:
        goal = d.get("goal") or {}
        return cls(
            goal_id=d.get("goal_id", "g0"),
            pure=[Hyp.from_json(h) for h in d.get("pure", [])],
            intuitionistic=[Hyp.from_json(h) for h in d.get("intuitionistic", [])],
            spatial=[Hyp.from_json(h) for h in d.get("spatial", [])],
            goal=goal.get("prop", ""),
            goal_hash=goal.get("hash", ""),
            modality=Modality.from_json(d.get("modality") or {}),
            is_ipm=bool(d.get("is_ipm", True)),
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
    #: Step index this state was already seen at (state-hash loop detection).
    loop_of: int | None = None

    def to_json(self) -> dict[str, Any]:
        d: dict[str, Any] = {
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
        if self.loop_of is not None:
            d["loop_of"] = self.loop_of
        if self.messages:
            # The feedback channel (the reflected `PCP1` records live here); optional so
            # the v=1 shape is unchanged for steps without messages.
            d["messages"] = list(self.messages)
        return d

    @classmethod
    def from_json(cls, d: dict[str, Any]) -> Step:
        return cls(
            step=int(d["step"]),
            state_id=int(d["state_id"]),
            tactic=d["tactic"],
            goals=[IrisGoal.from_json(g) for g in d.get("goals", [])],
            parent_goal=d.get("parent_goal"),
            ok=bool(d.get("ok", True)),
            error=d.get("error"),
            state_hash=d.get("state_hash"),
            elapsed_ms=int(d.get("elapsed_ms", 0) or 0),
            messages=[str(m) for m in (d.get("messages") or [])],
            loop_of=d.get("loop_of"),
        )


# --------------------------------------------------------------------- modality bits

#: ``▷``, ``▷^n`` (a literal counts n; a symbolic ``n`` counts 1), ``▷?p`` (conditional: counts 1).
_LATER = re.compile(r"^\s*▷(?:\^\s*(?P<n>\d+)|\^\s*(?:\([^)]*\)|\S+)|\?\s*(?:\([^)]*\)|\S+))?\s*")
_FUPD_HEAD = re.compile(r"^\s*\|=\{([^}]*)\}(?:\[([^\]]*)\])?(▷)?=>\s*")
_BUPD_HEAD = re.compile(r"^\s*\|==>\s*")
_EXCEPT0_HEAD = re.compile(r"^\s*◇\s*")
_WP_HEAD = re.compile(r"^\s*WP\b")
_STUCKNESS = re.compile(r"^\s*(?:NotStuck|MaybeStuck|\??[^\W\d][\w']*)\s*;\s*")


def scan_modality(prop: str) -> Modality:
    """Extract the modality block from the **head** of a printed conclusion.

    Conservative by construction: anything not recognised is simply absent from the
    block, never guessed at.  Only prefixes are consumed -- ``P -∗ |={E}=> Q`` is a wand,
    not a fupd, and ``WP e {{ v, |={⊤}=> Φ v }}`` is a WP whose postcondition happens
    to mention a fupd.
    """
    m = Modality()
    text = prop.strip()
    # Peel modality prefixes in any order until the head is something else.
    while True:
        mm = _LATER.match(text)
        if mm and mm.group(0).strip():
            m.laters += int(mm.group("n")) if mm.group("n") else 1
            text = text[mm.end() :]
            continue
        mm = _FUPD_HEAD.match(text)
        if mm:
            m.fupd = True
            left = (mm.group(1) or "").strip()
            parts = split_masks(left)
            right = parts[1] if len(parts) == 2 else ""
            left = parts[0] if parts else left
            if mm.group(2):
                right = mm.group(2).strip()
            if mm.group(3):
                m.laters += 1
            # `⇝` is the fupd's own mask change; `→` is reserved for a change between steps.
            m.mask = f"{left} ⇝ {right}" if right and right != left else (left or None)
            text = text[mm.end() :]
            continue
        mm = _BUPD_HEAD.match(text)
        if mm:
            m.bupd = True
            text = text[mm.end() :]
            continue
        mm = _EXCEPT0_HEAD.match(text)
        if mm:
            m.except0 = True
            text = text[mm.end() :]
            continue
        break

    wpm = _WP_HEAD.match(text)
    if wpm:
        rest = text[wpm.end() :]
        expr, after = _split_wp(rest)
        post = after.lstrip()
        total = post.startswith("[{")
        if post.startswith("@"):
            mask_text = post[1:]
            cut = _top_level_find(mask_text, ("{{", "[{"))
            # Total WP prints as `WP e @ E [{ Φ }]`: the opener after the mask decides.
            total = mask_text[cut:].startswith("[{")
            mask = mask_text[:cut].strip()
            mask = _STUCKNESS.sub("", mask, count=1).strip() if ";" in mask else mask
            if mask and m.mask is None:
                m.mask = mask
        m.wp = WPInfo(expr_hash=prop_hash(expr, prefix="e"), expr_summary=_summarise(expr), total=total)
    return m


def _top_level_find(text: str, needles: tuple[str, ...]) -> int:
    depth = 0
    for i, ch in enumerate(text):
        if depth == 0 and any(text.startswith(nd, i) for nd in needles):
            return i
        if ch in "([{":
            depth += 1
        elif ch in ")]}" and depth:
            depth -= 1
    return len(text)


def _split_wp(rest: str) -> tuple[str, str]:
    """``(program term, remainder starting at '@' or the postcondition)``."""
    depth = 0
    for i, ch in enumerate(rest):
        if depth == 0 and (ch == "@" or rest.startswith("{{", i) or rest.startswith("[{", i)):
            return rest[:i].strip(), rest[i:]
        if ch in "([{":
            depth += 1
        elif ch in ")]}" and depth:
            depth -= 1
    return rest.strip(), ""


def split_masks(text: str) -> list[str]:
    """Split ``E1,E2`` at the top level, respecting nesting."""
    out: list[str] = []
    depth, buf = 0, ""
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
    """``None`` (no modality) and ``⊤`` are the same ambient mask for diffing."""
    if mask is None:
        return "⊤"
    return " ".join(mask.split()) or "⊤"


def _summarise(expr: str, width: int = 48) -> str:
    one = " ".join(expr.split())
    return one if len(one) <= width else one[: width - 1] + "…"
