"""``pcp sketch`` -- compile a CSL proof sketch into frozen obligations (PLAN.md 9.3).

Design decisions should be made where cheating pressure is lowest, and that is the
sketch: there is no failing tactic to appease.  The sketch is **compiled, not
consulted**: amending it is amending frozen statements.

This is the annotation-DSL arm of open decision 5; the skeleton-with-admits arm is a
plain ``.v`` plan (``pcp prove --plan``).  Both compile to the same graph.

Format (line-oriented; ``#`` comments; ``--`` trailing comments)::

    context `{!heapGS Σ}
    ghost   γ : authR natUR
    invariant I : ∃ n, own γ (● n) ∗ l ↦ #n
      alloc: ⊢ |==> ∃ γ, I γ
    function incr
      spec: {{{ True }}} incr #l {{{ RET #(); True }}}
      commit: the CmpXchg that succeeds
      segment load    : ⌜True⌝
      segment cmpxchg : ⌜True⌝
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any

_DIRECTIVE = re.compile(r"^\s*(?P<key>[a-z_]+)\s*(?P<name>[^\s:]*)\s*:?\s*(?P<rest>.*)$")
_KEYS = ("context", "ghost", "invariant", "alloc", "function", "spec", "commit", "segment")


@dataclass
class Invariant:
    name: str
    body: str
    alloc: str = ""

    def obligations(self) -> list[tuple[str, str]]:
        """Every invariant carries an inhabitation witness as a sibling node (PLAN.md 8.4)."""
        alloc = self.alloc or f"⊢ |==> ∃ γ, {self.name} γ"
        return [(f"{self.name}_alloc", f"Lemma {self.name}_alloc : {alloc}.")]


@dataclass
class Segment:
    name: str
    assertion: str


@dataclass
class Function:
    name: str
    spec: str = ""
    commit: str = ""
    segments: list[Segment] = field(default_factory=list)

    def obligations(self) -> list[tuple[str, str]]:
        out: list[tuple[str, str]] = []
        if self.spec:
            out.append((f"{self.name}_spec", f"Lemma {self.name}_spec : {self.spec}."))
        for i, seg in enumerate(self.segments):
            out.append((f"{self.name}_seg_{seg.name}", f"Lemma {self.name}_seg_{seg.name} : {seg.assertion}."))
            if i:
                prev = self.segments[i - 1]
                out.append((
                    f"{self.name}_glue_{prev.name}_{seg.name}",
                    f"Lemma {self.name}_glue_{prev.name}_{seg.name} : ({prev.assertion}) -∗ ({seg.assertion}).",
                ))
        return out


@dataclass
class Sketch:
    context: list[str] = field(default_factory=list)
    ghost: list[tuple[str, str]] = field(default_factory=list)
    invariants: list[Invariant] = field(default_factory=list)
    functions: list[Function] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)

    def obligations(self) -> list[tuple[str, str]]:
        out: list[tuple[str, str]] = []
        for inv in self.invariants:
            out.extend(inv.obligations())
        for fn in self.functions:
            out.extend(fn.obligations())
        return out

    def render_plan(self) -> str:
        lines = [
            "(* Compiled from a proof sketch by `pcp sketch`.",
            "",
            "   These statements are frozen obligations: amending one is amending the",
            "   sketch, and goes through the amendment lattice. Tactic work cannot",
            "   silently diverge from the design because the design *is* these lines. *)",
            "",
        ]
        for name, ty in self.ghost:
            lines.append(f"(* ghost {name} : {ty} *)")
        if self.ghost:
            lines.append("")
        for _name, statement in self.obligations():
            lines.append(statement)
            lines.append("Proof. Admitted.")
            lines.append("")
        return "\n".join(lines)

    def render_summary(self) -> str:
        lines = [
            f"{len(self.invariants)} invariant(s), {len(self.functions)} function(s) → {len(self.obligations())} obligations"
        ]
        for inv in self.invariants:
            lines.append(f"  invariant {inv.name}: {' '.join(inv.body.split())[:80]}")
            lines.append("    + allocation witness (unsatisfiable interfaces must fail loudly)")
        for fn in self.functions:
            lines.append(f"  function {fn.name}: {len(fn.segments)} segment(s)")
            if fn.commit:
                lines.append(f"    commit point: {fn.commit}")
            elif is_logatom(fn.spec):
                lines.append("    ! logically atomic spec with no commit point named --")
                lines.append("      fix it at sketch time; it is a classic multi-day sink later")
        for w in self.warnings:
            lines.append(f"  warning: {w}")
        return "\n".join(lines)

    def to_json(self) -> dict[str, Any]:
        return {
            "context": self.context,
            "ghost": [{"name": n, "type": t} for n, t in self.ghost],
            "invariants": [{"name": i.name, "body": i.body, "alloc": i.alloc} for i in self.invariants],
            "functions": [
                {
                    "name": f.name,
                    "spec": f.spec,
                    "commit": f.commit,
                    "segments": [{"name": s.name, "assertion": s.assertion} for s in f.segments],
                }
                for f in self.functions
            ],
            "obligations": [{"name": n, "statement": s} for n, s in self.obligations()],
            "warnings": self.warnings,
        }


def is_logatom(spec: str) -> bool:
    return "<<<" in spec or "<<{" in spec or "atomic_update" in spec


def _strip_trailing_comment(raw: str) -> str:
    """Drop a `` -- comment`` (a `--` preceded by whitespace; `-∗` and `->` are untouched)."""
    m = re.search(r"\s--(\s|$)", raw)
    return raw[: m.start()] if m else raw


def compile_sketch(text: str) -> Sketch:
    sketch = Sketch()
    current_inv: Invariant | None = None
    current_fn: Function | None = None

    for raw in text.splitlines():
        line = _strip_trailing_comment(raw).rstrip()
        if not line.strip() or line.strip().startswith("#"):
            continue
        m = _DIRECTIVE.match(line)
        if not m or m.group("key") not in _KEYS:
            sketch.warnings.append(f"ignored line: {line.strip()[:60]}")
            continue
        key, name, rest = m.group("key"), m.group("name"), m.group("rest").strip()
        if key == "context":
            sketch.context.append(f"{name} {rest}".strip())
        elif key == "ghost":
            sketch.ghost.append((name, rest))
        elif key == "invariant":
            current_inv = Invariant(name=name or "I", body=rest)
            sketch.invariants.append(current_inv)
            current_fn = None
        elif key == "alloc" and current_inv is not None:
            current_inv.alloc = f"{name} {rest}".strip()
        elif key == "function":
            current_fn = Function(name=name or "f")
            sketch.functions.append(current_fn)
            current_inv = None
        elif key == "spec" and current_fn is not None:
            current_fn.spec = f"{name} {rest}".strip()
        elif key == "commit" and current_fn is not None:
            current_fn.commit = f"{name} {rest}".strip()
        elif key == "segment" and current_fn is not None:
            current_fn.segments.append(Segment(name=name or f"s{len(current_fn.segments)}", assertion=rest))
        else:
            sketch.warnings.append(f"`{key}` outside of an invariant/function: {line.strip()[:60]}")

    if not sketch.invariants:
        sketch.warnings.append(
            "no invariant declared. In CSL the invariant catalog is interface rank and "
            "is the highest-leverage audit in the system; sketching without one defers "
            "the most expensive decision to tactic time."
        )
    for fn in sketch.functions:
        if is_logatom(fn.spec) and not fn.commit:
            sketch.warnings.append(f"{fn.name}: logically atomic spec with no commit point identified")
    return sketch
