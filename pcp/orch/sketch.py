"""`pcp sketch` -- compile a CSL proof sketch into frozen obligations (PLAN.md 9.3).

Design decisions should be made where cheating pressure is lowest, and that is the
sketch: there is no failing tactic to appease.  But *error* pressure peaks there --
a wrong invariant baked in at sketch time is the most expensive mistake the system
can make -- so the sketch is trusted for honesty and audited for correctness.

The sketch is **compiled, not consulted**.  Compilation is what prevents tactic work
from silently diverging from the design: amending the sketch is amending frozen
statements, and goes through the amendment lattice.

Sketch format (open decision 5 in the plan; this is the annotation-DSL arm, and the
skeleton-with-admits arm is just a `.v` plan file, which ``pcp prove --plan`` already
takes -- so both arms compile to the same graph, as the plan requires):

    context `{!heapGS Σ}
    ghost   γ : authR natUR   -- the counter's authoritative fragment

    invariant I : ∃ n, own γ (● n) ∗ l ↦ #n
      alloc: ⊢ |==> ∃ γ, I γ

    function incr (l : loc)
      spec: {{{ True }}} incr #l {{{ RET #(); True }}}
      commit: the CmpXchg that succeeds
      segment load    : ⌜True⌝
      segment cmpxchg : ⌜True⌝
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any

_DIRECTIVE = re.compile(r"^(?P<indent>\s*)(?P<key>[a-z_]+)\s*(?P<name>[\w'γ]*)\s*:?\s*(?P<rest>.*)$")


@dataclass
class Invariant:
    name: str
    body: str
    alloc: str = ""

    def obligations(self) -> list[tuple[str, str]]:
        """Every invariant carries an inhabitation witness as a sibling node.

        An unsatisfiable interface makes every client lemma vacuously provable and
        the development rots invisibly (PLAN.md 8.4).  This failure must be loud and
        immediate, so the witness is an obligation, not a note.
        """
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
        # One stated WP obligation per program segment between assertions, plus glue
        # obligations connecting them (PLAN.md 9.3).
        for i, seg in enumerate(self.segments):
            out.append((f"{self.name}_seg_{seg.name}", f"Lemma {self.name}_seg_{seg.name} : {seg.assertion}."))
            if i:
                prev = self.segments[i - 1]
                out.append(
                    (
                        f"{self.name}_glue_{prev.name}_{seg.name}",
                        f"Lemma {self.name}_glue_{prev.name}_{seg.name} : "
                        f"({prev.assertion}) -∗ ({seg.assertion}).",
                    )
                )
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
        """Emit a `.v` plan file -- the same shape `pcp prove --plan` already takes."""
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
        for name, statement in self.obligations():
            lines.append(statement)
            lines.append("Proof. Admitted.")
            lines.append("")
        return "\n".join(lines)

    def render_summary(self) -> str:
        lines = [
            f"{len(self.invariants)} invariant(s), {len(self.functions)} function(s) "
            f"→ {len(self.obligations())} obligations"
        ]
        for inv in self.invariants:
            lines.append(f"  invariant {inv.name}: {' '.join(inv.body.split())[:80]}")
            lines.append("    + allocation witness (unsatisfiable interfaces must fail loudly)")
        for fn in self.functions:
            lines.append(f"  function {fn.name}: {len(fn.segments)} segment(s)")
            if fn.commit:
                lines.append(f"    commit point: {fn.commit}")
            elif _is_logatom(fn.spec):
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


def _is_logatom(spec: str) -> bool:
    return "<<<" in spec or "atomic_update" in spec


def compile_sketch(text: str) -> Sketch:
    sketch = Sketch()
    current_inv: Invariant | None = None
    current_fn: Function | None = None

    for raw in text.splitlines():
        line = raw.split("--")[0].rstrip() if "--" in raw and not raw.strip().startswith("--") else raw.rstrip()
        if not line.strip() or line.strip().startswith("#"):
            continue
        m = _DIRECTIVE.match(line)
        if not m:
            continue
        key, name, rest = m.group("key"), m.group("name"), m.group("rest").strip()

        if key == "context":
            sketch.context.append((name + " " + rest).strip())
        elif key == "ghost":
            sketch.ghost.append((name, rest))
        elif key == "invariant":
            current_inv = Invariant(name=name or "I", body=rest)
            sketch.invariants.append(current_inv)
            current_fn = None
        elif key == "alloc" and current_inv is not None:
            current_inv.alloc = (name + " " + rest).strip()
        elif key == "function":
            current_fn = Function(name=name or "f")
            sketch.functions.append(current_fn)
            current_inv = None
        elif key == "spec" and current_fn is not None:
            current_fn.spec = (name + " " + rest).strip()
        elif key == "commit" and current_fn is not None:
            current_fn.commit = (name + " " + rest).strip()
        elif key == "segment" and current_fn is not None:
            current_fn.segments.append(Segment(name=name or f"s{len(current_fn.segments)}", assertion=rest))

    if not sketch.invariants:
        sketch.warnings.append(
            "no invariant declared. In CSL the invariant catalog is interface rank and "
            "is the highest-leverage audit in the system; sketching without one defers "
            "the most expensive decision to tactic time."
        )
    for fn in sketch.functions:
        if _is_logatom(fn.spec) and not fn.commit:
            sketch.warnings.append(f"{fn.name}: logically atomic spec with no commit point identified")
    # Preservation probes are deliberately absent: stating one requires the pre-step
    # symbolic state that the proof itself computes, so they are research, not a
    # deliverable (PLAN.md 9.2).
    return sketch
