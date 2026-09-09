"""Random Iris-prop skeletons and intro patterns, for property testing.

Two generators that mirror each other:

* :func:`random_skel` builds a connective skeleton over a vocabulary of real Iris atoms
  (unicode included), pure facts, binders and nested modalities; ``render`` turns it
  into Iris notation and parsing that back must recover the tree;
* :func:`random_pattern_for` builds a pattern that *should* fit a skeleton and
  :func:`mutate_pattern` breaks it in one specific way, so the aligner is checked for
  both false negatives and false positives.

Dependency-free (no Hypothesis): the shapes are small and a seeded ``random`` makes
every failure reproducible from its seed.
"""

from __future__ import annotations

import copy
import random
from dataclasses import replace

from pcp.state.ipm.pattern import Pat, compile_auto
from pcp.state.ipm.skeleton import Skel

ATOMS = [
    "P", "Q", "R", "P v", "Φ v", "l ↦ v", "l ↦{#q} v", "own γ (● n)", "own γ (◯ n)",
    "inv N (I γ)", "is_lock γ lk R", "l ↦∗ vs", "na_own p E", "£ n", "cinv_own γ q",
    "sts_own γ s T", "auth_own γ a", "WP e {{ Φ }}", "WP e @ s; E [{ v, Φ v }]",
    "meta_token l ⊤", "pointsto l dq v", "state_interp σ ns κs nt", "l ↦ #(i1 + i2)",
    "(P ≡ Q)", "emp", "True",
]
PURE = ["n = 3", "v ≤ 3", "l ≠ l'", "0 < n", "is_Some (m !! i)", "vs !! i = Some v", "v = #()", "κ0 = []"]
BINDERS = ["x", "y", "γ", "v", "n", "q", "vs", "s", "nt'"]
MASKS = ["⊤", "⊤ ∖ ↑N", "E", "E ∖ ↑N", "∅", "⊤ ∖ ↑N,∅"]
LATER_ANNOTATIONS = ["", "", "", "^2", "^n", "?p"]

BRANCHING = ["sep", "and", "or"]
TIGHT = ["later", "intuitionistically", "persistently", "plainly", "except0", "affinely", "absorbingly"]
LOOSE = ["bupd", "fupd", "fupd_step"]
ARROW = ["wand", "impl", "iff", "wand_iff", "wand", "impl", "entails", "equiv"]


def random_skel(rng: random.Random, depth: int = 3, *, arrows: bool = True) -> Skel:
    """A random prop skeleton.  ``depth`` bounds nesting, not size."""
    if depth <= 0:
        return _leaf(rng)
    roll = rng.random()
    if roll < 0.34:
        kind = rng.choice(BRANCHING)
        n = rng.choice([2, 2, 2, 3, 4])
        kids = [random_skel(rng, depth - 1, arrows=arrows) for _ in range(n)]
        # ∗/∧/∨ associate right and the parser flattens the right spine, so a same-kind
        # last child would not round-trip as a nested node: shield it (left-nested
        # shapes are genuinely different terms and stay as generated).
        kids[-1] = _shield(kids[-1], kind)
        return Skel(kind, kids)  # type: ignore[arg-type]
    if roll < 0.50:
        kind = rng.choice(TIGHT)
        binders: list[str] = []
        if kind == "later":
            ann = rng.choice(LATER_ANNOTATIONS)
            binders = [ann] if ann else []
        elif kind == "persistently" and rng.random() < 0.2:
            binders = ["?p"]
        return Skel(kind, [random_skel(rng, depth - 1, arrows=arrows)], binders=binders)  # type: ignore[arg-type]
    if roll < 0.62:
        kind = rng.choice(LOOSE)
        if kind == "fupd":
            binders = [rng.choice(MASKS)]
        elif kind == "fupd_step":
            e1 = rng.choice(MASKS[:5])
            binders = [e1, rng.choice([e1, rng.choice(MASKS[:5])])]
            if rng.random() < 0.3:
                binders.append(rng.choice(["2", "n"]))
        else:
            binders = []
        return Skel(kind, [random_skel(rng, depth - 1, arrows=arrows)], binders=binders)  # type: ignore[arg-type]
    if roll < 0.76:
        kind = rng.choice(["exists", "forall"])
        n = rng.choice([1, 1, 2])
        return Skel(kind, [random_skel(rng, depth - 1, arrows=arrows)], binders=rng.sample(BINDERS, n))  # type: ignore[arg-type]
    if roll < 0.88 and arrows:
        kind = rng.choice(ARROW)
        kids = [random_skel(rng, depth - 1, arrows=arrows) for _ in range(2)]
        return Skel(kind, kids)  # type: ignore[arg-type]
    return _leaf(rng)


def _leaf(rng: random.Random) -> Skel:
    if rng.random() < 0.25:
        text = rng.choice(PURE)
        return Skel("pure", [Skel("atom", text=text)], text=text)
    return Skel("atom", text=rng.choice(ATOMS))


def _shield(node: Skel, parent_kind: str) -> Skel:
    if node.kind == parent_kind:
        return Skel("later", [node])
    return node


# ------------------------------------------------------------------------ patterns


def random_pattern_for(rng: random.Random, skel: Skel) -> Pat:
    """A pattern that fits ``skel``: the compiler's output with random names."""
    pat = compile_auto(skel, base=rng.choice(["H", "HΦ", "Hl", "Hown"])).pattern
    return _rename(pat, rng, [0])


def _rename(pat: Pat, rng: random.Random, counter: list[int]) -> Pat:
    out = replace(pat, children=[_rename(c, rng, counter) for c in pat.children])
    if out.kind == "name" and not out.pure:
        counter[0] += 1
        out.name = f"{rng.choice(['H', 'Hx', 'Ha'])}{counter[0]}"
    return out


#: Mutations the aligner must reject.
CAUGHT_MUTATIONS = ("swap_or_sep", "add_child", "over_destruct")
#: A mutation that yields a *legal* pattern (a sub-hypothesis merely stays whole):
#: a spurious mismatch would send the agent to the wrong place.
LEGAL_MUTATIONS = ("under_destruct",)
MUTATIONS = CAUGHT_MUTATIONS + LEGAL_MUTATIONS


def mutate_pattern(
    rng: random.Random, pat: Pat, kinds: tuple[str, ...] = CAUGHT_MUTATIONS, *, skel: Skel | None = None
) -> tuple[Pat, str] | None:
    """Break (or, for a legal kind, loosen) a fitting pattern in exactly one way.

    ``over_destruct`` is only applied to a name whose prop is *definitely* not
    splittable (a wand, a universal, an atomic pure fact ...): on an opaque atom the
    aligner is honest and accepts anything, because project notation may hide a
    connective it cannot see.
    """
    nodes = _collect(pat)
    rng.shuffle(nodes)
    definite = _definite_leaves(pat, skel) if skel is not None else {id(n) for n in nodes}
    for kind in rng.sample(list(kinds), len(kinds)):
        for node in nodes:
            if kind == "over_destruct" and id(node) not in definite:
                continue
            mutated = _apply(rng, pat, node, kind)
            if mutated is not None:
                return mutated, kind
    return None


_DEFINITE = frozenset({"wand", "impl", "iff", "wand_iff", "forall", "entails", "equiv"})


def _definite_leaves(pat: Pat, skel: Skel) -> set[int]:
    """Pattern names (by id) whose skeleton counterpart cannot be destructed.

    Mirrors ``compile_auto``: leading existentials became ``iDestruct`` binders, so the
    pattern's root corresponds to the body under them.
    """
    node = skel
    while True:
        node = node.strip_transparent()
        if node.kind == "exists" and node.children:
            node = node.children[0]
            continue
        break
    return _definite_leaves_go(pat, node)


def _definite_leaves_go(pat: Pat, skel: Skel) -> set[int]:
    from pcp.state.ipm.skeleton import parse_skeleton, peel

    out: set[int] = set()
    _, core = peel(skel)
    if pat.kind == "name":
        inner = parse_skeleton(core.children[0].text if core.children else core.text) if core.kind == "pure" else None
        if core.kind in _DEFINITE or (inner is not None and inner.kind == "atom"):
            out.add(id(pat))
    elif pat.kind in ("list", "or") and len(pat.children) == 2:
        first, second = pat.children
        if core.kind in ("sep", "and", "or") and len(core.children) >= 2:
            rest = core.children[1:]
            residual = rest[0] if len(rest) == 1 else Skel(core.kind, rest)
            out |= _definite_leaves_go(first, core.children[0]) | _definite_leaves_go(second, residual)
        elif core.kind == "exists" and core.children:
            body = Skel("exists", core.children, binders=core.binders[1:]) if len(core.binders) > 1 else core.children[0]
            out |= _definite_leaves_go(second, body)
    return out


def _collect(pat: Pat) -> list[Pat]:
    out = [pat]
    for c in pat.children:
        out.extend(_collect(c))
    return out


def _apply(rng: random.Random, root: Pat, target: Pat, kind: str) -> Pat | None:
    def rebuild(node: Pat) -> Pat | None:
        if node is target:
            return _mutate_node(rng, node, kind)
        for i, c in enumerate(node.children):
            new = rebuild(c)
            if new is not None:
                clone = copy.deepcopy(node)
                clone.children[i] = new
                return clone
        return None

    return rebuild(root)


def _mutate_node(rng: random.Random, node: Pat, kind: str) -> Pat | None:
    clone = copy.deepcopy(node)
    if kind == "swap_or_sep" and clone.kind in ("list", "or") and len(clone.children) == 2:
        clone.kind = "or" if clone.kind == "list" else "list"
        clone.amp = False
        return clone
    if kind == "add_child" and clone.kind in ("list", "or") and len(clone.children) == 2:
        clone.children.append(Pat("name", name="Hextra"))
        clone.amp = False
        return clone
    if kind == "over_destruct" and clone.kind == "name":
        return Pat("list", children=[Pat("name", name="Ha"), Pat("name", name="Hb")], intuit=clone.intuit, modal=clone.modal)
    if kind == "under_destruct" and clone.kind in ("list", "or") and clone.children:
        return Pat("name", name="Hwhole", intuit=clone.intuit, modal=clone.modal)
    return None
