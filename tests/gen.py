"""Random Iris-prop and intro-pattern generation, for property testing.

Two generators that mirror each other:

* :func:`random_skel` builds a connective skeleton, which ``Skel.to_notation``
  renders to real Iris notation.  Parsing that back must recover the tree.
* :func:`random_pattern_for` builds an intro pattern that *should* fit a skeleton,
  and :func:`mutate_pattern` breaks it in one specific way, so the aligner can be
  checked for both false negatives and false positives.

Deliberately dependency-free (no Hypothesis): the shapes we care about are small and
enumerable, and a seeded ``random`` keeps failures reproducible from the seed alone.
"""

from __future__ import annotations

import random
from dataclasses import replace

from pcp.core.ipm.pattern import Pat, compile_auto
from pcp.core.ipm.skeleton import Skel

#: Atoms drawn from what Iris proofs actually contain.
ATOMS = [
    "P", "Q", "R", "P v", "Φ v", "l ↦ v", "l ↦{#q} v", "own γ (● n)", "own γ (◯ n)",
    "inv N (I γ)", "is_lock γ lk R", "l ↦∗ vs", "na_own p E", "£ n",
    "cinv_own γ q", "sts_own γ s T", "auth_own γ a",
    "WP e {{ Φ }}", "meta_token l ⊤", "pointsto l dq v",
]
PURE = ["n = 3", "v ≤ 3", "l ≠ l'", "0 < n", "is_Some (m !! i)", "vs !! i = Some v", "v = #()"]
BINDERS = ["x", "y", "γ", "v", "n", "q", "vs", "s"]
MASKS = ["⊤", "⊤ ∖ ↑N", "E", "E ∖ ↑N", "∅"]

BRANCHING = ["sep", "and", "or"]
TIGHT = ["later", "intuitionistically", "persistently", "except0", "affinely", "absorbingly"]
LOOSE = ["bupd", "fupd"]
ARROW = ["wand", "impl", "iff", "wand_iff"]


def random_skel(rng: random.Random, depth: int = 3, *, arrows: bool = True) -> Skel:
    """A random prop skeleton.  ``depth`` bounds nesting, not size."""
    if depth <= 0:
        return _leaf(rng)
    roll = rng.random()
    if roll < 0.34:
        kind = rng.choice(BRANCHING)
        n = rng.choice([2, 2, 2, 3, 4])
        kids = [random_skel(rng, depth - 1, arrows=arrows) for _ in range(n)]
        # These connectives associate to the right, so `P ∗ (Q ∗ R)` *is*
        # `P ∗ Q ∗ R` and the parser flattens the right spine.  Shield only the last
        # child, so left-nested shapes -- which are genuinely different terms -- are
        # still generated and still round-trip.
        kids[-1] = _shield(kids[-1], kind)
        return Skel(kind, kids)
    if roll < 0.50:
        return Skel(rng.choice(TIGHT), [random_skel(rng, depth - 1, arrows=arrows)])
    if roll < 0.62:
        kind = rng.choice(LOOSE)
        binders = [rng.choice(MASKS)] if kind == "fupd" else []
        return Skel(kind, [random_skel(rng, depth - 1, arrows=arrows)], binders=binders)
    if roll < 0.76:
        kind = rng.choice(["exists", "forall"])
        n = rng.choice([1, 1, 2])
        return Skel(kind, [random_skel(rng, depth - 1, arrows=arrows)], binders=rng.sample(BINDERS, n))
    if roll < 0.88 and arrows:
        return Skel(rng.choice(ARROW), [random_skel(rng, depth - 1, arrows=arrows) for _ in range(2)])
    return _leaf(rng)


def _leaf(rng: random.Random) -> Skel:
    if rng.random() < 0.25:
        text = rng.choice(PURE)
        return Skel("pure", [Skel("atom", text=text)], text=text)
    return Skel("atom", text=rng.choice(ATOMS).strip())


def _shield(node: Skel, parent_kind: str) -> Skel:
    """Keep a child from being flattened into its parent by the n-ary rule."""
    if node.kind == parent_kind:
        return Skel("later", [node])
    return node


# ------------------------------------------------------------------------ patterns

def random_pattern_for(rng: random.Random, skel: Skel) -> Pat:
    """A pattern that fits ``skel`` -- the compiler's output, with random names."""
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
#: Mutations that produce a *legal* pattern -- ∗/∧/∨ associate right, so a shorter
#: pattern is fine and the aligner must not flag it.  False positives cost as much
#: as false negatives here: a spurious "mismatch" sends the agent to the wrong place.
LEGAL_MUTATIONS = ("drop_child",)
MUTATIONS = CAUGHT_MUTATIONS + LEGAL_MUTATIONS


def mutate_pattern(rng: random.Random, pat: Pat, kinds: tuple[str, ...] = CAUGHT_MUTATIONS) -> tuple[Pat, str] | None:
    """Break a fitting pattern in exactly one way the aligner must catch."""
    nodes = _collect(pat)
    rng.shuffle(nodes)
    for kind in rng.sample(list(kinds), len(kinds)):
        for node in nodes:
            mutated = _apply(rng, pat, node, kind)
            if mutated is not None:
                return mutated, kind
    return None


def _collect(pat: Pat) -> list[Pat]:
    out = [pat]
    for c in pat.children:
        out.extend(_collect(c))
    return out


def _apply(rng: random.Random, root: Pat, target: Pat, kind: str) -> Pat | None:
    import copy

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

    if target is root:
        return _mutate_node(rng, root, kind)
    return rebuild(root)


def _mutate_node(rng: random.Random, node: Pat, kind: str) -> Pat | None:
    import copy

    clone = copy.deepcopy(node)
    if kind == "swap_or_sep" and clone.kind in ("list", "or") and len(clone.children) >= 2:
        clone.kind = "or" if clone.kind == "list" else "list"
        return clone
    if kind == "drop_child" and clone.kind in ("list", "or") and len(clone.children) >= 3:
        clone.children.pop(rng.randrange(len(clone.children)))
        return clone
    if kind == "add_child" and clone.kind in ("list", "or") and len(clone.children) >= 2:
        clone.children.append(Pat("name", name="Hextra"))
        return clone
    if kind == "over_destruct" and clone.kind == "name" and not clone.pure:
        return Pat("list", children=[Pat("name", name="Ha"), Pat("name", name="Hb")])
    return None
