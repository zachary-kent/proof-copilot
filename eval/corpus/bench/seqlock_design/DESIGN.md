# Design brief: `Seqlock.v`

You are given **the implementation and the specifications, and nothing else**. The predicates the specifications are stated in terms of (`b10`, `efd30`) are present but **empty** -- defined as `True`, which makes the specifications unprovable as they stand.

Designing them is the task. Decide what the client owns, what invariant protects the cell, and what ghost state connects the two, then fill the definitions in and prove the specifications against them. You may add definitions, resource algebras, typeclass fields, imports and helper lemmas. You may **not** change the program or any specification: those are the theorem.

## What you must prove

### `bd31_spec`

```coq
Lemma bd31_spec (n : nat) (src : loc) dq vs :
    length vs = n → n > 0 →
      {{{ src ↦∗{dq} vs }}}
        bcaf2 n #src
      {{{ v γ, RET v; src ↦∗{dq} vs ∗ efd30 v γ n ∗ b10 γ vs  }}}.
```

### `x34_spec`

```coq
Lemma x34_spec (γₕ : gname) (v : val) (n : nat) :
    n > 0 →
      efd30 v γₕ n -∗
        <<{ ∀∀ vs, b10 γₕ vs  }>> 
          f4 n v @ ↑N
        <<{ ∃∃ copy : loc, b10 γₕ vs | RET #copy; copy ↦∗ vs }>>.
```

### `fc32_spec`

```coq
Lemma fc32_spec (γₕ : gname) (v : val) (src : loc) dq (vs' : list val) :
    efd30 v γₕ (length vs') -∗
      src ↦∗{dq} vs' -∗
        <<{ ∀∀ vs, b10 γₕ vs  }>> 
          c3 (length vs') v #src @ ↑N
        <<{ b10 γₕ vs' | RET #(); src ↦∗{dq} vs' }>>.
```

## Given definitions

The program is frozen. The predicates marked **(blank)** are yours to define; everything else is read-only.

- `da0`
- `cb1`
- `bcaf2`
- `c3`
- `f4`
- `fbe7`
- `fb8`
- `b10` **(blank -- yours to define)** -- the client-facing logical value of the structure
- `efd30` **(blank -- yours to define)** -- the persistent handle a client holds on the structure

## Given lemmas (already proved -- use them)

- `efd30_persistent`
