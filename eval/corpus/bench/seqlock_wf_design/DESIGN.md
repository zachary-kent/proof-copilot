# Design brief: `SeqlockWf.v`

You are given **the implementation and the specifications, and nothing else**. The predicates the specifications are stated in terms of (`b14`, `efd41`) are present but **empty** -- defined as `True`, which makes the specifications unprovable as they stand.

Designing them is the task. Decide what the client owns, what invariant protects the cell, and what ghost state connects the two, then fill the definitions in and prove the specifications against them. You may add definitions, resource algebras, typeclass fields, imports and helper lemmas. You may **not** change the program or any specification: those are the theorem.

## What you must prove

### `bd42_spec`

```coq
Lemma bd42_spec (n : nat) (src : loc) dq vs :
    length vs = n → n > 0 →
      {{{ src ↦∗{dq} vs }}}
        bcaf2 n #src
      {{{ v γ, RET v; src ↦∗{dq} vs ∗ efd41 v γ n ∗ b14 γ vs  }}}.
```

### `x51_spec`

```coq
Lemma x51_spec (γ : gname) (v : val) (n : nat) :
    n > 0 →
      efd41 v γ n -∗
        <<{ ∀∀ vs, b14 γ vs  }>> 
          f5 n v @ ↑N
        <<{ ∃∃ copy : loc, b14 γ vs | RET #copy; copy ↦∗ vs }>>.
```

### `fc50_spec`

```coq
Lemma fc50_spec (γ : gname) (v : val) (src : loc) dq (vs' : list val) :
    efd41 v γ (length vs') -∗
      src ↦∗{dq} vs' -∗
        <<{ ∀∀ vs, b14 γ vs  }>> 
          c4 (length vs') v #src @ ↑N
        <<{ b14 γ vs' | RET #(); src ↦∗{dq} vs' }>>.
```

## Given definitions

The program is frozen. The predicates marked **(blank)** are yours to define; everything else is read-only.

- `da0`
- `cb1`
- `bcaf2`
- `x3`
- `c4`
- `f5`
- `fbe10`
- `fb11`
- `x12`
- `b14` **(blank -- yours to define)** -- the client-facing logical value of the structure
- `efd41` **(blank -- yours to define)** -- the persistent handle a client holds on the structure

## Given lemmas (already proved -- use them)

- `efd41_persistent`
