# Design brief: `Rwcas.v`

You are given **the implementation and the specifications, and nothing else**. The predicates the specifications are stated in terms of (`value`, `is_rwcas`) are present but **empty** -- defined as `True`, which makes the specifications unprovable as they stand.

Designing them is the task. Decide what the client owns, what invariant protects the cell, and what ghost state connects the two, then fill the definitions in and prove the specifications against them. You may add definitions, resource algebras, typeclass fields, imports and helper lemmas. You may **not** change the program or any specification: those are the theorem.

## What you must prove

### `new_rwcas_spec`

```coq
Lemma new_rwcas_spec (n : Z) :
    {{{ True }}}
      new_rwcas #n
    {{{ γ l, RET l; is_rwcas γ l ∗ value γ n }}}.
```

### `read_spec`

```coq
Lemma read_spec (γ : gname) (v : val) :
    is_rwcas γ v -∗
      <<{ ∀∀ (n : Z), value γ n }>> read v @ ↑N <<{ value γ n | RET #n }>>.
```

### `write_spec`

```coq
Lemma write_spec γ v (q : Z) :
    is_rwcas γ v -∗
      <<{ ∀∀ (n : Z), value γ n }>> write v #q @ ↑N <<{ value γ q | RET #() }>>.
```

## Given definitions

The program is frozen. The predicates marked **(blank)** are yours to define; everything else is read-only.

- `new_rwcas`
- `read`
- `write`
- `rwcasG`
- `rwcasN`
- `value` **(blank -- yours to define)**
- `is_rwcas` **(blank -- yours to define)**

## Given lemmas (already proved -- use them)

- `is_rwcas_persistent`
