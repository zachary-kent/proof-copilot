# Design brief: `Mf6dd3f.v`

This development's design is **given**: the implementation, the invariants, the ghost state and the helper lemmas are all present and correct. What is held out is the tactic work for the specifications below.

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

These are frozen. Read them; do not change them.

- `da0`
- `cb1`
- `bcaf2` -- allocates a fresh big-atomic cell
- `c3` -- the write operation: bump the version, copy, bump again
- `f4` -- the read operation: a seqlock-style optimistic read, retried until the version is stable
- `d5`
- `x6`
- `fbe7`
- `fb8`
- `x9_own` -- authoritative ownership of the version history
- `b10` -- the abstract state of the cell -- the list of values a client owns
- `a11_own` -- a fragment of the version history, pinning one version's contents
- `a15`
- `e16_inv`
- `efd30`

## Given lemmas (already proved -- use them)

- `ef12_update`
- `ff13_alloc`
- `c14_agree`
- `ac19'`
- `ff18_agree`
- `ac19`
- `de20`
- `cbf21`
- `af22`
- `x23`
- `a25'`
- `a25`
- `b26`
- `eefe27`
- `ec28`
- `d29`
- `e33_inv`
