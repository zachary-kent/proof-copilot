# Design brief: `M480dd7.v`

This development's design is **given**: the implementation, the invariants, the ghost state and the helper lemmas are all present and correct. What is held out is the tactic work for the specifications below.

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

These are frozen. Read them; do not change them.

- `da0`
- `cb1`
- `bcaf2` -- allocates a fresh big-atomic cell
- `x3`
- `c4` -- the write operation: bump the version, copy, bump again
- `f5` -- the read operation: a seqlock-style optimistic read, retried until the version is stable
- `d6`
- `x7`
- `c8`
- `b9`
- `fbe10`
- `fb11`
- `x12`
- `x13_own` -- authoritative ownership of the version history
- `b14` -- the abstract state of the cell -- the list of values a client owns
- `a15_own` -- a fragment of the version history, pinning one version's contents
- `bad19`
- `ba20`
- `ac23`
- `d24_inv`
- `ad25_inv`
- `x26_inv`
- `e28_inv`
- `efd41`

## Given lemmas (already proved -- use them)

- `ef16_update`
- `ff17_alloc`
- `c18_agree`
- `f21_update`
- `bfd22_agree`
- `cd27`
- `wp_array_copy_to'`
- `ff30_agree`
- `c31`
- `de32`
- `cbf33`
- `af34`
- `a36'`
- `a36`
- `b37`
- `eefe38`
- `ec39`
- `d40`
- `da43`
- `c44`
- `be45`
- `fc46`
- `x47`
- `fbe48`
- `x49`
