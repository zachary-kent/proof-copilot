# Design brief: `M8f1e46.v`

This development's design is **given**: the implementation, the invariants, the ghost state and the helper lemmas are all present and correct. What is held out is the tactic work for the specifications below.

## What you must prove

### `cec21_spec`

```coq
Lemma cec21_spec (n : Z) :
    {{{ True }}}
      a0 #n
    {{{ γ l, RET l; afa20 γ l ∗ b9 γ n }}}.
```

### `x22_spec`

```coq
Lemma x22_spec (γ : gname) (v : val) :
    afa20 γ v -∗
      <<{ ∀∀ (n : Z), b9 γ n }>> f1 v @ ↑N <<{ b9 γ n | RET #n }>>.
```

### `fc23_spec`

```coq
Lemma fc23_spec γ v (q : Z) :
    afa20 γ v -∗
      <<{ ∀∀ (n : Z), b9 γ n }>> c2 v #q @ ↑N <<{ b9 γ q | RET #() }>>.
```

## Given definitions

These are frozen. Read them; do not change them.

- `a0` -- the constructor: allocates a fresh cell
- `f1` -- the read operation (a plain dereference)
- `c2` -- the write operation: CmpXchg against the value just read, with a prophecy
- `c3`
- `b4`
- `d5`
- `bb6` -- the namespace of the main invariant
- `x7` -- the namespace of the per-writer invariants
- `c8` -- reads the prophecy: did the CmpXchg succeed, and with what value
- `b9` -- the abstract state of the cell -- what a client owns and reasons about
- `ac10` -- the atomic update a writer holds
- `a11` -- the atomic update a reader holds
- `d12_inv` -- the per-writer invariant holding a pending atomic update, for helping
- `x13_inv` -- ties each registered request to its linearization flag
- `bad14` -- authoritative ownership of the request registry
- `ba15` -- fragmental ownership of a single request
- `eb16_inv` -- the main invariant, protecting the physical cell and the request registry
- `afa20` -- the client-facing "this value is a cell" predicate

## Given lemmas (already proved -- use them)

- `f17_update` -- allocates a new request in the registry
- `bfd18_agree` -- the authoritative registry agrees with a fragment
- `cd19` -- linearizes all pending writers while preserving the registry invariant

## Design notes from the author

> This example proves the correctness of a linearizable [f1]/[c2] cell
> implemented using just [f1] and [CmpXchg]. For a location [l] and value [v],
> [c2(l, v)] is implemented as [CmpXchg l !l v]. Obviously, if another thread
> changes the value stored in [l] between the load and [CmpXchg], then the
> [CmpXchg] fails and the write has no physical effect. However, this means that
> the failing write can linearize immediately before the succeeding conflicting write
> that caused the [CmpXchg] to fail. We prove that this implementation is logically
> atomic.
> 
> In the proof of the write spec, a prophecy is used by every writer to predict whether its
> [CmpXchg] will succeed. If the prophecy predicts that the operation will fail,
> then its linearization point (LP) is external, as the conflicting successful write
> will have to carry out its LP on its behalf. Thus, the failing write will have to
> store its atomic update in an invariant so that the
> successful write can carry out its LP and consume the update. A successful
> writer is obligated to consume every atomic update stored d in the invariant,
> linearizing all writers prophesied to fail.

