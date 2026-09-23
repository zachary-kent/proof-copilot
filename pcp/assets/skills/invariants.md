# Invariants

The invariant catalog is **interface rank**. It is frozen before proof work begins,
and getting it wrong is the most expensive mistake in the system: a bad invariant is
discovered many steps away from where it was chosen, and the rework is a whole
subtree.

## An invariant fails in two directions

- **Too strong → unmaintainable.** Some program step cannot restore it before
  closing. The proof dies at an `iInv` *close* site, many steps after the design
  error. Symptom: an undischargeable goal at the close, with resources that cannot be
  reassembled.
- **Too weak → insufficient.** Opening it does not yield what the use site needs. The
  proof dies at the *open* site. Symptom: you open the invariant and immediately want
  something it does not contain.

Both become churn in the amendment lattice later, so this is the highest-leverage
audit in the system. Spend attention here, where it is cheapest.

## Every invariant owes an allocation witness

An interface nobody can inhabit makes every client lemma vacuously provable, and the
development rots invisibly. So each invariant carries an inhabitation obligation as a
sibling node — for an Iris invariant, the standard allocation lemma:

```coq
Lemma I_alloc : ⊢ |==> ∃ γ, I γ.
```

This must be a node, not a note. It fails loudly and immediately or it does not
protect you at all.

## Checklist when reviewing an invariant

1. **Allocation.** Can it be established at all, from resources available at
   allocation time?
2. **Per-step preservation.** For each atomic step that opens it: is there enough in
   the invariant plus the local resources to restore it before closing? Answer this
   in prose at sketch time — the machine cannot check it without the symbolic state
   the proof itself computes.
3. **Use sites.** Does opening it yield what each use site actually needs, or only
   something adjacent?
4. **Ghost state.** Which resource algebra, what does each ghost name mean, and which
   fragments are authoritative? An invariant whose ghost story is vague is an
   invariant that will be amended.
5. **Masks.** Which namespace, and is it disjoint from everything opened around it?
6. **Laters.** Everything under `inv` comes back guarded. Is the use site prepared to
   strip a `▷`, or does it need timelessness?

## Preservation probes are research, not a promise

Auto-checking that each atomic step can re-establish each invariant requires the
pre-step symbolic state that the proof itself computes. Do not plan around having it.
The allocation witness is the sentinel that genuinely helps here, and it is cheap.
