# Logically atomic triples

Logatom specs are their own genre. Misstating one is a classic multi-day sink — the
proof fails in ways that look like tactic problems for days before anyone questions
the spec — so the templates come first and the tactics come second.

## The canonical shape

```coq
<<< ∀ x, α x >>> e @ ↑N <<< β x, RET v >>>
```

- `α x` is the **abstract state** the operation observes, owned by the client.
- `β x` is the state after the commit.
- Everything between is invisible to the client: the operation appears to happen
  atomically at one instant.

## Is a logatom spec the right spec at all?

Ask before writing one. A logatom triple is right when clients must be able to
compose the operation with *their own* invariants over the abstract state. It is
overkill when a plain Hoare triple over a fixed invariant would do, and it is wrong
when the operation has no single linearization point and you have not identified a
prophecy or a helping protocol to supply one.

## The standard skeleton

```coq
iIntros (Φ) "AU".            (* the atomic update, not a plain precondition *)
...
iMod "AU" as (x) "[Hα Hclose]".   (* open the atomic update: gives you α x *)
(* either abort: *)
iMod ("Hclose" with "Hα") as "AU".
(* or commit: *)
iMod ("Hclose" $! v with "Hβ") as "HΦ".
```

Two rules that account for most failures:

1. **Open the atomic update exactly at the commit point, not before.** If you open it
   early you must abort on every path that does not commit, and the mask bookkeeping
   compounds.
2. **Abort and commit are different closes.** Aborting returns the same abstract
   state and gives you the atomic update back; committing consumes it and gives you
   the postcondition. Using the wrong one produces a mask error several steps later.

## Commit points are a sketch artifact

Identify the commit point **before proving**, in the sketch, and write it down. For a
`CmpXchg`-based operation it is the successful `CmpXchg`; for a read it is the read
itself; for an operation whose outcome depends on a value not yet determined, it is
not a fixed point at all, and you need one of the next two sections.

## Prophecy variables

Use when the linearization point is **in the future or outcome-dependent** — you must
decide "did this operation commit here?" before you know the answer.

```coq
iMod (new_proph) as (p pvs) "Hp".      (* allocate *)
wp_resolve with "Hp".                   (* resolve at the operation *)
```

The proof structure is: allocate the prophecy, case on the prophesied value to decide
whether this step commits, and resolve at the physical step that determines it.

## Helping

Use when **another thread commits your operation**. The atomic update travels through
the invariant: the operation registers a descriptor containing its atomic update, and
whichever thread performs the physical step commits it on the registerer's behalf.

The invariant must own the atomic update between registration and commit, which is
why this pattern needs an invariant that stores an `AU` — plan for it at sketch time,
because retrofitting it means restating the invariant.

## Mask bookkeeping

The single most common mechanical failure. Track it as arithmetic, not intuition:
which mask are you under, which namespace does each open remove, and is the atomic
update's mask disjoint from the invariants you have open around it.
