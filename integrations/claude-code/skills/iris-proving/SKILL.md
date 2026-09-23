---
name: iris-proving
description: Prove or debug a Rocq/Iris lemma interactively with the pcp proof-state tools (proof_open, proof_step, proof_ledger, proof_destruct, premise_search, verify_node) and the pcp prover norms. Use when writing or repairing an Iris proof by hand, when a spatial hypothesis goes missing, iFrame/iDestruct/iApply fails, or a pcp run handed off a stuck node.
allowed-tools: Bash(pcp skill show *) Bash(pcp trace *) Bash(pcp ledger *) Bash(pcp state *) Bash(pcp destruct *)
---

# Proving Iris lemmas with pcp

## The loop

Step the proof through the `pcp` MCP tools instead of editing the file and recompiling.
Paths are relative to the project root.

1. `proof_open(file, lemma)` -- a session id and the Iris goal, per hypothesis
   (spatial / intuitionistic / pure). `fast` (default) elaborates only the statements
   before the lemma: seconds, not minutes.
2. `proof_step(session, tactic)` -- one tactic sentence; the answer is what changed. On
   failure read the structured diagnosis before retrying. `mode="speculative"` does not
   move the session.
3. `proof_try(session, [t1, ..., t20])` -- when unsure between candidates, try them all
   at once and keep a survivor. Cheap; use it instead of guessing serially.
4. `proof_state(session, select=..., budget=...)` -- the goal under a token budget,
   diff-only by default; `select` ("HP,H*,spatial,mentions:γ,head:WP") pins what you need.
5. When the proof is written, `verify_node(file, lemma, body)` runs the same gate a pcp
   run uses (compile, `Print Assumptions` whitelist, no admits or escape hatches). Only
   then edit the `.v` file.

## When resources go wrong -- ask the ledger, do not guess

- `proof_ledger(session, "blame", hyp="HP")` -- what consumed `HP` and how to repair it
  (e.g. "framed at step 2 -- frame later, or split the goal first").
- `"where_did_it_go"` for the provenance of a hypothesis, `"leftovers"` for why
  `iFrame`/`done` fails, `"unused_at_qed"` for dead hypotheses, `"events"` for the log.
- `proof_trace(file, lemma)` replays an existing proof (or `script`) and returns the
  ledger events plus a session to query -- start here for a broken existing proof.
- `unknown` from the ledger means it cannot tell. Treat it as no answer, not a hint.

## Patterns, names, notations

- Never hand-write a nested `iDestruct` pattern: `proof_destruct(session, "H")`
  synthesises it from the hypothesis' structure; with `spec` it compiles your intent;
  with `apply=true` it runs it or says exactly where the pattern and the prop diverge.
- `premise_search(session, pattern="_ ↦ _")` or `query="big_sepL insert"` finds lemmas
  that apply at this goal. Search before inventing a lemma name.
- `notation_resolve(session, "|={E}=>")` -- what a notation unfolds to and which IPM
  tactics apply.

A tool answer with `"lost": true` means the Rocq process restarted: `proof_open` again
and replay; it is not a tactic failure. Without the MCP tools the CLI does the same
offline: `pcp trace FILE LEMMA -o t.jsonl`, `pcp ledger t.jsonl blame --hyp HP`,
`pcp state t.jsonl --select spatial`, `pcp destruct 'PROP'`.

## Norms

These are the norms pcp gives its prover workers, printed by the installed pcp. Parts
of them describe the worker protocol (returning a body, `contested`); interactively the
equivalent is: never change a statement or add a hypothesis to make a proof go through
-- if a statement is wrong, stop and tell the user why. Everything about Iris technique
applies to you as written.

!`pcp skill show prover`

For logically atomic triples (`<<< ∀ x, α x >>> e @ ↑N <<< β x, RET v >>>`,
`atomic_update`, `AU`) read `pcp skill show logatom` before touching the proof; when
choosing or strengthening an invariant, read `pcp skill show invariants`.
