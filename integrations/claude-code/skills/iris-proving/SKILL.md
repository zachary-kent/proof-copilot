---
name: iris-proving
description: Prove or debug a Rocq/Iris lemma interactively with the pcp proof-state tools (proof_open, proof_step, proof_trace, proof_ledger, proof_destruct, proof_inv, proof_expect, premise_search, verify_node) and the pcp prover norms. Use when writing or repairing an Iris proof by hand, when a spatial hypothesis goes missing, iFrame/iDestruct/iApply fails, or a pcp run handed off a stuck node.
allowed-tools: Bash(pcp skill show *) Bash(pcp trace *) Bash(pcp ledger *) Bash(pcp state *) Bash(pcp destruct *) Bash(pcp tools *)
---

# Proving Iris lemmas with pcp

## The loop

Step the proof through the `pcp` MCP tools instead of editing the file and recompiling.
Paths are relative to the project root.

Every answer has the same head: `ok`, `what` (one line), `where` (`file`, `line`,
`column`, `sentence`, `step`), `goal` (the rendered goals: after the step on success,
the goals the failing sentence met on failure) and `next` (concrete next calls). A
failure adds `error` (the cause is kept, even when cut), `timed_out`, or `lost`. Read
`what` and `next` first; the rest is detail.

1. `proof_open(file, lemma)` -- a session id and the Iris goal, per hypothesis
   (spatial / intuitionistic / pure). `fast` (default) elaborates only the statements
   before the lemma: seconds, not minutes.
2. `proof_step(session, tactic)` -- one tactic sentence; the answer is what changed.
   When the goals change, `goal_list` lists them in order with their shapes (`new` /
   `kept`, which is `focused`, what `closed`): check it after `wp_apply`, `iSplit`,
   `destruct` instead of guessing where a side goal went. `warnings` flags a success that
   is often a mistake. On failure read `diagnosis` (with `diagnosis_class` and
   `diagnosis_confidence`: a `low` one is a lead, not an answer) before retrying; if its
   class was wrong, `diagnosis_feedback(diagnosis_id, actual=...)`. `mode="speculative"`
   does not move the session. Several sentences in one call run one by one: a failure
   names the failing one (`chain`) and the sentences before it stay committed. A failing
   `t; [t1|...|tn]` or `t; first tac` says in `compound` whether the head failed or which
   branch failed on which goal. File paths are relative to the pcp project, even when the
   host started in the git root.
   A timeout is a budget, not a verdict: `timeout` in the answer has the per-sentence budget,
   the wall time and the machine's load. Rerun with `timeout=120` before changing a sentence
   `coqc` accepts. When no goal is focused but the proof is not finished, `open_ends` says why
   (a bullet sibling still open, shelved goals, an uninstantiated evar) and what `Qed` would say.
3. `proof_try(session, [t1, ..., t20])` -- when unsure between candidates, try them all
   at once and keep a survivor. Cheap; use it instead of guessing serially. A failed row
   that is a near variant of a survivor says what differs (`vs_survivor`).
4. `proof_state(session, select=..., budget=...)` -- the goal under a token budget,
   diff-only by default; `select` ("HP,H*,spatial,mentions:γ,head:WP") pins what you need.
5. `proof_expect(session, "WP ! #(l +ₗ 1) {{ v, Φ v }}")` -- assert the goal's shape
   before relying on it (`_`/`?x` holes); a mismatch names the differing subterm.
   `proof_inv(session, "Hinv")` generates the `iInv ... as (...) "(>H1 & ...)"` pattern
   from the invariant's definition -- never hand-write one.
6. When the proof is written, `verify_node(file, lemma, body)` runs the same gate a pcp
   run uses (compile, `Print Assumptions` whitelist, no admits or escape hatches); a
   finished `proof_step` puts the exact call in `next`. Only then edit the `.v` file.
   `proof_close(session)` when you are done with a session.

## When resources go wrong -- ask the ledger, do not guess

- `proof_ledger(session, "blame", hyp="HP")` -- what consumed `HP` and how to repair it
  (e.g. "framed at step 2 -- frame later, or split the goal first").
- `"where_did_it_go"` for the provenance of a hypothesis, `"leftovers"` for why
  `iFrame`/`done` fails, `"unused_at_qed"` for dead hypotheses, `"events"` for the log.
- `proof_trace(file, lemma)` replays an existing proof (or `script`) and returns the
  ledger events plus a session to query -- start here for a broken existing proof. A
  failure's `where` has the sentence and its line/column, `goal` the goal it met; the
  session sits right before it, so `proof_step` a replacement there. After editing the
  file, `proof_trace` again: only the sentences from the first changed one rerun
  (`replayed_from`, `saved_ms`). `events` holds only the last steps' ledger events
  (`events="all"` or `proof_ledger(session, "events")` for the whole log). A long replay
  answers `replaying: true` after `wait_s` (90 s) instead of timing out in the client; the
  same call again waits for it.
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
and replay; it is not a tactic failure. Without the MCP tools (plugin not loaded yet in
this session) the same tools run from Bash through a per-project daemon that keeps the
sessions alive between commands: `pcp tools call proof_open '{"file": "F.v", "lemma": "L"}'`,
then `pcp tools call proof_step --arg session=s1 --arg 'tactic=iIntros "H".'`; every tool
and argument is the same (`pcp tools list`), and `pcp tools stop` ends it. Offline, on a
recorded trace: `pcp trace FILE LEMMA -o t.jsonl`, `pcp ledger t.jsonl blame --hyp HP`,
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
