# proof-copilot — design and development plan

> **This is the design record, not the manual.** It was written before the code and
> kept as the rationale behind it: why each part is shaped the way it is, including
> ideas that were deferred or dropped. Where it disagrees with the code, the code and
> [`../ARCHITECTURE.md`](../ARCHITECTURE.md) are authoritative; [`../../README.md`](../../README.md)
> is how to use the tool. Code comments cite it by section ("PLAN.md 8.11"). The
> phase plan (§12) and repo layout (§15) are historical.

Original status: draft v1, 2026-08-28, before any code existed.

## 0. Thesis

Two separable products live under this name. Keep them separable.

**`pcp-state`** — an Iris-aware, structured, diffable, per-hypothesis proof-state layer over Rocq.
Exposed as a Python library, a CLI, and an MCP server. This is the durable asset: it outlives
any harness, any model, any orchestration framework.

**`pcp-orch`** — an obligation-graph orchestrator that turns the manual loop (frontier model holds
a dependency graph in its head, dispatches tightly-scoped tasks to cheap workers, maximizes
parallelism) into a program with durable state.

Both accept work at any granularity — an entire development, or a single fixed lemma the user
wants proved, which may be open. The control flow is the same recursive procedure either way:
given a frozen statement, dispatch it if judged simple, otherwise decompose and recurse (§8.2).

The design below is speculative and will be tuned. One commitment is not: the common workflow — a
lemma the user already has high-level intuition for, with the orchestrator doing nothing cleverer
than managing parallel worker dispatch — must work every time. That workflow is the product; the
ambitious machinery is progressive enhancement behind feature flags, and §8.11 defines the
degenerate pipeline that owns the reliability budget.

Cost and wall-clock are the binding constraints throughout — the operator is a PhD student, not a
lab with a token firehose. Three rules recur below. **Deterministic before model:** everything a
program can do, a program does — the gate, the sentinels, the impact reports, the ledger, replay,
liveness, staleness are all code, and a model is the last resort, for judgment only. **No model
ever reviews a success:** the kernel already did (§11). **Saturate the flat-rate window:**
subscription capacity is the workhorse; metered frontier tokens buy only decomposition and
adjudication.

Two claims drive every design decision below.

**Claim 1 — the lemma statement is the interface contract, and `Admitted` is a type-checked
stub.** To be precise about status: an admit is *unsound* — it is an axiom by another name, and
the development is only a proof once every admit is gone and `Print Assumptions` is clean. The
useful property is narrower and structural. Because `Qed` proofs are opaque, a proof written
against an admitted lemma can depend only on its *statement*, never on the missing body — so the
work done against the stub is exactly the work that survives once the stub is filled, provided the
statement itself does not change (statement renegotiation is the `contested` path, §8.5). In
general software engineering, parallelizing a decomposition is hard because the interfaces are
informal and the mocks are lies; here the interface either type-checks or does not, and the stub
cannot leak an implementation. Therefore **every node whose statement type-checks is dispatchable
immediately, in parallel, regardless of where it sits in the graph** — with the development's
validity deferred, not corrupted, until the last admit is discharged. Parallelism is bounded by
decomposition rate and token budget, not by graph depth. And completion has a machine oracle:
`Qed` plus a clean `Print Assumptions`. Design the orchestrator around that, not around a generic
workflow DAG. (One exception class: obligations that must be transparent — `Defined`, definitions
that dependents must *compute* with — cannot be stubbed by an admit. Mark those nodes
`non-mockable`; they genuinely block their dependents and are scheduled first. §8.1.)

**Claim 2 — Iris debugging failures are resource-accounting failures.** "One spatial hypothesis
gets eliminated by some tactic, but is needed by another tactic many steps later" is not a
reasoning failure; it is a bookkeeping failure. Bookkeeping over 200 steps is exactly what a
machine does well and an LLM does badly. The flagship feature is therefore a **spatial resource
ledger**: a per-step record of which hypotheses were consumed, produced, renamed, split, or
framed, so that "`H` is not available at step 47" is answered with

> `H` was consumed at step 12 by `iDestruct "H" as "[H1 H2]"`; `H2` was then consumed at step 19
> by `iApply wp_store`. `H1` is still live.

instead of a 200-line goal dump the model has to re-derive the answer from.

---

## 1. Problem analysis: where the leverage actually is

Failure taxonomy for LLM agents in Iris, roughly in order of how much time they waste:

1. **Premature consumption.** A spatial hypothesis is eliminated early and needed later. The agent
   cannot see *when* it went away, only that it is gone.
2. **Leftover spatial context.** `iFrame` / `done` / `iApply` fails because the spatial context is
   not empty. The agent sees "cannot solve" and starts guessing.
3. **Mask arithmetic.** `↑N ⊆ E`, `E ∖ ↑N`, invariant open/close pairing, `iInv` under the wrong
   mask. Purely mechanical, and agents get it wrong constantly.
4. **Later / update modality timing.** Missing `iNext`, `iMod` at the wrong point, `▷` depth
   mismatch between hypothesis and goal.
5. **Persistent vs spatial confusion.** `iDestruct` on a persistent hypothesis keeps it; on a
   spatial one it does not. Agents mispredict duplicability, and the answer is one typeclass
   resolution away.
6. **Retrieval.** Wrong lemma name, wrong instance. The Iris/stdpp corpus is large with
   non-obvious naming; agents hallucinate plausible names.
7. **Context pollution.** Iris goals are enormous — WP goals carry whole program terms, invariant
   bodies are multi-line. Dumping the full state every step destroys the context window.

Every item is (a) resource accounting, (b) modality/mask arithmetic, or (c) retrieval. All three
are *tool* problems, not *model* problems. That is the whole design brief. Nothing here requires a
better prover; it requires the state to be legible.

---

## 2. Architecture

```
┌──────────────────────────────────────────────────────────────┐
│ Layer 3  orchestrator (frontier model + pcp-orch)            │
│          obligation graph · dispatch · escalation · gates    │
└──────────────────────────┬───────────────────────────────────┘
                           │ MCP / CLI / adapter
┌──────────────────────────▼───────────────────────────────────┐
│ Layer 2  pcp-mcp  ·  pcp CLI                                 │
│          small tool surface, budgeted rendering              │
└──────────────────────────┬───────────────────────────────────┘
┌──────────────────────────▼───────────────────────────────────┐
│ Layer 1  pcp-core (Python)                                   │
│   session   pet-server pool, sandboxing, timeouts            │
│   trace     step-by-step capture, deterministic replay       │
│   ipm       Iris context model: parser (v1) / reflector (v2) │
│   ledger    resource provenance, structural diff, blame      │
│   digest    elision, content-addressed prop store            │
│   search    premise retrieval, notation resolution           │
└──────────────────────────┬───────────────────────────────────┘
                           │ pytanque JSON-RPC
┌──────────────────────────▼───────────────────────────────────┐
│ Layer 0  pet-server (coq-lsp) ── Rocq ── Iris / stdpp        │
└──────────────────────────────────────────────────────────────┘
```

### Layer 0 choice: petanque, not SerAPI, not raw coqtop

Petanque (shipped with coq-lsp, driven from Python via `pytanque`) is the right substrate:

- **State ids.** Every proof state is a handle you can return to. This makes tactic-by-tactic
  tracing and backtracking cheap.
- **Speculative execution.** `petanque/run` from a state without committing to a file edit — lets
  you fan out N candidate tactics from one state and report which survive.
- **`state/hash` and `state/eq`.** Client-side state dedup and loop detection: an agent applying a
  no-op tactic in a cycle is detectable mechanically.
- **`premises`** for retrieval, **`ast`** for statement comparison in the integrity gate.
- It is what `rocq-mcp` already builds on, so the ground is tested.

Keep `coqc` as a second path for the final integrity check (whole-file compile, `Print Assumptions`),
and coq-lsp document-level goals as a fallback for whole-file offline annotation runs
(the Alectryon-style use case). Isolate all three behind one adapter module — this ecosystem churns.

### Layer 1 choice: Python

`pytanque` and CoqPyt already exist; the MCP Python SDK is mature; this layer is glue, not compute.
The hot path is Rocq, not you. Do not write this in OCaml for performance reasons that do not exist.

---

## 3. The Iris proof-state model

This is the core data structure. Everything else is a view over it.

### 3.1 Two acquisition paths

**Primary path — the reflected dump, spiked first.** The Ltac2 `iDump` (v2 below) is comparable
effort to a robust printer parser and is version-proof; the one open question is whether tactic
message output is cleanly capturable through petanque `run`. That spike is Phase 2, week 1. Only
if it fails does the printer parser get built.

**Fallback — printer parsing.** Petanque returns a Coq goal whose `ty` is the IPM notation
render. An Iris goal prints as:

```
  <ordinary Coq hypotheses>
  ============================
  "Hinv" : inv N (I γ)                     ← intuitionistic context
  --------------------------------------□
  "Hl" : l ↦ v                             ← spatial context
  --------------------------------------∗
  WP e {{ Φ }}                             ← goal
```

Both separator lines are omitted when the corresponding context is empty, so handle all four
shapes. Cheap, works on day one, and layout-fragile.

Cheap but layout-fragile; per-version golden tests required. Either way the printed goal is
kept as an untrusted display fallback.

**v2 — the reflected dump.** An Ltac2 tactic `iDump` that matches
`envs_entails (Envs ?Γp ?Γs ?c) ?Q`, walks the two `env PROP` lists, and emits one delimited record
per hypothesis. This is not layout-dependent, survives Iris version bumps, and — critically — lets
you set printing options *per hypothesis*: print one hypothesis with `Set Printing All` while
everything else stays folded.

`iStopProof` (which reifies the IPM goal back into an ordinary `⊢` entailment) is a useful third
view for serialization and for handing a stable term to retrieval.

### 3.2 Data model

Versioned JSON, one record per step:

```json
{
  "step": 47,
  "state_id": 1183,
  "tactic": "iDestruct \"HΦ\" as \"[H1 H2]\"",
  "goals": [{
    "goal_id": "g0",
    "pure": [{"names": ["σ"], "ty": "state", "hash": "p:4f1a"}],
    "intuitionistic": [
      {"id": "Hinv", "prop": "inv N (I γ)", "hash": "h:9c2e", "persistent": true}
    ],
    "spatial": [
      {"id": "H1", "prop": "l ↦ v", "hash": "h:3ab0", "persistent": false, "affine": true}
    ],
    "goal": {"prop": "WP e {{ Φ }}", "hash": "h:77d1"},
    "modality": {
      "mask": "⊤ ∖ ↑N",
      "laters": 1,
      "fupd": true,
      "wp": {"expr_hash": "e:12bc", "expr_summary": "CmpXchg #l #0 #1"}
    }
  }]
}
```

Three things worth noting.

**The `modality` block is first-class.** Mask and later-depth are extracted into fields, not left
inside a printed blob. Mask arithmetic is failure mode #3 and it is entirely mechanical; once it is
a field, you can diff it, assert on it, and tell the agent "you are under mask `⊤ ∖ ↑N` but
`wp_store` needs `↑N ⊆ E`".

**Everything is content-addressed.** Props live once in a side table keyed by hash; steps reference
hashes. In a 300-step proof where a large invariant sits untouched, you store one copy, not 300 —
and rendering can say "unchanged since step 4" instead of reprinting it.

**Props carry their connective skeleton** — the ∗ / −∗ / ∃ / ⌜⌝ / □ / ▷ tree — alongside the
printed form. That skeleton is what turns `iDestruct`-pattern handling (§7) into a deterministic
compile instead of a model guess.

---

## 4. The resource ledger — the flagship feature

### 4.1 Structural diff

For each step, match the previous context against the next:

| condition                      | event      |
|--------------------------------|------------|
| same name, same hash           | unchanged  |
| same hash, different name      | **rename** |
| same name, different hash      | **update** |
| in prev, not in next           | **consume**|
| in next, not in prev           | **produce**|

Then attribute: `produce(step, tactic, from=[consumed ids])`. Matching is **name-first,
hash-second**: IPM names are unique within a context and are the primary key; hashes distinguish
a rename (`iDestruct "H" as "H'"`) from destroy-and-create — and matter because identical printed
props are routine in Iris (fractional halves, duplicate `own` fragments). Hashes are computed
**modulo evar names**: Iris proofs are evar-dense, and instantiating an evar reprints hypotheses
no tactic touched, so a step whose only differences are such reprints is classified `Instantiate`,
never consume/produce. Steps that spawn sibling goals (`iSplit`, `wp_bind`, destructing a
disjunction) record **goal parentage**, and the ledger's guarantees are scoped to
single-focused-goal steps — a worker discipline the prover skill enforces.

Event vocabulary: `Intro · Consume · Produce · Split · Rename · Instantiate · Frame · Persist` (spatial →
intuitionistic, e.g. `iDestruct ... as "#H"`) `· Specialize · ModIntro · MaskChange(E₁→E₂) ·
LaterIntro`.

### 4.2 Queries exposed to the agent

- `where_did_it_go(hyp)` — the full provenance chain for a hypothesis, forwards and backwards.
- `blame(failing_step, needed_hyp)` — the step and tactic that consumed what the failing step
  needs, plus a repair class: *split differently* / *frame later* / *it is `Persistent`, duplicate it*.
- `leftovers(step)` — spatial hypotheses still live. Surfaces failure mode #2 *before* the agent
  hits `done` and gets an opaque error.
- `first_use(hyp)` / `last_use(hyp)`.
- `unused_at_qed` — resources never consumed. Usually a sign the *statement* is over-strong, which
  is orchestration-relevant signal (see §8, `contested`).

### 4.3 The persistence oracle

For each spatial hypothesis, ask Rocq whether `Persistent P` and `Affine P` resolve at that state
(one typeclass query, speculative, no commit). If persistent, the agent never has to reason about
consuming it. This is a two-line feature that removes an entire failure category.

### 4.4 Honesty requirement

Exotic tactics (`iInduction`, `iLöb`, hand-rolled `iSpecialize` patterns, custom IPM tactics in
your own project) will defeat the matcher. When matching is ambiguous the ledger must emit
`unknown` and say so. **A confidently wrong provenance chain is worse than no chain**, because the
agent will trust it and spend twenty turns in the wrong place.

---

## 5. Context economy

Per-hypothesis granularity, as requested. Every render passes through a budget.

Controls on the render call:
- `select` — id globs (`"H*"`), classes (`spatial`, `intuitionistic`, `changed`), or predicates
  (`mentions:γ`, `head:WP`).
- `mode` — `full | folded | summary | hash-only`, settable per selection.
- **auto-fold** — any prop over N lines renders as `⟨fold:a3f1 · inv N (…) · 24 lines⟩`, expandable
  by id in one call.
- **diff-only by default** — after the first step, render what changed plus a one-line manifest of
  what did not.
- **relevance filter** — given the failing tactic or lemma, keep hypotheses whose head symbols
  intersect the goal's; demote the rest to the manifest.
- **notation control** — render one hypothesis with notations off to disambiguate `∗` from `*`,
  without disturbing the rest.

Make elision *visible*: every render ends with `rendered 8/41 hypotheses · 1.2k/4k token budget`.
A model that knows it is looking at a partial view asks for more; a model that does not, hallucinates.

---

## 6. Sandboxing and robustness

- pet-server **pool** with per-call wall-clock and RSS caps. Kill and restart on divergence.
- **The physical ceiling is Rocq, not the rate window.** A pet-server with Iris loaded costs on
  the order of 1–2 GB RSS and executes tactics serially, so raw process count caps at a handful
  per machine — and `petanque/start` re-elaborates the file prefix, so spawning is minutes, not
  milliseconds. Workers therefore multiplex as immutable state-ids over a few shared pet-server
  processes (petanque states make this nearly free), and each worker builds in an isolated dir
  over a read-only cached dependency switch, so parallel workers never race on `.vo` artifacts.
  The measured session ceiling is part of the §8.11 contract.
- Typeclass resolution in Iris can loop. Wrap steps in `Timeout`, and on failure capture
  `Set Typeclasses Debug` output — that trace is itself a good diagnostic to hand the agent.
- LRU state table; `state/hash` for loop detection (agent repeating a no-op — detect it and say so).
- **Deterministic replay.** A trace is (root state, tactic list). Everything else is derived and
  cacheable by hash, so re-running a trace after a tool change is free for the unchanged prefix.
- **Context compaction is safe because the transcript is a cache, not the record.** All durable
  state lives outside the model context — the graph in SQLite, proof states behind
  content-addressed ids. So both roles compact aggressively, and the harness does it
  deterministically rather than asking a model to summarize itself: the orchestrator rehydrates
  from the graph plus a short running summary; a worker's history compacts to the frozen
  statement, the intent brief, the ledger event log, and the current state — old goal renders
  drop, re-fetchable by hash if ever needed.
- **Heartbeats and the deadline ladder.** Progress is measured, not asserted: a new state hash
  is the heartbeat. One-shot runners (`codex exec`, `claude -p`) have no mid-flight channel, so
  for them the ladder is: soft deadline → kill → requeue with the partial trace as evidence. An
  interactive runner (a Claude Code session) gets one ping first — current goal, plan, blocker,
  one line each — and one extension if the reply shows progress. With surplus subscription
  window, stragglers are raced regardless: re-dispatch, keep whichever finishes first.

---

## 7. Tool surface (MCP)

Keep it small. Every tool is a place the model can get lost, and every tool needs an ablation
showing it earns its context (§13).

**State and trace**
- `proof_open(file, lemma | position)` → session, root state, initial IPM state
- `proof_step(session, tactic, mode = commit | speculative)` → new state + ledger delta + structured
  diagnosis on error
- `proof_trace(file, lemma, script?)` → the tactic-by-tactic dump, with `select` / `mode`
- `proof_state(session | step, select, mode)` → budgeted render
- `proof_ledger(session, query)` → §4.2
- `proof_try(session, tactics[])` → speculative fan-out from one state (petanque caps at ~20),
  returns which survive and the resulting states. Very high value per token.
- `proof_destruct(session, hyp, spec | auto)` → structured destructuring. Complex intro patterns
  are a known agent choke point, and they are entirely mechanical given the prop's connective
  skeleton (§3.2): with `auto`, synthesize the `iDestruct` pattern from the skeleton; with a
  structured `spec` (a name per conjunct, pure/persistent/later markers as fields), compile it to
  the pattern string. On failure, align the pattern tree against the prop tree and report the
  exact mismatch point. The same compiler serves `iIntros`. No model ever hand-assembles a nested
  pattern string — and the diagnosis is not opt-in: any `proof_step` whose tactic is
  pattern-bearing (`iDestruct`, `iIntros`, `iMod … as`, specialization patterns) that fails
  returns the same alignment report automatically — the prop's skeleton, the pattern's tree, and
  the first mismatch — so the agent examines the object and the pattern every time by
  construction, not by discipline. The same aligner powers **unification-failure reports**: a
  failed `iApply` / `wp_apply` / `iFrame` returns the lemma's specialized conclusion rendered
  against the goal, the first mismatch point, and the premises that would remain — the single
  most common worker failure loop, answered structurally instead of by a goal dump.

**Search**
- `premise_search(session, pattern | nl_query, scope)` → `Search` / `SearchPattern` evaluated at the
  current state, plus source-grep passthrough; an embedding index is not built unless measured retrieval
  failures justify it
- `notation_resolve(session, token)` → what `={E}=∗` means, what it unfolds to, which IPM tactics apply

**Integrity**
- `verify_node(node)` → §8.7

**Deliberately not tools:** `prove_this_lemma`, `fix_this_proof`. Those are agent jobs. A tool that
tries to be an agent is a tool you cannot ablate.

---

## 8. Orchestration: the recursive freeze→prove pipeline

An agent-built development can be fully `Qed`-clean and still worthless, because the kernel checks
proofs, not statements. Agents make proofs go through by adding hypotheses, weakening conclusions,
or quietly editing definitions — no admit appears, and the unsoundness lives entirely in statement
drift. Two more observed failures compound it: a lemma refuted mid-flight poisons every transitive
dependent, and effort leaks into provable-but-useless lemmas ("productive procrastination"). The
design answer to all three: **split the statement from the proof, give them separate lifecycles,
freeze statements before proofs are attempted, and enforce the freeze deterministically — by
assembly, not by instructions to the model.** The control flow that runs inside this machinery
is one recursive procedure (§8.2).

### 8.1 The obligation graph: two ledgers

A **node** couples a *statement* (a spec-side artifact) with its *proof attempts* (worker-side
artifacts). The two have separate lifecycles:

```
statement:  proposed → audited → frozen@e ──amend──▶ frozen@e+1
                                    └────────────▶ refuted   (machine-checked; terminal)

proof:      open → claimed → qed → gated → integrated        (per statement epoch)
                      └──▶ contested(evidence) | stuck(evidence, lemma requests)
```

Node metadata: owner, rank (root / interface / local), epoch, attempts, cost, budget, mockability
(§0), closure hash. Edge A→B = A's proof references B, *pinned to B's epoch*. A proof is always of
a specific statement epoch; integration requires all edges current, so staleness detection is pure
graph arithmetic.

**The scheduling invariant survives the split:** every statement `frozen@e` with an `open` proof
is dispatchable *now* — its dependencies' statements are frozen and admissible as stubs. Edges are
for invalidation, assembly, and axiom accounting, not readiness: dispatch the whole open frontier
at once — and the concurrency cap is always the ceiling the rate window and the session pool
allow, never a smaller number. (`non-mockable` nodes, §0, still block their dependents and
are scheduled first.)

### 8.2 The control flow: recursive decomposition

Everything the orchestrator does is one recursive procedure:

```
prove(stmt frozen@e, budget B):
    if estimate_simple(stmt):
        r ← dispatch(stmt, small b ⊂ B)        # optimistic probe
        if r = qed: return                      # cheap models are cheap
    plan ← decompose(stmt)                      # children + GLUE PROOF
    freeze children  (sentinels always; audit only if triggered, §8.5)
    for c in plan.children, in parallel: prove(c, share of B)
```

**The no-gap rule.** A decomposition is accepted only when its **glue proof `Qed`s with the
children admitted**. A plan is not prose — it is a machine-checked proof of the parent from its
children. This kills the classic decomposition failure (children individually plausible, jointly
insufficient, discovered only at assembly after the leaf budget is spent), and it is the demand
edge of §8.8 in its strong form: a child exists because the glue literally uses it. The relaxed form is
the **default for all plans**: children freeze and dispatch immediately, and the glue is itself a
concurrent node — blocking dispatch on glue-`Qed` would idle the flat-rate window and put frontier
tokens on the tactic path. Gate-blocking strict no-gap is an opt-in mode for campaigns where a bad
plan costs more than idle workers. Either way the rule stands: a plan *integrates* only when its
glue `Qed`s.

**"Simple enough" is measured, not felt.** The dispatch-or-decompose call uses a difficulty
estimate — statement size, quantifier and modality depth, invariants in scope, similarity to the
solved-trace corpus (§13), the cheap tier's observed solve rate on similar nodes — but the
default policy is **probe-then-decompose**: try a cheap prover under a small budget first,
decompose on `stuck`. Ex-ante judgment alone is not reliable enough to gate on; probes are cheap,
and a failed probe returns the ledger trace of where it got stuck — exactly the evidence that
makes the subsequent decomposition better.

**Budget flows down, failure flows up.** Every node inherits a budget from its parent;
decomposition splits it; exhaustion propagates upward as `stuck`. Runaway recursion is bounded by
construction, not vigilance. `stuck` and `contested` return to the decomposer that stated the
node — the owner with the context to refine the plan, restate, or escalate its own `stuck` one
level up. The human sits at the root and sees only what nothing below could absorb.

**Depth is a smell.** The no-gap rule means a deep tree cannot drift *logically* — every node is
connected to the root by machine-checked glue. What deep recursion still drifts is cost and
idiom: each level states children in terms of "what I happen to have," accumulating incidental
hypotheses and losing the development's vocabulary, and depth usually signals a missing
abstraction rather than a genuinely deep problem. Controls: (a) **geometric budgets** — children
get fractions of the parent's budget, so depth is bounded and the cheap direction is width, which
the scheduling invariant already rewards; (b) a **depth cap** (default 2–3) — at the cap a
decomposer may not decompose further: dispatch or return `stuck`, forcing a re-plan one level up
instead of another layer down; (c) a **hygiene sentinel** comparing a child's hypothesis load
against its parent's, flagging accumulation (the unused-premise report, §8.7, catches it
post-hoc); (d) the context packet carries a two-line **intent brief** — root goal, parent's
rationale — so deep nodes are stated in the root's idiom, not the local one. Per-node fixed costs
(state, freeze, gate) also mean that below a certain grain subdivision costs more than proving;
the estimator learns that floor from traces. (The estimate stays a cheap heuristic; a learned
estimator is not built unless traffic ever justifies it.)

**Alternatives for hard lemmas.** For a fixed hard target a single decomposition is a bet, so a
node may carry **alternative plans (OR-nodes)**: two candidate decompositions raced under split
budgets; the first complete integration wins and the loser goes to the attic. AND/OR is what
makes the graph a proof search rather than a build system. Alternatives are opt-in and
root-adjacent — this is where cost explodes if used casually — and are not built until a
hard-lemma campaign actually needs them.

### 8.3 What a freeze pins

Freezing source text is not enough. `Section`/`Context` variables are added hypotheses that are
invisible on the lemma line; a changed upstream `Definition` silently changes what an unchanged
statement means; notation changes can do the same. A freeze therefore pins the **statement
closure**: the elaborated, post-section-discharge kernel type of the constant, plus the transitive
closure of definitions and notations it references, all content-addressed. Two statements are the
same iff their closures hash the same.

Enforcement is by construction, not by trust:

- **Two-zone repo.** `specs/` belongs to the spec side; `proofs/<node>/` to that node's prover. A
  worker's output is a patch, and the gate **reassembles the development from the frozen spec
  store plus the patch** — anything the worker did to spec files is discarded by construction,
  not detected by review.
- **Statement pinning.** The statement line is spec-owned and worker patches are constrained to
  proof-body spans, so the proved type is frozen byte-for-byte by construction (§8.7); the
  elaborated-closure comparison survives only as an opt-in deep audit.
- **Provers cannot create nodes.** A prover that needs a lemma returns
  `stuck(evidence, requested_statement)`; the request routes through the statement pipeline
  (its decomposer states → sentinels → audit → freeze) before anyone proves it.
- **Private helpers are free; sharing requires promotion.** Node-namespaced helper lemmas and
  definitions are unrestricted — provers must be able to scaffold — but nothing outside the node
  may reference them until they are **promoted** through the statement pipeline. This blocks the
  growth of an unaudited shadow-spec ecosystem, which is exactly how hypothesis-smuggling
  compounds.

### 8.4 Statement sentinels (deterministic, run at freeze time)

- **Duplicate detection** by closure hash — agents love restating existing lemmas.
- **Vacuity probes** — budgeted automated attempts to derive `False` from the statement's
  hypotheses. In Iris this catches real cases, since contradictions are derivable in-logic:
  `l ↦ v ∗ l ↦ w ⊢ False`.
- **Satisfiability co-obligations** — every frozen interface or invariant carries an inhabitation
  witness as a sibling node (for an Iris invariant, the standard allocation lemma
  `⊢ |==> ∃ γ, I γ`), and one exemplar instantiation of every abstract interface compiles at all
  times. An unsatisfiable interface makes every client lemma vacuously provable and the
  development rots invisibly; this failure must be loud and immediate.
- **Partial-correctness flag** — Iris `WP` is partial: divergence satisfies every spec.
  Termination-relevant statements must use total weakest preconditions (`twp`) or carry an
  explicit termination side condition; the sentinel flags `WP`-only specs so an auditor decides
  deliberately rather than by default.
- **Truth probes** — test before proving, where testable: QuickChick-style property testing for
  pure, executable side conditions. Most Iris statements are `iProp`s and cannot be tested this
  way — the sentinel is narrow and cheap, not a safety net. Where it applies, a falsehood found by
  testing costs seconds instead of a worker's budget plus an amendment cycle.
- **Reduction sentinels — no lateral moves.** A requested lemma whose closure hash equals (or
  trivially matches) the requester's own goal is rejected mechanically: restating the goal is not
  progress. A request or plan child that duplicates a node already `stuck`, `contested`, or
  escalated is not dispatched; it routes to the owning decomposer as a design signal —
  independent reductions converging on one hard obligation mean the statement, or the invariant
  above it, is wrong, and the fix is a re-plan, not another worker.

### 8.5 The amendment lattice

A frozen statement changes only through a typed amendment — and the crucial observation is that
**three of the four amendment classes are machine-checkable**, so scarce audit attention
concentrates on the fourth.

| class | evidence required | dependents | decision |
|---|---|---|---|
| `refute` | machine-checked counterexample: a proof of `stmt → False` in the frozen environment, or an adequacy-level counterexecution | tainted, transitively | auto-accept |
| `iso` | migration shims `old ⊣⊢ new` | untouched — `old@e` is kept as a corollary of `new@e+1` via the shim | auto-accept |
| `strengthen` | migration shim `new ⊢ old` | untouched — same corollary trick; only this node's proof burden grows | auto-accept |
| `weaken` (add hypothesis, weaken conclusion or definition) | prose rationale — no shim can exist | genuinely re-opened at every use site | **audit quorum** |

`weaken` is the class the observed failure lives in — hypotheses added to make proofs go through.
Its obligation does not vanish, it *moves*: every added hypothesis must now be discharged at every
use site. So before any vote, the graph computes a deterministic **impact report**: which
dependents re-open, which new obligations appear at which call sites, and which of those
automation already discharges (each tried under a budget; the residue reported). Auditors vote
with the true cost in hand, and "just add a hypothesis" stops looking free.

**Audit is a ladder, climbed only as needed:** deterministic checks (always) → one auditor →
quorum → human. Blast radius picks the rung. Node-local statements: the impact report and at most
one auditor. Interface-rank weakenings: one auditor by default, a quorum only when that auditor
flags doubt or the impact report is large. The root and its definitions: human only. A quorum of
similar models shares blind spots — K correlated votes are closer to one vote with confidence
theater than to K independent checks — so when a quorum does convene it must buy real diversity:
mixed model families, no access to the requesting prover's transcript (audit the claim, not the
rhetoric), structured verdicts with falsifiable rationales, disagreement escalating to the human.

**And audit is event-driven, not ambient.** A model audit fires only on: `weaken` amendments
(always); initial freeze of interface-rank statements; sentinel hits; `contested` adjudication;
and a small ε spot-check of everything else. The worker norm — *never propose added hypotheses
unless you can state the reason* — lives in the prover skill, but the mechanism is what carries
it: a worker cannot add a hypothesis silently at all (the freeze); it can only file a `weaken`
request, which costs an audit, so requests are rationed by construction.

**Two rungs are built first; the rest is design.** Until measured amendment traffic justifies
more, the built paths are machine-checked `refute` and human edit — quorum plumbing, shim TTLs,
and audit routing stay on paper (Phase 7). And one routine Iris change is pre-cleared: a `weaken`
whose only additions are typeclass constraints (`inG Σ …`, `Countable …`) that the impact replay
discharges automatically at every use site is auto-accepted — everyday plumbing, not a design
change.

**Fixed roots.** A lemma the user hands down as the target — including an open one — is frozen at
rank root with no amendment path except human edit. A machine-checked `refute` of a fixed root is
a legitimate research outcome, and the pipeline treats it as a success mode: it returns evidence,
not failure.

**Falsification propagation.** `refute` taints transitive dependents along two mechanically
distinguishable channels: *proof-invalidation* (the dependent's proof used the refuted lemma; its
statement stands, its proof re-opens → `open`) and *statement-invalidation* (the dependent's
statement closure includes an amended definition; the statement no longer means anything → back to
`proposed` for restatement). Salvage is replay-first: on any re-opening, replay the old proof
script against the new epoch — with migration shims available — before dispatching a worker. After small
amendments most proofs survive verbatim, and replay is deterministic and nearly free.

**Shims are migrations, not architecture.** The `iso`/`strengthen` proofs above are compatibility
shims: they exist so an amendment does not stall the frontier, and for no other purpose. They are
emphatically not the "bridge proof" anti-pattern — a worker reducing its goal to some other
obligation that was itself deemed unprovable, shuffling difficulty sideways instead of
discharging it. That move is blocked outright: workers cannot state nodes, and the reduction
sentinels (§8.4) reject it at the request stage. And to stop shim *accretion* — layers of
old-as-corollary compatibility sludge papering over a design that should simply be restated —
shims carry a TTL: once an amendment integrates, dependents are migrated to the new statement by
background replay and the shim is deleted. A shim surviving more than one epoch, or a corollary
chain deeper than one, is flagged in the trusted-base report as design debt.

### 8.6 Roles

- **Human.** Owns the root: top-level statements, the definitions they mention, the axiom
  whitelist, the toolchain pins. Sole authority over amendments to any of it.
- **Decomposers** (frontier model at the root, cheaper tiers deeper in the recursion). Each owns
  the statements it created: it develops the plan — children plus glue proof (§8.2) — absorbs its
  children's failures, and escalates its own. The v1 "architect" is just the root decomposer. It
  proposes; sentinels and auditors dispose.
- **Auditors** (quorum, mixed models). Judge `weaken` amendments and initial interface-rank
  statements, from the frozen spec, the amendment, and the impact report — never the prover's
  transcript.
- **Provers** (cheap models, many, parallel). One node, proof zone only, hard budget. Each
  receives a deterministic **context packet** — the frozen statement, its closure, a premise
  shortlist, the intent brief, the nearest solved siblings from the trace corpus — and returns
  `qed / contested(evidence) / stuck(evidence, requests)`: never a partial edit, never a
  statement.
- **Gate** — no model at all. Below.

### 8.7 The integrity gate (deterministic, model-free)

Run as a pure function of (frozen store, worker patch) in a clean container:

1. **Assembly** — rebuild from frozen specs + patch; worker edits outside their assigned
   proof-body spans are discarded by construction.
2. **Statement pinning by construction** — the statement line lives spec-side and patches touch
   only proof bodies, so the proved statement is byte-identical to the frozen one; with item 7
   and fixed `Require` order, its meaning is pinned too. The kernel-level closure comparison
   (elaborated types, content-addressed definition closure) is an opt-in deep audit, not the
   critical path — petanque's `ast` is pre-elaboration and cannot do it, and the serialization it
   actually needs is a subproject in itself.
3. **`Proof using` discipline** — every assembled proof file sets
   `Set Default Proof Using "Type"` (as Iris itself does), and explicit `Proof using` annotations
   are part of the frozen closure; otherwise the `Qed`'d constant's discharged arity can differ
   from the admitted stub's and break dependents compiled against the stub.
4. **Axiom hygiene** — `Print Assumptions` ⊆ whitelist.
5. **No new `Admitted` / `admit` / `Axiom` / `Parameter`** anywhere in the assembled diff.
6. **No escape hatches** — `Unset Universe Checking`, `Unset Guard Checking`,
   `Obligation Tactic` overrides.
7. **Ambient-state hygiene** — worker-added `Instance` / `Hint` / `Notation` / `Ltac` are
   node-local by default; global registration is a spec-zone change requiring audit, because
   globals change how *future* statements elaborate — a statement-meaning attack surface.
8. **Unused-premise report** — scan the proof term for premises it never uses: the kernel-level
   analogue of the ledger's `unused_at_qed`, deterministic and free, and the best early warning
   that a statement is over-strong and headed for a `weaken` fight later.

### 8.8 Anti-drift: demand, liveness, burndown

"Productive procrastination" is blocked structurally, not by exhortation:

- **Pull-only node creation.** The graph rejects any node without a **demand edge** — and the
  demand edge is the parent's glue proof referencing the child (§8.2's no-gap rule is its strong
  form). Root demands come only from the human. If nothing uses it, it cannot enter the graph.
- **Liveness is computed, not asserted.** After each integration, walk real kernel dependencies
  from the root's proof terms. A node outside the root's dependency cone is dead regardless of how
  elegant it is; dead proved nodes move to an `attic/` (re-demandable, but not progress).
- **Progress = live admits discharged**, weighted by position in the root's cone — a burndown the
  agent cannot inflate by proving side lemmas. Fifty attic lemmas measure as zero progress and are
  reported as waste, per role and per model — which also tells you which prompts drift.

### 8.9 Escalation ladder

cheap model → cheap model *with ledger blame evidence attached* → frontier model. A node escalated
twice is a statement problem, not a prover problem — return it to its decomposer as a `contested`
candidate rather than burning frontier tokens. Convergent failures are the loudest signal of all: when several nodes' failures
reduce to the same hard obligation, stop dispatching at it — that node's statement, or the design
above it, is the problem. The cost of an amendment includes the re-proof cost it causes; track it
per statement epoch, because that is how you learn whether audits are strict enough. Keep the root decomposer decomposing while provers run; never idle the expensive
model on a barrier.

### 8.10 The trusted base, and the adequacy capstone

The kernel reduces trust to: root statements + the definitions they mention + axioms + toolchain.
The pipeline exists to keep the *evolution* of that trusted base under explicit control, so the
system continuously emits a **trusted-base report** — root statements, their definition closures,
axiom whitelist, pins — and any growth of it is an event requiring human acknowledgment. Reviewing
that diff *is* the human's job; everything else is machine-checked.

The capstone: the root should include at least one **closed corollary through Iris adequacy** — a
pure statement about a concrete program run, with no hypotheses left. Closed statements are the
one thing hypothesis-smuggling cannot touch: there is nowhere left to put the hypothesis. It is
the development's end-to-end test, and it should be frozen first, before decomposition begins.

### 8.11 The daily loop: the degenerate pipeline is the product

Everything above will be tuned; this subsection is the part that is not allowed to be. The common
workflow — *"I have a lemma and high-level intuition for its proof; the orchestrator manages
parallel dispatch"* — must work every time.

```
pcp prove Foo.v foo_correct --plan plan.v
```

1. The user's lemma is the fixed root, and the user is the root decomposer: they state the
   children (or draft them with the frontier model and approve). Statements freeze immediately —
   hash and closed-type pin, plus only the free sentinels (duplicates, closure hashing).
2. The whole frontier dispatches at once, in parallel, budgeted. The glue — the root from its
   admitted children — is itself a node, dispatched concurrently or drafted by the frontier
   model. **The no-gap rule relaxes from gate to node here:** a human-vouched plan is trusted
   enough to dispatch against immediately, and a gap in the plan surfaces as an ordinary `stuck`
   on the glue node rather than as up-front ceremony.
3. Returns are gated (§8.7 — already deterministic and cheap). Failures retry once with blame
   evidence attached. What remains lands back with the user in one of three shapes, always with
   evidence: `qed`, `stuck` (ledger blame trace), `contested` (worker's reason). The user
   adjudicates; at this scale they are the entire audit ladder.

**Dependencies, by design:** the session pool (§6), the gate's cheap subset (§8.7: assembly,
assumptions, no-admit), dispatch/retry with hard timeouts, SQLite persistence — and no pcp-state
at all: day-one workers ride rocq-mcp or plain `coqc` feedback, and the state layer (Phases 2–4)
upgrades their solve rate rather than gating the loop. **Non-dependencies, by design:**
quorums, OR-nodes, the sketch compiler, the difficulty estimator, depth > 1 recursion, more than
one provider. Every human-judgment slot in the full pipeline degrades to the actual human here —
which is fine, because at one lemma and five to twenty children the human's judgment is faster
and better than the machinery that would replace it.

The engineering contract for this loop, enforced from Phase 1 onward:

- **It never wedges.** Every node terminates in one of the three shapes within its budget. A dead
  pet-server or a hung worker is a timeout-and-requeue, not a hang, and a slow worker climbs the
  ping ladder (§6) before it is killed. `pcp prove` resumed after a
  crash picks up from the SQLite graph, and deterministic replay makes re-entry nearly free.
- **A permanent canary.** One golden end-to-end run — a known lemma, a known plan, cheap workers —
  executes in CI and before every release of the tool. Speculative features are feature-flagged
  off by default and are not allowed to break the canary.
- **Short reports.** The end-of-run summary fits on one screen: n `qed`, m `stuck` with a
  one-line blame each, k `contested` with a one-line reason each. The dashboard is optional; the
  summary is not.
- **No model ever reviews a success** (§11). A gated `qed` is final; model judgment is spent on
  failure paths only, one evidence-informed retry each.
- **Handoff is a file.** `pcp handoff <node>` emits a `.v` with the frozen statement, the best
  partial script, and the blame trace as comments — a stuck node lands in your editor with full
  state, not in a report.

---

## 9. The CSL mode: freeze the design, then prove

The general pipeline gets a domain-specific front end for concurrent separation logic, because
the artifacts at stake are different: not only lemma statements but the **implementation** and
the **invariants** — and each attracts its own characteristic cheating.

### 9.1 The implementation is part of the theorem

The most tempting repair in program verification is editing the program; that changes the
theorem. Implementations are spec-zone artifacts: frozen, worker-untouchable, amendable only with
human sign-off — an auditor model cannot know whether the new code is still the program you
meant. The assembly gate (§8.7) enforces this for free once the code lives in `specs/`.

### 9.2 The invariant catalog is interface rank

Invariants and the ghost-state plan behind them are frozen before proof work begins, with a
CSL-specific audit rubric, because an invariant fails in two directions and each produces a
different disease:

- **Too strong → unmaintainable.** Some program step cannot restore it before closing; the proof
  dies at an `iInv` close site many steps after the design error. Ledger evidence: the
  undischargeable close-site goal.
- **Too weak → insufficient.** Opening it does not yield what the use site needs; the proof dies
  at the open site.

Both become `weaken`-class churn downstream, so this is the highest-leverage audit in the system.
One deterministic sentinel genuinely helps here: the allocation witness (§8.4). Preservation
probes — auto-checking that each atomic step can re-establish each invariant — are *not*
promised: stating the probe requires the pre-step symbolic state that the proof itself computes,
so they are research, not a phase deliverable.

### 9.3 Sketch first, compile the sketch

Design decisions should be made where cheating pressure is lowest — and that is the sketch,
where there is no failing tactic to appease. Before tactic work, the human or a frontier model
writes a **proof sketch**: the invariant catalog, the ghost-state plan (which RAs, what each
ghost name means), per-function outlines with intermediate assertions at program points, and —
for logically atomic operations — the commit-point analysis.

Low cheating pressure does not mean low stakes: *error* pressure peaks here, because a wrong
invariant baked in at sketch time is the most expensive mistake the system can make — a
whole-subtree rework discovered weeks later. So the sketch is trusted for honesty and audited
for correctness: preservation probes, allocation witnesses, and the human's scarce attention are
spent here first, where they are cheapest and matter most.

The sketch is compiled, not consulted: `pcp sketch` turns an annotated outline into the frozen
obligation graph — one stated WP obligation per program segment between assertions, glue
obligations connecting them, allocation and preservation obligations per invariant — all
entering the pipeline as `proposed`, with the sketch as their demand justification. Compilation
is what prevents tactic work from silently diverging from the design: amending the sketch is
amending frozen statements, and goes through the lattice (§8.5).

### 9.4 The logatom skill

Logically atomic triples are their own genre and get a dedicated skill pack — worker
instructions, statement templates, tactic patterns:

- the canonical shape `<<< ∀ x, α x >>> e @ E <<< β, RET v >>>`, and when it is the right spec at
  all — misstating a logatom spec is a classic multi-day sink, and templates prevent it;
- the standard skeleton: atomic-update access, abort vs commit paths, and the mask bookkeeping
  around them — wired to the §3 modality block, which is where mask and `fupd` tracking pays off
  most;
- **commit-point identification as a sketch artifact**, fixed before proving;
- **prophecy variables** when the linearization point is in the future or outcome-dependent;
- **helping**, where another thread commits your operation and the atomic update travels through
  an invariant — the standard pattern, encoded once.

`skills/` is where this lives (`logatom.md`, `invariants.md`, `prover.md`, `decomposer.md`), and
where institutional knowledge accumulates out of the eval traces (§13).

---

## 10. The cockpit: a harness you already have, plus a browser

A bespoke TUI would duplicate a harness — login flows, session management, interactive input —
that Claude Code, codex, and pi already own. Owning none of that is the design. The interaction
problem splits into three parts, and each has a cheaper home than a curses app:

- **Login is delegated, never implemented.** Each provider's CLI owns its auth flow
  (`codex login`, Claude Code's `/login`); pcp only *checks* (`codex auth status`, a claude ping)
  and prints the command to run when a window is unauthenticated. Inside a Claude Code cockpit
  session, `! codex login` runs the interactive flow without leaving the session.
- **Steering is MCP tools, not UI.** `orch_status`, `orch_pin`, `orch_kill_subtree`,
  `orch_grant_budget`, `orch_hint` — callable from whatever harness you are already sitting in.
  The orchestrator session (frontier model, the root decomposer) *is* the cockpit; steering is a
  sentence, not a keybinding.
- **Live visualization is a browser tab.** `pcp serve` — a read-only localhost dashboard over the
  SQLite graph, server-sent events for live updates. Every pane from the old TUI design lands
  here: frontier, in-flight, the tree with taint ripples, burndown, the human inbox. A browser is
  a strictly better graph renderer than curses at a fraction of the build cost (~200 lines of
  HTML + SSE, no framework). `pcp report` stays as the static snapshot export and `pcp status` as
  the one-screen terminal summary.

So the "TUI" is: your existing harness session for interaction, one browser tab for watching.
Nothing is forked, no curses code is owned, and the whole §8.11 loop is drivable from the tool
you already live in.

**If a standalone harness is ever genuinely wanted,** fork pi rather than building one: it is
minimal, model-agnostic, explicitly designed to be extended, and already owns multi-provider
subscription login. Claude Code is not forkable and the codex CLI is heavyweight for this
purpose. Revisit only if the harness-as-cockpit model fails in practice.

---

## 11. Backend: Atomic vs Pi vs Claude Code vs roll-your-own

| option | fit | mismatch |
|---|---|---|
| **Atomic** (bastani-inc) — TypeScript, Node ≥22.19, DAG stages, gates, artifacts, checkpoints, retries, MCP, 20+ providers, built on Pi | Strong on the *generic* parts: parallel stages, bounded repair loops, resumability after interruption, human approval gates, multi-provider routing for a cheap-model tier | Its DAG is **authored and acyclic** — the README states stage dependencies must form a DAG and cycles are unsupported. Yours is *discovered at runtime* and has renegotiation cycles (§8.5) |
| **Pi** — minimal model-agnostic loop (read/write/edit/bash), you own orchestration | Clean provider abstraction without opinions; good worker substrate | You build the graph yourself anyway |
| **Claude Code subagents** — what you use today | Zero new infrastructure; good prover tier; MCP works natively | The graph lives in the orchestrator's context window and dies with it. No durability, no cost accounting, no resumption |
| **Roll your own** | Exact semantics | You maintain a scheduler |

**Recommendation: own the graph, rent the runner.**

The obligation graph is the part that is specific to you, needs cycles, and must survive process
death. That is ~400 lines of Python over SQLite at `.pcp/graph.db` — small enough that owning it is
cheaper than bending someone else's DAG engine around `contested` edges.

Everything below it — running one node attempt — is commodity. Define a ~30-line adapter interface:

```python
class Runner(Protocol):
    async def run_node(self, node: NodePayload) -> NodeResult: ...
```

Implement it in priority order. `CodexCLIRunner` first: it spawns `codex exec --json` per node,
and it is the only route to the workhorse tier — the 20× subscription is reachable through the
CLI login, not a meterable API. Then `ClaudeHeadlessRunner` (`claude -p`, the same trick on the
Claude subscription), `ClaudeCodeSubagentRunner` (interactive sessions — the one runner with a
mid-flight channel, §6), and `DirectAPIRunner` (for the eval harness, where you want no harness
in the way). `AtomicRunner` is deferred, not cut: the auditor recommends dropping it outright;
it stays on the list only for the case where durable checkpoints and gates start to matter.
Then you can A/B the substrates empirically instead of betting on one up front.

Practical note: this machine has Node v12. Atomic needs ≥22.19, so that is an `nvm install 22` away.

### Model access: many providers, many login methods

Model access is a first-class config concern, as it is in Atomic: roles bind to tiers, tiers bind
to provider profiles, and each profile carries its own login method.

```toml
# .pcp/config.toml
[tiers]
decomposer = "anthropic/claude-fable-5"
prover     = ["codex/luna", "anthropic/claude-sonnet-5"]      # flat-rate workhorse first
auditor    = ["anthropic/claude-opus-5", "google/gemini-…"]   # mixed families, §8.5

[providers.anthropic]
auth = "subscription"        # OAuth device flow (Pro/Max-style); or "api-key"

[providers.codex]
auth = "subscription"        # e.g. a 20× plan — near-zero marginal cost, budget in requests/window

[providers.bedrock]
auth = "sdk"                 # ambient AWS credentials

[providers.local]
auth = "none"
endpoint = "http://localhost:11434"
```

- **Delegate where a harness already owns login.** `ClaudeCodeSubagentRunner` inherits the Claude
  Code session's own auth (subscription or key); `AtomicRunner` inherits Atomic's multi-provider
  login — part of why it is the second runner rather than a fork of it. Only `DirectAPIRunner`
  resolves profiles itself: OAuth device flow for subscription providers, keys from env or
  keychain, ambient SDK credentials for Bedrock/Vertex, nothing for local endpoints.
- **The auditor ladder needs this on day one.** Mixed model families (§8.5) are only real if a
  second provider is a config line, not an integration project.
- **Secrets hygiene.** Credentials live in the keychain or a 0600 file outside the repo — never in
  the graph DB, the traces, or a context packet. Traces become training data later (§13); nothing
  secret may ever enter them.

### Economics: schedule against windows, not tokens

Cost and wall-clock are the binding constraints, and the main workhorse is a flat-rate
subscription (e.g. a 20× codex plan) whose marginal token cost is near zero but whose capacity
comes in rate windows. That inverts the usual accounting, and the scheduler is built for the
inverted version:

- **Budgets are vectors, denominated per provider.** Subscription tiers budget in requests per
  window; metered tiers in tokens and dollars. The budget that flows down the tree (§8.2) carries
  both, and the dashboard cost meter shows window utilization alongside spend.
- **Saturate the window; never burst-and-idle.** Unused window capacity expires worthless, so the
  dispatcher keeps a deep queue against it and steals work when workers finish early. Surplus
  window is exactly what to spend on speculative fan-out (`proof_try`, probes, evidence-informed
  retries) — near-free there, expensive on a metered API.
- **Cheap-tier concurrency is always maximal.** In-flight worker count defaults to the ceiling
  the rate window and the session pool allow; parallelism is never the knob you turn down.
  Budgets bound cost — concurrency stays pinned at max.
- **Metered frontier tokens buy only what cheap models are structurally wrong for:** root
  decomposition, `weaken` adjudication, absorbed escalations. Never bookkeeping the graph does
  deterministically, and never review of successes.
- **Wall-clock hides in the slow checks, so batch them.** Petanque checks incrementally per node;
  the full `coqc` assembly gate runs at integration milestones, not per return; deterministic
  replay makes re-gating a prefix nearly free. Tight node scoping is also what makes luna-class
  workers effective at all — scope discipline is a speed feature, not just a quality one.

### No model ever reviews a success

The cheapest review loop is the one that never runs. A gated `qed` is final: the kernel and the
deterministic gate have already checked everything a reviewer could, so no model rereads a
successful proof — style passes are an explicit opt-in, never a default. Model judgment is a
failure-path resource, and bounded even there: one evidence-informed retry (blame trace attached)
per node before escalation; workers killed on no-progress by state-hash loop detection (§6)
rather than left to spin; sentinels and impact reports produced by programs, not prompts; and the
ε spot-check (§8.5) defaults to zero in the daily loop, where the human is the auditor.

---

## 12. Phases

| phase | scope | est. | deliverable |
|---|---|---|---|
| **0** | Environment: `opam init`, Rocq 9.x switch, `coq-lsp` (provides `pet-server`), Iris + stdpp, a scratch Iris project. Pin everything in `env.sh` / `flake.nix`. | ½ day | reproducible toolchain |
| **1** | **The daily loop, lite (§8.11):** SQLite graph, statement pin by construction (proof-span patches), max-parallel dispatch over `CodexCLIRunner` / `ClaudeHeadlessRunner`, `coqc` + `Print Assumptions` + no-`Admitted` gate, one evidence retry, crash-resume, the permanent canary. Day-one workers ride rocq-mcp or plain `coqc` feedback. | 1–2 wk | **`pcp prove` works before any state tooling exists** |
| **2** | Trace spine: pytanque wrapper, session pool with state-id multiplexing (§6). Week-1 spike: Ltac2 `iDump` via petanque message capture — if it works, the printer parser is never built. CLI `pcp trace file.v Lemma` → JSONL. | 1 wk | tactic-by-tactic Iris state dump |
| **3** | IPM model + ledger: evar-aware hashing, name-first matching, goal parentage, event log, `where_did_it_go` / `blame` / `leftovers`, persistence oracle. | 1–2 wk | the thing that fixes failure mode #1 |
| **4** | Context economy + MCP server + pattern/unification diagnosis (`proof_destruct`, the aligner reports). Wire into workers; measure the solve-rate delta. | 1 wk | measured worker upgrade |
| **5** | Retrieval + speculative fan-out: `premise_search` (`Search` + grep passthrough), `notation_resolve`, `proof_try`. | 1 wk | failure modes #5 and #6 |
| **6** | `pcp handoff` + `pcp status`; hardening from real usage. | ½ wk | stuck nodes land in your editor |
| **7** | Full pipeline, behind flags: epochs, amendment lattice (`refute` + human only at first), impact reports, probe-then-decompose, provider auth profiles, cost accounting. | 2 wk | orchestration you can leave running |
| **8** | CSL mode: `pcp sketch` compiler, implementation/invariant freeze wiring, logatom + invariant skill packs. | 1–2 wk | sketch-driven CSL pipeline |
| **9** | Cockpit: steering MCP tools + `pcp serve` live dashboard (SSE over SQLite). | 1 wk | watch and steer from harness + browser |
| **10** | Evaluation harness. **Start by Phase 4, not at the end.** | ongoing | evidence |

Phases 0–1 come first and are unconditional — the audit's strongest finding was that the old
ordering (state layer before loop) contradicted §8.11, and it did. Phases 2–6 are measured
upgrades to worker solve rate. Phases 7–9 are built only if measured against the daily loop in
the hands of a well-equipped human (see §14).

---

## 13. Evaluation — build it early

Without this you cannot tell whether the tooling helps, and every subsequent design decision is
taste.

- **Corpus.** Hold out lemmas from `iris-examples`, `actris`, `reloc`, and your own project.
  Replace bodies with `Admitted`; ask an agent to reprove them.
- **Metrics.** Solve rate · tokens per solved lemma · tool calls per solved lemma · wall clock ·
  dollar cost · subscription-window utilization · **cheap-model solve rate**. The last one is the number that decides whether the
  whole orchestration thesis pays.
- **Ablations.** no tools (baseline) → raw goal dump → `+ledger` → `+retrieval` → `+speculative`.
  You need to know which features actually earn their context, and to delete the ones that do not.
- **Trace collection.** Every real session writes to `.pcp/traces/`. That is your regression corpus,
  your debugging record, and — later — training data.
- **Traces feed forward.** The difficulty estimator (§8.2) and premise retrieval train on
  collected traces; and a dependency bump (a new Iris release) becomes a replay run whose
  failures re-enter the pipeline as ordinary obligations — maintenance mode for free.

---

## 14. Risks and how each is contained

- **Printer-parsing brittleness across Iris/Rocq versions.** Phase 5 removes the dependency. Until
  then: pin versions, and keep golden-output tests per version.
- **petanque / coq-lsp API churn.** One adapter module, `coqc` fallback path retained.
- **Ledger heuristics wrong on exotic tactics.** Degrade to `unknown`, never guess (§4.4).
- **Tool-surface bloat.** Hard cap on tool count; every tool must survive an ablation.
- **Over-orchestration.** The graph pays off above roughly ten obligations. Below that, one agent
  with good tools wins on both cost and latency. Measure before building Phase 7 — it is entirely
  possible that Phases 1–6 capture most of the value and the full pipeline is a smaller win than
  it looks.
- **Cheating workers.** §8.7 is not optional.
- **Freeze friction drives workarounds.** If amending is expensive, agents contort proofs instead
  of contesting false statements — the exact failure the freeze exists to stop, reappearing inside
  proofs. Contain: `iso`/`strengthen` amendments auto-accept with a shim, so legitimate
  refactoring stays cheap; and monitor the contested rate — near-zero under heavy proving is a red
  flag, not a success.
- **Auditor rubber-stamping.** Auditors are models too, and correlated ones fail together.
  Contain: mixed model families, no access to prover transcripts, structured falsifiable verdicts,
  human spot-samples of approved `weaken` amendments.
- **Decomposition gaps.** Children all proved, parent unprovable from them. Contained
  structurally: the no-gap rule (§8.2) refuses any plan whose glue does not already `Qed` against
  admitted children.
- **Runaway or drifting recursion.** Bounded by geometric budgets and the depth cap; idiom drift
  contained by the hygiene sentinel and intent brief (§8.2). Exhaustion surfaces as `stuck` at
  the parent, never as an unbounded tree.
- **Difficulty misestimation.** Probe-then-decompose makes the error cheap and informative; the
  estimator retrains on eval traces.
- **Sketch–proof divergence.** The sketch is compiled into the frozen obligations (§9.3), so
  tactic work cannot silently diverge; sketch changes go through the amendment lattice.
- **Implementation drift (CSL).** The program is spec-zone: editing it is amending the theorem,
  human sign-off only (§9.1).
- **Speculative machinery destabilizing the core.** The daily loop (§8.11) depends only on the
  deterministic subset; everything speculative ships behind a feature flag, off by default, and
  is not allowed to break the canary.
- **Wasted tokens in review and retry loops.** No model reviews a success (§11); one
  evidence-informed retry per node, then escalate; no-progress workers are killed by state-hash
  loop detection (§6); ε spot-checks default to zero in the daily loop.
- **Shim accretion and lateral reductions.** Migration shims carry a TTL and are deleted after
  background replay (§8.5); goal-restatement and reduction-to-stuck requests are rejected by the
  reduction sentinels (§8.4).
- **Building a research project instead of a tool.** The failure mode of this kind of project is
  gold-plating the state model. Ship Phase 1 in a week and use it on a real proof before designing
  Phase 2 in detail.

---

## 15. Repo layout

```
proof-copilot/
  pcp/
    core/
      session.py      pet-server pool, sandboxing, timeouts
      trace.py        step capture, deterministic replay
      ipm/
        parse.py      v1 printer parser
        model.py      IrisGoal, Hyp, Modality
        reflect.py    v2 Ltac2 iDump driver
      ledger/
        diff.py       structural matching
        events.py     event log
        query.py      where_did_it_go / blame / leftovers
      digest.py       content-addressed store, elision, budgets
      search.py       premise + notation retrieval
    mcp/server.py
    cli/main.py
    orch/
      graph.py        SQLite obligation graph, statement epochs, OR-plans
      decompose.py    recursive decomposition, difficulty policy, budgets
      schedule.py     frontier dispatch, escalation
      gate.py         deterministic integrity gate
      amend.py        amendment lattice, impact reports, audit routing
      sketch.py       CSL sketch compiler: outline → stated obligations
      providers.py    model tiers, provider profiles, login methods
      runners/        codex_cli.py · claude_headless.py · claude_code.py · direct.py · atomic.py (deferred)
    dash/
      serve.py        pcp serve: localhost live dashboard (SSE over SQLite)
      report.py       static HTML export (pcp report)
  skills/
    prover.md         worker norms (no added hypotheses without stated reason)
    decomposer.md     the no-gap decomposition contract
    logatom.md        logatom templates: commit points, prophecy, helping
    invariants.md     invariant strength rubric, preservation probes
  coq/
    IDump.v           Ltac2 reflected dump (Phase 5)
  eval/
    corpus/ · harness.py · ablations.py
  docs/PLAN.md
```

---

## 16. Open decisions

1. **Rocq version and Iris pin** — driven by whatever project you actually want to point this at.
   Everything downstream (parser goldens, Ltac2 availability, coq-lsp version) follows from this.
2. **Runner to implement first** — Claude Code subagents is the zero-infrastructure default; Atomic
   is the answer if durability and cross-provider cheap-model routing matter sooner than expected.
3. **Whether Phase 7+ happens at all** — decide on measurements from the daily-loop era
   (Phases 1–6), not now.
4. **Quorum parameters** — K, the model mix, and which statement ranks require a full quorum
   versus a single auditor. Decide on real amendment traffic, not a priori.
5. **Sketch formalism** — an annotation DSL over the program versus a skeleton Coq file with
   admits (both compile to the same graph). Decide by writing one real sketch each way.

---

## 17. References

- [LLM4Rocq/rocq-mcp](https://github.com/LLM4Rocq/rocq-mcp) — 13-tool MCP server over `coqc` + petanque;
  the module-wrapping verification trick and `rocq_step_multi` fan-out are directly worth borrowing.
- [coq-lsp petanque](https://github.com/ejgallego/coq-lsp/tree/main/petanque) and
  [PROTOCOL.md](https://github.com/ejgallego/coq-lsp/blob/main/etc/doc/PROTOCOL.md) — `Hyp`/`Goal`/`GoalConfig`
  types, `petanque/{start,run,goals,premises,ast,state/eq,state/hash}`.
- [Alectryon](https://github.com/cpitclaudel/alectryon) — the canonical whole-file tactic-by-tactic
  proof-state capture, via SerAPI. Good reference for the offline annotation path.
- [CoqPyt](https://arxiv.org/pdf/2405.04282) — Python proof navigation; prior art for Layer 1.
- [Iris Proof Mode (POPL'17)](https://iris-project.org/pdfs/2017-popl-proofmode-final.pdf) and
  [iris/docs/proof_mode.md](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md) —
  the `Π; Σ ⊩ Q` judgement, `envs_entails`, `Envs Γp Γs c`, `iStopProof`.
- [Atomic](https://github.com/bastani-inc/atomic) — DAG workflows, skills, subagents, gates,
  checkpoints; built on [Pi](https://pi.dev/).
- [The Future is Ours: Prophecy Variables in Separation Logic (POPL'20)](https://iris-project.org/pdfs/2020-popl-prophecies-final.pdf),
  Iris's `lib/atomic.v`, and the `iris-examples` logatom directory — raw material for the logatom
  skill pack.
- [QuickChick](https://github.com/QuickChick/QuickChick) — property-based testing for the
  truth-probe sentinel.
- Lean-side inspiration: LeanDojo (tracing + premise selection), Pantograph (goal-level API),
  lean-lsp-mcp. Premise selection is the transferable idea.
