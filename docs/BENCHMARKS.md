# Benchmarks: hard Iris developments, held out and isolated

PLAN.md 13 asks for held-out lemmas from real developments. This is that, on a real
concurrent-separation-logic development — [bigatomic-mechanization][repo] — with the
contamination controls a *public* corpus needs.

[repo]: https://github.com/cmuparlay/bigatomic-mechanization

## The ladder

Five rungs, in increasing order of held-out proof size. Everything except the named
specifications is given: the implementation, the invariants, the ghost-state plan and
every helper lemma, exactly as the original had them. Only the tactic work is removed.

| rung | file | held out | hardest single proof |
|---|---:|---:|---|
| `rwcas` | 317 L | 116 L | `write_spec` 92 L / 119 tactics |
| `seqlock` | 783 L | 223 L | `read_spec` 112 L / 180 tactics |
| `seqlock_wf` | 1123 L | 299 L | `write_spec` 178 L / 285 tactics |
| `cached_strong` | 3180 L | 935 L | `cas_spec` 712 L / 1069 tactics |
| `cached_wf` | 3320 L | 1068 L | `cas_spec` 712 L / 1069 tactics |

`cached_strong` is the **strongly linearizable implementation, without prophecy**
(upstream commit `251ff8b`, the parent of "Make read non-strongly linearizable").
Its `cas_spec` is byte-identical to `cached_wf`'s and its `read'_spec` is 147 L
against 280 L — so running both isolates the cost of the prophecy-and-helping
argument from everything else in the development.

`rwcas` is the smallest example of the same pattern: a prophecy predicts whether a
`CmpXchg` will succeed, and a writer prophesied to fail parks its atomic update in an
invariant for a successful writer to commit on its behalf.

## Porting

Upstream targets Iris ≥ 4.3; the pinned switch is 4.5.0. Four renames, all mechanical:

```
heapG                        → heapGS
auth_update_frac_alloc       → auth_update_dfrac_alloc
auth_both_frac_valid_discrete → auth_both_dfrac_valid_discrete
auth_auth_frac_op_inv        → auth_auth_dfrac_op_inv
```

`eval/corpus/bench/../port.sh` does this by iteration: compile, read the first
"not found" identifier, try the frac→dfrac rename, repeat. `CachedWaitFree.v` needed
no changes at all.

## Building the corpus

The upstream sources are **not vendored**: their proofs are the answer key, and the
point of the corpus is that the answer key is not reachable from a worker.

```bash
PCP_BENCH_SRC=/path/to/ported/sources ./eval/corpus/bench/build.sh
```

`eval/make_benchmark.py` holds out the named proofs, anonymises the development, and
writes the answer key somewhere else entirely. It **verifies by compiling** — a
benchmark that does not build is worse than no benchmark.

## Design rungs: the invariant is the task

`rwcas_design` gives the worker **the implementation and the specifications, and
nothing else**. `value`, `rwcas_inv` and `is_rwcas` are present but defined as
`True`, which makes the specifications unprovable as they stand; the ghost-state
imports, the resource algebra, the helper lemmas and every comment are gone.
Designing them is the task.

What may change is declared by the developer, in `design.json`, and enforced by
comparison rather than by instruction:

```json
{ "mutable": ["is_rwcas", "rwcasG", "rwcas_inv", "value"],
  "allow_additions": true, "allow_imports": true }
```

`rwcasG` is mutable because a designer that invents ghost state must be able to
declare it; imports are **additive** — a design that picks `ghost_var` has to be able
to import it, but removing an existing import changes what the surrounding code
means. A design that touches anything else is refused, whether it came from a
decomposer or a worker (`pcp check --design`).

### The degenerate solution, and the obligation that blocks it

Freezing the three specifications is not enough to make the rung hard. Nothing in
them requires `is_rwcas` to be *shared*, so this design passes everything:

```coq
Definition value (γ : gname) (n : Z) : iProp Σ := ghost_var γ (1/2) n.
Definition is_rwcas (γ : gname) (v : val) : iProp Σ :=
  (∃ (l : loc) (n : Z), ⌜v = #l⌝ ∗ l ↦ #n ∗ ghost_var γ (1/2) n)%I.
```

Exclusive ownership of the cell. All three specifications go through, `rwcas_inv` is
left as `True`, and both `Print Assumptions` come back `Closed under the global
context` — a clean gate pass. `write_spec` is twelve lines whose only interesting
step is `wp_cmpxchg_suc`: with no interference the CmpXchg cannot fail, so the
prophecy is stepped past rather than reasoned about and the helping protocol is never
needed. The rung would have measured nothing.

Note what is *not* the hole. `value` cannot be blanked to `True`: opening the atomic
update yields an opaque `n`, the load returns the physical `m`, and committing needs
`Φ #n` — nothing connects them, so `read_spec` already forces `value` to pin down the
observable. `new_rwcas_spec` blocks the other direction, since `False` cannot be
allocated from `True`. Agreement lemmas and read-back clients add nothing.

The hole is sharing, and one held-out obligation closes it:

```coq
Lemma is_rwcas_persistent (γ : gname) (v : val) : Persistent (is_rwcas γ v).
```

`--persistent is_rwcas` inserts it **given proved** (`apply _.`) and does *not* hold
it out. Holding it out would make it inert: the stub is `True`, which is persistent,
so it would sit there as an `Admitted.` proving nothing until some worker bothered to
discharge it. Left proved, every compile enforces it — including the design-compile
check in `_apply_design` — so a degenerate design is rejected at adoption, before a
worker is dispatched, and the decomposer gets the error as revision feedback:

```
the design does not compile: Error: Cannot infer this placeholder of type
"Persistent (is_rwcas γ v)" (no type class instance found)
```

It is registered in `design.json` under `results`, so it is a **frozen result** and no
design may restate it away. The generator's reference compile checks the guard was
satisfiable by the design it guards, so a rung can never ship an impossible one.

Every design rung needs this. A rung that stubs a client-facing predicate without it
is measuring whether the model can find the easy way out.

The first orchestrated run on this rung died on `The reference ghost_varG was not
found in the current environment`, from two causes worth separating:

1. **A restriction.** A design fragment had to be a named declaration, so an inline
   `Require` was rejected outright — the design had chosen `ghost_var` for its ghost
   state and had no permitted way to import it. A design fragment is now *any*
   non-proof vernacular: definitions, classes, notations, scopes, `Require` lines.
   The only two things it may not be are a proof and a new obligation (an obligation
   goes in `children`, so it gets stated, frozen and dispatched like any other).
   Preamble vernacular is hoisted out of the `Section` automatically, because where
   a `Require` is legal is not the designer's problem to solve.
2. **A missing check.** The design was adopted **without being compiled**, so five
   workers each spent ~20 turns rediscovering the same unrelated failure. Designs are
   now compiled before anything is dispatched against them, and a failure feeds the
   compiler's own error into a revision round.

## Contamination control

The solutions are on GitHub and in an iris-examples merge request, and — less
obviously — they can end up *on this machine*: an agent session's transcript is a
file under `$HOME`, so if the reference proof was ever pasted into a session, a
worker with `Bash` can grep it out. Four layers, in decreasing order of strength:

1. **A masked `$HOME`.** `--sandbox` runs each worker under bubblewrap with `$HOME`
   replaced by a tmpfs and only the provider's credential files bound back. Session
   transcripts, shell history and stray checkouts are simply not there.
2. **The answer key is masked** and the repo is read-only. The only writable
   directory is the node's own workdir.
3. **Anonymised identifiers.** `write_spec` becomes `fc23_spec`, `rwcas_inv` becomes
   `eb16_inv`. Role suffixes survive so the task stays readable. A memorised lemma
   name is no longer a handle.
4. **Code forges and search engines are blackholed** in the sandbox's `/etc/hosts`.

### Documentation is *not* blocked

Layer 4 would be too blunt on its own — an agent that cannot read the Iris
documentation is being measured on the wrong thing. It is affordable only because the
worker does not need the network for documentation:

- the **Iris and std++ sources** are bound into the sandbox — the same version the
  goal is stated in, which is better than anything online;
- `pcp docs` builds a grep-able index of **every declaration in them** (11 646 of
  them) and the packet points the worker at it;
- documentation *sites* (`iris-project.org`, `rocq-prover.org`, `coq.inria.fr`,
  arXiv, Stack Overflow) are left reachable. They carry papers and manuals, not proof
  scripts.

### What this does not do

It does not prove a model has not memorised the proof structure of a public
development. Anonymisation makes recall harder, not impossible. **Treat a solve rate
on a public corpus as an upper bound**, and compare against a private development
before believing it.

The sandbox also is not an adversary-proof jail: with the network up so the worker can
reach its provider, `/etc/hosts` stops an agent that reaches for a URL, not one that
reaches for an IP. `network=False` is airtight but only usable with a runner that
executes the model outside the sandbox.

## Climbing the ladder: what a rung is allowed to carry

The rungs are the same development at growing scale, and a person working through
them would not restart from nothing each time. They would have their own previous
proof open in the next buffer, and they would have read the paper. `eval/ladder.py`
gives a rung exactly that and nothing else:

```bash
python eval/ladder.py --stamp overnight              # the whole ladder
python eval/ladder.py --only rwcas seqlock           # a prefix
python eval/ladder.py --no-carry --no-paper          # every rung cold, for contrast
```

- **The paper.** `.pcp/library/paper` holds arXiv:2501.07503 (*Big Atomics*), the
  algorithms paper these developments mechanise: pseudocode, linearizability
  arguments in prose, experiments. Checked before it was admitted — it contains no
  Coq, no Iris, no ghost state, no prophecy. It says *why* the algorithm is correct;
  the proof obligations are still the run's.
- **Earlier rungs' own solutions.** After each rung, `<record>/<run>/solution/` is
  copied to `.pcp/library/solved/<rung>/`. That file is what *this system* produced,
  never what the corpus knew. It is exported whether or not the rung integrated, and
  carries a `(* Produced by proof-copilot … COMPLETE / INCOMPLETE *)` header so
  nothing downstream reads an `Admitted` as a result.

Everything that was closed stays closed. `--library` binds **after** the masks, so
`eval/corpus/` (every other rung — for a design rung, the answer), `.pcp/reference/`,
`docs/`, `tests/`, `.git` and the operator's `$HOME` are gone regardless of what the
library holds. `_assert_library_is_clean` refuses to start a run if any `.v` in the
library lacks the generated-by header, because a reference proof reaching a worker
does not make the run fail — it makes every number after it a lie.

Whatever a rung is given, the packet **names** (`render_library`). This is the same
lesson as `describe_tools`: a granted resource the worker is never told about is an
ungranted resource, and it also means the trace records what the run actually had.

## Spec-only design rungs: results (2026-09-04/05)

Every design rung run with `--brief spec-only --no-carry --no-paper`: the worker and the
decomposer saw the implementation and the specifications and nothing else. All three targets
integrate (`Qed`, `Print Assumptions` clean). Costs are the sum over every attempt on the rung's
graph, including the runs that failed while the orchestration was being fixed.

| rung | target | design rounds | wall clock | cost | what it took |
|---|---|---|---|---|---|
| `rwcas_design` | `write_spec` | 1 | 45 min | $14 | first proposal held |
| `seqlock_design` | `write_spec` | 1 (on rerun) | 34 min | $15 | first run lost to an unrelated bug, rerun integrated |
| `seqlock_wf_design` | `fc50_spec` | 8 | ~2 days of runs | $98 | rounds 4–7 each lost to a decomposer *shape* slip (key synonyms, root restated as a child, a one-token syntax error, `statement` used for a definition); round 8 held, and its last two children were contested validly (a resource stated outside a `□`-boxed triple) and settled by the approver **restating** them -- 10 s each, no ninth round |

The `seqlock_wf_design` row is the one that changed the orchestration: the repair tier (a
mis-shaped design is re-asked at the cheap tier, never a new round), tolerant protocol reading,
`standing_failures` in the revision loop, the restatement verdict, the cheap tier after every
revision's dispatch, and the resource-outside-triple sentinel all come from its failures. Its
solution file is `PARTIAL` for the *file*: the two specifications that were not the target
(`bd42_spec`, `x51_spec`) stay `Admitted`. Records: `.pcp/runs/ladder_spec3_20260904_seqlock_wf_design/`
(final run `20260905-195056`); the ladder's own summary JSON still holds the timed-out row from the
first attempt, because manual resumes are not written back to it.

## Running

```bash
python eval/harness.py \
  --corpus eval/corpus/bench/rwcas --reference .pcp/reference/rwcas \
  --sandbox --runner claude --record .pcp/records
```

Then read the traces rather than the score:

```bash
pcp failures .pcp/records/<run-id>
pcp failures .pcp/records/<run-id> --class mask-arithmetic
```

Every attempt leaves the packet the worker saw, its full event stream, what it sent
back, the gate's report, and a classification. A solve rate says whether the tooling
helped; the traces say what to build next.

### Read the solves, not only the failures

The instructive question about a *successful* proof is how much friction it cost. A
lemma one-shot and a lemma won after six turns of mask arithmetic score identically
and mean completely different things — the second is a standing invitation to build
mask tooling.

So workers run with `--output-format stream-json`, and every attempt records:

- **turns**, **tool calls**, and **gate-check iterations** — how many times it asked
  Rocq whether it was right yet;
- **token usage and dollars** — §13's *tokens per solved lemma*, which is otherwise
  unobtainable for a subscription CLI runner;
- **the friction sequence** — every error the worker saw, classified against the same
  taxonomy as terminal failures, and reported **whether or not it solved**.

The first run of this benchmark was done with `--output-format text`, which reports
only the closing message. It scored `tokens/solved 0`, `tools/solved 0.0`, and kept
about a kilobyte of prose per solve — the score was there, and everything that would
have explained it was not. That is the failure mode this section exists to prevent.

## Why these are slow, and what was done about it

These files take minutes to compile because of proof automation, and the per-node
gate compiles the file on **every** worker iteration. That is unusable at 3320 lines.

The fix is `stub_prefix`: for a *per-node* check, every other proof in the file is
replaced by `Admitted.`, leaving statements only. It is sound by the same argument as
Claim 1 — `Qed` proofs are opaque, so this proof can depend only on its siblings'
statements, never on their bodies — and integration still compiles everything for
real.

| file | full compile | prefix stubbed |
|---|---:|---:|
| `rwcas.v` | 11.6 s | 2.1 s |
| `seqlock.v` | 32.5 s | 2.9 s |
| `seqlockWf.v` | 55.1 s | 3.1 s |

The stubbed time is roughly constant in file size, because it is statements-only
elaboration. That is what makes `pcp check` usable as an inner loop.

## `proof_open` was the other half of the same problem

The gate was not the only thing paying for other people's proof automation.
`petanque/start` has to elaborate everything before the theorem, so opening a lemma
for interactive stepping cost as much as compiling the file — which would have made
the state layer unusable on exactly the developments it exists for.

Three levers, measured rather than assumed:

| lever | `seqlockWf.v` (1123 L) | `CachedWaitFree.v` (3320 L) |
|---|---:|---:|
| plain `proof_open` | 23.5 s | minutes |
| + statements-only twin | 3.1 s | 5.7 s |
| + warm document cache | 0.1 s | 0.3 s |

1. **A statements-only twin.** Same argument as the gate's `stub_prefix`: `Qed`
   proofs are opaque, so the goal state at a theorem depends on the *statements*
   before it and never on their bodies. `tests/test_state_layer.py` asserts the
   equality rather than trusting the argument — stubbed and unstubbed produce an
   identical goal.
2. **Pool affinity.** coq-lsp caches a checked document, so the *second* `start` on a
   file costs 0.3 s against 22 s for the first. The session pool now routes a file
   back to the server that already knows it, which matters far more than spreading
   work across servers.
3. **`-async-proofs` does not help — it is slower.** Measured on `seqlockWf.v`:
   56.9 s serial, 63.5 s at `-j 16`, 66.3 s at `-j 64`. Each async worker re-loads
   the whole Iris environment, and the marshalling dominates when the environment is
   large and the individual proofs are not. Recorded here so nobody tries it twice.
   What makes interactive stepping feel fast is the incremental document cache, which
   is lever 2, not proof-level parallelism.

## Budgets, and partial credit

The hard tier does not fit in a short budget. On the first run `rwcas`'s `write_spec`
— the prophecy-and-helping one — was killed at 1500 s having written 91 lines and 152
tactics, and having independently reconstructed the right architecture: prophecy
allocation, the case split on the prophesied outcome, and a helping request
registered in the invariant.

It scored zero, and worse, **the 91 lines were discarded**: the packet tells a worker
to edit the assembled `.v` in place, and the answer reader only looked at
`answer.json`, `proof.v` and fenced blocks. PLAN.md 6 says a kill is followed by a
requeue "with the partial trace as evidence"; the evidence was on the floor.

Both are fixed — the reader now recovers the body from the edited file, and reports
it as a *partial* rather than a claimed success — but the lesson generalises: on this
tier, give workers a real budget (2400 s+) and read the partials.
