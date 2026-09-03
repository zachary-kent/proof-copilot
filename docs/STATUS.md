# Status: what is built, what is not, and why

Written 2026-08-28, against [`PLAN.md`](PLAN.md). The plan's own phasing is the ordering here:
Phases 0–1 are unconditional and come first, Phases 2–6 are measured upgrades to worker solve
rate, Phases 7–9 are built only if the daily loop justifies them.

## Toolchain (Phase 0) — done

Pinned in [`env.sh`](../env.sh), built by [`scripts/setup-toolchain.sh`](../scripts/setup-toolchain.sh):

| component | pin | note |
|---|---|---|
| OCaml | 5.2.1 | coq-lsp needs `>= 5.0, < 5.3` |
| Rocq | 9.1.1 | `rocq-core` / `rocq-stdlib` |
| coq-lsp | 0.2.5+9.1 | ships `pet`, the petanque binary |
| std++ | 1.13.0 | |
| Iris | 4.5.0 | plus `rocq-iris-heap-lang` |

Two findings that changed the code:

- **coq-lsp 0.2.5 ships `pet` (stdio), not `pet-server` (socket).** `SessionPool` drives either;
  it prefers the socket server when present and falls back to stdio.
- **Rocq's `Timeout` vernacular takes an integer.** pytanque wraps every `run` in it, so a float
  timeout fails with `This number is not an integer` — a confusing error a long way from its
  cause. `session.py` coerces.

## Phase 1 — the daily loop — done, and exercised against live models

`pcp prove Foo.v lemma --plan plan.v` runs end to end. Verified on the canary with the mock
runner (deterministic, in CI) and with `--runner claude` against real workers: 3 obligations
dispatched in parallel, gated, integrated with a clean `Print Assumptions`, in 23 s.

| plan | module | note |
|---|---|---|
| §8.1 obligation graph, two ledgers | `pcp/orch/graph.py` | SQLite at `.pcp/graph.db`; epochs, pinned edges, events |
| §8.3 two-zone assembly | `pcp/orch/assemble.py` | patches reach only proof-body spans |
| §8.4 free sentinels | `pcp/orch/sentinels.py` | duplicates, partial-correctness, reduction, converging failures, hygiene |
| §8.7 integrity gate | `pcp/orch/gate.py` | all eight checks; model-free |
| §8.11 dispatch, retry, resume | `pcp/orch/schedule.py`, `prove.py` | max-parallel, one evidence-informed retry |
| §11 runners | `pcp/orch/runners/` | codex CLI, claude headless, Claude Code subagent, direct API, mock |
| §8.11 handoff | `pcp/orch/handoff.py` | stuck node → `.v` in your editor |
| §8.11 canary | `tests/test_canary.py` | 7 tests: integration, retry, no-wedge, resume, gate-jumping, admit-smuggling, report length |

### The gate, check by check

All eight items of §8.7 are implemented. Two deserve comment:

- **Unused-premise report** is a *removal probe*, not a term scan. `Qed` makes the proof term
  opaque, and even with `Defined` the printer elides implicit arguments — a premise that is used
  can look absent. Reporting a used premise as unused would send you to weaken a statement that
  is exactly right, so the check restates the lemma without the premise and re-runs the proof.
  Ground truth, one compile per candidate, opt-in and bounded.
- **Axiom hygiene** allows sibling nodes that are still `Admitted` stubs. That is the content of
  Claim 1: a per-node gate that refused stubs would serialise the frontier. Integration, where
  there are no stubs left, is where the whitelist bites.

## Phases 2–5 — the state layer — built, and validated on real Iris

| plan | module | note |
|---|---|---|
| §3.1 printer parser (v1) | `pcp/core/ipm/parse.py` | all four separator shapes |
| §3.1 reflected dump (v2) | `coq/IDump.v`, `pcp/core/ipm/reflect.py` | **the spike succeeded** — see below |
| §3.2 data model, skeletons | `pcp/core/ipm/model.py`, `skeleton.py` | modality is a first-class block |
| §4 resource ledger | `pcp/core/ledger/` | name-first matching, evar-aware hashing, goal parentage, `unknown` on ambiguity |
| §4.3 persistence oracle | `pcp/core/ipm/oracle.py` | asks in IPM's own language, not by re-parsing printed props |
| §5 context economy | `pcp/core/render.py` | select / mode / auto-fold / diff-only / relevance; elision is always reported |
| §6 session pool | `pcp/core/session.py` | state-id multiplexing, RSS cap, `Timeout`, state-hash loop detection |
| §7 tool surface | `pcp/mcp/server.py` | 10 tools, capped at 12 |
| §7 pattern compiler + aligner | `pcp/core/ipm/pattern.py`, `pcp/mcp/diagnose.py` | diagnosis is by construction, not opt-in |
| §5/§7 retrieval | `pcp/core/search.py` | `Search` at the goal + grep passthrough; no embedding index |
| §7 diagnosis on the compile path | `pcp/mcp/explain.py` | `pcp check` replays a failed proof through petanque and diagnoses the failing tactic |

**Diagnosis is delivered where the worker already is.** An ablation measured five of
seven workers never touching a granted MCP tool while 100% of them ran the compiler, so
`pcp check` now does the replay itself: it finds the proof block the compiler error falls
in, steps it through petanque, and reports the Iris goal as it stood at the failing
tactic. Wrapping `coqc` was considered and rejected — the gate's authority rests on
"it compiles" meaning what `coqc` means. This is *not* an alternative to the state layer:
measured, `diagnose(tactic, error, goal=None)` returns the error unchanged, so the replay
is what makes the report worth anything. It is granted with the state tools
(`pcp-node.json:diagnose`) so an ablation's control arm cannot get the state layer
through the checker.

**The Phase-2 spike is resolved: tactic message output is cleanly capturable through petanque
`run`.** Each Rocq message arrives as its own entry in `State.feedback`, so one `Message.print`
per hypothesis survives transport with its record boundaries intact. The reflected `iDump` path
works, including the thing the printer parser fundamentally cannot do — `Set Printing All` for
*one* hypothesis while everything else stays folded. The printer parser is kept as the fallback.

## Phases 7–9 — the speculative machinery — designed, flagged off

Present as code so the decisions live next to what they constrain, and **off by default**
(`pcp/orch/providers.py: DEFAULT_FLAGS`). None of it is on the daily loop's path, and the canary
runs with all of it disabled.

| plan | module | built |
|---|---|---|
| §8.2 recursive decomposition, depth cap, budgets | `pcp/orch/decompose.py` | policy + difficulty estimate + no-gap check; the recursion itself is not wired into `prove` |
| §8.5 amendment lattice | `pcp/orch/amend.py` | machine-checked `refute`, taint propagation, impact reports, audit-rung routing, replay-first salvage. Quorum plumbing and shim TTLs are **not** built, per the plan's own "two rungs first" |
| §9.3 sketch compiler | `pcp/orch/sketch.py` | annotation DSL → frozen obligations, with allocation witnesses |
| §10 cockpit | `pcp/dash/` | `pcp serve` (SSE over SQLite) and `pcp report`. Steering MCP tools (`orch_*`) are **not** built |
| §11 provider profiles | `pcp/orch/providers.py` | tiers, auth modes, secrets refusal |
| §13 evaluation | `eval/harness.py`, `eval/ablations.py` | held-out-lemma harness and the five-rung ablation ladder |
| §13 benchmark corpora | `eval/make_benchmark.py`, `docs/BENCHMARKS.md` | five rungs from a real CSL development, held out, anonymised, sandboxed |
| §13 failure taxonomy | `pcp/orch/failures.py`, `pcp/orch/record.py` | every attempt recorded and classified; `pcp failures` aggregates |
| §13 worker traces | `pcp/orch/runners/stream.py` | turns, tool calls, tokens, dollars, and the friction sequence — recorded on solves as well as failures |
| §6 worker isolation | `pcp/orch/runners/sandbox.py` | bubblewrap: masked `$HOME`, hidden answer key, blackholed forges |
| §8.6 role separation | `pcp/orch/decomposer.py`, `decompose.py` | the decomposer states obligations and cannot prove: read-only toolbox, a proposal type with no field for a proof, and a store that refuses proof writes from any role but `prover` |
| §8.2 orchestration required | `pcp/orch/prove.py` | `require_orchestration` defaults on; a run with no plan must decompose first |
| §8.5 progressive design revision | `pcp/orch/prove.py`, `decomposer.py` | bounded design rounds driven by prover evidence, with replay-first salvage |
| §9.1/9.3 design contract | `pcp/orch/contract.py` | the developer declares which definitions may change; enforced by comparison, imports additive-only |
| §11 role → model/effort | `pcp/orch/providers.py` | providers detected, per-role model and effort, `pcp models` |

## Benchmarks on real developments

`docs/BENCHMARKS.md` covers this in full. Two findings worth recording here because
they changed the code:

- **Per-node checks must stub the rest of the file.** These developments take minutes
  to compile because of proof automation, and the gate compiled the whole file on
  every worker iteration. `stub_prefix` replaces every *other* proof with `Admitted.`
  for a per-node check — sound by the same argument as Claim 1, since `Qed` proofs are
  opaque — and turns 55 s into 3 s, roughly constant in file size.
- **`proof_open` needed the same treatment as the gate.** Elaborating a file prefix
  cost 23.5 s on a 1123-line development; a statements-only twin plus pool affinity
  brings that to 3.1 s cold and 0.1 s warm, and 5.7 s / 0.3 s on the 3320-line one.
  `-async-proofs` was measured and *rejected* — it is 12–17% slower, because each
  worker re-loads the Iris environment.
- **The lookup threat is local as well as remote.** An agent session's transcript is a
  file under `$HOME`. Blocking the network while leaving `$HOME` readable would have
  left the reference proof one `grep` away.

## Roles, models and effort

Roles bind to models and effort levels, both derived from the providers actually
present and overridable per run (`--decomposer`, `--prover-model`,
`--decomposer-effort`, `--prover-effort`) or in `.pcp/config.toml`:

```
providers detected: anthropic
  decomposer  anthropic/claude-fable-5         effort xhigh
  prover      anthropic/claude-sonnet-5        effort medium
  auditor     anthropic/claude-opus-5          effort high
```

The decomposer gets the most effort because a bad decomposition is the most expensive
error in the pipeline — it is discovered only after the children's budget is spent.
Provers grind tactics in bulk, where the same spend buys more attempts than thinking.
Every attempt records the *resolved* model, not the runner's label: a run whose most
consequential decision cannot be attributed to a model is one you cannot conclude
from.

## Deliberately not built

- **An embedding index for premise retrieval.** Not built unless measured retrieval failures
  justify it (§7). `Search` at the goal plus grep is the baseline it would have to beat.
- **`AtomicRunner`.** Deferred (§11). Atomic's DAG is authored and acyclic; this graph is
  discovered at runtime with renegotiation cycles. `pcp/orch/runners/atomic.py` records the
  decision and refuses to pretend.
- **Preservation probes** for invariants. Stating one needs the pre-step symbolic state the proof
  itself computes; §9.2 calls this research, not a deliverable, and the code says so.
- **A bespoke TUI.** §10: the cockpit is the harness you already have, plus a browser tab.
- **Quorum audits, OR-nodes, shim TTLs.** §8.5 says two rungs first. They are designed in
  `amend.py`'s docstrings and routed to by `audit_rung`, but nothing implements them.

## Verification

433 tests. The Rocq-dependent ones skip cleanly without a toolchain, which is itself a tested
property (`tests/test_layering.py`): `pcp prove` must import and run where the only Rocq binary
is `coqc`.

- **Property tests** (`test_skeleton_fuzz.py`, `test_pattern_fuzz.py`): 3 500+ generated Iris
  props round-tripped through the skeleton parser; every compiled intro pattern must align with
  its prop, and every one-step corruption of a fitting pattern must be caught. These found five
  real parser bugs, including `P ∗-∗ Q` mis-read as a separating conjunction and `l ↦∗ vs`
  (heap_lang arrays) split at its `∗`.
- **Golden tests** (`test_goldens.py`): 2 030 goal states captured by replaying real proofs from
  the installed Iris library through petanque (`eval/extract_goldens.py`). Hypothesis counts are
  cross-checked against an independent reading of the same text.
- **Real-Rocq integration**: the gate, the ledger, the oracle, the reflected dump and the MCP
  tools are all exercised against actual Iris proofs, not fixtures.

Bugs found while building the benchmark ladder, all now covered by tests: Rocq comments **nest**,
so a non-greedy regex stripper left a dangling `*)` that surfaced as a syntax error a thousand
lines from its cause; the sandbox wrapper mutated the wrapped runner's `argv`, which races as soon
as the frontier dispatches in parallel; the generated `/etc/hosts` was created per attempt and
raced with `/tmp` cleanup; and the failure classifier blamed a worker for a bubblewrap failure,
which points the reader at the prompt instead of the harness.

Bugs the test suite caught that a reading would not have: a comment before a lemma hid the
declaration from the source lexer (13% of real Iris declarations were invisible); `Print
Assumptions` output was matched positionally against names scraped from the wrong stream, so a
`Warning:` line parsed as an axiom; crash-resume did not re-open nodes a previous run left
`stuck`; and `iDestruct` tactics were emitted without their terminating `.`, which Rocq reports
as a syntax error that reads like a pattern problem.

## Open decisions from §16

1. **Rocq/Iris pin** — settled at 9.1.1 / 4.5.0 by what coq-lsp 0.2.5 supports. Revisit when you
   point this at a real project.
2. **First runner** — `codex` is implemented first per the plan, but is not installed on this
   machine; `claude -p` is what the loop has actually been driven with.
3. **Whether Phase 7+ happens** — undecided, as intended. Decide on daily-loop measurements.
4. **Quorum parameters** — untouched. No amendment traffic exists yet.
5. **Sketch formalism** — both arms compile to the same graph today: the annotation DSL via
   `pcp sketch`, and the skeleton-with-admits arm via `pcp prove --plan`. Write one real sketch
   each way before choosing.
