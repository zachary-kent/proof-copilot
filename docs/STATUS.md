# Status: what is built, what is not, and why

Written 2026-09-04, after the from-scratch rewrite (the original implementation is git `40d5b0b`).
The design is [`PLAN.md`](PLAN.md); the structure and the guarantees the structure buys are
[`ARCHITECTURE.md`](ARCHITECTURE.md). This file is the inventory.

## Why a rewrite

An audit of the original tree found 451 defects, 22 of them critical: a worker body of
`Abort.` plus a redefinition of the lemma passed every gate check; the gate kept compiler output
in shared instance state while being run from parallel tasks; petanque state ids were sent to
whichever pool server was free; `--node-seconds` never reached a worker; stale `answer.json`
files were credited to new attempts; six independent regex scanners disagreed about where a
Rocq comment ends. Nearly all of these fall into a dozen classes, and each class is now
precluded by a structural rule rather than a fix (ARCHITECTURE.md §8). Every remaining bug has a
regression test named after its scenario.

## Toolchain (Phase 0) — unchanged

Pinned in [`env.sh`](../env.sh): OCaml 5.2.1, Rocq 9.1.1, coq-lsp 0.2.5+9.1 (ships `pet`, stdio),
std++ 1.13.0, Iris 4.5.0. Facts the code depends on: Rocq's `Timeout` takes an integer; the
Rocq 9 front end is `rocq compile`; coqc's `characters a-b` are byte offsets; `Print Assumptions`
prints `X is assumed to be guarded` (colon-less) under `Unset Guard Checking` and
`X relies on an unsafe hierarchy` under `Unset Universe Checking`.

## Phase 1 — the daily loop

`pcp prove Foo.v lemma --plan plan.v` runs end to end. Verified on the canary with scripted
workers (CI) and with `--runner claude`: three obligations dispatched in parallel, gated,
integrated with a clean `Print Assumptions` in 36 s; the same under `--sandbox --state-tools`
in 23 s with the MCP server connected inside bubblewrap.

| plan | module | note |
|---|---|---|
| §8.1 obligation graph, two ledgers | `pcp/orch/graph.py`, `model.py` | SQLite, schema v2 with a migration from v1; every transition validated against the lattice; bodies writable only by the prover role |
| §8.3 two-zone assembly | `pcp/rocq/assemble.py` | patches reach only proof-body spans; scopes tracked through `Module Import`, aliases and `Module Type` |
| §8.4 free sentinels | `pcp/orch/sentinels.py` | duplicates, restated root, converging failures, partial-correctness (Texan triples too), non-persistent resources stated outside a `□`-boxed triple (blocking; repaired at the cheap tier), hygiene — run on plans **and** decomposer proposals |
| §8.7 integrity gate | `pcp/orch/gate.py`, `pcp/rocq/body.py`, `assumptions.py` | immutable; bodies tactic-only by construction; structural recheck of the assembly; `Locate`-keyed assumptions with qualified names |
| §8.11 dispatch, retry, resume | `pcp/orch/schedule.py`, `prove/` | per-node isolation, attempts bounded across runs, fresh directory per attempt, retry sees the partial, salvage on resume, run lock |
| §11 runners | `pcp/orch/runners/` | one factory (`RunnerSpec`) that refuses ignored options; exit codes and stream verdicts are first-class; process-group kills; bubblewrap with an env allowlist |
| §8.11 handoff | `pcp/orch/handoff.py` | stuck node → `.v` in your editor |
| §8.5 incremental amendments | `pcp/orch/prove/amendments.py`, `pcp/orch/amend.py` | a prover that needs a fact the invariant lacks asks for it (`amendments` in `answer.json`); a strengthening that compiles is applied mechanically, every proof is replayed, and only the close sites that broke re-open — no design round; `replace` requests and contests go to a cheap **approver** (`--approver-effort medium`) that accepts, adjusts or rejects, or tells a contesting prover its strategy was wrong; contests and twice-failed nodes (`--review-after`) go to the approver, who may restate the obligation in place (`AmendmentRun.restate`) |
| §6/§8.11 run durability | `pcp/orch/outage.py`, `supervise.py`, `prove/resume.py` | provider outages pause the run instead of failing nodes (probe with backoff, reset times honoured, `--pause-hours`); in-flight partials recovered on resume; `pcp prove --supervise` restarts from the graph after a crash; `eval/ladder.py --resume` |
| §8.11 canary | `tests/test_canary.py` | integration, one evidence-carrying retry, no wedge, crash-resume, ungated qed is stuck, one-screen report, lock excludes a second run |

## Phases 2–5 — the state layer

| plan | module | note |
|---|---|---|
| §6 session pool | `pcp/state/petanque.py`, `pool.py`, `session.py` | a session is bound to the process that created its states; every call has a Python-side wall clock; a restart invalidates its sessions with a message that says what to do; hard memory limit via a per-uid wrapper, no `PR_SET_PDEATHSIG` |
| §3.1 printer parser | `pcp/state/ipm/parse.py` | all four separator shapes; anonymous `_ : P` hypotheses; 2 030 golden states |
| §3.1 reflected dump | `coq/IDump.v`, `pcp/state/ipm/reflect.py` | wired in as the primary path when `--reflect`/`reflect=True`; the printer is the fallback |
| §3.2 model, skeletons | `pcp/state/ipm/model.py`, `skeleton.py` | modality read at the head only; `twp` detected from `[{ }]`; every fupd shape; Iris's real precedence |
| §4 ledger | `pcp/state/ledger/` | name-first matching, evar-aware hashing incl. unicode evars, goal parentage incl. closing a non-final goal, `unknown` on ambiguity |
| §4.3 persistence oracle | `pcp/state/ipm/oracle.py` | always at the step's own state |
| §5 context economy | `pcp/state/render.py`, `digest.py` | explicit selection beats diff-only; `full` never folds; elision always reported |
| §7 tool surface | `pcp/mcp/server.py` | 10 tools, capped at 12; thread-safe; a dead petanque is reported as a lost session |
| §7 pattern compiler + aligner | `pcp/state/ipm/pattern.py`, `diagnose.py` | every IPM token; conjunction patterns are binary as Iris 4.5 requires |
| §5/§7 retrieval | `pcp/state/search.py` | quoted substring `Search`, grep fallback over the sources |
| §7 diagnosis on the compile path | `pcp/state/explain.py` | `pcp check` replays the failing body by byte offset, ignores located warnings, maps Qed-time errors |

## Phases 7–9 — designed, flagged off

Present as code so the decisions live next to what they constrain, and **off by default**
(`pcp/config/flags.py`). The canary runs with all of it disabled.

| plan | module | built |
|---|---|---|
| §8.2 recursive decomposition | `pcp/orch/decompose.py` | policy + difficulty estimate + no-gap check; the recursion is not wired into `prove` |
| §8.5 amendment lattice | `pcp/orch/amend.py` | machine-checked `refute` (binders kept), taint, impact reports, audit-rung routing, replay-first salvage (used by resume). Quorums and shim TTLs are not built |
| §8.6 decomposer role | `pcp/orch/decomposer.py`, `prove/design.py` | read-only toolbox, a proposal type with no proof field, a store that refuses proof writes; every design fragment passes the gate's static scan; the contract is loaded once from the corpus and carried through every round |
| §9.3 sketch compiler | `pcp/orch/sketch.py` | annotation DSL → frozen obligations |
| §10 cockpit | `pcp/dash/` | `pcp serve` (read-only, resumable SSE) and `pcp report`. Steering tools are not built |
| §11 provider profiles | `pcp/config/providers.py` | tiers as ordered preferences; a binding applies only when its provider matches the runner |
| §13 evaluation | `eval/harness.py`, `ladder.py`, `ablations.py`, `make_benchmark.py` | one runner per ablation arm; the ladder's `--brief spec-only` gives a rung only the specification |

## Deliberately not built

- **An embedding index for premise retrieval** (§7): `Search` at the goal plus grep is the
  baseline it would have to beat.
- **`AtomicRunner`** (§11): deferred; `pcp/orch/runners/atomic.py` records the decision.
- **Preservation probes** for invariants (§9.2): research, not a deliverable.
- **A bespoke TUI** (§10).
- **Quorum audits, OR-nodes, shim TTLs** (§8.5): two rungs first.
- **A mid-flight ping for one-shot CLIs** (§6): not implementable for `claude -p`; the runner is
  honest about it and gives the worker its whole budget.

## Verification

The suite (about 1 100 tests) runs in about five minutes with the toolchain and skips its Rocq/petanque parts cleanly
without one — a tested property (`tests/test_layering.py`). Property tests round-trip thousands
of generated Iris props through the skeleton parser and align every compiled intro pattern with
its prop; golden tests replay 2 030 real Iris goal states; the gate, the ledger, the oracle, the
reflected dump, the MCP tools and the pipeline are exercised against actual Rocq. Three review
passes attacked the finished packages as adversaries (a wrong proof accepted, a hang, a lost
session, a wedged run) and every confirmed finding became a regression test.
