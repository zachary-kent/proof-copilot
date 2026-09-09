# proof-copilot

Tooling for orchestrated, agent-driven proof engineering in Rocq — with a focus on affine
logics (Iris), where current LLM agents fail at resource accounting rather than at reasoning.

Two layers, deliberately separable:

- **`pcp-state`** — structured, diffable, per-hypothesis Iris proof state over Rocq/petanque.
  Tactic-by-tactic traces, a spatial-resource ledger that answers *"where did this hypothesis go?"*,
  and budgeted rendering so goals don't eat the context window. Python lib + CLI + MCP server.
- **`pcp-orch`** — an obligation-graph orchestrator: a frontier model decomposes a target into
  `Admitted` lemma statements; cheap models prove them in parallel; a machine-checkable gate
  (`Qed` + `Print Assumptions`) decides completion.

Design: [`docs/PLAN.md`](docs/PLAN.md) · How the code is organised and what it guarantees by
construction: [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) · What is built:
[`docs/STATUS.md`](docs/STATUS.md)

---

## Install

```bash
./scripts/setup-toolchain.sh     # Rocq 9.1.1 + coq-lsp 0.2.5 + Iris 4.5.0 / std++ 1.13.0
. ./env.sh
uv venv --python 3.11 .venv && . .venv/bin/activate
uv pip install -e '.[mcp,dev]' 'pytanque @ git+https://github.com/LLM4Rocq/pytanque'
pcp doctor
```

`pcp doctor` reports the toolchain, the Python deps and which runners are reachable. **Login is
delegated, never implemented**: it prints the command to run (`codex login`, Claude Code's
`/login`) rather than asking for a credential.

## The daily loop

You have a lemma and an intuition for its proof. You state the children; the orchestrator runs
the workers.

```bash
pcp prove Foo.v foo_correct --plan plan.v
```

`plan.v` is Rocq, not prose — child statements with `Proof. Admitted.`:

```coq
Lemma helper_swap (A B : PROP) : A ∗ B -∗ B ∗ A.
Proof. Admitted.
```

What happens:

1. **Statements freeze immediately**, by construction: a worker returns a *proof body*, the
   development is reassembled from the frozen source plus that body, and the body is checked to
   be tactic sentences and nothing else before Rocq ever sees it. Free sentinels run (duplicate
   detection, restated root, partial-correctness flag).
2. **The whole frontier dispatches at once.** Every frozen statement with an open proof is
   dispatchable *now* — its dependencies are admissible as `Admitted` stubs — so parallelism is
   bounded by your rate window, never by graph depth.
3. **Every return is gated deterministically**, with no model involved: assembly from the frozen
   store, structural recheck of the assembled file, `Proof using` discipline, compile,
   `Print Assumptions` ⊆ whitelist (module-qualified, keyed by `Locate` markers so nothing a proof
   prints can forge a block), no new admits, no escape hatches, no global registrations.
4. **Failures retry once with evidence**, and the retry sees the previous attempt's partial proof.
   Then they land back with you as `qed` / `stuck` / `contested`. `pcp handoff <node>` drops a
   stuck node into your editor as a `.v` with the statement, the best partial script, and the
   blame trace as comments.

```
3 qed · 0 stuck · 0 contested   (36s, 3 dispatches)
  qed       canary_main  (33s, 1 attempt(s))
  qed       canary_swap  (16s, 1 attempt(s))
  qed       canary_assoc  (19s, 1 attempt(s))

integrated: `canary_main` Qeds and Print Assumptions is clean.
```

A run always resumes from its graph; a crash mid-dispatch picks up where it stopped, a proof that
gated before the crash is salvaged rather than re-proved, and a partial left in a worker's file
becomes the next attempt's starting point. A provider outage (logged out, session limit) pauses the
run and it resumes by itself when the provider is back; `pcp prove --supervise` runs detached and
restarts from the graph after a crash. One `pcp prove` per graph: the run holds a lock. Watch it in a browser with `pcp serve`; check on it with `pcp status`; read every
attempt's packet, transcript, gate report and classification under `--record`.

When a prover discovers mid-proof that the invariant lacks a fact, it asks for it instead of
failing: a strengthening that compiles is applied mechanically, every proof is replayed, and only
the close sites that broke re-open with the change named in their packet. Contests are adjudicated
by a cheap approver before anything is redesigned, and so is any node that fails twice
(`--review-after`): the approver either corrects the statement in place or tells the prover what
to do differently, in seconds rather than another attempt's clock.

Without a plan, a read-only **decomposer** (a model granted `Read`/`Glob`/`Grep` and nothing else)
states the obligations and, on a design rung, the invariants; its proposal is compiled, checked
against the corpus's design contract, and revised in bounded rounds from the provers' evidence.

## The state layer

```bash
pcp trace Foo.v foo_correct -o trace.jsonl     # tactic-by-tactic Iris state + ledger
pcp ledger trace.jsonl blame --hyp H1          # what consumed H1, and how to repair it
pcp ledger trace.jsonl leftovers               # why iFrame/done is failing
pcp state trace.jsonl --select spatial --budget 2000
pcp destruct '∃ γ, own γ (◯ n) ∗ ⌜n = 3⌝'      # compile the iDestruct pattern
pcp docs                                       # index every Iris/std++ declaration
pcp mcp                                        # the same, as MCP tools
```

The ledger answers the question that eats the most time in Iris:

```
why is "HP" not available at step 5?
  "HP" was framed at step 2 by `iFrame "HP".`
  repair class: frame-later
  step 2 framed it into the goal -- frame later, or split the goal first.
```

…and when it cannot tell, it says `unknown` rather than guessing. A confidently wrong provenance
chain is worse than none.

Sessions are pinned to the petanque process that created their states, every call has a
wall clock, and a process that dies mid-session is reported as a *lost session* — never as
"your tactic failed".

## Two claims this is built on

**The lemma statement is the interface contract, and `Admitted` is a type-checked stub.** Because
`Qed` proofs are opaque, a proof written against an admitted lemma can depend only on its
*statement*. So work done against a stub is exactly the work that survives once the stub is
filled — which is why the whole frontier can go out in parallel, and why completion has a machine
oracle instead of a review.

**Iris debugging failures are resource-accounting failures.** "A spatial hypothesis was eliminated
early and is needed 40 steps later" is bookkeeping, not reasoning. Bookkeeping over 200 steps is
what a machine does well and an LLM does badly, so the flagship feature is a per-step resource
ledger rather than a better prompt.

## Layout

```
pcp/util/     stdlib-only helpers: subprocesses that die with their tree, atomic files, locks
pcp/config/   environment, feature flags, .pcp/config.toml, provider bindings
pcp/rocq/     Rocq text and coqc: the one lexer, declarations, body validation, assembly,
              Print Assumptions -- no petanque
pcp/state/    pcp-state: petanque process/pool/session, IPM model + parser + reflection,
              skeletons, patterns, ledger, render, search, diagnosis
pcp/mcp/      the tool surface (10 tools, hard-capped)
pcp/orch/     pcp-orch: SQLite graph, gate, packets, runners, scheduler, the prove pipeline,
              decomposer role, records, failure taxonomy
pcp/dash/     `pcp serve` (SSE over SQLite) and `pcp report`
pcp/cli/      the `pcp` command, one module per subcommand
coq/IDump.v   the Ltac2 reflected IPM dump
skills/       prover · decomposer · invariants · logatom
eval/         held-out-lemma harness, the ablation ladder, the design-rung ladder, the corpora
```

The import rule between layers (`pcp.orch` never imports `pcp.state`; the daily loop runs where
the only Rocq binary is `coqc`) is a test, `tests/test_layering.py`.

## Benchmarks

Five proof rungs and three design rungs from a real concurrent-separation-logic development. On
a design rung the invariants and ghost state are blank; designing them is the task.

```bash
python eval/harness.py --corpus eval/corpus/bench/rwcas \
  --reference .pcp/reference/rwcas --sandbox --runner claude --record .pcp/records
pcp failures .pcp/records/<run-id>            # what to fix, not just how many passed

python eval/ladder.py --brief spec-only --no-carry --no-paper   # every design rung, given only the spec
```

`--sandbox` runs each worker under bubblewrap with `$HOME` replaced by a tmpfs, the environment
cleared to an allowlist, the answer key masked, and the code forges blackholed — while leaving
the Iris sources and a grep-able index of every declaration bound in. `--brief spec-only` stages
the corpus without its design brief, so neither workers nor the decomposer can read a hint that
is not in the specification. See [`docs/BENCHMARKS.md`](docs/BENCHMARKS.md).

## Development

```bash
make test                    # the whole suite; Rocq/petanque-dependent tests skip without a toolchain
make fast                    # everything that does not need Rocq
make lint typecheck
python eval/extract_goldens.py --limit-files 40   # refresh the real-Iris golden corpus
```

The **canary** (`tests/test_canary.py`) is one golden end-to-end run of the daily loop with
scripted workers. It runs in CI, and speculative features are not allowed to break it.
