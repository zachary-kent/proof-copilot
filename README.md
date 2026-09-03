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

Design: [`docs/PLAN.md`](docs/PLAN.md) · What is built and what is not: [`docs/STATUS.md`](docs/STATUS.md)

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

1. **Statements freeze immediately**, by construction: worker patches are constrained to
   proof-body spans, so the proved statement is byte-identical to the frozen one. Free sentinels
   run (duplicate detection, partial-correctness flag).
2. **The whole frontier dispatches at once.** Every frozen statement with an open proof is
   dispatchable *now* — its dependencies are admissible as `Admitted` stubs — so parallelism is
   bounded by your rate window, never by graph depth.
3. **Every return is gated deterministically**, with no model involved: assembly from the frozen
   store, statement pinning, `Proof using` discipline, `Print Assumptions` ⊆ whitelist, no new
   admits, no escape hatches, no global registrations, unused-premise probe.
4. **Failures retry once with evidence**, then land back with you as `qed` / `stuck` /
   `contested`. `pcp handoff <node>` drops a stuck node into your editor as a `.v` with the
   statement, the best partial script, and the blame trace as comments.

```
3 qed · 0 stuck · 0 contested   (23s, 3 dispatches)
  qed       canary_main  (23s, 1 attempt(s))
  qed       canary_swap  (22s, 1 attempt(s))
  qed       canary_assoc  (21s, 1 attempt(s))

integrated: `canary_main` Qeds and Print Assumptions is clean.
```

Watch it in a browser with `pcp serve`; check on it with `pcp status`.

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
pcp/core/     pcp-state: session pool, trace, IPM model + parser + reflection, ledger, render, search
pcp/orch/     pcp-orch:  SQLite graph, assembly, gate, sentinels, scheduler, runners, amendments
pcp/mcp/      the tool surface (10 tools, hard-capped) + structured failure diagnosis
pcp/cli/      the `pcp` command
pcp/dash/     `pcp serve` (SSE over SQLite) and `pcp report`
coq/IDump.v   the Ltac2 reflected IPM dump
skills/       prover · decomposer · invariants · logatom
eval/         held-out-lemma harness, the ablation ladder, the corpora
```

## Benchmarks

Five rungs from a real concurrent-separation-logic development, in increasing order of
held-out proof size — up to a single `cas_spec` of 712 lines / 1069 tactics. The design
is given (implementation, invariants, ghost state, helper lemmas); only the tactic work
is removed.

```bash
python eval/harness.py --corpus eval/corpus/bench/rwcas \
  --reference .pcp/reference/rwcas --sandbox --runner claude --record .pcp/records
pcp failures .pcp/records/<run-id>            # what to fix, not just how many passed
```

`--sandbox` runs each worker under bubblewrap with `$HOME` replaced by a tmpfs, the
answer key masked, and the code forges blackholed — while leaving the Iris sources and
a grep-able index of all 11 646 declarations bound in, so documentation is *better*
than the network rather than absent. See [`docs/BENCHMARKS.md`](docs/BENCHMARKS.md),
including what these controls do **not** prove.

## Development

```bash
pytest                       # 433 tests; Rocq-dependent ones skip without a toolchain
pytest -m "not slow" -q
python eval/extract_goldens.py --limit-files 40   # refresh the real-Iris golden corpus
```

The **canary** (`tests/test_canary.py`) is one golden end-to-end run of the daily loop with
scripted workers. It runs in CI, and speculative features are not allowed to break it.
