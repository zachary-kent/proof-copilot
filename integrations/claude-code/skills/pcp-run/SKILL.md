---
name: pcp-run
description: Drive a proof-copilot orchestrated run (the daily loop) - launching `pcp prove FILE LEMMA --plan plan.v`, supervising or resuming it, reading `pcp status`, watching it with `pcp serve`, handing off stuck nodes with `pcp handoff`, and classifying recorded failures. Use when the user wants pcp to prove a lemma with workers, asks how a run is going, or has stuck/contested nodes.
allowed-tools: Bash(pcp status) Bash(pcp status *) Bash(pcp models) Bash(pcp failures *)
---

# Driving a pcp run

A run proves one lemma by dispatching workers (codex / claude) at frozen child
statements and gating every returned proof deterministically (compile + `Print
Assumptions`). The graph lives in `.pcp/graph.db`; everything below reads or resumes it.
Run commands from the project root. `pcp <cmd> --help` is authoritative for flags.

## Launch

```bash
pcp prove Foo.v foo_correct --plan plan.v        # you state the children
pcp prove Foo.v foo_correct                      # a read-only decomposer states them
pcp prove Foo.v foo_correct --plan plan.v --supervise   # detached; restarts after a crash
```

- `plan.v` is Rocq: child `Lemma`s ending in `Proof. Admitted.` Help the user write it;
  `pcp sketch sketch.v --out plan.v` compiles a CSL proof sketch into one.
- A run takes minutes to hours. Prefer `--supervise` (it prints the pid and the log to
  `tail -f`); otherwise run `pcp prove` in the background. Never block the session on it.
- Useful flags: `--state-tools` (give provers the pcp MCP tools), `--record DIR`
  (keep every attempt, for `pcp failures`), `--intent "..."` (a two-line brief every
  worker sees), `--sandbox` (bubblewrap), `--runner`, `--prover-model`, `--decomposer`,
  `--concurrency`, `--node-seconds`, `--attempts`. Check `pcp models` before a first run.
- One `pcp prove` per graph: a second one fails on the lock. Do not work around it.

## Resume

Re-run the same `pcp prove` command: it resumes from the graph, salvages proofs that
gated before a crash, and keeps partial proofs as the next attempt's start. `--fresh`
discards the graph and workroot -- only when the user asks for it. A provider outage
pauses the run and it resumes by itself (`--pause-hours`).

## Watch

```bash
pcp status              # one screen: qed / stuck / contested per node
pcp status --json       # the same, for you to parse
pcp serve               # live dashboard at http://127.0.0.1:8765 (a server: background it)
pcp report -o .pcp/report.html   # static snapshot to share
```

## When nodes come back stuck or contested

1. `pcp handoff NODE -o NODE.v` writes a `.v` with the statement, the best partial
   script and the blame trace as comments. Read it first.
2. Debug it with the `iris-proving` skill (the pcp MCP tools). The statement is frozen:
   if it is wrong, say so and propose the corrected statement to the user; do not edit
   it in the source to make a proof go through.
3. A `contested` node means a worker argued the statement is unprovable; weigh the
   reason before trying to prove it.
4. With `--record DIR`: `pcp failures DIR/<run-id>` classifies every attempt by failure
   mode, `--class NAME` lists one class. Report what to fix, not only how many failed.

Check a finished body yourself with the `verify_node` tool -- the same gate the
scheduler runs (inside a node's workdir under `.pcp/work/`, `pcp check body.v` is the
worker's view of it).
