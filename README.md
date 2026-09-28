# proof-copilot

Tools for agent-driven proof engineering in Rocq, aimed at affine logics (Iris). There,
LLM agents tend to fail at keeping track of resources, not at the reasoning itself.

There are two layers, and they can be used separately:

- **pcp-state** gives you a structured, diffable Iris proof state over Rocq/petanque, one
  hypothesis at a time. It records traces tactic by tactic and keeps a spatial-resource ledger
  that answers *"where did this hypothesis go?"*. It renders goals to a budget so they don't
  fill the context window. It comes as a Python library, a CLI and an MCP server.
- **pcp-orch** is an orchestrator over an obligation graph. You (or a frontier model) split a
  lemma into `Admitted` child statements. Cheaper models prove them in parallel. A
  machine-checkable gate (`Qed` plus `Print Assumptions`) decides when the lemma is done.

## Two claims this is built on

**The lemma statement is the interface contract, and `Admitted` is a type-checked stub.** A
`Qed` proof is opaque, so a proof written against an admitted lemma can depend only on the
lemma's *statement*. Work done against a stub is therefore exactly the work that survives once
the stub is filled. That is why the whole frontier can be dispatched in parallel, and why a
machine can decide completion instead of a reviewer.

**Iris debugging failures are resource-accounting failures.** A typical failure is "a spatial
hypothesis was eliminated early and is needed 40 steps later". That is bookkeeping, not
reasoning. A machine does bookkeeping over 200 steps well and an LLM does it badly, so the
main feature is a per-step resource ledger rather than a better prompt:

```
why is "HP" not available at step 3?
  "HP" was framed at step 2 by `iFrame.`
  repair class: frame-later
  step 2 framed it into the goal -- frame later, or split the goal first.
```

When the ledger cannot tell, it says `unknown` instead of guessing. A confidently wrong
provenance chain is worse than none.

---

## Install

You need Linux, [uv](https://docs.astral.sh/uv/) (or pipx), `git` and
[opam](https://opam.ocaml.org/doc/Install.html). For `--sandbox` you also need `bubblewrap`.
To run provers you need at least one model CLI that is logged in: Claude Code (`claude`) or
Codex (`codex`).

```bash
# 1. pcp itself. Pick a tag from CHANGELOG.md; the [mcp] extra enables `pcp mcp` and --state-tools.
#    --python 3.11: from a git URL uv does not pick an interpreter by requires-python (it fetches one if needed).
uv tool install --python 3.11 'proof-copilot[mcp] @ git+https://github.com/zachary-kent/proof-copilot@v0.4.0'

# 2. A toolchain. A project with its own opam switch (`_opam`) needs none of this:
#    pcp uses that switch, see "Using a project's own Rocq/Iris" below.
#    Otherwise, pcp's tested default in an opam switch named `pcp`:
#    Rocq 9.1.1, coq-lsp 0.2.5, Iris 4.5.0, std++ 1.13.0.
pcp setup --dry-run      # show the opam commands
pcp setup                # idempotent; the first run takes a while

# 3. Can pcp open a lemma here? Shows the toolchain in use and why, the versions it reads
#    from that toolchain, and opens a real lemma through petanque. Also checks the packaged
#    files, the Python deps and which runners are reachable.
pcp doctor

# 4. In your Rocq project, write .pcp/config.toml and git-ignore .pcp/.
cd ~/my-iris-project && pcp init
```

pipx works as well and takes the same `'proof-copilot[mcp] @ git+…'` spec. To upgrade, run
the install again with a newer tag and `--force`.

**You don't need to activate anything.** pcp finds the toolchain by itself, per project (see
below), falling back to `$OPAMROOT/pcp/bin` (default `~/.opam/pcp/bin`). So pcp works when
Claude Code or Codex starts it without a login shell. If you want `rocq`/`coqc` on your own
shell's `PATH`, run `eval "$(pcp env)"`; in a project with a local switch it exports that one.

### Using a project's own Rocq/Iris

pcp's pins are only the default it is tested with. A project on another Rocq or Iris (say
Rocq 9.2 with Iris dev in a project-local switch) works as it is:

- **Auto-detection.** pcp takes `coqc`/`rocq` from, in order: `PCP_COQC`; the nearest `_opam`
  above the file or workspace (a project-local opam switch, as opam finds it); the switch
  `PCP_OPAM_SWITCH` names, if it is not the default `pcp`; `PATH`; the pinned switch. The
  project root is the nearest `_RocqProject`/`_CoqProject`, or a `dune-project` that uses
  `rocq`/`coq`.
- **Everything else follows the compiler.** Packages and versions are read from the same
  switch. `pet` comes from that switch too, else from a *sidecar* (below), else from `PATH` or
  the pinned switch only if it was built for the same Rocq. A `ROCQPATH`/`COQPATH` entry that
  belongs to another switch (a leftover `pcp env`) is dropped, so two Iris builds never mix.
- **Explicit overrides.** `PCP_COQC`, `PCP_PET`, `PCP_PET_SERVER` name binaries directly;
  `PCP_OPAM_SWITCH=NAME` (or a directory holding `_opam`) picks a switch.
- **No petanque for that Rocq?** Don't install coq-lsp into the project's switch: opam may
  rebuild its Rocq, std++ and Iris, and every `.vo` the project built becomes "inconsistent
  assumptions". Instead run

  ```bash
  pcp setup --for-project --dry-run   # in the project: the exact opam commands
  pcp setup --for-project             # builds only pet, in a switch pcp-pet-rocq-<version>
  ```

  This creates a separate switch with the project's OCaml and exactly its Rocq, and
  installs a coq-lsp release for that Rocq, or pins coq-lsp's `v<major>.<minor>` branch
  there if none exists. No opam command names the project's switch. pcp then picks the
  sidecar's `pet` up by itself and points it at the project's libraries (`ROCQLIB`,
  `OCAMLPATH`).
- **`pcp doctor`** (or `pcp doctor --project DIR`) shows which `coqc` is in use and why, its
  switch, the Rocq, std++, Iris and coq-lsp versions *in that switch*, where `pet` comes from
  and the Rocq it was built for, the library roots, and any `ROCQPATH` entries it ignores. It
  judges versions against what pcp needs (`PCP_MIN_*` in `pcp/assets/toolchain.env`, such as
  Rocq >= 9.0 and coq-lsp >= 0.2.5). A difference from the tested pins is shown but is not an
  error. It then answers "can pcp open a lemma here?" by opening one: the first lemma of the
  project's smallest built file, or the one you give with `--lemma FILE:NAME`. On failure it
  prints petanque's error. `--no-probe` skips this step.
- **Workers** (`pcp prove`, sandboxed or not) get the development's toolchain pinned
  explicitly, because they run in a scratch directory that has no `_opam` above it.

**pcp never implements login.** `pcp doctor` prints the command to run (`codex login`, or
`/login` in Claude Code) and never asks for a credential.

## Quickstart

### Prove a lemma from a plan (pcp-orch)

Suppose you have a lemma and an idea of how to prove it. You write down the child
statements, and the orchestrator runs the workers. Here is the full example, from an empty
directory:

```bash
mkdir demo && cd demo && git init -q
echo '-Q . demo' > _CoqProject
```

`Demo.v` is the development. The target can be `Admitted`:

```coq
From iris.proofmode Require Import proofmode.

Section demo.
  Context {PROP : bi}.

  Lemma sep_rotate (P Q R : PROP) : P ∗ Q ∗ R -∗ R ∗ Q ∗ P.
  Proof. Admitted.
End demo.
```

`plan.v` is Rocq, not prose. It holds the child statements, each ending in `Proof. Admitted.`
The children go into the target's section, so they inherit its `Context`:

```coq
Lemma sep_swap (A B : PROP) : A ∗ B -∗ B ∗ A.
Proof. Admitted.

Lemma sep_assoc (A B C : PROP) : A ∗ (B ∗ C) -∗ (A ∗ B) ∗ C.
Proof. Admitted.
```

```bash
pcp init
pcp prove Demo.v sep_rotate --plan plan.v --record .pcp/records
```

```
prover: anthropic/claude-sonnet-5 (from .pcp/config.toml)
runner: claude:claude-sonnet-5/medium
3 qed · 0 stuck · 0 contested   (27s, 3 dispatches)
  qed       sep_rotate  (23s, 1 attempt(s))
  qed       sep_swap  (17s, 1 attempt(s))
  qed       sep_assoc  (18s, 1 attempt(s))

integrated: `sep_rotate` Qeds and Print Assumptions is clean.
solution: .pcp/records/<run-id>/solution/Demo.v
```

pcp never edits your source file. The proved development is written to
`<record>/<run-id>/solution/`, with a header that says whether it is complete. Run state
lives in `.pcp/`: the graph is in `.pcp/graph.db` and each attempt's directory is under
`.pcp/work/`.

What happens during a run:

1. **Statements freeze immediately.** A worker returns only a *proof body*. pcp checks that
   the body contains tactic sentences and nothing else, then rebuilds the development from
   the frozen source plus that body. Cheap checks (sentinels) run at freeze time: duplicate
   statements, a restated root, a partial-correctness flag.
2. **The whole frontier is dispatched at once.** Every frozen statement with an open proof can
   be dispatched right away, because its dependencies are available as `Admitted` stubs. So
   parallelism is limited by your rate window, not by the depth of the graph.
3. **Every returned proof is gated deterministically**, with no model involved. The gate
   assembles the file from the frozen store, rechecks its structure, enforces `Proof using`,
   compiles, and checks that `Print Assumptions` stays within a whitelist. It also rejects
   new admits, escape hatches and global registrations.
4. **A failed proof is retried once with evidence.** The retry sees the previous attempt's
   partial proof. After that the node comes back to you as `qed`, `stuck` or `contested`.
   `pcp handoff <node>` writes a stuck node to a `.v` file with the statement, the best
   partial script, and the blame trace as comments.

A run always resumes from its graph:

- If pcp crashes mid-dispatch, the next run picks up where it stopped. Proofs that were gated
  before the crash are kept, not re-proved.
- If a provider has an outage (you were logged out, or hit a session limit), the run pauses
  and resumes by itself when the provider is back.
- `pcp prove --supervise` runs the prove loop detached and restarts it from the graph after a
  crash.
- Only one `pcp prove` can run per graph, because the run holds a lock.
- To watch a run, use `pcp status` or `pcp serve` (a browser dashboard on port 8765).
  `--record` keeps every attempt's packet, transcript, gate report and failure class. Run
  `pcp failures <record>/<run-id>` to read them.

Sometimes a prover finds mid-proof that an invariant is missing a fact. It asks for the fact
instead of failing. If the strengthened definition compiles, pcp applies it, replays every
proof, and reopens only the proofs that broke. A cheap approver model adjudicates contested
statements before anything is redesigned. The same happens for any node that fails twice
(`--review-after`). Without `--plan`, a read-only **decomposer** model states the obligations
itself (it can use `Read`/`Glob`/`Grep` and nothing else). pcp compiles its proposal and checks
it against the design contract. It revises the proposal in bounded rounds, using what the
provers report back. `pcp prove --help` lists every knob.

### Inspect a proof state (pcp-state)

The state layer works on any proved lemma. For example, give `sep_rotate` in `Demo.v` a
hand-written proof, `Proof. iIntros "[HP [HQ HR]]". iFrame. Qed.`, and trace it:

```bash
pcp trace Demo.v sep_rotate -o trace.jsonl      # tactic-by-tactic Iris state + ledger
pcp ledger trace.jsonl events                   # every intro, destruct, frame, ...
pcp ledger trace.jsonl where --hyp HP           # where "HP" came from and where it went
pcp ledger trace.jsonl blame --hyp HP           # what consumed it, and how to repair that
pcp ledger trace.jsonl leftovers                # why iFrame/done is failing
pcp state trace.jsonl --select spatial --budget 2000
pcp destruct '∃ γ, own γ (◯ n) ∗ ⌜n = 3⌝'       # iDestruct "H" as (γ) "[H1 %H2]".
pcp docs                                        # a grep-able index of every Iris/std++ declaration
pcp mcp                                         # the same tools over MCP (stdio)
```

Each session is pinned to the petanque process that created its states, and every call has a
wall clock. If that process dies mid-session, pcp reports a *lost session*. It never reports
that as "your tactic failed".

## Integrations

pcp ships a Claude Code plugin and a Codex MCP configuration. With them, an agent you are
already working with can call the proof-state tools (`pcp mcp`), run `pcp prove`, and read the
gate's verdicts, without any setup beyond `uv tool install` and `pcp setup`. Installation and
usage for both are in [`docs/INTEGRATIONS.md`](docs/INTEGRATIONS.md).

## Configuration

**`.pcp/config.toml`** is per project. `pcp init` writes it and `pcp models --example` prints
the same template. It sets:

- `[tiers]`: the models for each role (decomposer, prover, auditor), as ordered preferences
  such as `"anthropic/claude-sonnet-5"`;
- `[providers.<name>]`: how each provider is reached (`auth = "subscription"`, `"api-key"`
  or `"none"`). pcp refuses a config that contains a key, token or password;
- `[effort]`: effort per role;
- `concurrency` and `axiom_whitelist`;
- `[flags]`: speculative features, all off by default. See
  [ARCHITECTURE §12](docs/ARCHITECTURE.md#12-what-is-built).

pcp reads the config from the current directory, so run pcp from the project root or pass
`--config`. `pcp models` shows which model each role resolves to and why. The per-run flags on
`pcp prove` (`--runner`, `--prover-model`, `--decomposer`, `--*-effort`, `--node-seconds`,
`--attempts`, …) override the config.

**Environment variables.** All of them are defined in `pcp/config/env.py`. None is required.

| variable | effect |
|---|---|
| `PCP_OPAM_SWITCH` | switch that `pcp setup` builds; a non-default name is also used ahead of `PATH` (default `pcp`) |
| `OPAMROOT` | opam root (default `~/.opam`) |
| `PCP_COQC` | `coqc` to use (else the project's `_opam`, `PCP_OPAM_SWITCH`, `PATH`, the pinned switch) |
| `PCP_PET`, `PCP_PET_SERVER` | petanque binaries, stdio and socket (else the compiler's switch, a sidecar, then `PATH`/the pinned switch when built for the same Rocq) |
| `PCP_PET_MEM_LIMIT_MB` | hard memory limit for petanque (default 24576) |
| `PCP_BWRAP` | bubblewrap binary for `--sandbox` (else `bwrap` on `PATH`) |
| `ROCQPATH`, `COQPATH` | extra Rocq library roots, searched before the switch's `user-contrib` (another switch's entries are ignored) |
| `ANTHROPIC_API_KEY` | enables `--runner direct` (needs the `[api]` extra) |
| `CLAUDE_CODE_MAX_OUTPUT_TOKENS` | raised to 128000 for Claude workers unless you set it |

pcp sets `PCP_SANDBOX=1` inside a sandbox itself; don't set it by hand.

## Troubleshooting

- **`pcp doctor` shows `coqc` or `pet` missing.** Run `pcp setup`. If you build the switch
  under another name or opam root, set `PCP_OPAM_SWITCH` / `OPAMROOT` for every pcp process
  (or run `pcp setup --switch NAME` and export the variable).
- **`pcp doctor` shows a version that differs from the tested default.** That's fine as long as
  the version meets what pcp needs and the "can pcp open a lemma here?" check says yes. The
  "chosen because" line says where the `coqc` came from. A binary on `PATH` wins over the
  pinned switch, so point `PCP_COQC` elsewhere if that is the wrong one.
- **`petanque was built for Rocq X but coqc is Rocq Y`, or `no petanque for this Rocq`.** Run
  `pcp setup --for-project` in the project (see "Using a project's own Rocq/Iris").
- **`no runner is available`.** Install `claude` or `codex` and log in. `pcp doctor` lists
  which runners it can reach.
- **`import pytanque` fails, or pytanque behaves strangely.** pcp depends on LLM4Rocq's
  pytanque, pinned to commit `4092b12`. The package named `pytanque` on PyPI is an **unrelated
  project**, so never `pip install pytanque`. Reinstall pcp to restore the pin.
- **`another pcp run holds .pcp/graph.db.lock`.** A run is already going on that graph. Check
  it with `pcp status`, or give this run a different `--graph`. `--fresh` discards the graph
  and the work directory.
- **`--sandbox needs a subprocess runner`.** Use `--runner claude` or `--runner codex`. The
  sandbox also needs `bwrap`.
- **`session … was lost when petanque restarted (…); call proof_open again`.** The petanque
  process died, often because it hit the memory limit. Reopen the proof, and raise
  `PCP_PET_MEM_LIMIT_MB` if it keeps happening.

---

## Development

```bash
git clone https://github.com/zachary-kent/proof-copilot && cd proof-copilot
make install                 # uv venv --python 3.11 .venv + editable install with [mcp,dev]
. ./env.sh                   # activates .venv and the pinned switch (a checkout only)
pcp setup                    # build the switch if you have none (= make toolchain), then re-source env.sh
make fast                    # everything that needs neither Rocq nor petanque
make test                    # the whole suite; Rocq/petanque tests skip without a toolchain
make canary                  # the golden end-to-end run of the daily loop
make lint typecheck          # ruff, mypy
make install-check           # build a wheel, install it in a fresh venv, load every packaged asset
make help                    # everything else (bench, ladder, goldens, docs-index)
```

The version pins live only in `pcp/assets/toolchain.env`. To bump one, edit it, run
`pcp setup`, then `make goldens` to re-extract the real-Iris golden corpus. The benchmarks and
the design-rung ladder (`eval/`) need a checkout. See [`docs/BENCHMARKS.md`](docs/BENCHMARKS.md).

Before sending a change, read [`CONTRIBUTING.md`](CONTRIBUTING.md): it covers the layering
rule, the canary, feature flags and test markers. Record user-visible changes in
[`CHANGELOG.md`](CHANGELOG.md).

**Further reading:**

- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md): how the code is organised, the guarantees
  its structure provides, and what is built.
- [`docs/design/PLAN.md`](docs/design/PLAN.md): the design record, i.e. why the code is shaped
  this way.

## License

MIT. See [`LICENSE`](LICENSE).
