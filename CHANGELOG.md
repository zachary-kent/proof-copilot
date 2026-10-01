# Changelog

All notable changes to proof-copilot. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and versions follow
[Semantic Versioning](https://semver.org/). Install a release with
`uv tool install --python 3.11 'proof-copilot[mcp] @ git+https://github.com/zachary-kent/proof-copilot@vX.Y.Z'`.

## [0.4.3] - 2026-10-01

Fixes from pcp-issues.md "Session 5" (space credits for Cached-WaitFree, through the MCP
plugin and `pcp tools call`).

### Fixed
- A worker no longer keeps a stale library after `make` rebuilds it (issue 37). The pool
  records the project `.vo` files each process loaded (the opened files' `Require`s,
  transitively, through the `-Q`/`-R` mappings) with their mtimes. A new session never
  lands on a process whose libraries changed; when the pool is full, the least-loaded
  such process is restarted, its sessions are marked lost with the reason, and the
  answer carries `worker_restarted`. An older session whose own libraries were rebuilt
  says so (`stale_libraries`) in its failures and trace answers.
- A sentence that runs past petanque's wall clock (Rocq's `Timeout` did not stop it) is a
  timed-out failure of that sentence, with its goal and diagnosis, instead of an
  anonymous "session lost"; the answer says the session is gone and not to rerun the
  sentence unchanged, and the replay cache drops the dead states (issue 42).
- An early `proof_trace` answer names the step and sentence it is on and for how long,
  says the same call collects the result (`wait_s=0` waits until done), and flags a
  sentence past the default per-sentence budget (issue 42).
- A timed-out `iFrame` whose goal has evars, or conjuncts headed by a definition no
  hypothesis has, is diagnosed `split-before-frame` (instantiate or split first) ahead
  of the budget report; high confidence with evars (issue 40).
- `Unable to unify "?P x y" with …` is diagnosed `give-predicate` (give the predicate
  explicitly), and no longer as a mask problem because the quoted terms mention masks
  (issue 41).
- `}` on a block with goals still open is diagnosed `finish-block`, not "no goal is
  focused"; the "no goal is focused" reading is high confidence only when no goal was
  focused (issue 36).
- A failed `lia`/`nia`/`ring`/… reprints the state with implicit arguments and names atoms
  that print alike but are different terms (`implicit-mismatch`, e.g. two `size fm` with
  different `Size` instances) (issue 35). `select` naming `goal` now shows the goal's
  implicit arguments too.
- `case_bool_decide`/`case_decide` that split on a decision from a hypothesis while the
  goal has its own warns, and gives the `destruct_decide (bool_decide_reflect (…))` that
  splits on the goal's (a new `CaseSplit` effect) (issue 38).

## [0.4.2] - 2026-09-29

Fixes from pcp-issues.md "Session 4" (a writable big atomic proved through the MCP plugin).

### Fixed
- Timeouts are reported as budgets, not proof failures (issues 28, 29, 33):
  - A timed-out result carries `timeout`: the per-sentence budget, the wall time, the
    machine's 1-minute load and core count, and whether the sentence is known to pass.
  - `proof_step`, `proof_trace` and `proof_try` accept `timeout` (seconds per sentence).
  - A timeout is retried once at twice the budget when the machine is busy (load ≥ 0.75
    per core) or the sentence is known to pass (the same sentence after the same two
    sentences is in the committed proof or passed in the last trace of the lemma).
  - The diagnosis of a timeout is `budget` (high confidence when the sentence is known to
    pass), and every other lead except a β-redex drops to low confidence. A timed-out
    `wp_*` step no longer claims a points-to is missing.
  - Rocq's `Anomaly "… Control.Timeout."` (from `lia` under `Timeout`) counts as a timeout.
- The WP diagnosis finds a points-to for a multi-token location, and one the printer shows
  through a coercion (`(l +ₗ 1) ↦ …` for `Some (l +ₗ 1) &ₜ 0`) (issue 29).
- A failing `t; [t1|…|tn]`, `t; first tac`, `t; last tac` or `t; tac` is taken apart
  (issues 30, 32). The head is rerun alone, then each tail tactic on its own goal, all
  speculatively. `compound` says whether the head failed, a dispatch had the wrong number
  of branches, or which branch failed on which goal. The diagnosis and `goal` are then
  those of the failing part. A `first`/`last` tail that met the main goal says the side
  goal was already solved.
- A proof with no focused goal that is not finished says why, in `what` and in
  `open_ends` (issue 31): unfocused goals under a bullet or brace, shelved or given-up
  goals, or uninstantiated evars (named, with the step where each first shows). It also
  gives what a speculative `Qed` says. "1 goal remain" now reads "1 goal remains".
- `proof_trace` runs in the background. When it is still running after `wait_s` seconds
  (default 90, below Claude Code's 120 s tool limit; `0` waits until done), it answers
  `replaying: true` with its progress. The same call again waits for it and returns its
  answer; a different script stops it at the next sentence. Other tools on the session
  say it is still replaying instead of blocking (issue 28).
- Smaller answers (issue 34):
  - `diagnosis` is the report alone; the error is only in `error`, so an error that
    carries a Rocq environment is no longer printed twice.
  - A multi-sentence `proof_step`'s `ledger` keeps the last 5 steps' events
    (`ledger_total` counts them all), with each event's detail and rewrite sites cut to
    size.

## [0.4.1] - 2026-09-29

Fixes from pcp-issues.md "Session 3" (a Cached-ME proof driven through the MCP plugin).

### Fixed
- The MCP server and the `pcp tools` daemon pick the same workspace: the pcp project at,
  above or (one project, else the one with `.pcp/config.toml`) below the directory the host
  started in. Claude Code passes the git root, so relative paths, the paths in answers and
  `next`, and the run state used to belong to the git root instead of the project. Relative
  paths also still resolve against the launch directory (issues 19, 24).
- Every writer of run state creates `.pcp/.gitignore` (run state ignored, `config.toml`
  tracked), so a stray `.pcp/` never shows up as untracked files (issue 26).
- `proof_trace` answers are small: `events` keeps the last 5 steps' ledger events by default
  (`events="all"|"none"`; `events_total` counts them all), warnings carry their step, and
  `failure` no longer repeats the goal and error of the result block. A 35-sentence replay
  dropped from roughly 60 KB to 2 KB (issue 20).
- A multi-sentence `proof_step` runs sentence by sentence. A failure is reported for the
  failing sentence against the goal it met, with a `chain` field saying how many sentences
  ran and were committed (issue 23).

### Added
- Diagnoses for routine mistakes that used to come back `unknown` (issue 21):
  `strip-later` (a hypothesis the tactic uses is under `▷`, including `▷` over a `match`
  that must be destructed first), `beta-reduce` (a timeout against a goal with an unreduced
  `(λ x, …) a`), and `already-simplified` (a `wp_*` on a goal with no WP left, or a
  `rewrite` whose left-hand side the previous tactic already removed). A timed-out step
  now surfaces a confident diagnosis in `next`, and the "no goal focused" diagnosis says
  the previous tactic may already have discharged the side goal.
- `proof_try` rows that fail but are near variants of a survivor carry `vs_survivor`:
  the token difference and what it means (`/=` simplifies first, `"[H]"` is a spec
  pattern, `//`, `$!`) (issue 22).

## [0.4.0] - 2026-09-28

Using pcp on a project with its own Rocq/Iris (for example Rocq 9.2 and Iris dev in a
project-local `_opam`, while pcp pins Rocq 9.1.1 and Iris 4.5.0).

### Added
- pcp resolves the toolchain per project (`pcp/config/toolchain.py`). It takes `coqc` from
  `PCP_COQC`, else the nearest `_opam`, else a non-default `PCP_OPAM_SWITCH`, else `PATH`,
  else the pinned switch. It takes `pet` from the same switch, a sidecar, or a `PATH`/pinned
  pet built for the *same* Rocq. `ROCQPATH`/`COQPATH` entries that belong to another switch
  are ignored. A `dune-project` that uses `rocq`/`coq` now counts as a project root.
- `pcp setup --for-project [DIR] [--dry-run]` builds only petanque for the project's Rocq,
  in a separate switch `pcp-pet-rocq-<version>`. The switch has the project switch's OCaml
  and exactly its `rocq-core`/`rocq-runtime`. The command uses a coq-lsp release if the
  solver finds one, else pins coq-lsp's `v<major>.<minor>` branch there. No opam command
  names the project's switch. pcp picks the sidecar up by itself (`ROCQLIB`, `OCAMLPATH`).
- `pcp doctor --project DIR --lemma FILE:NAME --no-probe`. Doctor now answers "can pcp open
  a lemma here?" by opening one through petanque: the first lemma of the project's smallest
  built file, or a one-line lemma in a temporary file outside a project. On failure it
  prints petanque's error.
- Version floors `PCP_MIN_ROCQ`/`_COQLSP`/`_STDPP`/`_IRIS` in `toolchain.env`: what pcp
  needs, as opposed to the pins it is tested with.
- README / docs/INTEGRATIONS.md: "Using a project's own Rocq/Iris".
- `pcp tools call|list|status|stop|serve`: the MCP proof tools from a shell, through a
  per-workspace daemon (socket under `.pcp/tools/`), with no plugin and no client restart.
- One result schema for every MCP tool: `ok`, `what`, `where` (file/line/column/sentence/step),
  `goal`, `next`, plus `error` (cause kept, environment dump elided), `timed_out`, `lost`.
  A failure carries the failing sentence, its location and the goal before it.
- After each tactic, the goals in order with their shapes (new / kept / focused / closed).
- Tactic effects in the ledger: side goals created, the occurrence a `rewrite` hit, the
  conjuncts `iFrame` closed and the witnesses it picked, instantiated evars, and the redex
  `wp_pures` stopped at and why. Each one says `unknown` rather than guess.
- Hypotheses reprinted with what the printer hides: coercions (`Z.of_nat`), the carrier of
  every equality (`[= at Z]`), implicit arguments on request.
- `proof_expect`: assert the goal's shape, checked by Rocq, with the minimal differing subterm.
- `proof_inv`: the `iInv … as (…) "(>H1 & H2 …)"` pattern generated from the invariant's
  definition, `>` exactly on the Timeless conjuncts, checked speculatively.
- Incremental `proof_trace`: reruns only from the first edited sentence (`replayed_from`).
- `proof_close`, `diagnosis_feedback`; `pcp diagnoses` summarises hit/miss per repair class
  from `.pcp/diagnoses.jsonl`. Diagnoses carry a repair class and a confidence.
- An `iDestruct` that splits a `↦∗` fraction instead of the list is flagged (`fraction_split`).

### Changed
- `pcp doctor` reports the toolchain actually in use: which `coqc` and why, its prefix,
  and the package versions read from *that* switch (coq-lsp from the pet's). It also shows
  where `pet` comes from and the Rocq it was built for, the library roots, and ignored
  `ROCQPATH` entries. A difference from the pins is informational. Doctor fails only on no
  `coqc`, no petanque, a pet/`coqc` Rocq mismatch, a version below a floor, or a lemma that
  does not open.
- `pcp env` inside a project with a local switch prints that switch's exports.
- `pcp prove` workers, sandboxed or not, get the development's toolchain pinned. The sandbox
  binds its prefixes, even below a masked path.

- The step count of `pcp trace` / `proof_trace` is the number of sentences run, and a
  failed step's number matches `proof_state`'s `step`.
- Diagnoses no longer offer generic tactic lists or leftover-resource paragraphs without
  evidence; a focusing error suggests a bullet or `{ }`.
- `proof_open` elaborates only the statements (the target's own body is stubbed too) and has
  a 300 s start budget.

### Fixed
- `pcp doctor` printed "ok" for the pinned switch's packages while another `coqc` was in use.
- `pcp trace`, the MCP server and the gate used the file's directory as the workspace, so a
  root `_CoqProject` (`-Q theories smr`) was lost. All three now use the nearest
  `_RocqProject`/`_CoqProject`, and the gate's scratch copies get an absolute-path project file.
- A failed `petanque/start` reported only "Theorem not found"; it now reports the document's
  first error before the lemma (a failing `Require`, a wrong load path, a bad statement).
- A diverging tactic in the target's own proof wedged `proof_open` and the whole pool; a start
  timeout is now a result naming where coqc stopped, and the pool recovers.
- Statements-only twins (`__pcpfast.v`) are written under `.pcp/twins/` and removed on close,
  not left beside the source.
- A framing failure under `iMod (r.(lemma) …)` was blamed on the record `r`; it now names the
  term to frame against the closest hypothesis ("rewrite first").

## [0.3.1] - 2026-09-23

Found by driving the Claude Code plugin from a real install.

### Fixed
- `/proof-copilot:status` failed outright in a project with no run yet: `pcp status`
  exited non-zero, which aborts a command's shell injection. New `pcp status --missing-ok`
  reports "no pcp run in this project yet" and exits 0; the plugin command uses it.
- The `proof_step` and `proof_try` MCP tools add a missing final `.` to a tactic (bullets
  and goal braces excepted) instead of returning Rocq's opaque syntax error.

Keep pcp and the plugin on the same version: the plugin is served from `master`, and
its commands call pcp flags that older releases lack.

## [0.3.0] - 2026-09-23

Packaging: an installed copy now behaves exactly like a checkout.

### Added
- `pcp setup [--dry-run] [--switch NAME] [--jobs N] [--force]` builds the pinned
  Rocq/Iris/coq-lsp opam switch. It is idempotent and runs the packaged opam script.
- `pcp env [--switch NAME]` prints shell exports for the pinned switch (`eval "$(pcp env)"`).
  This is optional: pcp finds the switch without it.
- `pcp init [DIR] [--force]` writes `.pcp/config.toml` and a `.pcp/.gitignore` that ignores
  the run state but keeps the config committable.
- `pcp doctor` now also reports the installed version of each pinned package against its pin,
  and checks that every packaged asset loads.
- Switch discovery: every binary lookup falls back to `$OPAMROOT/$PCP_OPAM_SWITCH/bin` after
  `PATH`, and workers get that directory appended to `PATH`. pcp therefore works when Claude
  Code or Codex launches it without a login shell.
- Sandbox install binds: `--sandbox` binds pcp's own installation (interpreter prefix,
  package, entry point) read-only, so `pcp check` runs inside the sandbox even for a `uv tool`
  install under the masked `$HOME`. The checkout-only masks (`.git`, `eval`, `docs`, `tests`)
  now apply only when the project is a proof-copilot checkout.
- Integrations: a Claude Code plugin and a Codex MCP configuration
  ([docs/INTEGRATIONS.md](docs/INTEGRATIONS.md)).
- `make install-check` and `tests/test_install.py`: build a wheel, install it non-editable in
  a fresh venv, and load every packaged asset from it.
- This changelog and [CONTRIBUTING.md](CONTRIBUTING.md).

### Changed
- Packaged files moved under `pcp/assets/`: `skills/`, `coq/IDump.v`,
  `setup-toolchain.sh`, and `toolchain.env`. They are read only through `pcp.util.assets`.
- The toolchain pins exist once, in `pcp/assets/toolchain.env`. `pcp setup`, `pcp doctor`,
  `pcp env` and `env.sh` all read that file.
- pytanque is pinned to LLM4Rocq commit `4092b12` (v0.2.2) as a direct dependency, so
  `make install` and `uv tool install` need no separate pytanque step. The PyPI package named
  `pytanque` is unrelated; never replace the pin with a version range.
- Documentation restructured. The README follows the user's path (install, quickstart,
  integrations, configuration, troubleshooting, development). `docs/PLAN.md` moved to
  `docs/design/PLAN.md` as the design record. The inventory from `docs/STATUS.md` became
  `docs/ARCHITECTURE.md` §11–12.
- Package metadata: readme, authors, URLs, classifiers.

### Removed
- Feature flags that nothing read: `vacuity_probes`, `sketch_compiler`, `state_layer`,
  `epsilon_spot_check`, `or_nodes`, `strict_no_gap`. A config that still sets one gets a
  warning and the flag is ignored.
- `repo_root()`. Library code has no notion of a checkout.
- `scripts/setup-toolchain.sh` (now `pcp setup`) and `docs/STATUS.md` (folded into
  ARCHITECTURE).

### Fixed
- An installed copy ran workers without their skill file. The old checkout-relative lookup
  found nothing and silently used an empty default. A missing asset is now an error.

## [0.2.0] - 2026-09-09

A from-scratch modular rewrite of the original implementation (git `40d5b0b`), split into the
layers `util`/`config`/`rocq`/`state`/`orch`/`mcp`/`dash`/`cli` with an import rule that a test
enforces. The v1 audit found a dozen classes of defect, and each is now ruled out by a
structural rule (see [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) §8).
