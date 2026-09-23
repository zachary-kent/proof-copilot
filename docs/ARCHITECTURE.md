d# proof-copilot — architecture

How the code is organised, what the layers may depend on, the engineering rules every module
follows, and what is built (§12). The rationale behind the design is the design record,
[`design/PLAN.md`](design/PLAN.md), which code comments cite by section ("PLAN.md 8.7"); where
it and the code disagree, this file and the code are authoritative. Using the tool is the
[README](../README.md).

Two products live here, separable:

- **pcp-state** (`pcp.state`, `pcp.mcp`): the Iris-aware proof-state layer over Rocq/petanque.
- **pcp-orch** (`pcp.orch`): the obligation-graph orchestrator, whose daily loop (`pcp prove`)
  must run where the only Rocq binary is `coqc`.

## 1. Layers and the import rule

```
pcp.util      stdlib only.                                  (proc, io, text, hashing, paths, locks, assets)
pcp.assets    data, no code                                 skills, IDump.v, setup script + pins
pcp.config    ← util                                        (schema, load, flags, providers, env)
pcp.rocq      ← util, config                                Rocq *text* and the coqc path. NO petanque.
pcp.state     ← util, config, rocq                          petanque, IPM model, ledger, render, search
pcp.mcp       ← state, rocq                                 the MCP tool surface
pcp.orch      ← util, config, rocq                          MUST NOT import pcp.state, pcp.mcp or pytanque
pcp.dash      ← orch.graph                                  pcp serve / pcp report
pcp.cli       ← everything, lazily per subcommand
eval/         ← orch, state (scripts; not part of the package)
```

`tests/test_layering.py` enforces this by importing each package in a subprocess and checking
`sys.modules`. Lazy imports inside functions are allowed only across the `cli` boundary and
for optional third-party packages (`pytanque`, `mcp`, `anthropic`).

Packaged files are read only through `pcp.util.assets` (`importlib.resources`), never by a
path relative to a checkout: there is no "repo root", because an installed package has none
(§11).

## 2. Package layout

```
pcp/
  __init__.py          __version__
  errors.py            PcpError hierarchy: UsageError, ToolchainError, ProtocolError, GateError,
                       RoleViolation, StateError (each carries a one-line user message)
  util/
    proc.py            run() / run_async(): argv, cwd, env, timeout, stdin, streaming capture.
                       Always start_new_session=True; on timeout kill the whole process group;
                       always reap. Returns Completed(rc, stdout, stderr, timed_out, elapsed_s).
    io.py              atomic_write_text, read_text (utf-8, errors="replace"), json_load/dump,
                       slug(), ensure_dir, rm_tree
    text.py            one_line, tail_lines, clip, indent, wrap
    hashing.py         blake2b content hashes with prefixes (b:/s:/c:/h:/p:/e:)
    paths.py           resolve_from(path, base), home(), tmpdir() -- deliberately no repo root
    locks.py           RunLock (fcntl flock on <graph>.lock); holder pid + started_at
    assets.py          the packaged files (skill, IDump.v, setup script, toolchain_pins());
                       a missing asset is an error, never an empty default
  assets/
    skills/*.md        worker norms: prover, decomposer, invariants, logatom
    coq/IDump.v        the Ltac2 reflected IPM dump
    setup-toolchain.sh `pcp setup`'s opam script
    toolchain.env      the version pins -- the single source (env.sh, doctor, env, setup)
  config/
    env.py             every environment variable name in one place + lookups
                       (coqc_binary, pet_binary, pet_server_binary, bwrap_binary, library_roots);
                       the pinned-switch fallback (opam_root, switch_prefix, with_switch_path)
    flags.py           DEFAULT_FLAGS (all off)
    schema.py          Config dataclass (tiers, providers, effort, flags, concurrency,
                       axiom_whitelist) + validation
    load.py            load(path) with the secrets refusal; EXAMPLE_CONFIG
    providers.py       detect_providers, Binding, resolve(role, provider=None), describe_bindings,
                       ROLE_EFFORT, EFFORT_LEVELS, PROVIDER_DEFAULTS
  rocq/
    lexer.py           THE lexer: comments (nested), strings (""), sentences, bullets/braces,
                       goal selectors. Nothing else in the tree scans Rocq text with a regex.
    decls.py           Declaration/ProofBlock parsing; section/module stack; qualified names
    body.py            proof-body validation (tactic-only, denylist of vernacular),
                       strip_proof_wrapper, split into tactic sentences
    statement.py       normalize_statement, statement_hash, binders, remove_binder
    project.py         _CoqProject flags, rebasing, compile(text, ...) -> CompileResult
    assumptions.py     Print Assumptions parsing (wrapped types, colon-less entries,
                       qualified names) and whitelist/stub matching by suffix
    assemble.py        Development, NodeSpec, Assembly, assemble(), stub_proof_bodies,
                       parse_plan, plan_preamble, stubbed_twin()
    library.py         library roots, declaration index (pcp docs), grep over sources
  state/
    petanque.py        PetProcess: one `pet` (or pet-server) process, owns its state ids;
                       hard memory limit; Python-side wall clock on EVERY call; explicit
                       close; a restart invalidates every session bound to it
    pool.py            SessionPool: sessions are PINNED to the process that created their
                       states; file affinity; bounded acquire; safe under threads
    session.py         ProofSession (start/run/try_many/goals/query/replay), StepResult,
                       loop detection reported to callers
    ipm/model.py       IrisGoal, Hyp, Modality, WPInfo (+ scan_modality at the HEAD only)
    ipm/parse.py       printer parser: all four separator shapes, anonymous `_ : P` hyps
    ipm/skeleton.py    connective skeleton parser (precedence, binders in operand position,
                       every modality prefix incl. |={E}▷=>, |={E1}[E2]▷=>)
    ipm/pattern.py     intro-pattern grammar (all IPM tokens), compiler, aligner
    ipm/oracle.py      persistence/affinity oracle, always at the step's own state
    ipm/reflect.py     IDump build + driver (wired in, printer parser as fallback)
    digest.py          PropStore, evar normalisation (unicode evars), Selector, folding
    trace.py           Tracer, Trace, JSONL (schema v=1, unchanged)
    ledger/events.py   Event vocabulary (unchanged)
    ledger/diff.py     structural diff: name-first/hash-second, evar-aware, goal parentage
                       incl. closing a non-final goal, `unknown` on ambiguity
    ledger/query.py    where_did_it_go / blame / leftovers / unused_at_qed
    render.py          budgeted render; explicit selection beats diff-only; elision footer
    search.py          premise_search (quoted substrings), notation_resolve
    diagnose.py        pattern/apply/leftover/mask diagnosis by construction
    explain.py         `pcp check` replay diagnosis (char offsets, warnings ignored)
    props.py           evar-aware prop normalisation and content hashing
    tactic.py          one tactic sentence as tokens (head, quoted names, `as` clause)
  mcp/
    names.py           TOOLS (10), MAX_TOOLS (12), STATE_TOOLS, mcp_tool_name, blurbs
    server.py          PcpServer (transport-free, locked) + register() for mcp 1.x/2.x
    config.py          write_mcp_config
  orch/
    model.py           Node, Budget, statuses, transition() (validated lattice)
    graph.py           SQLite store; schema version + migrations; every mutation an event;
                       one connection per Graph, serialised by a lock
    sentinels.py       free sentinels, run at every freeze (plan and decomposer children)
    gate.py            Gate: immutable, reentrant; static body checks -> assembly ->
                       structural recheck -> compile -> assumptions
    protocol.py        NodePayload, NodeResult, LemmaRequest, read_result (attempt-scoped)
    packet.py          build_packet (fresh attempt dir), render_task, describe_tools
    record.py          Recorder/AttemptRecord; record dirs keyed by (lemma, round, attempt)
    failures.py        taxonomy, classify (anchored regexes), summarize (same inputs as classify)
    handoff.py
    contract.py        DesignContract
    decomposer.py      decomposer role: prompts, parse_proposal, validate_proposal
    decompose.py       policy (flagged)
    amend.py           amendment lattice (flagged; refute + human edit only)
    sketch.py          CSL sketch compiler
    schedule.py        Scheduler: frontier dispatch, per-node isolation, retry, gate, outage pause
    outage.py          provider outage recognition (auth, rate/session limit, unreachable), reset-time
                       parsing, probe, the run's one ProviderPause
    supervise.py       `pcp prove --supervise`: detached restart loop over the graph
    runners/base.py    Runner protocol
    runners/stream.py  stream-json parser (init/assistant/user/result; is_error; cache tokens)
    runners/cli.py     CLIRunner (process group, deadline, exit code -> error), codex, claude
    runners/claude_code.py, direct.py, mock.py, sandbox.py, atomic.py
    prove/__init__.py  run(), ProveConfig, ProveResult
    prove/plan.py      plan_nodes, build_graph (reconcile by hash), plan-body gating
    prove/design.py    design application + revision loop (contract from the corpus dir,
                       every design fragment scanned by the static checks)
    prove/integrate.py integrate(), export_solution
    prove/resume.py    reopen_incomplete (salvage gated bodies from attempts), RunLock
  dash/serve.py, dash/report.py, dash/dashboard.html
  cli/main.py          parser + dispatch only; cli/cmd_<command>.py per subcommand
                       (cmd_setup: `pcp setup`/`pcp env`; cmd_init: `pcp init`);
                       cli/runners.py (runner selection, model flags, sandbox choice)
```

## 3. Rules every module follows

1. **Subprocesses** go through `pcp.util.proc`. No bare `subprocess.run`/`Popen` elsewhere
   except `pcp.state.petanque` (which owns `pet`) and even that uses the same kill/reap helper.
2. **Rocq text** is lexed only by `pcp.rocq.lexer`. No ad-hoc regex over source or bodies.
3. **Every file another process may read** is written with `atomic_write_text`.
4. **Paths** are absolute by the time they leave the CLI. Library code never calls `Path.cwd()`.
5. **Errors**: raise `PcpError` subclasses; only `pcp.cli.main` maps them to exit codes and
   messages. Nothing else calls `SystemExit`. Runners never raise for ordinary failure: they
   return `NodeResult(status="error")` with the cause, and the scheduler isolates every node.
6. **No shared mutable state** across concurrent work: `Gate` is immutable, `PcpServer` locks,
   `Graph` serialises its connection, workdirs are per attempt.
7. **Status transitions** go through `orch.model.transition()`; the graph refuses invalid ones.
8. **Feature flags** (`config.flags`) gate every speculative path; the canary runs with all off.
9. **Public functions are typed**, dataclasses have `to_json`/`from_json` where they persist.
10. **Tests**: every confirmed legacy bug has a regression test named after its scenario;
    Rocq-dependent tests carry `needs_rocq`/`needs_petanque` and skip cleanly.

## 4. The gate, redesigned (PLAN.md 8.7)

A worker returns a *proof body*. The gate proves it is a body and nothing else:

1. **Body validation** (`rocq.body.validate_body`): lex into sentences; every sentence must be
   a tactic sentence. A sentence whose first token is a capitalised vernacular command is
   rejected unless it is on the harmless allowlist (`Check Print Search* About Show Locate
   Compute Eval Fail Succeed Time Timeout Unshelve Existential Grab Optimize Info
   Set/Unset Printing`). This rejects `Qed/Defined/Admitted/Abort/Save/Proof`, every
   declaration head, `Set Nested Proofs Allowed`, every escape hatch, `Require/Import`,
   `Ltac`, `Instance`, `Hint`, `Notation`, `Opaque/Transparent`, `Arguments` ... by
   construction rather than by denylist. Tactic-level forbidden tokens (`admit`, `give_up`)
   are still checked on comment-stripped text using the nesting-aware lexer.
2. **Assembly** from the frozen development plus the body (`rocq.assemble`).
3. **Structural recheck**: the assembly is re-lexed; the target block must have exactly the
   frozen statement, exactly the submitted body, the expected ender, and the set of
   declaration names must be exactly the expected set.
4. **Compile** with `coqc` in a fresh directory; `Print Assumptions` trailer uses the
   module-qualified name; output parsed by `rocq.assumptions` (wrapped types, colon-less
   guardedness/positivity entries, qualified names, suffix matching for whitelist and stubs).
5. `GateResult` is self-contained; the `Gate` object holds no per-run state.

Design submissions (`Gate.run_design`) run the same static scan over every non-proof
fragment, and hoisted preamble vernacular is scanned too.

## 5. Worker protocol invariants

- Each attempt gets a **fresh** workdir `<workroot>/<node.id>/a<N>/` (N = global attempt
  number for the node), so nothing stale is ever read as a current answer. The packet
  contract (files and TASK.md layout) is unchanged.
- `read_result` reads only the current attempt dir.
- Runner exit codes are inspected; a non-zero exit with no answer is `error`, never a
  worker's `stuck`.
- Deadline kills kill the process group; whatever was streamed is parsed; a complete
  `answer.json` written before the kill is honoured.
- The full event stream is persisted in records (`transcript.txt`), not the final text.

## 6. Petanque invariants

- A `ProofSession` is bound to the `PetProcess` that created its root state. State ids are
  never sent to another process. A process restart invalidates its sessions with a clear
  `StateError("session s3 was lost when petanque restarted; call proof_open again")`.
- Every petanque call has a Python-side wall clock (`threading` timer + kill on expiry).
- The pdeathsig is never used from worker threads; lifetime is tied by an explicit
  `close()` + `atexit` + a parent-watch thread in `pcp mcp`.

## 7. What changed from v1, deliberately

v1 is the original implementation (git `40d5b0b`); this tree is a from-scratch rewrite of it.

- `pcp.core` → `pcp.rocq` + `pcp.state`; `pcp.orch.prove` is a package; the CLI is one file
  per command. Module names referenced by docs and tests are updated accordingly.
- The graph schema is versioned (`schema_version = 2`) with a migration from v1 that keeps
  every existing `.pcp/graph*.db` readable.
- Records are keyed by `(lemma, round, attempt)`; nothing is overwritten.
- `--node-seconds` is honoured (it *is* the per-node clock unless a node budget sets one).
- Config keys `concurrency`, `axiom_whitelist`, `[flags]` are read and applied.

## 8. Bug classes designed out

The audit of v1 found 451 defects. Grouped by cause, almost all of them fall into a dozen
classes, and each class is precluded by a structural rule rather than a fix:

| class (v1 count) | v1 cause | v2 rule that makes it impossible |
|---|---|---|
| stale worker output credited to a new attempt (9) | one workdir reused across attempts, runs and rounds | every attempt gets a fresh directory; `read_result` takes the attempt dir and cannot see another |
| gate cross-contamination and unsound acceptance (14) | mutable `Gate`, regexes over bodies, positional `Print Assumptions` parsing | `Gate` is a pure function; bodies are validated as tactic-only *by construction* (allowlist); assemblies are re-lexed and structurally compared; assumptions are parsed by strict entry grammar with qualified names |
| Rocq text mis-lexed (31) | six independent regex scanners for comments, sentences, bullets, requires, sections | one lexer, one declaration parser, one section/module stack; every other module consumes their output |
| petanque state sent to the wrong process / lost on restart (7) | sessions borrowed *any* pool server; restart kept stale ids | a session is bound to the `PetProcess` that created its root; the process generation is part of every state handle; a restart invalidates its sessions explicitly |
| hangs with no deadline (6) | pytanque timeouts ignored in stdio mode; `communicate()` under `wait_for` | every external call has a Python-side wall clock in one helper (`util.proc`, `state.petanque.call`) |
| one exception wedging the whole frontier (5) | `gather` without isolation; runners raising | runners return `NodeResult(error)`; the scheduler wraps each node; nodes cannot stay `claimed` past a run |
| records overwritten (6) | record dirs keyed by (lemma, attempt-in-round) | record dirs keyed by the graph's global attempt id, which is unique by construction |
| configuration accepted but ignored (12) | flags parsed in one place and read nowhere | one `Settings` object built by the CLI; every field has exactly one consumer and a test that flips it |
| runner options silently dropped (4) | per-runner keyword plumbing | `RunnerSpec` → runner constructors reject unsupported options with `UsageError` |
| invalid graph transitions and duplicate ids (5) | free-form `update()`; slug collisions | `transition()` table enforced by the store; slugs are collision-free (hash suffix) |
| misclassified failures (7) | unanchored regexes, exit codes never read, `is_error` ignored | exit status and stream `result.is_error` are first-class inputs; `classify()` runs on the same inputs everywhere |
| dead documented features (8) | wiring never finished (`--reflect`, `--node-seconds`, plan preamble, sentinels on decomposer children) | each documented flag has an end-to-end test; the packet, gate and scheduler share one `Assembly` context object so nothing is computed and dropped |

Everything else is a plain bug with a regression test.

## 9. Incremental amendments and adjudication

A prover that discovers mid-proof that a definition lacks a fact does not contest the statement; it
asks. `answer.json` may carry `amendments: [{definition, add | replace, at, why}]` on a `stuck` (or
`contested`) answer. The orchestrator (`pcp/orch/prove/amendments.py`):

1. checks the definition exists and is declared mutable by the corpus contract;
2. builds the new sentence (`add` → `(body) ∗ (add)` with the `%I` scope kept outside; `replace` → the
   given sentence, same name) and runs it through the same static scan a design fragment gets;
3. applies it through `apply_design` (contract check, compile, children typechecked as stubs);
4. sends every request to the **approver** (the decomposer runner at `--approver-effort medium`)
   for accept/adjust/reject -- a conjunct added to a predicate in hypothesis position weakens the
   theorem, so even a strengthening is reviewed; only with no approver configured is a compiled
   `add` applied unreviewed, and the report says so;
5. replays every proved body (`revalidate`) and reopens, at `epoch+1` with bodies cleared and edges
   repinned, only the proofs that broke plus the nodes whose statements mention the definition; every
   reopened packet says exactly what changed under "The design changed since your last attempt".

Amendments have their own cap (`--amendments`, default 6) and never consume a design round. The
same cheap tier repairs a *stated* design that fails to compile, typecheck or fit the contract, or
arrives in a shape the protocol cannot read (a missing key, an entry with no sentence): the
approver re-asks for the fix (`Decomposer.amend(repair=True)`, recorded under role `repairer`, at
most three per settle loop) and the decomposer's expensive rounds are reserved for the design
being wrong. Only a deadline is not a repair. The protocol itself is read tolerantly first: an
entry's Rocq text is taken from any documented key and, failing that, from any string field that
begins with a vernacular keyword -- a synonym the model chose must never cost a round. A
`contested` node is adjudicated once per epoch by the approver: `strategy` gives the prover a hint and
one more attempt; `statement` with a one-definition fix feeds the amendment path; `statement` with
a `restatement` (the obligation's own sentence corrected, same name) is compiled and checked like a
decomposer's design, adopted at `epoch+1`, and every proof that used the old statement is replayed
(`AmendmentRun.restate`, event `node.restated_by_adjudication`) -- no design round is spent;
otherwise the existing design revision runs. The cheap tier (amendment loop and adjudication) also
runs after every revision's dispatch, before the next expensive round is considered.

The approver is also asked *before* a node's budget is spent: after `--review-after N` failed
prover attempts at an epoch (default 2; `0` never; only with an approver) the scheduler parks the
node `stuck` for review instead of retrying (`NodeOutcome.review`, event `node.for_review`), and
the amendment loop adjudicates it with the review variant of the contest prompt. `strategy` reopens
it at `epoch+1` with the hint; a fix or restatement is applied as for a contest; `statement` with
neither makes it `contested` -- the one `stuck -> contested` move in the lattice, and it is
human-only, because it is a verdict. An epoch is reviewed once (the graph meta
`contest_adjudicated:<id>` says so), after which the remaining budget is spent normally; a
resumed run hands nodes parked for review to the approver before its first dispatch
(`parked_for_review`). Verdicts reopen a node at most `MAX_VERDICT_REOPENS` (2) times over its
life (`contest_adjudicated:reopens:<id>`): the third `strategy` counts as reviewed and the budget
is spent, so a strategy-always approver and a stuck-always prover cannot cycle. A one-definition
fix is applied by the adjudication itself, and a node the fix reopened is left to that retry.
Siblings parked "blocked" on a reopened non-mockable node reopen with it. Review needs an approver
and `--amendments > 0`, since the amendment loop is what adjudicates. The retry right after an
amendment reopened a node at its own epoch runs before any review. PLAN.md
8.9 treats a twice-escalated node as a statement problem; a verdict costs seconds where each further
attempt costs the node's clock (on the spec-only seqlock_wf run, `i31` spent four 45-minute attempts
before anything looked at its statement). Approver attempts are recorded under role `approver`, so they never
count as design rounds.


## 10. Durability of the run

State is durable (the graph is the record; a run resumes, salvages gated bodies and keeps
attempts bounded), and so is the *run* (`pcp/orch/outage.py`, `supervise.py`,
`prove/resume.py`):

- **Outage pause.** A worker, decomposer or approver attempt that fails for a provider reason
  (logged out, revoked token, session or rate limit, CLI unreachable) is not charged and its node is
  not parked. The run holds one `ProviderPause`: dispatch waits, the provider is probed with backoff
  (a "resets at HH:MM" message is honoured), and the run resumes by itself. Bounded by `--pause-hours`
  (default 12); an exhausted pause parks the affected nodes as `stuck` with the outage as evidence and
  the run still reaches its report. Every pause and resume is a graph event and a `run.log` line.
- **In-flight recovery.** On resume, a node left `claimed` by a crash has its attempt directory read
  back: a partial proof in the scratch file becomes the next attempt's starting point, and the row is
  closed as interrupted. Interrupted decomposer rounds are closed too.
- **Supervision.** `pcp prove --supervise` re-execs itself detached, restarts from the graph after a
  crash with backoff (`--max-restarts`, default 20), logs to the record directory, and stops on a
  normal return. SIGTERM kills the child's process group and leaves the graph resumable.
- **Ladder resume.** `eval/ladder.py --resume STAMP` continues wall-killed rungs from their graphs.


## 11. Installation: a checkout and an installed copy behave the same

`pcp` runs from a checkout's `.venv` or from a `uv tool`/`pipx` install, and nothing may depend
on which (`tests/test_install.py` builds a wheel, installs it non-editable in a fresh venv, and
loads every asset from it; `make install-check`).

- **Assets.** Everything a run needs besides Python is under `pcp/assets/` and read through
  `pcp.util.assets`. A missing asset raises `MissingAsset`, because the v1 checkout-relative
  lookup silently found nothing in an installed copy and workers ran without their skill file.
- **Toolchain.** `pcp setup` runs the packaged `setup-toolchain.sh`, which sources
  `toolchain.env`; `pcp doctor` and `pcp env` parse the same file, and `env.sh` reads it too.
  Bumping a pin is one edit there.
- **Finding the switch.** Every binary lookup in `pcp.config.env` tries the explicit variable
  (`PCP_COQC`, `PCP_PET`, ...), then `PATH`, then `$OPAMROOT/$PCP_OPAM_SWITCH/bin` (defaults
  `~/.opam`, `pcp`). Library roots are `ROCQPATH`/`COQPATH` entries, then the switch's
  `user-contrib`. Worker environments get the switch's `bin` *appended* to `PATH`. So pcp
  launched by Claude Code or Codex, with no login shell, finds the toolchain; `eval "$(pcp env)"`
  is only for a human shell that wants `rocq` on `PATH`. A binary on `PATH` always wins, and
  `pcp doctor` reports when it does not match the pins.
- **Sandbox binds.** `--sandbox` replaces `$HOME` with a tmpfs, so a `uv tool` install under
  `~/.local/share/uv` would vanish inside it. `Sandbox.for_benchmark` therefore binds pcp's own
  installation read-only (`install_paths()`: `sys.prefix`, `sys.base_prefix`, the package
  directory; never `$HOME` or an ancestor of it) plus the `pcp` entry point's directories, so
  `pcp check` runs inside. The bound project root is the enclosing proof-copilot checkout, else
  the nearest ancestor with a `.pcp/`, else the invocation directory; `/`, `$HOME` and its
  ancestors are refused, as is a file outside the root. Every `.pcp/` under the root is masked,
  and so are `CHECKOUT_MASKS` (`.git`, `eval`, `docs`, `tests`) of every checkout under it; a
  user's own `docs/` and `tests/` stay visible. `wrap` emits mounts shallowest first, so the
  deepest rule on a path decides and a carve-back can never undo a mask beneath it.
- **pytanque** is pinned to LLM4Rocq commit `4092b12` (v0.2.2, which speaks coq-lsp 0.2.5's
  petanque) as a direct git dependency. The PyPI package named `pytanque` is an unrelated
  project; never replace the pin with a version range.

## 12. What is built

"PLAN" is the section of [`design/PLAN.md`](design/PLAN.md) a feature implements.

### The daily loop (pcp-orch)

`pcp prove FILE LEMMA --plan plan.v` runs end to end: on the canary with scripted workers (CI),
and with `--runner claude`, with and without `--sandbox --state-tools`.

| PLAN | module | what it does |
|---|---|---|
| 8.1 obligation graph, two ledgers | `pcp/orch/graph.py`, `model.py` | SQLite, schema v2 with a migration from v1; every transition validated against the lattice; bodies writable only by the prover role |
| 8.3 two-zone assembly | `pcp/rocq/assemble.py` | patches reach only proof-body spans; scopes tracked through `Module Import`, aliases and `Module Type` |
| 8.4 free sentinels | `pcp/orch/sentinels.py` | duplicates, restated root, converging failures, partial correctness (Texan triples too), non-persistent resources stated outside a `□`-boxed triple, hygiene; run on plans and decomposer proposals |
| 8.7 integrity gate | `pcp/orch/gate.py`, `pcp/rocq/body.py`, `assumptions.py` | §4 |
| 8.11 dispatch, retry, resume | `pcp/orch/schedule.py`, `prove/` | per-node isolation, attempts bounded across runs, fresh directory per attempt, retry sees the partial, salvage on resume, run lock |
| 8.11 handoff | `pcp/orch/handoff.py` | stuck node → `.v` for your editor |
| 8.5 incremental amendments | `pcp/orch/prove/amendments.py`, `amend.py` | §9: provers ask for facts, approver adjudicates contests and `--review-after` reviews |
| 6 / 8.11 run durability | `pcp/orch/outage.py`, `supervise.py`, `prove/resume.py` | §10: outage pause, in-flight recovery, `--supervise` |
| 8.6 decomposer role | `pcp/orch/decomposer.py`, `prove/design.py` | read-only toolbox; a proposal type with no proof field; every design fragment passes the gate's static scan; the design contract is loaded once from the corpus |
| 11 runners | `pcp/orch/runners/` | `codex`, `claude` (headless), `claude-code`, `direct` (Messages API, `[api]` extra), `mock`; one `RunnerSpec` factory that refuses ignored options; bubblewrap sandbox with an env allowlist |
| 11 provider profiles | `pcp/config/providers.py` | tiers as ordered preferences; a binding applies only when its provider matches the runner (`pcp models`) |
| 10 cockpit | `pcp/dash/` | `pcp serve` (read-only, resumable SSE) and `pcp report`; no steering |
| 9.3 sketch compiler | `pcp/orch/sketch.py` | annotation DSL → frozen obligations (`pcp sketch`) |
| 13 evaluation | `eval/` (checkout only) | harness, ablation arms, the design-rung ladder with `--brief spec-only` ([BENCHMARKS.md](BENCHMARKS.md)) |

### The state layer (pcp-state)

| PLAN | module | what it does |
|---|---|---|
| 6 session pool | `pcp/state/petanque.py`, `pool.py`, `session.py` | §6; hard memory limit (`PCP_PET_MEM_LIMIT_MB`) via a per-uid wrapper |
| 3.1 printer parser | `pcp/state/ipm/parse.py` | all four separator shapes; anonymous `_ : P` hypotheses; 2 030 golden states |
| 3.1 reflected dump | `pcp/assets/coq/IDump.v`, `pcp/state/ipm/reflect.py` | primary path under `pcp trace --reflect`; the printer is the fallback |
| 3.2 model, skeletons | `pcp/state/ipm/model.py`, `skeleton.py` | modality read at the head only; `twp` from `[{ }]`; every fupd shape; Iris's precedence |
| 4 ledger | `pcp/state/ledger/` | name-first matching, evar-aware hashing, goal parentage, `unknown` on ambiguity (`pcp ledger`) |
| 4.3 persistence oracle | `pcp/state/ipm/oracle.py` | always at the step's own state (`pcp trace --oracle`) |
| 5 context economy | `pcp/state/render.py`, `digest.py` | explicit selection beats diff-only; `full` never folds; elision always reported (`pcp state`) |
| 7 tool surface | `pcp/mcp/server.py` | 10 tools, capped at 12; thread-safe (`pcp mcp`, `pcp prove --state-tools`) |
| 7 pattern compiler + aligner | `pcp/state/ipm/pattern.py`, `diagnose.py` | every IPM token; binary conjunction patterns as Iris 4.5 requires (`pcp destruct`) |
| 5 / 7 retrieval | `pcp/state/search.py`, `pcp/rocq/library.py` | quoted-substring `Search`, grep fallback, a declaration index (`pcp docs`) |
| 7 compile-path diagnosis | `pcp/state/explain.py` | `pcp check --diagnose` replays the failing body by byte offset |

### Feature flags (`pcp/config/flags.py`, `[flags]` in `.pcp/config.toml`)

All default to `false`; the canary runs with all of them off.

| flag | PLAN | state |
|---|---|---|
| `recursive_decomposition` | 8.2 | policy, difficulty estimate and no-gap check in `pcp/orch/decompose.py`; the recursion is not wired into `prove` |
| `amendment_lattice` | 8.5 | machine-checked `refute`, taint, impact reports, audit routing in `pcp/orch/amend.py`; quorums and shim TTLs not built |

### Deliberately not built

- An embedding index for premise retrieval (PLAN 7): `Search` at the goal plus grep is the
  baseline it would have to beat.
- `AtomicRunner` (PLAN 11): `pcp/orch/runners/atomic.py` records the decision.
- Preservation probes for invariants (PLAN 9.2), a bespoke TUI (PLAN 10), quorum audits and
  shim TTLs (PLAN 8.5).
- A mid-flight ping for one-shot CLIs (PLAN 6): not implementable for `claude -p`; the runner
  gives the worker its whole budget instead.

### Toolchain facts the code depends on

Rocq's `Timeout` takes an integer; the Rocq 9 front end is `rocq compile`; coqc's
`characters a-b` are byte offsets; `Print Assumptions` prints `X is assumed to be guarded`
(colon-less) under `Unset Guard Checking` and `X relies on an unsafe hierarchy` under
`Unset Universe Checking`. A pin bump must re-check these and re-extract the goldens
(`make goldens`).

### Verification

About 1 300 tests; the Rocq/petanque parts skip cleanly without a toolchain, which is itself
tested (`tests/test_layering.py`). Property tests round-trip generated Iris props through the
skeleton parser and align every compiled intro pattern with its prop; golden tests replay 2 030
real Iris goal states; the gate, ledger, oracle, reflected dump, MCP tools and pipeline run
against real Rocq. Every confirmed defect, from the v1 audit and from later adversarial reviews,
has a regression test named after its scenario.
