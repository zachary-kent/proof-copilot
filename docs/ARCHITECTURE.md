d# proof-copilot — architecture (v2, September 2026)

This is the rewrite of the original implementation (git `40d5b0b`). The *design* is unchanged
and lives in [`PLAN.md`](PLAN.md); this document says how the code is organised, what the
layers may depend on, and the engineering rules every module follows. If the two disagree,
PLAN.md wins on *what* and this file wins on *how*.

Two products still live here, still separable:

- **pcp-state** (`pcp.state`, `pcp.mcp`): the Iris-aware proof-state layer over Rocq/petanque.
- **pcp-orch** (`pcp.orch`): the obligation-graph orchestrator, whose daily loop (`pcp prove`)
  must run where the only Rocq binary is `coqc`.

## 1. Layers and the import rule

```
pcp.util      stdlib only.                                  (proc, io, text, hashing, paths, locks)
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
    paths.py           repo_root() (from package), workspace(), resolve_from(cwd)
    locks.py           RunLock (fcntl flock on <graph>.lock); holder pid + started_at
  config/
    env.py             every environment variable name in one place + lookups
                       (coqc_binary, pet_binary, pet_server_binary, bwrap_binary, library_roots)
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
  cli/main.py          parser + dispatch only; cli/<command>.py per subcommand;
                       cli/runners.py (runner selection, model flags)
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

## 9. Incremental amendments and adjudication (added 2026-09-05)

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


## 10. Durability of the run (added 2026-09-05)

State was durable from the start (the graph is the record; a run resumes, salvages gated bodies and
keeps attempts bounded). The *run* is now durable too (`pcp/orch/outage.py`, `supervise.py`,
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
