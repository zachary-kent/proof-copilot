# Integrations: Claude Code and Codex

How to give an interactive agent the `pcp` proof-state tools and the prover norms. Both
integrations assume the `pcp` CLI is installed and its toolchain works:

```bash
uv tool install --python 3.11 'proof-copilot[mcp] @ git+https://github.com/zachary-kent/proof-copilot@vX.Y.Z'
pcp setup      # the pinned Rocq / coq-lsp / Iris switch (tens of minutes, once);
               # not needed for a project with its own switch, see below
pcp doctor     # everything below depends on this being clean
```

The `[mcp]` extra is required: it is the MCP SDK `pcp mcp` runs on.

## Using a project's own Rocq/Iris

The MCP server, `pcp trace`/`state` and the gate all run the toolchain of the project
they work on, not necessarily pcp's pinned one (Rocq 9.1.1, Iris 4.5.0). A project with a
local opam switch (`_opam`) on Rocq 9.2 and Iris dev works as it is, with no variables to set.

**How the toolchain is found** (`pcp/config/toolchain.py`, one resolution per project):

1. `coqc`/`rocq`: `PCP_COQC`; else the nearest `_opam` above the file or workspace; else
   the switch `PCP_OPAM_SWITCH` names, when that is not the default `pcp`; else `PATH`;
   else the pinned switch `pcp setup` built.
2. The versions come from that compiler's switch (opam's `.opam-switch/packages`, so no
   `opam` binary is needed).
3. `pet`/`pet-server`: `PCP_PET`/`PCP_PET_SERVER`; else the same switch; else a sidecar
   switch `pcp-pet-rocq-<version>`; else `PATH` or the pinned switch, but only when that
   pet was built for the same Rocq.
4. The Rocq child's environment drops `ROCQPATH`/`COQPATH` entries that belong to another
   switch. A sidecar pet gets `ROCQLIB` and `OCAMLPATH` pointing at the project's
   libraries and plugins.

The project root is the nearest `_RocqProject` or `_CoqProject`, or a `dune-project` that
declares `(using rocq …)` or `(using coq …)`.

**No petanque for the project's Rocq.** opam has no coq-lsp release for every Rocq (none
for 9.2 at the time of writing). Installing one into the project's own switch lets opam
rebuild its Rocq, std++ and Iris, and every `.vo` then fails with "inconsistent
assumptions". Build it on the side instead:

```bash
cd my-project
pcp setup --for-project --dry-run   # the exact opam commands; none names the project's switch
pcp setup --for-project             # or: pcp setup --for-project path/to/project
```

This creates the switch `pcp-pet-rocq-<version>` under the opam root, with the project
switch's OCaml and exactly its `rocq-core`/`rocq-runtime` (pinned, and named in every
request so the solver cannot swap them). It installs a coq-lsp release that accepts
that Rocq if there is one, and otherwise pins `git+https://github.com/ejgallego/coq-lsp#v<major>.<minor>`
in the sidecar. Only the sidecar changes, and pcp uses it without further setup.
`pet-server` may not exist for a git branch; pcp then uses stdio `pet`.

**Explicit overrides**, for the MCP server's environment (`env` in the JSON,
`[mcp_servers.pcp.env]` in TOML) or a shell: `PCP_COQC`, `PCP_PET`, `PCP_PET_SERVER`
(absolute paths), `PCP_OPAM_SWITCH` (a switch name, or a directory that holds `_opam`).

**What `pcp doctor` shows** (`--project DIR` for another project):

- which `coqc` is in use and why (for example "the project's local opam switch"), its prefix,
  the Rocq and OCaml versions;
- `pet`/`pet-server`, where they come from (same switch, sidecar, `PATH`, explicit), the
  Rocq they were built for, a sidecar's `ROCQLIB`/`OCAMLPATH`, and any pet it passed over
  because it was built for another Rocq;
- the library roots, and any foreign `ROCQPATH` entries it ignores;
- `rocq-core`, `rocq-stdlib`, std++, Iris, `iris-heap-lang` and coq-lsp, read from *that*
  switch (coq-lsp from the pet's switch). Each is checked against what pcp needs (the
  `PCP_MIN_*` floors) and shown next to the tested pins. A difference from the pins is
  information, not an error;
- **"can pcp open a lemma here?"**: it opens a real lemma through petanque with the
  project as workspace (the first lemma of the smallest built file, or `--lemma FILE:NAME`),
  runs one tactic, and prints petanque's error if that fails. Outside a project it opens a
  one-line lemma in a temporary file. `--no-probe` skips this step.

`pcp doctor` fails only when there is no `coqc`, no petanque, a pet built for a different
Rocq than `coqc`, a component below what pcp needs, or a lemma that does not open.
`pcp env` inside such a project prints the exports for its local switch.

## Claude Code: the plugin

```text
/plugin marketplace add zachary-kent/proof-copilot
/plugin install proof-copilot@proof-copilot
```

(or from a shell: `claude plugin marketplace add zachary-kent/proof-copilot` then
`claude plugin install proof-copilot@proof-copilot`; from a checkout,
`claude plugin marketplace add /path/to/proof-copilot`). Restart the session, then
`/mcp` should list `plugin:proof-copilot:pcp` as connected.

The marketplace is `.claude-plugin/marketplace.json` at the repo root; the plugin is
`integrations/claude-code/`. What it adds:

| Component | What it does |
|---|---|
| MCP server `pcp` | `pcp mcp --workspace ${CLAUDE_PROJECT_DIR}`: the proof-state tools below, rooted at the project (a file in another `_CoqProject` gets a pool rooted there). |
| skill `pcp-setup` | First run and troubleshooting: install, `pcp setup`, `pcp doctor`, `pcp init`, `pcp models`, a server that will not connect. |
| skill `pcp-run` | The daily loop: `pcp prove … --plan`, `--supervise`, resuming, `pcp status`/`serve`/`report`, `pcp handoff`, `pcp failures`. |
| skill `iris-proving` | Proving or debugging an Iris lemma by hand with the tools, plus the prover norms (below). |
| command `/proof-copilot:status` | Runs `pcp status` and says what to do about each open node. Only when you type it. |

Claude loads the skills when they apply. You can also invoke them yourself
(`/proof-copilot:iris-proving`). The plugin has no hooks.

### Which workspace

The server resolves every `file` argument, and starts its Rocq sessions, relative to its
workspace. An interactive session works on one project, the directory Claude Code was
started in, so the plugin passes `${CLAUDE_PROJECT_DIR}`. Claude Code substitutes that
in plugin MCP args. A literal `.` would depend on the server's cwd; the placeholder does
not. This was checked headlessly: `proof_open("nope.v", …)` answers
`no such file (resolved against <project dir>)`. Workers never use this entry: each one
gets its own `.mcp.json` rooted in its node workdir (`pcp.mcp.config.write_mcp_config`).

### The norms: `pcp skill show`

`pcp/assets/skills/{prover,logatom,invariants}.md` are the norms `pcp prove` puts in
every worker packet. They are just as useful to an interactive prover. The plugin does
not copy them. `iris-proving` inlines `pcp skill show prover` when it loads, using Claude
Code's `` !`command` `` injection, and tells Claude to run `pcp skill show logatom` or
`invariants` when those apply. The norms therefore always match the installed pcp, not
whatever version of the plugin is cached, and there is nothing to drift. The cost is
that the skill needs a pcp new enough to have `pcp skill`. With an older pcp the skill
fails to load with a usage error.

### Tool names and permissions

In a plugin, the tools are named `mcp__plugin_proof-copilot_pcp__<tool>`. To stop being
asked about each call, allow them in `.claude/settings.json`:

```json
{ "permissions": { "allow": ["mcp__plugin_proof-copilot_pcp"] } }
```

### Without the plugin

`pcp integrate claude` prints the same server entry two ways: as `.mcp.json` JSON and
as a `claude mcp add --scope user pcp -- /abs/path/to/pcp mcp` line. The user-level line
uses this machine's absolute pcp path, so it works even when Claude Code's PATH lacks
`~/.local/bin`. `pcp integrate claude --write --project .` merges a committable
`.mcp.json` (bare `pcp`) into the project instead. These entries leave out `--workspace`,
because Claude Code starts a stdio server in the project directory. The tools are then
`mcp__pcp__<tool>`. Don't install both the plugin and this entry, or you get two
copies of every tool.

## Codex

Codex is not installed on the machine this was built on. The generated config is
checked against the Codex documentation (`[mcp_servers.<name>]` with `command`, `args`,
`startup_timeout_sec`, `tool_timeout_sec`) and parsed as TOML by the tests, but it has
not been run against a live Codex.

```bash
pcp integrate codex            # print the [mcp_servers.pcp] table (and a `codex mcp add` line)
pcp integrate codex --write    # merge it into ~/.codex/config.toml ($CODEX_HOME respected)
pcp integrate codex --write --project .   # or into ./.codex/config.toml (trusted projects only)
```

The table sets `startup_timeout_sec = 30` and `tool_timeout_sec = 600`. Codex's defaults
are 10 s and 60 s, which is too short: `proof_open` on a cold pool and `verify_node`
both compile. That is also why the TOML is preferred over the printed `codex mcp add`
line, which cannot set timeouts. `--write` keeps the rest of the file as it is. It
refuses to change a different existing `pcp` entry unless you pass `--force`. The
user-level entry has no `--workspace`, so the server roots itself in the directory Codex
starts it in, which is the project you run Codex from. This is the part that has not
been observed live. If paths resolve against the wrong directory, add
`"--workspace", "/abs/project"` to `args` in a project-scoped config.

Then give Codex the norms and the workflow:

```bash
pcp integrate agents-md                     # print the block
pcp integrate agents-md --write --project . # add it to ./AGENTS.md (replaces it in place on re-run)
```

The block lists the tools (generated from `pcp.mcp.names.BLURBS`), the stepping
workflow, and tells Codex to read `pcp skill show prover` (and `logatom` / `invariants`)
before proving. Codex also reads `SKILL.md` skills from `.agents/skills/` and
`~/.agents/skills/`. You can copy `integrations/claude-code/skills/*` there from a
checkout, but Codex does not run the `` !`pcp skill show prover` `` line, so the
AGENTS.md block is the supported route.

## The tools

| Tool | What it does |
|---|---|
| `proof_open` | open a lemma and get its Iris proof state, per hypothesis |
| `proof_step` | run one tactic and see exactly what changed, with no file edit or recompile |
| `proof_state` | render the current goal under a token budget, saying what it elided |
| `proof_trace` | replay a script and get the resource-ledger event log |
| `proof_ledger` | where did a hypothesis go? what consumed it? what is still live? |
| `proof_try` | run up to 20 candidate tactics from one state and report which survive |
| `proof_destruct` | compile an `iDestruct`/`iIntros` pattern from the hypothesis' structure, or find where yours diverges |
| `premise_search` | search for a lemma at this goal instead of guessing a name |
| `notation_resolve` | what a notation means, what it unfolds to, which tactics apply |
| `verify_node` | run the deterministic gate on a proof body (the same gate `pcp prove` runs) |
| `proof_close` | close a session you are done with (frees its scratch twin) |
| `proof_expect` | assert the goal's shape before relying on it; a mismatch names the differing subterm |
| `proof_inv` | generate the `iInv` pattern that opens an invariant, `>` exactly on the Timeless parts |
| `diagnosis_feedback` | say when a failure's diagnosis named the wrong repair class |

Every result opens with the same block: `ok`, `what` (one line), `where` (`file`, `line`,
`column`, `sentence`, `step`), `goal` (rendered goals) and `next` (concrete next calls);
a failure adds `error`, and `timed_out` or `lost` when that is what happened
(`pcp.mcp.result`).

`pcp trace` / `ledger` / `state` / `destruct` do the same from a shell, without MCP.

## Troubleshooting

- **A plugin command or skill fails with a pcp usage error.** The plugin is newer than the
  installed pcp. Reinstall pcp at the latest tag (`pcp --version` should match the plugin's
  version in `/plugin`).
- **In headless `claude -p`, a skill or pcp tool call is refused.** Headless sessions deny
  anything that would prompt; pass `--allowedTools "Skill mcp__plugin_proof-copilot_pcp"`.
- **The server is "failed" in `/mcp`, or Codex says it cannot start `pcp`.** The client's
  PATH does not contain pcp. This happens when it was started from a GUI, a harness,
  or a shell without `~/.local/bin`. Either start the client from a shell where
  `command -v pcp` works, or register the absolute path: run the line
  `pcp integrate claude` prints (user scope), or `pcp integrate codex --write`, which
  writes the absolute path by default.
- **"no usable MCP server API found".** pcp was installed without the extra. Reinstall
  with `uv tool install --python 3.11 --force 'proof-copilot[mcp] @ git+…'`.
- **A tool reports the toolchain or opam switch missing.** Run `pcp doctor` in the project.
  pcp finds the toolchain by itself (a project `_opam`, else `$PCP_OPAM_SWITCH`, else the
  switch named `pcp`), with no login shell or `opam env` needed. For pcp's own switch, run
  `pcp setup`. For a project without a petanque for its Rocq, run `pcp setup --for-project`.
  For a switch with another name, set `PCP_OPAM_SWITCH` in the server's environment (`env`
  in the JSON, `[mcp_servers.pcp.env]` in TOML).
- **"no such file (resolved against DIR)".** Paths are relative to the workspace, which is
  the project root. If DIR is not your project, see "Which workspace" above.
- **`iris-proving` fails to load with `invalid choice: 'skill'`.** The installed pcp
  predates `pcp skill`. Upgrade it.
- **A tool answers `"lost": true`.** The Rocq process restarted. Call `proof_open` again.
  This is not a tactic failure.
