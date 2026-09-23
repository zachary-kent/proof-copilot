# Integrations: Claude Code and Codex

How to give an interactive agent the `pcp` proof-state tools and the prover norms. Both
integrations assume the `pcp` CLI is installed and its toolchain works:

```bash
uv tool install --python 3.11 'proof-copilot[mcp] @ git+https://github.com/zachary-kent/proof-copilot@vX.Y.Z'
pcp setup      # the pinned Rocq / coq-lsp / Iris switch (tens of minutes, once)
pcp doctor     # everything below depends on this being clean
```

The `[mcp]` extra is required: it is the MCP SDK `pcp mcp` runs on.

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
| MCP server `pcp` | `pcp mcp --workspace ${CLAUDE_PROJECT_DIR}`: the ten tools below, rooted at the project. |
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

`pcp trace` / `ledger` / `state` / `destruct` do the same from a shell, without MCP.

## Troubleshooting

- **The server is "failed" in `/mcp`, or Codex says it cannot start `pcp`.** The client's
  PATH does not contain pcp. This happens when it was started from a GUI, a harness,
  or a shell without `~/.local/bin`. Either start the client from a shell where
  `command -v pcp` works, or register the absolute path: run the line
  `pcp integrate claude` prints (user scope), or `pcp integrate codex --write`, which
  writes the absolute path by default.
- **"no usable MCP server API found".** pcp was installed without the extra. Reinstall
  with `uv tool install --python 3.11 --force 'proof-copilot[mcp] @ git+…'`.
- **A tool reports the toolchain or opam switch missing.** Run `pcp doctor`. pcp finds its
  switch by itself (`$PCP_OPAM_SWITCH`, else the switch named `pcp`), with no login shell
  or `opam env` needed. If the switch is missing, run `pcp setup`. For a switch with
  another name, set `PCP_OPAM_SWITCH` in the server's environment (`env` in the JSON,
  `[mcp_servers.pcp.env]` in TOML).
- **"no such file (resolved against DIR)".** Paths are relative to the workspace, which is
  the project root. If DIR is not your project, see "Which workspace" above.
- **`iris-proving` fails to load with `invalid choice: 'skill'`.** The installed pcp
  predates `pcp skill`. Upgrade it.
- **A tool answers `"lost": true`.** The Rocq process restarted. Call `proof_open` again.
  This is not a tactic failure.
