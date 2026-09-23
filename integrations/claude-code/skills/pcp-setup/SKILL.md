---
name: pcp-setup
description: First-run setup and troubleshooting for proof-copilot (pcp) - installing the pcp CLI, building the pinned Rocq/Iris opam switch, making a directory a pcp project, and fixing a pcp MCP server that does not connect. Use when pcp is missing, `pcp doctor` reports problems, the pcp tools are absent or failing, or the user asks how to set proof-copilot up.
allowed-tools: Bash(pcp doctor) Bash(pcp doctor *) Bash(pcp models) Bash(pcp setup --dry-run *) Bash(pcp setup --dry-run) Bash(pcp --version) Bash(command -v pcp)
---

# Setting up proof-copilot

`pcp` is a Python CLI plus a pinned Rocq toolchain. This plugin only tells Claude Code how
to launch `pcp mcp`; the CLI itself is installed separately. Work through the steps in
order and stop at the first one that is already fine -- `pcp doctor` is the source of
truth at every step.

## 1. The CLI

```bash
command -v pcp && pcp --version
```

If missing, install it (the `[mcp]` extra is what `pcp mcp` needs):

```bash
uv tool install 'proof-copilot[mcp] @ git+https://github.com/zachary-kent/proof-copilot@vX.Y.Z'
# or: pipx install 'proof-copilot[mcp] @ git+https://github.com/zachary-kent/proof-copilot@vX.Y.Z'
```

Ask the user which tag to pin; do not pick one yourself. `uv tool` puts `pcp` in
`~/.local/bin`, which must be on the PATH Claude Code was started with.

## 2. The toolchain

```bash
pcp setup --dry-run   # the opam commands it would run; changes nothing
pcp setup             # builds the pinned switch (Rocq, coq-lsp, Iris, std++); idempotent
```

A real `pcp setup` takes tens of minutes and writes to `~/.opam`: confirm with the user
before running it, and run it in the background. pcp finds its switch by itself
(`$PCP_OPAM_SWITCH`, else the switch named `pcp`); no `eval $(opam env)` is needed, even
when a harness starts pcp without a login shell. `eval "$(pcp env)"` gives an interactive
shell the same environment for running `coqc` by hand.

## 3. Check

```bash
pcp doctor
```

It reports the switch and each pin, the packaged assets, pytanque, whether the MCP
server API is usable, and which runners (codex, claude) are reachable and logged in.
Login is never done by pcp: it prints the command (`codex login`, `/login`), which the
user runs themselves -- tell them to, do not attempt it.

## 4. The project

```bash
pcp init            # writes .pcp/config.toml, git-ignores .pcp/
pcp models          # which model each role resolves to, and why
```

Edit the `[tiers]` in `.pcp/config.toml` to the models the user actually has.

## The pcp tools are missing or fail to connect

Run `/mcp` to see the server's status. Then:

- **`pcp` not found by Claude Code** (it was started from a GUI or a harness whose PATH
  lacks `~/.local/bin`): either start Claude Code from a shell where `command -v pcp`
  works, or register the absolute path once:
  `pcp integrate claude` prints a `claude mcp add --scope user pcp -- /abs/path/pcp mcp`
  line to run.
- **"no usable MCP server API"**: pcp was installed without the extra; reinstall with
  `proof-copilot[mcp]`.
- **toolchain / switch not found** from a tool call: `pcp doctor`, then `pcp setup`.
- **"no such file (resolved against DIR)"**: tool paths are relative to the project
  root (the directory Claude Code was started in); pass paths relative to it.
