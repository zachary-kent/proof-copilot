# Changelog

All notable changes to proof-copilot. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and versions follow
[Semantic Versioning](https://semver.org/). Install a release with
`uv tool install --python 3.11 'proof-copilot[mcp] @ git+https://github.com/zachary-kent/proof-copilot@vX.Y.Z'`.

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
