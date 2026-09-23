# Contributing

Set up a checkout as described in the README's Development section. The rules below are the
ones reviewers check. [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) §3 has the full list, with
the reasons.

## Layering

Each package may import only the ones listed after it (ARCHITECTURE §1):

```
pcp.util     stdlib only
pcp.config   util
pcp.rocq     util, config                (no petanque)
pcp.state    util, config, rocq
pcp.mcp      state, rocq
pcp.orch     util, config, rocq          (never state, mcp or pytanque)
pcp.dash     orch.graph
pcp.cli      everything, lazily per subcommand
```

- `pcp.orch` never imports `pcp.state`, `pcp.mcp` or `pytanque`. The daily loop must run
  where the only Rocq binary is `coqc`.
- Subprocesses go through `pcp.util.proc`; `pcp.state.petanque` is the one exception, because
  it owns `pet`. Only `pcp.cli` may raise `SystemExit` or map errors to exit codes. Library code
  takes absolute paths and never calls `Path.cwd()`.
- Rocq text is lexed only by `pcp.rocq.lexer`, never with an ad-hoc regex.
- Packaged files are read through `pcp.util.assets`, never by a path relative to a checkout.

`tests/test_layering.py` checks all of this. It fails the build; it is not a lint warning.

## The canary

`tests/test_canary.py` (`make canary`) is one golden end-to-end run of the daily loop with
scripted workers: freeze, parallel dispatch, gate, retry, resume, integrate. It runs in CI. A
change that breaks it does not merge, however useful the feature.

## Feature flags

Any speculative or partly built behaviour goes behind a flag in `pcp/config/flags.py`, and the
flag defaults to off. The canary and the fast suite run with every flag off, so a flagged path
must not change behaviour when its flag is off. A new flag also gets a row in
ARCHITECTURE §12.

## Tests

- Mark tests that need the toolchain: `pytest.mark.rocq` for `coqc`, `pytest.mark.petanque`
  for a `pet` binary (a test that uses the `pool` fixture gets this automatically), and
  `pytest.mark.slow` for long-running tests (the wheel install). Marked tests skip cleanly
  when their toolchain is missing, and `make fast` deselects them.
- Every bug fix comes with a regression test named after the scenario it reproduces.
- Before you send a change, run `make fast lint`. If you touched anything Rocq-facing, also run
  `make test` with the toolchain (`. ./env.sh` first).

## Documentation

- Comments cite the design record by section ("PLAN.md 8.11",
  [docs/design/PLAN.md](docs/design/PLAN.md)) and the architecture by section
  ("docs/ARCHITECTURE.md §3"). Keep section numbers stable, and append new sections at the end.
- Every command and flag in the README must exist; check it with `--help`.
- Record user-visible changes under the unreleased version in
  [CHANGELOG.md](CHANGELOG.md).
