#!/usr/bin/env bash
# Phase 0: build the pinned Rocq/Iris/coq-lsp opam switch.  Run it as `pcp setup`.
#
# Idempotent: re-running only installs what is missing. Safe to run in parallel
# with development; nothing outside the opam root (~/.opam or $OPAMROOT) is touched.
# The pins live next to this script in toolchain.env (the single source; `pcp doctor`
# reads the same file).  PCP_OPAM_SWITCH overrides the switch name; PCP_SETUP_DRY_RUN=1
# prints the opam commands that would change something instead of running them.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
set -a
# shellcheck disable=SC1091
. "$here/toolchain.env"
set +a
export PCP_OPAM_SWITCH="${PCP_OPAM_SWITCH:-$PCP_DEFAULT_OPAM_SWITCH}"
DRY="${PCP_SETUP_DRY_RUN:-0}"

export OPAMYES=1
export OPAMCOLOR=never
JOBS="${PCP_JOBS:-$(nproc)}"

log() { printf '\n=== %s ===\n' "$*"; }
# Every state-changing opam call goes through `act`, so --dry-run is exact.
act() {
  if [ "$DRY" = 1 ]; then
    printf '  would run: %s\n' "$*"
  else
    "$@"
  fi
}
# ... for the calls whose failure means "already done".
act_quiet() {
  if [ "$DRY" = 1 ]; then
    printf '  would run: %s\n' "$*"
  else
    "$@" >/dev/null 2>&1 || true
  fi
}

PACKAGES=(
  "rocq-core.$PCP_ROCQ_VERSION"
  "rocq-stdlib.$PCP_ROCQ_STDLIB_VERSION"
  "coq-lsp.$PCP_COQLSP_VERSION"
  "rocq-stdpp.$PCP_STDPP_VERSION"
  "rocq-iris.$PCP_IRIS_VERSION"
  "rocq-iris-heap-lang.$PCP_IRIS_VERSION"
)

if ! command -v opam >/dev/null 2>&1; then
  if [ "$DRY" = 1 ]; then
    echo "warning: opam is not installed; a real run would stop here" >&2
    have_switch=0
  else
    echo "error: opam is not installed (https://opam.ocaml.org/doc/Install.html)" >&2
    exit 1
  fi
else
  have_switch=0
  opam switch list --short 2>/dev/null | grep -qx "$PCP_OPAM_SWITCH" && have_switch=1
fi

[ "$DRY" = 1 ] && log "dry run: switch '$PCP_OPAM_SWITCH' ($([ "$have_switch" = 1 ] && echo exists || echo missing))"

log "opam init (bare, idempotent)"
act_quiet opam init --bare -y

log "repositories"
act_quiet opam repo add --all-switches --set-default rocq-released https://rocq-prover.org/opam/released
act_quiet opam repo add --all-switches --set-default coq-released https://coq.inria.fr/opam/released
act opam update

if [ "$have_switch" != 1 ]; then
  log "creating switch $PCP_OPAM_SWITCH (ocaml $PCP_OCAML_VERSION)"
  act opam switch create "$PCP_OPAM_SWITCH" "ocaml-base-compiler.$PCP_OCAML_VERSION" -j "$JOBS"
fi

log "installing Rocq $PCP_ROCQ_VERSION, coq-lsp $PCP_COQLSP_VERSION, Iris $PCP_IRIS_VERSION (-j $JOBS)"
act opam install --switch="$PCP_OPAM_SWITCH" -j "$JOBS" -y "${PACKAGES[@]}"

# Optional extras: nice to have, never load-bearing.
act opam install --switch="$PCP_OPAM_SWITCH" -j "$JOBS" -y "rocq-equations.$PCP_EQUATIONS_VERSION" || \
  echo "warning: rocq-equations failed to install (optional, continuing)"

if [ "$DRY" = 1 ]; then
  log "dry run: nothing was changed"
  exit 0
fi

log "verifying"
eval "$(opam env --switch="$PCP_OPAM_SWITCH" --set-switch)"
for bin in rocq coqc pet pet-server; do
  if command -v "$bin" >/dev/null 2>&1; then
    printf '  %-12s %s\n' "$bin" "$(command -v "$bin")"
  else
    printf '  %-12s MISSING\n' "$bin"
  fi
done
rocq c --version 2>/dev/null || coqc --version

log "done — pcp finds the switch by itself; for rocq/coqc in this shell: eval \"\$(pcp env)\""
