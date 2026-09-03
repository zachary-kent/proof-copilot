#!/usr/bin/env bash
# Phase 0: build the pinned Rocq/Iris/coq-lsp opam switch.
#
# Idempotent: re-running only installs what is missing. Safe to run in parallel
# with development; nothing outside ~/.opam is touched.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
. "$here/env.sh"

export OPAMYES=1
export OPAMCOLOR=never
JOBS="${PCP_JOBS:-$(nproc)}"

log() { printf '\n=== %s ===\n' "$*"; }

log "opam init (bare, idempotent)"
opam init --bare -y >/dev/null 2>&1 || true

log "repositories"
opam repo add --all-switches --set-default rocq-released \
  https://rocq-prover.org/opam/released >/dev/null 2>&1 || true
opam repo add --all-switches --set-default coq-released \
  https://coq.inria.fr/opam/released >/dev/null 2>&1 || true
opam update

if ! opam switch list --short | grep -qx "$PCP_OPAM_SWITCH"; then
  log "creating switch $PCP_OPAM_SWITCH (ocaml $PCP_OCAML_VERSION)"
  opam switch create "$PCP_OPAM_SWITCH" "ocaml-base-compiler.$PCP_OCAML_VERSION" -j "$JOBS"
fi
eval "$(opam env --switch="$PCP_OPAM_SWITCH" --set-switch)"

log "installing Rocq $PCP_ROCQ_VERSION, coq-lsp $PCP_COQLSP_VERSION, Iris $PCP_IRIS_VERSION (-j $JOBS)"
opam install -j "$JOBS" -y \
  "rocq-core.$PCP_ROCQ_VERSION" \
  "rocq-stdlib.$PCP_ROCQ_STDLIB_VERSION" \
  "coq-lsp.$PCP_COQLSP_VERSION" \
  "rocq-stdpp.$PCP_STDPP_VERSION" \
  "rocq-iris.$PCP_IRIS_VERSION" \
  "rocq-iris-heap-lang.$PCP_IRIS_VERSION"

# Optional extras: nice to have, never load-bearing.
opam install -j "$JOBS" -y "rocq-equations.$PCP_EQUATIONS_VERSION" || \
  echo "warning: rocq-equations failed to install (optional, continuing)"

log "verifying"
for bin in rocq coqc pet-server; do
  if command -v "$bin" >/dev/null 2>&1; then
    printf '  %-12s %s\n' "$bin" "$(command -v "$bin")"
  else
    printf '  %-12s MISSING\n' "$bin"
  fi
done
rocq c --version 2>/dev/null || coqc --version

log "done — run '. ./env.sh' to activate in a new shell"
