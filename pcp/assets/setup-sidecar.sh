#!/usr/bin/env bash
# Build only petanque (coq-lsp's pet) for a project's own Rocq, in a separate *sidecar*
# opam switch.  Run it as `pcp setup --for-project [DIR]`, which passes:
#
#   PCP_SIDECAR_SWITCH     the switch to create (pcp-pet-rocq-<version>)
#   PCP_SIDECAR_OCAML      the project switch's OCaml version
#   PCP_SIDECAR_CORE       the project's Rocq core packages, exactly (rocq-runtime.9.2.0 ...)
#   PCP_SIDECAR_COQLSP_GIT coq-lsp branch to pin when no opam release fits that Rocq
#   PCP_SETUP_DRY_RUN=1    print the state-changing opam commands instead of running them
#
# Why a sidecar: installing coq-lsp into the project's switch lets opam's solver rebuild
# rocq-core, std++ and Iris there, and every .vo the project built becomes "inconsistent
# assumptions".  This script is never told where the project switch is, and every opam
# call names the sidecar (--switch=) or no switch at all, from a directory with no
# `_opam` above it, so opam cannot pick the project's local switch up either.  pcp then
# runs the sidecar's pet against the project's own libraries (ROCQLIB, OCAMLPATH).
set -euo pipefail

: "${PCP_SIDECAR_SWITCH:?}" "${PCP_SIDECAR_OCAML:?}" "${PCP_SIDECAR_CORE:?}" "${PCP_SIDECAR_COQLSP_GIT:?}"
S="$PCP_SIDECAR_SWITCH"
DRY="${PCP_SETUP_DRY_RUN:-0}"
read -r -a CORE <<<"$PCP_SIDECAR_CORE"

# opam selects a local switch from the cwd, and one from OPAMSWITCH for calls without
# --switch: neither may point at the project.
unset OPAMSWITCH OPAM_SWITCH_PREFIX
cd /

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
act_quiet() {
  if [ "$DRY" = 1 ]; then
    printf '  would run: %s\n' "$*"
  else
    "$@" >/dev/null 2>&1 || true
  fi
}

have_switch=0
if ! command -v opam >/dev/null 2>&1; then
  if [ "$DRY" = 1 ]; then
    echo "warning: opam is not installed; a real run would stop here" >&2
  else
    echo "error: opam is not installed (https://opam.ocaml.org/doc/Install.html)" >&2
    exit 1
  fi
else
  opam switch list --short 2>/dev/null | grep -qx "$S" && have_switch=1
fi

[ "$DRY" = 1 ] && log "dry run: sidecar switch '$S' ($([ "$have_switch" = 1 ] && echo exists || echo missing))"

log "repositories (registered, selected for no existing switch)"
act_quiet opam init --bare -y
act_quiet opam repo add --dont-select rocq-released https://rocq-prover.org/opam/released
act opam update default rocq-released

if [ "$have_switch" != 1 ]; then
  log "creating sidecar switch $S (ocaml $PCP_SIDECAR_OCAML, like the project's)"
  act opam switch create "$S" "ocaml-base-compiler.$PCP_SIDECAR_OCAML" \
    --repositories=default,rocq-released --no-switch -j "$JOBS"
  [ "$DRY" = 1 ] || have_switch=1
fi

log "pinning the project's exact Rocq: ${CORE[*]}"
for spec in "${CORE[@]}"; do
  act opam pin add --switch="$S" -n -y "${spec%%.*}" "${spec#*.}"
done
act opam install --switch="$S" -j "$JOBS" -y "${CORE[@]}"

# The core packages are named in every request: a version pin alone does not stop the
# solver from *removing* them to satisfy an old coq-lsp (it offered coq-lsp 0.2.5+8.20
# by replacing Rocq 9.2 with Coq 8.20).  Dependencies go first, in their own request: a
# release branch's opam file may not declare rocq-core (v9.2 has it commented out), so
# opam would build coq-lsp while it recompiles rocq-runtime for a new optional dependency
# (memprof-limits) -- 'Library "rocq-runtime.vernac" not found'.
coqlsp() {
  act opam install --switch="$S" -j "$JOBS" -y --deps-only coq-lsp "${CORE[@]}"
  act opam install --switch="$S" -j "$JOBS" -y coq-lsp "${CORE[@]}"
}
log "coq-lsp (pet) for that Rocq"
release=unknown
if [ "$have_switch" = 1 ] && command -v opam >/dev/null 2>&1; then
  # Read-only: asks the solver whether a coq-lsp it knows (a release, or a branch pinned
  # by an earlier run) accepts exactly this Rocq.
  if opam install --switch="$S" --dry-run -y coq-lsp "${CORE[@]}" >/dev/null 2>&1; then release=yes; else release=no; fi
fi
case "$release" in
  yes) coqlsp ;;
  no)
    act opam pin add --switch="$S" -n -y coq-lsp "$PCP_SIDECAR_COQLSP_GIT"
    coqlsp
    ;;
  *)
    if [ "$DRY" != 1 ]; then
      # A real run always has the switch by now, so this is only reached dry.
      echo "error: the sidecar switch $S was not created" >&2
      exit 1
    fi
    printf '  would check: opam install --switch=%s --dry-run -y coq-lsp %s (is there a release for this Rocq?)\n' "$S" "${CORE[*]}"
    printf '  if not, would run: opam pin add --switch=%s -n -y coq-lsp %s\n' "$S" "$PCP_SIDECAR_COQLSP_GIT"
    printf '  then:\n'
    coqlsp
    ;;
esac

if [ "$DRY" = 1 ]; then
  log "dry run: nothing was changed"
  exit 0
fi

log "verifying"
prefix="$(opam var --switch="$S" prefix)"
for bin in pet pet-server; do
  if [ -x "$prefix/bin/$bin" ]; then printf '  %-12s %s\n' "$bin" "$prefix/bin/$bin"; else printf '  %-12s MISSING\n' "$bin"; fi
done
[ -x "$prefix/bin/pet" ] || [ -x "$prefix/bin/pet-server" ] || { echo "error: no pet was built in $S" >&2; exit 1; }
for spec in "${CORE[@]}"; do
  [ -d "$prefix/.opam-switch/packages/$spec" ] || { echo "error: $S does not have $spec installed (the solver moved it)" >&2; exit 1; }
done

log "done — pcp picks the sidecar up by itself for a project on this Rocq (see \`pcp doctor\`)"
