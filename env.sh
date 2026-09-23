# proof-copilot developer shell (a checkout only; an installed pcp needs none of this).
#
#     . ./env.sh
#
# Activates the pinned opam switch and this checkout's .venv.  The pins themselves live
# in pcp/assets/toolchain.env (shipped with the package, read by `pcp setup`/`pcp doctor`);
# this file only reads them.  Build the switch with `pcp setup` (or `make toolchain`).
# Installed users: `eval "$(pcp env)"` does the switch part, and is optional.

_pcp_here="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")" && pwd)"

# --- pinned versions (exported for scripts that want them) -----------------
set -a
# shellcheck disable=SC1091
. "$_pcp_here/pcp/assets/toolchain.env"
set +a
export PCP_OPAM_SWITCH="${PCP_OPAM_SWITCH:-$PCP_DEFAULT_OPAM_SWITCH}"

# Python: 3.11+ required (pcp uses `X | Y` annotations and tomllib).
export PCP_PYTHON="${PCP_PYTHON:-python3.11}"

# --- activate --------------------------------------------------------------
if command -v opam >/dev/null 2>&1; then
  if opam switch list --short 2>/dev/null | grep -qx "$PCP_OPAM_SWITCH"; then
    eval "$(opam env --switch="$PCP_OPAM_SWITCH" --set-switch 2>/dev/null)"
  fi
fi

# The project's own venv, if it has been created.
if [ -d "$_pcp_here/.venv" ]; then
  # shellcheck disable=SC1091
  . "$_pcp_here/.venv/bin/activate"
fi
unset _pcp_here
