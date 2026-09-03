# proof-copilot toolchain pins (Phase 0).
#
# Source this to get `rocq`, `coqc`, `pet-server` and the Iris libraries on PATH:
#     . ./env.sh
#
# To build the switch from scratch: ./scripts/setup-toolchain.sh

# --- pinned versions -------------------------------------------------------
export PCP_OPAM_SWITCH="${PCP_OPAM_SWITCH:-pcp}"
export PCP_OCAML_VERSION="5.2.1"
export PCP_ROCQ_VERSION="9.1.1"
export PCP_ROCQ_STDLIB_VERSION="9.1.0"
export PCP_COQLSP_VERSION="0.2.5+9.1"
export PCP_STDPP_VERSION="1.13.0"
export PCP_IRIS_VERSION="4.5.0"
export PCP_EQUATIONS_VERSION="1.3.1+9.1"

# Python: 3.11+ required (pcp uses `X | Y` annotations and tomllib).
export PCP_PYTHON="${PCP_PYTHON:-python3.11}"

# --- activate --------------------------------------------------------------
if command -v opam >/dev/null 2>&1; then
  if opam switch list --short 2>/dev/null | grep -qx "$PCP_OPAM_SWITCH"; then
    eval "$(opam env --switch="$PCP_OPAM_SWITCH" --set-switch 2>/dev/null)"
  fi
fi

# The project's own venv, if it has been created.
if [ -d "$(dirname "${BASH_SOURCE[0]:-$0}")/.venv" ]; then
  # shellcheck disable=SC1091
  . "$(dirname "${BASH_SOURCE[0]:-$0}")/.venv/bin/activate"
fi
