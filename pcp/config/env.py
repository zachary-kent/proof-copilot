"""Every environment variable the tool reads, in one place, with one lookup each.

Nothing else in the tree calls ``os.environ.get("PCP_...")``.  The names are part of the
external contract (docs/ARCHITECTURE.md, README).
"""

from __future__ import annotations

import os
import shutil
from collections.abc import Mapping
from pathlib import Path

#: Path of ``coqc`` (else ``coqc``, then ``rocq`` on PATH, then the pinned switch).
COQC = "PCP_COQC"
#: The opam switch ``pcp setup`` builds and pcp falls back to (default: the pinned name).
OPAM_SWITCH = "PCP_OPAM_SWITCH"
#: opam's own root (default ``~/.opam``).
OPAMROOT = "OPAMROOT"
#: Path of the stdio petanque binary.
PET = "PCP_PET"
#: Path of the socket petanque server (preferred when present).
PET_SERVER = "PCP_PET_SERVER"
#: Hard RLIMIT_AS for petanque, in MB.
PET_MEM_LIMIT_MB = "PCP_PET_MEM_LIMIT_MB"
#: Path of bubblewrap.
BWRAP = "PCP_BWRAP"
#: Set to ``1`` inside every sandbox.
SANDBOX = "PCP_SANDBOX"
#: Rocq library roots.
ROCQPATH = "ROCQPATH"
COQPATH = "COQPATH"
#: API-key provider detection.
ANTHROPIC_API_KEY = "ANTHROPIC_API_KEY"
#: The Claude CLI's per-response output ceiling.  Its default (64 000 tokens) is
#: below what a decomposer at xhigh effort writes for a large design, and a reply
#: that overruns it is lost entirely ("API Error: ... exceeded the 64000 output
#: token maximum"), so runners raise it unless the operator set it.
CLAUDE_MAX_OUTPUT_TOKENS = "CLAUDE_CODE_MAX_OUTPUT_TOKENS"
DEFAULT_CLAUDE_MAX_OUTPUT_TOKENS = "128000"

#: Variables a sandbox passes through to the worker.
SANDBOX_PASSTHROUGH = (
    "PATH", "LANG", "LC_ALL", "TERM", ROCQPATH, COQPATH, "OCAMLPATH", COQC, PET, PET_SERVER,
    PET_MEM_LIMIT_MB,  # the MCP server inside a sandbox reads it
    OPAM_SWITCH, OPAMROOT,  # so `pcp check` inside finds the same switch as outside
    CLAUDE_MAX_OUTPUT_TOKENS,
)

DEFAULT_PET_MEM_LIMIT_MB = 24576


# ---------------------------------------------------------------- the pinned switch
#
# pcp finds the switch ``pcp setup`` built by itself: every binary lookup falls back to
# ``<opam root>/<switch>/bin`` after PATH, and workers get that directory appended to
# their PATH.  So ``eval "$(pcp env)"`` is only for a human shell that wants ``rocq``
# on PATH -- pcp launched by Claude Code or Codex (no login shell, no eval) still works.
# A binary on PATH wins, so an operator's own toolchain is never overridden;
# ``pcp doctor`` reports when it does not match the pins.


def opam_root() -> Path:
    raw = os.environ.get(OPAMROOT)
    return Path(raw).expanduser() if raw else Path.home() / ".opam"


def opam_switch() -> str:
    from pcp.util.assets import toolchain_pins

    return os.environ.get(OPAM_SWITCH) or toolchain_pins()["PCP_DEFAULT_OPAM_SWITCH"]


def switch_prefix(switch: str | None = None) -> Path | None:
    """The prefix of ``switch`` (default :func:`opam_switch`), if it exists: a named
    switch under the root, or a local switch (a directory holding ``_opam``)."""
    name = switch or opam_switch()
    candidates = [Path(name) / "_opam"] if os.sep in name else [opam_root() / name]
    for prefix in candidates:
        if (prefix / "bin").is_dir():
            return prefix
    return None


def switch_bin_dir() -> Path | None:
    prefix = switch_prefix()
    return prefix / "bin" if prefix is not None else None


def _switch_binary(name: str) -> str | None:
    bin_dir = switch_bin_dir()
    if bin_dir is not None and os.access(bin_dir / name, os.X_OK):
        return str(bin_dir / name)
    return None


def _which(name: str) -> str | None:
    return shutil.which(name) or _switch_binary(name)


def coqc_binary() -> str | None:
    return os.environ.get(COQC) or shutil.which("coqc") or shutil.which("rocq") or _switch_binary("coqc") or _switch_binary("rocq")


def pet_binary() -> str | None:
    return os.environ.get(PET) or _which("pet")


def pet_server_binary() -> str | None:
    return os.environ.get(PET_SERVER) or _which("pet-server")


def petanque_available() -> bool:
    return pet_binary() is not None or pet_server_binary() is not None


def bwrap_binary() -> str | None:
    return os.environ.get(BWRAP) or shutil.which("bwrap")


def pet_mem_limit_mb() -> int:
    raw = os.environ.get(PET_MEM_LIMIT_MB)
    try:
        return int(raw) if raw else DEFAULT_PET_MEM_LIMIT_MB
    except ValueError:
        return DEFAULT_PET_MEM_LIMIT_MB


def api_key(provider: str) -> str | None:
    return os.environ.get(f"{provider.upper()}_API_KEY")


def library_roots() -> list[Path]:
    """Rocq library roots: every existing ``ROCQPATH``/``COQPATH`` entry, then the pinned switch's."""
    out: list[Path] = []
    for var in (ROCQPATH, COQPATH):
        for entry in (os.environ.get(var) or "").split(os.pathsep):
            if entry:
                p = Path(entry)
                if p.is_dir() and p not in out:
                    out.append(p)
    switch = switch_user_contrib()
    if switch is not None and switch not in out:
        out.append(switch)
    return out


def switch_user_contrib(switch: str | None = None) -> Path | None:
    prefix = switch_prefix(switch)
    contrib = prefix / "lib" / "coq" / "user-contrib" if prefix is not None else None
    return contrib if contrib is not None and contrib.is_dir() else None


def with_switch_path(env: Mapping[str, str]) -> dict[str, str]:
    """``env`` with the pinned switch's ``bin`` *appended* to ``PATH`` (absent entries
    only): a worker's own ``coqc``/``rocq`` calls find the switch without ``pcp env``,
    and anything the operator put on PATH still wins."""
    out = dict(env)
    bin_dir = switch_bin_dir()
    if bin_dir is None:
        return out
    entries = [e for e in (out.get("PATH") or "").split(os.pathsep) if e]
    if str(bin_dir) not in entries:
        out["PATH"] = os.pathsep.join([*entries, str(bin_dir)])
    return out


def iris_root() -> Path | None:
    """The first library root that contains the Iris sources."""
    for root in library_roots():
        if (root / "iris").is_dir():
            return root
    return None


def with_library_root(env: dict[str, str], extra: Path) -> dict[str, str]:
    """Return ``env`` with ``extra`` prepended to both ``ROCQPATH`` and ``COQPATH``.

    Both are set, and existing entries of *both* are kept, because a machine may be
    configured through either one (CI sets only ``ROCQPATH``).
    """
    out = dict(env)
    existing: list[str] = []
    for var in (ROCQPATH, COQPATH):
        for entry in (out.get(var) or "").split(os.pathsep):
            if entry and entry not in existing:
                existing.append(entry)
    value = os.pathsep.join([str(extra), *[e for e in existing if e != str(extra)]])
    out[ROCQPATH] = value
    out[COQPATH] = value
    return out


def with_runner_defaults(env: Mapping[str, str] | None = None) -> dict[str, str]:
    """``env`` (default: the process environment) plus the defaults every model CLI
    run gets unless the operator chose otherwise."""
    out = with_switch_path(os.environ if env is None else env)
    out.setdefault(CLAUDE_MAX_OUTPUT_TOKENS, DEFAULT_CLAUDE_MAX_OUTPUT_TOKENS)
    return out
