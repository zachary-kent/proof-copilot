"""Every environment variable the tool reads, in one place, with one lookup each.

Nothing else in the tree calls ``os.environ.get("PCP_...")``.  The names are part of the
external contract (docs/ARCHITECTURE.md, README).
"""

from __future__ import annotations

import os
import shutil
from collections.abc import Mapping
from pathlib import Path

#: Path of ``coqc`` (else ``coqc``, then ``rocq`` on PATH).
COQC = "PCP_COQC"
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
#: token maximum" -- seqlock_wf_design, 2026-09-04), so runners raise it unless the
#: operator set it.
CLAUDE_MAX_OUTPUT_TOKENS = "CLAUDE_CODE_MAX_OUTPUT_TOKENS"
DEFAULT_CLAUDE_MAX_OUTPUT_TOKENS = "128000"

#: Variables a sandbox passes through to the worker.
SANDBOX_PASSTHROUGH = (
    "PATH", "LANG", "LC_ALL", "TERM", ROCQPATH, COQPATH, "OCAMLPATH", COQC, PET, PET_SERVER,
    PET_MEM_LIMIT_MB,  # the MCP server inside a sandbox reads it (review finding)
    CLAUDE_MAX_OUTPUT_TOKENS,
)

DEFAULT_PET_MEM_LIMIT_MB = 24576


def coqc_binary() -> str | None:
    return os.environ.get(COQC) or shutil.which("coqc") or shutil.which("rocq")


def pet_binary() -> str | None:
    return os.environ.get(PET) or shutil.which("pet")


def pet_server_binary() -> str | None:
    return os.environ.get(PET_SERVER) or shutil.which("pet-server")


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


def in_sandbox() -> bool:
    return os.environ.get(SANDBOX) == "1"


def api_key(provider: str) -> str | None:
    return os.environ.get(f"{provider.upper()}_API_KEY")


def library_roots() -> list[Path]:
    """Rocq library roots: every existing ``ROCQPATH``/``COQPATH`` entry, then the pinned switch."""
    out: list[Path] = []
    for var in (ROCQPATH, COQPATH):
        for entry in (os.environ.get(var) or "").split(os.pathsep):
            if entry:
                p = Path(entry)
                if p.is_dir() and p not in out:
                    out.append(p)
    switch = Path.home() / ".opam" / "pcp" / "lib" / "coq" / "user-contrib"
    if switch.is_dir() and switch not in out:
        out.append(switch)
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
    out = dict(os.environ if env is None else env)
    out.setdefault(CLAUDE_MAX_OUTPUT_TOKENS, DEFAULT_CLAUDE_MAX_OUTPUT_TOKENS)
    return out
