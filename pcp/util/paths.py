"""Where things are.  Library code takes absolute paths; the CLI resolves them here.

There is deliberately no "repo root": an installed package has none.  Packaged files
come from :mod:`pcp.util.assets`; the project a command runs on is the invocation
directory.
"""

from __future__ import annotations

import os
from pathlib import Path


def resolve_from(path: str | Path, base: str | Path | None = None) -> Path:
    """Absolute ``path``, resolved against ``base`` (default: the current directory)."""
    p = Path(path).expanduser()
    if p.is_absolute():
        return p.resolve()
    root = Path(base) if base is not None else Path(os.getcwd())
    return (root / p).resolve()


def home() -> Path:
    return Path(os.path.expanduser("~"))


def tmpdir() -> Path:
    import tempfile

    return Path(tempfile.gettempdir())
