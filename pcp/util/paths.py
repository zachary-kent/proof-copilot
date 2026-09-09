"""Where things are.  Library code takes absolute paths; the CLI resolves them here."""

from __future__ import annotations

import os
from pathlib import Path


def repo_root() -> Path:
    """The checkout this package was imported from (for ``coq/IDump.v``, ``skills/``).

    For an installed (non-editable) package this is the site-packages parent and the
    repo-only assets are absent; callers check for existence.
    """
    return Path(__file__).resolve().parents[2]


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
