"""Files and JSON, the way every layer does them."""

from __future__ import annotations

import json
import os
import re
import shutil
import stat
import tempfile
from pathlib import Path
from typing import Any


def ensure_dir(path: str | Path) -> Path:
    p = Path(path)
    p.mkdir(parents=True, exist_ok=True)
    return p


def read_text(path: str | Path) -> str:
    """UTF-8 with replacement: a stray byte in a worker's file is not a crash."""
    return Path(path).read_text(encoding="utf-8", errors="replace")


def atomic_write_text(path: str | Path, text: str, *, mode: int | None = None) -> Path:
    """Write ``text`` to ``path`` atomically (temp file + rename in the same directory).

    Anything another process may read concurrently -- packets, answers, wrappers,
    records -- goes through here, so a reader never sees a truncated file.
    """
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix=f".{target.name}.", dir=str(target.parent))
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            fh.write(text)
        if mode is not None:
            os.chmod(tmp, mode)
        os.replace(tmp, target)
    except BaseException:
        with _suppress_oserror():
            os.unlink(tmp)
        raise
    return target


class _suppress_oserror:
    def __enter__(self) -> None:
        return None

    def __exit__(self, exc_type, exc, tb) -> bool:
        return exc_type is not None and issubclass(exc_type, OSError)


def json_load(path: str | Path) -> Any:
    return json.loads(read_text(path))


def json_dumps(data: Any, *, indent: int | None = 2) -> str:
    return json.dumps(data, indent=indent, ensure_ascii=False, default=_default)


def json_dump(path: str | Path, data: Any, *, indent: int | None = 2) -> Path:
    return atomic_write_text(path, json_dumps(data, indent=indent) + "\n")


def _default(obj: Any) -> Any:
    if isinstance(obj, Path):
        return str(obj)
    if hasattr(obj, "to_json"):
        return obj.to_json()
    if isinstance(obj, set | frozenset):
        return sorted(obj)
    return str(obj)


_SLUG_BAD = re.compile(r"[^A-Za-z0-9_\-]+")


def slug(name: str, *, limit: int = 64) -> str:
    """A filesystem- and id-safe rendering of a name.

    Distinct names must map to distinct slugs where callers use the slug as a key,
    so anything lossy appends a short hash.
    """
    from pcp.util.hashing import content_hash

    cleaned = _SLUG_BAD.sub("_", name).strip("_") or "node"
    if cleaned == name and len(cleaned) <= limit:
        return cleaned
    tag = content_hash(name, prefix="")[:8]
    keep = max(1, limit - len(tag) - 1)
    return f"{cleaned[:keep]}_{tag}"


def rm_tree(path: str | Path) -> None:
    shutil.rmtree(path, ignore_errors=True)


def copy_if_exists(src: Path, dst: Path, *, max_bytes: int | None = None) -> bool:
    """Copy ``src`` to ``dst`` if it is a regular file (and, with ``max_bytes``, small
    enough).  A FIFO, a device or a directory under a worker-chosen name is skipped:
    copying it hung or raised inside the recorder (review finding)."""
    try:
        st = os.stat(src)
    except OSError:
        return False
    if not stat.S_ISREG(st.st_mode) or (max_bytes is not None and st.st_size > max_bytes):
        return False
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)
    return True
