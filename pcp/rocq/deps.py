"""The project libraries a file loads: its ``Require``s, transitively, as ``.vo`` files.

A ``pet`` process loads a ``.vo`` once and keeps it -- coq-lsp's document cache and
Rocq's library table both outlive a session -- so a library rebuilt by ``make`` after a
worker loaded it stays stale in that worker, and every lemma opened there sees the old
definitions ("The variable NoSpace was not found", session 5, issue 37).  The pool
records the ``.vo`` files behind each opened file with their mtimes and restarts a
worker whose libraries changed on disk.

Only the project's own libraries are followed (its ``-Q``/``-R`` mappings); installed
ones (Iris, stdpp) do not change under a running proof.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

from pcp.config import toolchain
from pcp.rocq.lexer import strip_comments
from pcp.rocq.project import _read_flags
from pcp.util.io import read_text

#: At most this many project files are followed from one file (a guard, not a limit
#: real developments reach).
MAX_FILES = 2000


@dataclass(frozen=True)
class Mapping:
    logical: str
    directory: Path
    recursive: bool


def mappings(start: str | Path) -> list[Mapping]:
    """The ``-Q``/``-R`` mappings of the project ``start`` belongs to, directories absolute."""
    found = toolchain.project_file(Path(start))
    if found is None or found.name == "dune-project":
        return []
    flags = _read_flags(found)
    out: list[Mapping] = []
    for i, flag in enumerate(flags):
        if flag in ("-Q", "-R") and i + 2 < len(flags):
            out.append(Mapping(flags[i + 2], (found.parent / flags[i + 1]).resolve(), flag == "-R"))
    return out


def requires(source: str) -> list[str]:
    """The qualified names a source ``Require``s (``From A Require B`` is ``A.B``)."""
    code = strip_comments(source)
    out: list[str] = []
    for sentence in re.split(r"\.(?=\s|$)", code):
        words = sentence.split()
        if "Require" not in words:
            continue
        k = words.index("Require")
        prefix = words[1] if len(words) > 2 and words[0] == "From" and k == 2 else None
        names = [w for w in words[k + 1:] if w not in ("Import", "Export", "-") and not w.startswith("(")]
        for name in names:
            name = name.strip("()")
            if name and re.fullmatch(r"[\w'.]+", name):
                out.append(f"{prefix}.{name}" if prefix else name)
    return out


def resolve(name: str, maps: list[Mapping]) -> Path | None:
    """The project ``.v`` file behind a qualified (or, under ``-R``/a suffix, partial) name."""
    parts = name.split(".")
    for m in maps:
        logical = m.logical.split(".") if m.logical not in ("", '""') else []
        if parts[: len(logical)] == logical and len(parts) > len(logical):
            candidate = m.directory.joinpath(*parts[len(logical):]).with_suffix(".v")
            if candidate.is_file():
                return candidate
    # `From smr Require Import primitive_laws` names `smr.lang.primitive_laws` by suffix.
    for m in maps:
        logical = m.logical.split(".") if m.logical not in ("", '""') else []
        if parts[: len(logical)] != logical:
            continue
        rest = parts[len(logical):]
        if not rest:
            continue
        for candidate in m.directory.rglob(f"{rest[-1]}.v"):
            rel = candidate.relative_to(m.directory).with_suffix("").parts
            if tuple(rel[-len(rest):]) == tuple(rest):
                return candidate
    return None


def library_files(file: str | Path) -> list[Path]:
    """The ``.vo`` files of the project libraries ``file`` loads, transitively (not its own)."""
    root = Path(file).resolve()
    maps = mappings(root)
    if not maps:
        return []
    seen: set[Path] = {root}
    todo = [root]
    out: list[Path] = []
    while todo and len(seen) < MAX_FILES:
        current = todo.pop()
        try:
            source = read_text(current)
        except OSError:
            continue
        for name in requires(source):
            dep = resolve(name, maps)
            if dep is None or dep in seen:
                continue
            seen.add(dep)
            todo.append(dep)
            out.append(dep.with_suffix(".vo"))
    return out


def mtime(path: Path) -> float | None:
    try:
        return path.stat().st_mtime
    except OSError:
        return None
