"""The installed Rocq libraries: roots, a grep-able declaration index, source grep.

``pcp docs`` builds ``.pcp/docs/index.txt``: one line per declaration,
``<rel path>:<line>  <statement on one line>``, so a worker with no network can find a
lemma by shape instead of guessing its name (PLAN.md 7, docs/BENCHMARKS.md).
"""

from __future__ import annotations

import re
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path

from pcp.config.env import library_roots
from pcp.rocq.decls import parse_blocks
from pcp.util.io import atomic_write_text, read_text

INDEX_HEADS = ("Lemma", "Theorem", "Definition", "Instance", "Corollary")
INDEX_HEADER = (
    "# proof-copilot declaration index -- one declaration per line\n"
    "# <relative path>:<line>  <statement>\n"
    "# grep it: grep -nE 'Lemma .*↦.*∗' index.txt\n"
)


@dataclass(frozen=True)
class IndexEntry:
    path: str
    line: int
    statement: str

    def render(self) -> str:
        return f"{self.path}:{self.line}  {' '.join(self.statement.split())}"


def index_file(root: Path, path: Path) -> list[IndexEntry]:
    source = read_text(path)
    rel = str(path.relative_to(root))
    out: list[IndexEntry] = []
    for block in parse_blocks(source):
        if block.head in INDEX_HEADS and block.name:
            line = source.count("\n", 0, block.statement_start) + 1
            out.append(IndexEntry(rel, line, block.statement))
    return out


def build_index(out: Path, *, libraries: Iterable[str] = ("iris", "stdpp"), roots: list[Path] | None = None) -> tuple[int, list[str]]:
    """Index every declaration under ``<root>/<library>`` for each root; returns (count, libraries found)."""
    roots = roots if roots is not None else library_roots()
    entries: list[IndexEntry] = []
    found: list[str] = []
    for lib in libraries:
        for root in roots:
            base = root / lib
            if not base.is_dir():
                continue
            found.append(lib)
            for path in sorted(base.rglob("*.v")):
                entries.extend(index_file(root, path))
            break
    atomic_write_text(out, INDEX_HEADER + "\n" + "\n".join(e.render() for e in entries) + "\n")
    return len(entries), found


def grep_sources(pattern: str, *, roots: list[Path] | None = None, libraries: Iterable[str] = ("iris", "stdpp"), limit: int = 40) -> list[str]:
    """``<path>:<line>: <text>`` for lines matching ``pattern`` in the library sources."""
    roots = roots if roots is not None else library_roots()
    try:
        rx = re.compile(pattern)
    except re.error:
        rx = re.compile(re.escape(pattern))
    hits: list[str] = []
    for lib in libraries:
        for root in roots:
            base = root / lib
            if not base.is_dir():
                continue
            for path in sorted(base.rglob("*.v")):
                for i, line in enumerate(read_text(path).splitlines(), start=1):
                    if rx.search(line):
                        hits.append(f"{path.relative_to(root)}:{i}: {line.strip()}")
                        if len(hits) >= limit:
                            return hits
            break
    return hits
