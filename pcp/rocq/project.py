"""``_CoqProject`` flags and one way to run ``coqc``."""

from __future__ import annotations

import os
import re
import shlex
import shutil
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

from pcp.config import env as penv
from pcp.util.proc import run

DEFAULT_COMPILE_TIMEOUT = 600.0

_LOCATION = re.compile(r'^File "(?P<file>[^"]+)", line (?P<line>\d+), characters (?P<a>\d+)-(?P<b>\d+):', re.M)


def coq_project_flags(root: Path) -> list[str]:
    """Load-path flags from ``root/_CoqProject`` (file lists are ignored).

    Lines are split like the shell does, so ``-arg "-w -deprecated"`` is two flags
    and a ``#`` comment is not honoured (review finding: a whitespace split handed
    coqc a literal ``"-w``).
    """
    path = Path(root) / "_CoqProject"
    if not path.exists():
        return []
    flags: list[str] = []
    tokens: list[str] = []
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        try:
            tokens += shlex.split(line, comments=True)
        except ValueError:
            tokens += line.split()
    i = 0
    while i < len(tokens):
        tok = tokens[i]
        if tok in ("-Q", "-R") and i + 2 < len(tokens):
            flags += tokens[i : i + 3]
            i += 3
        elif tok == "-I" and i + 1 < len(tokens):
            flags += tokens[i : i + 2]
            i += 2
        elif tok == "-arg" and i + 1 < len(tokens):
            flags += shlex.split(tokens[i + 1]) or [tokens[i + 1]]
            i += 2
        else:
            i += 1
    return flags


def rebase_flags(flags: list[str], root: Path, work: Path) -> list[str]:
    """Make relative ``-Q``/``-R``/``-I`` paths resolve from ``work`` instead of ``root``.

    ``.`` means "this development": it is pointed at the scratch directory (which
    holds the assembled file) with the original kept as a second search path.
    """
    out: list[str] = []
    i = 0
    while i < len(flags):
        if flags[i] in ("-Q", "-R") and i + 2 < len(flags):
            path = flags[i + 1]
            resolved = Path(path) if os.path.isabs(path) else (Path(root) / path).resolve()
            if path in (".", "./"):
                out += [flags[i], str(work), flags[i + 2], flags[i], str(resolved), flags[i + 2]]
            else:
                out += [flags[i], str(resolved), flags[i + 2]]
            i += 3
        elif flags[i] == "-I" and i + 1 < len(flags):
            path = flags[i + 1]
            resolved = Path(path) if os.path.isabs(path) else (Path(root) / path).resolve()
            out += [flags[i], str(resolved)]
            i += 2
        else:
            out.append(flags[i])
            i += 1
    return out


@dataclass(frozen=True)
class ErrorLocation:
    file: str
    line: int
    char_start: int
    char_end: int


@dataclass
class CompileResult:
    ok: bool
    stdout: str = ""
    stderr: str = ""
    timed_out: bool = False
    elapsed_s: float = 0.0
    argv: list[str] = field(default_factory=list)
    #: Set when coqc could not be run at all (missing binary).
    unavailable: str = ""

    @property
    def output(self) -> str:
        return self.stdout + ("\n" + self.stderr if self.stderr else "")

    def first_error(self, width: int = 400) -> str:
        if self.unavailable:
            return self.unavailable
        if self.timed_out:
            return f"coqc timed out after {self.elapsed_s:.0f}s"
        lines = self.output.splitlines()
        for i, line in enumerate(lines):
            if line.startswith("Error") or "Error:" in line:
                return " ".join(ln.strip() for ln in lines[max(0, i - 1) : i + 3])[:width]
        return "\n".join(lines[-3:])[:width]

    def error_location(self) -> ErrorLocation | None:
        """The location attached to the *error*, ignoring located warnings."""
        text = self.output
        best: ErrorLocation | None = None
        for m in _LOCATION.finditer(text):
            after = text[m.end() : m.end() + 400]
            if re.match(r"\s*Error", after):
                return ErrorLocation(m.group("file"), int(m.group("line")), int(m.group("a")), int(m.group("b")))
            if best is None and not re.match(r"\s*Warning", after):
                best = ErrorLocation(m.group("file"), int(m.group("line")), int(m.group("a")), int(m.group("b")))
        return best


def compile_text(
    text: str,
    *,
    filename: str,
    root: Path,
    flags: list[str] | None = None,
    timeout: float = DEFAULT_COMPILE_TIMEOUT,
    scratch_root: Path | None = None,
    keep: bool = False,
) -> CompileResult:
    """Write ``text`` as ``filename`` in a fresh scratch directory and run ``coqc`` on it.

    Each compile gets its own directory over the shared read-only dependency switch,
    so parallel checks never race on ``.vo`` artifacts.  The directory is removed
    afterwards unless ``keep`` is set.
    """
    coqc = penv.coqc_binary()
    if coqc is None:
        return CompileResult(False, unavailable="no coqc on PATH -- run ./scripts/setup-toolchain.sh and `. ./env.sh`")
    base = Path(scratch_root) if scratch_root is not None else None
    if base is not None:
        base.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="pcp-gate-", dir=str(base) if base is not None else None))
    try:
        target = work / filename
        target.write_text(text, encoding="utf-8")
        # The Rocq 9 front end is ``rocq compile``; handing it coqc's flags directly
        # fails with "Unknown subcommand" (review finding).
        front = [coqc, "compile"] if Path(coqc).name == "rocq" else [coqc]
        argv = [*front, *rebase_flags(list(flags or coq_project_flags(root)), root, work), "-w", "-notation-overridden", target.name]
        done = run(argv, cwd=work, timeout=timeout)
        if done.spawn_error:
            return CompileResult(False, unavailable=done.spawn_error, argv=argv)
        return CompileResult(
            done.ok,
            stdout=done.stdout,
            stderr=done.stderr,
            timed_out=done.timed_out,
            elapsed_s=done.elapsed_s,
            argv=argv,
        )
    finally:
        if not keep:
            shutil.rmtree(work, ignore_errors=True)
