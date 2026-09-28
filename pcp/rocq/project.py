"""Project-file (``_RocqProject``/``_CoqProject``) flags and one way to run ``coqc``."""

from __future__ import annotations

import os
import re
import shlex
import shutil
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

from pcp.config import toolchain
from pcp.config.toolchain import PROJECT_FILES
from pcp.config.toolchain import resolve as resolve_toolchain
from pcp.util.io import atomic_write_text
from pcp.util.proc import run

DEFAULT_COMPILE_TIMEOUT = 600.0
#: First line of a project file pcp wrote for a copy: where the development came from.
ORIGIN_MARKER = "# pcp-origin: "
_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

_LOCATION = re.compile(r'^File "(?P<file>[^"]+)", line (?P<line>\d+), characters (?P<a>\d+)-(?P<b>\d+):', re.M)


def project_file_in(root: Path) -> Path | None:
    """``root``'s own project file: ``_RocqProject`` when both exist, as Rocq itself prefers."""
    for name in PROJECT_FILES:
        if (Path(root) / name).is_file():
            return Path(root) / name
    return None


def coq_project_flags(root: Path) -> list[str]:
    """Load-path flags from ``root``'s ``_RocqProject``/``_CoqProject`` (file lists are ignored).

    Only ``root``'s own file; :func:`development_flags` is the one that finds the
    project a file belongs to.
    """
    found = project_file_in(root)
    return _read_flags(found) if found is not None else []


def _read_flags(path: Path) -> list[str]:
    """Lines are split like the shell does, so ``-arg "-w -deprecated"`` is two flags
    and a ``#`` comment is not honoured; a plain whitespace split would hand coqc a
    literal ``"-w``.
    """
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


def _source_dir(start: str | Path) -> Path:
    start = Path(start).resolve()
    return start if start.is_dir() else start.parent


def development_flags(start: str | Path) -> list[str]:
    """The load-path flags of the project ``start`` (a file or its directory) belongs to,
    written relative to ``start``'s directory: the form :func:`rebase_flags` and a copied
    project file both need.

    The project file is the nearest ``_RocqProject``/``_CoqProject`` at or above it, so
    a development in ``theories/sub/`` of a root ``-Q theories foo`` project is found.
    Every path becomes absolute except a mapping of the development's own directory,
    which stays ``.``: a scratch copy then compiles under the same logical name as the
    original (``foo.sub.x``), and the original directory still serves its siblings'
    ``.vo`` files.  When no mapping names the directory itself, one is derived from the
    nearest mapped ancestor (``-Q . foo.sub``) -- unless a path component is not a Rocq
    identifier, where the copy simply stays outside the namespace.
    """
    here = _source_dir(start)
    found = toolchain.project_file(here)
    if found is None:
        return []
    return _localize(_read_flags(found), found.parent, here)


def _localize(flags: list[str], base: Path, here: Path) -> list[str]:
    out: list[str] = []
    names_here = False
    #: (depth of the mapped ancestor, flag, logical name for ``here``)
    derived: tuple[int, str, str] | None = None
    i = 0
    while i < len(flags):
        flag = flags[i]
        if flag in ("-Q", "-R") and i + 2 < len(flags):
            phys = _absolute(flags[i + 1], base)
            logical = flags[i + 2]
            if phys == here:
                names_here = True
                out += [flag, ".", logical]
            else:
                out += [flag, str(phys), logical]
                if here.is_relative_to(phys):
                    parts = here.relative_to(phys).parts
                    if all(_IDENT.fullmatch(p) for p in parts) and (derived is None or len(phys.parts) > derived[0]):
                        derived = (len(phys.parts), flag, ".".join([logical, *parts]) if logical else ".".join(parts))
            i += 3
        elif flag == "-I" and i + 1 < len(flags):
            out += [flag, str(_absolute(flags[i + 1], base))]
            i += 2
        else:
            out.append(flag)
            i += 1
    if derived is not None and not names_here:
        out = [derived[1], ".", derived[2], *out]
    return out


def _absolute(path: str, base: Path) -> Path:
    return Path(path).resolve() if os.path.isabs(path) else (Path(base) / path).resolve()


def project_origin(start: str | Path) -> Path:
    """The directory of the project ``start`` really belongs to.

    A project file pcp wrote into a scratch copy (:func:`write_portable_project`) names
    its origin, so the copy is compiled by the original project's toolchain (its
    ``_opam``) even from a workroot outside that project.
    """
    here = _source_dir(start)
    found = toolchain.project_file(here)
    if found is None:
        return here
    for line in found.read_text(encoding="utf-8", errors="replace").splitlines():
        if line.startswith(ORIGIN_MARKER):
            origin = Path(line[len(ORIGIN_MARKER) :].strip())
            if origin.is_dir():
                return origin
    return found.parent


def portable_project_text(start: str | Path) -> str | None:
    """A ``_CoqProject`` for a copy of the development at ``start`` placed in any other
    directory: :func:`development_flags` (absolute paths, the copy's own directory as
    ``.``), other flags as ``-arg``.  ``None`` outside any project."""
    here = _source_dir(start)
    if toolchain.project_file(here) is None:
        return None
    flags = development_flags(here)
    lines = [f"{ORIGIN_MARKER}{project_origin(here)}"]
    i = 0
    while i < len(flags):
        if flags[i] in ("-Q", "-R") and i + 2 < len(flags):
            lines.append(" ".join(shlex.quote(t) for t in flags[i : i + 3]))
            i += 3
        elif flags[i] == "-I" and i + 1 < len(flags):
            lines.append(" ".join(shlex.quote(t) for t in flags[i : i + 2]))
            i += 2
        else:
            lines.append(f"-arg {shlex.quote(flags[i])}")
            i += 1
    return "\n".join(lines) + "\n"


def write_portable_project(start: str | Path, dest_dir: str | Path) -> Path | None:
    """Write :func:`portable_project_text` as ``dest_dir/_CoqProject`` (nothing outside a project).

    Copying the file beside the development instead lost a root ``-Q theories foo``
    whenever the development lives below the project root, and a relative path in it
    means nothing from the copy's directory.
    """
    text = portable_project_text(start)
    if text is None:
        return None
    target = Path(dest_dir) / "_CoqProject"
    atomic_write_text(target, text)
    return target


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
                return ErrorLocation(m.group("file"), int(m.group("line")), int(m.group("a")))
            if best is None and not re.match(r"\s*Warning", after):
                best = ErrorLocation(m.group("file"), int(m.group("line")), int(m.group("a")))
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
    chain = resolve_toolchain(project_origin(root))
    if chain.coqc is None:
        return CompileResult(False, unavailable="no coqc on PATH or in the pinned switch -- run `pcp setup` (see `pcp doctor`)")
    base = Path(scratch_root) if scratch_root is not None else None
    if base is not None:
        base.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="pcp-gate-", dir=str(base) if base is not None else None))
    try:
        target = work / filename
        target.write_text(text, encoding="utf-8")
        # The compiler is the one for ``root``'s project (its ``_opam`` if it has one),
        # never the scratch directory's, and runs in that toolchain's environment.
        argv = [*chain.compiler_argv(), *rebase_flags(list(flags or development_flags(root)), root, work), "-w", "-notation-overridden", target.name]
        done = run(argv, cwd=work, timeout=timeout, env=chain.env())
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
