"""Which Rocq toolchain pcp runs for a project -- resolved once, as one coherent unit.

A toolchain is ``coqc``, the petanque binaries and the compiled libraries they load, and
the three must agree: a ``pet`` built for Rocq 9.1 cannot load ``.vo`` files compiled by
9.2, and a ``ROCQPATH`` that still names another switch's ``user-contrib`` silently
mixes two Iris builds.  So nothing picks a binary on its own; :func:`resolve` picks the
compiler first and derives the rest from where it lives:

1. ``coqc``: ``PCP_COQC``; else the project's local opam switch (the nearest ``_opam``
   above the file or workspace, as opam itself finds it); else ``PCP_OPAM_SWITCH`` when
   it names a switch other than the pinned default; else ``coqc``/``rocq`` on ``PATH``;
   else the pinned switch ``pcp setup`` builds.
2. Its opam *prefix* (``<prefix>/bin/coqc``) gives the Rocq version and every package
   version (read from opam's bookkeeping, no ``opam`` binary needed).
3. ``pet``/``pet-server``: ``PCP_PET``/``PCP_PET_SERVER``; else the compiler's own
   prefix; else a *sidecar* switch ``pcp setup --for-project`` built for exactly that
   Rocq (and OCaml) without touching the project's switch; else ``PATH`` / the pinned
   switch, but only when that pet was built for the same Rocq version.
4. The environment every Rocq child gets (:meth:`Toolchain.env`) drops ``ROCQPATH`` /
   ``COQPATH`` entries that belong to a *different* opam switch, and points a sidecar
   pet at the project's libraries with ``ROCQLIB`` (verified: pet honours it).

``pcp doctor`` reports exactly this object, so what it calls "ok" is what will load.
The project root (:func:`project_root`) is the nearest ``_RocqProject``/``_CoqProject``,
or a ``dune-project`` that uses rocq/coq.  Versions are judged against floors
(:func:`meets_minimum`), not pcp's pins: the pins are only what it is tested with.
"""

from __future__ import annotations

import dataclasses
import os
import re
import shutil
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path

from pcp.config import env as penv

#: Files that mark a Rocq project root, nearest first wins (``_RocqProject`` is the
#: Rocq 9 name; coq-lsp reads either).
PROJECT_FILES = ("_RocqProject", "_CoqProject")
#: The package that carries Rocq's version, by era.
_ROCQ_PACKAGES = ("rocq-core", "coq-core", "coq")
#: Name of the sidecar switch holding a pet for Rocq ``version`` (``pcp setup --for-project``).
SIDECAR_PREFIX = "pcp-pet-rocq-"


def sidecar_switch_name(rocq_version: str) -> str:
    return f"{SIDECAR_PREFIX}{rocq_version}"


def version_key(version: str) -> tuple[float, ...]:
    """A sortable key for an opam version: ``9.2.0`` -> ``(9, 2, 0)``; a ``+suffix``
    (``0.2.5+9.1``) is dropped; ``dev``/``dev.2026-07-19...`` sorts above every release."""
    base = version.partition("+")[0].strip().lower()
    if base.startswith(("dev", "master", "~dev")):
        return (float("inf"),)
    out: list[float] = []
    for part in re.split(r"[.\-~]", base):
        if not part.isdigit():
            break
        out.append(int(part))
    return tuple(out)


def meets_minimum(version: str | None, minimum: str) -> bool | None:
    """Whether ``version`` is at least ``minimum`` (``None``: nothing installed)."""
    if version is None:
        return None
    return version_key(version) >= version_key(minimum)


# ------------------------------------------------------------------ discovery


def _ancestors(start: Path) -> list[Path]:
    start = Path(start).resolve()
    if start.is_file() or (not start.exists() and start.suffix):
        start = start.parent
    return [start, *start.parents]


#: A dune project is a Rocq project when its ``dune-project`` enables the Rocq (or
#: Coq-era) build language: ``(using rocq 0.11)`` / ``(using coq 0.8)``.
_DUNE_ROCQ = re.compile(r"\(\s*using\s+(rocq|coq)\b")


def _dune_rocq_project(d: Path) -> Path | None:
    candidate = d / "dune-project"
    try:
        return candidate if candidate.is_file() and _DUNE_ROCQ.search(candidate.read_text(encoding="utf-8", errors="replace")) else None
    except OSError:
        return None


def project_file(start: str | Path) -> Path | None:
    """The nearest ``_RocqProject``/``_CoqProject`` -- or ``dune-project`` using
    rocq/coq -- at or above ``start`` (a file or directory).  In one directory the
    ``_*Project`` files win: they carry the ``-Q`` flags coq-lsp reads."""
    for d in _ancestors(Path(start)):
        for name in PROJECT_FILES:
            if (d / name).is_file():
                return d / name
        dune = _dune_rocq_project(d)
        if dune is not None:
            return dune
    return None


def project_root(start: str | Path) -> Path | None:
    """The directory of :func:`project_file`, or ``None`` outside any Rocq project."""
    found = project_file(start)
    return found.parent if found is not None else None


def local_switch(start: str | Path) -> Path | None:
    """The prefix of the nearest local opam switch (``<dir>/_opam``) at or above ``start``."""
    for d in _ancestors(Path(start)):
        prefix = d / "_opam"
        if (prefix / "bin").is_dir():
            return prefix
    return None


def prefix_of(binary: str | Path | None) -> Path | None:
    """The opam prefix a binary is installed in (``<prefix>/bin/<binary>``), if it is one.

    Symlinks are followed, so a ``~/bin/coqc`` link into a switch counts as that switch.
    """
    if not binary:
        return None
    path = Path(binary)
    if not path.is_absolute():
        found = shutil.which(str(binary))
        if found is None:
            return None
        path = Path(found)
    for candidate in dict.fromkeys([path, path.resolve()]):
        if candidate.parent.name == "bin":
            prefix = candidate.parent.parent
            if (prefix / ".opam-switch").is_dir() or (prefix / "lib" / "coq").is_dir():
                return prefix
    return None


def packages(prefix: Path | None) -> dict[str, str]:
    """``{package: version}`` installed in the opam switch at ``prefix`` (empty if none).

    Read from ``.opam-switch/packages/<name>.<version>/`` -- works from a shell that
    never ran ``opam env``.  A pinned package reports the version its opam file claims
    (a ``coq-lsp`` pinned from a git branch may still say ``+9.1``), which is why pet
    compatibility is judged by the Rocq *in the same prefix*, not by this string.
    """
    out: dict[str, str] = {}
    if prefix is None:
        return out
    root = Path(prefix) / ".opam-switch" / "packages"
    if root.is_dir():
        for entry in root.iterdir():
            name, sep, version = entry.name.partition(".")
            if sep:
                out[name] = version
    return out


def rocq_version_of(prefix: Path | None) -> str | None:
    installed = packages(prefix)
    for name in _ROCQ_PACKAGES:
        if name in installed:
            return installed[name]
    return None


def ocaml_version_of(prefix: Path | None) -> str | None:
    installed = packages(prefix)
    for name in ("ocaml-base-compiler", "ocaml-variants", "ocaml"):
        if name in installed:
            return installed[name].split("+")[0]
    return None


def _user_contrib(prefix: Path | None) -> Path | None:
    if prefix is None:
        return None
    contrib = Path(prefix) / "lib" / "coq" / "user-contrib"
    return contrib if contrib.is_dir() else None


def _owning_prefix(entry: Path) -> Path | None:
    """The opam prefix whose ``lib/coq/user-contrib`` ``entry`` is (or lies inside), if any."""
    parts = entry.resolve().parts
    for i in range(len(parts) - 3, 0, -1):
        if parts[i : i + 3] == ("lib", "coq", "user-contrib"):
            return Path(*parts[:i])
    return None


def _executable(path: Path) -> str | None:
    return str(path) if os.access(path, os.X_OK) and path.is_file() else None


def in_prefix(prefix: Path | None, *names: str) -> str | None:
    """The first of ``names`` that is an executable in ``<prefix>/bin``."""
    return _in_prefix(prefix, *names)


def _in_prefix(prefix: Path | None, *names: str) -> str | None:
    if prefix is None:
        return None
    for name in names:
        found = _executable(Path(prefix) / "bin" / name)
        if found:
            return found
    return None


# ------------------------------------------------------------------ the toolchain


@dataclass(frozen=True)
class Toolchain:
    """The resolved toolchain for one project (see the module docstring)."""

    coqc: str | None
    #: Why this ``coqc``: ``PCP_COQC``, ``project switch``, ``PCP_OPAM_SWITCH``, ``PATH``, ``pinned switch``.
    source: str
    prefix: Path | None
    rocq_version: str | None
    pet: str | None
    pet_server: str | None
    pet_prefix: Path | None
    pet_source: str
    project: Path | None = None
    #: ``ROCQPATH``/``COQPATH`` entries dropped because they belong to another switch.
    ignored_paths: tuple[Path, ...] = ()
    #: Petanque binaries passed over because they were built for another Rocq
    #: (``"<path> (PATH, built for Rocq 9.1.1)"``) -- what ``pcp doctor`` explains.
    rejected_pets: tuple[str, ...] = ()

    #: Sources that mean "the project's (or the operator's explicit) toolchain", against
    #: which pcp's pins are a tested default, not a requirement.
    PROJECT_SOURCES = (penv.COQC, "project switch", penv.OPAM_SWITCH)

    @property
    def project_toolchain(self) -> bool:
        return self.source in self.PROJECT_SOURCES

    @property
    def sidecar(self) -> bool:
        """Petanque comes from a different prefix than the compiler and its libraries."""
        return self.pet_prefix is not None and self.prefix is not None and self.pet_prefix != self.prefix

    @property
    def user_contrib(self) -> Path | None:
        return _user_contrib(self.prefix)

    @property
    def packages(self) -> dict[str, str]:
        return packages(self.prefix)

    @property
    def pet_rocq_version(self) -> str | None:
        return rocq_version_of(self.pet_prefix)

    @property
    def pet_packages(self) -> dict[str, str]:
        """The packages of the prefix petanque comes from (``coq-lsp`` lives there)."""
        return packages(self.pet_prefix)

    @property
    def ocaml_version(self) -> str | None:
        return ocaml_version_of(self.prefix)

    def compiler_argv(self) -> list[str]:
        """How to invoke the compiler: ``[coqc]``, or ``[rocq, "compile"]`` -- the Rocq 9
        front end refuses coqc's flags without the subcommand ("Unknown subcommand")."""
        if self.coqc is None:
            return []
        return [self.coqc, "compile"] if Path(self.coqc).name == "rocq" else [self.coqc]

    @property
    def petanque_available(self) -> bool:
        return self.pet is not None or self.pet_server is not None

    def library_roots(self, environ: Mapping[str, str] | None = None) -> list[Path]:
        """Where the compiled libraries live: every kept ``ROCQPATH``/``COQPATH`` entry,
        then this toolchain's ``user-contrib`` -- never another switch's."""
        environ = os.environ if environ is None else environ
        out: list[Path] = []
        for entry in _search_path(environ):
            if entry.is_dir() and not self._foreign(entry) and entry not in out:
                out.append(entry)
        contrib = self.user_contrib
        if contrib is not None and contrib not in out:
            out.append(contrib)
        return out

    def _foreign(self, entry: Path) -> bool:
        owner = _owning_prefix(entry)
        return owner is not None and self.prefix is not None and owner.resolve() != self.prefix.resolve()

    def env(self, base: Mapping[str, str] | None = None) -> dict[str, str]:
        """``base`` (default ``os.environ``) made safe for spawning this toolchain's Rocq.

        * ``PATH``: the compiler's ``bin`` is prepended when it was not found on
          ``PATH`` (so a worker's own ``coqc`` is the same compiler), else untouched;
        * ``ROCQPATH``/``COQPATH``: entries owned by a different switch are removed;
        * a sidecar pet gets ``ROCQLIB`` = the compiler's ``lib/coq`` (the project's
          ``Corelib``, the one its ``.vo`` files were checked against) and
          ``OCAMLPATH`` = its own plugins first, then the project's.
        """
        out = dict(os.environ if base is None else base)
        for var in (penv.ROCQPATH, penv.COQPATH):
            raw = out.get(var)
            if raw is None:
                continue
            kept = [e for e in raw.split(os.pathsep) if e and not self._foreign(Path(e))]
            if kept:
                out[var] = os.pathsep.join(kept)
            else:
                out.pop(var, None)
        if self.prefix is not None and self.source != "PATH":
            bin_dir = str(self.prefix / "bin")
            entries = [e for e in (out.get("PATH") or "").split(os.pathsep) if e and e != bin_dir]
            out["PATH"] = os.pathsep.join([bin_dir, *entries])
        if self.sidecar:
            assert self.prefix is not None and self.pet_prefix is not None
            out["ROCQLIB"] = str(self.prefix / "lib" / "coq")
            ocamlpath = [str(self.pet_prefix / "lib"), str(self.prefix / "lib")]
            ocamlpath += [e for e in (out.get("OCAMLPATH") or "").split(os.pathsep) if e and e not in ocamlpath]
            out["OCAMLPATH"] = os.pathsep.join(ocamlpath)
        return out

    def worker_env(self, base: Mapping[str, str] | None = None) -> dict[str, str]:
        """:meth:`env` plus :meth:`exports`: what a model worker runs with, so the
        ``pcp check`` / ``coqc`` it runs from a scratch packet (whose ancestry has no
        ``_opam``) still gets this toolchain."""
        out = self.env(base)
        out.update(self.exports())
        return out

    def exports(self) -> dict[str, str]:
        """The explicit variables that pin this toolchain for a child that cannot
        re-resolve it (a sandboxed worker whose cwd is a scratch packet)."""
        out: dict[str, str] = {}
        if self.coqc:
            out[penv.COQC] = self.coqc
        if self.pet:
            out[penv.PET] = self.pet
        if self.pet_server:
            out[penv.PET_SERVER] = self.pet_server
        return out

    def prefixes(self) -> list[Path]:
        """Every opam prefix this toolchain reads (a sandbox must bind them all)."""
        return [p for p in dict.fromkeys([self.prefix, self.pet_prefix]) if p is not None]

    def problems(self) -> list[str]:
        """Inconsistencies that will make Rocq fail in a confusing way."""
        out: list[str] = []
        if self.coqc is None:
            out.append("no coqc/rocq found (PCP_COQC, a project _opam, PATH, or the pinned switch -- run `pcp setup`)")
        if not self.petanque_available:
            hint = (
                f"`pcp setup --for-project` builds one for Rocq {self.rocq_version} in a separate switch"
                if self.rocq_version
                else "run `pcp setup`"
            )
            passed = f" (passed over: {', '.join(self.rejected_pets)})" if self.rejected_pets else ""
            out.append(f"no petanque (pet/pet-server) for this Rocq{passed}; {hint}")
        pv, cv = self.pet_rocq_version, self.rocq_version
        if self.petanque_available and pv and cv and pv != cv:
            out.append(f"petanque was built for Rocq {pv} but coqc is Rocq {cv}: every .vo will be refused")
        for entry in self.ignored_paths:
            out.append(f"ignoring {entry} on ROCQPATH/COQPATH: it belongs to another opam switch than the coqc in use")
        return out

    def blocking(self) -> list[str]:
        """The subset of :meth:`problems` that makes pcp unusable (``pcp doctor`` fails
        on these; a dropped foreign ``ROCQPATH`` entry is only reported)."""
        return [p for p in self.problems() if not p.startswith("ignoring ")]

    def describe(self) -> str:
        where = f" ({self.prefix})" if self.prefix else ""
        return f"Rocq {self.rocq_version or '?'} via {self.source}{where}"


def _search_path(environ: Mapping[str, str]) -> list[Path]:
    out: list[Path] = []
    for var in (penv.ROCQPATH, penv.COQPATH):
        for entry in (environ.get(var) or "").split(os.pathsep):
            if entry and Path(entry) not in out:
                out.append(Path(entry))
    return out


def _explicit_switch(environ: Mapping[str, str]) -> str | None:
    """``PCP_OPAM_SWITCH`` when it names something other than the pinned default
    (``env.sh`` exports the default unconditionally, so the default is no signal)."""
    from pcp.util.assets import toolchain_pins

    name = environ.get(penv.OPAM_SWITCH)
    if name and name != toolchain_pins()["PCP_DEFAULT_OPAM_SWITCH"]:
        return name
    return None


def _pick_coqc(start: Path, environ: Mapping[str, str]) -> tuple[str | None, str, Path | None]:
    explicit = environ.get(penv.COQC)
    if explicit:
        return explicit, penv.COQC, prefix_of(explicit)
    local = local_switch(start)
    found = _in_prefix(local, "coqc", "rocq")
    if found:
        return found, "project switch", local
    name = _explicit_switch(environ)
    if name:
        prefix = penv.switch_prefix(name)
        found = _in_prefix(prefix, "coqc", "rocq")
        if found:
            return found, penv.OPAM_SWITCH, prefix
    path = environ.get("PATH")
    for exe in ("coqc", "rocq"):
        found = shutil.which(exe, path=path)
        if found:
            return found, "PATH", prefix_of(found)
    prefix = penv.switch_prefix()
    found = _in_prefix(prefix, "coqc", "rocq")
    if found:
        return found, "pinned switch", prefix
    return None, "none", None


def _pick_pet(
    name: str, var: str, prefix: Path | None, rocq: str | None, environ: Mapping[str, str]
) -> tuple[str | None, Path | None, str, list[str]]:
    explicit = environ.get(var)
    if explicit:
        return explicit, prefix_of(explicit), var, []
    own = _in_prefix(prefix, name)
    if own:
        return own, prefix, "same switch as coqc", []
    if rocq:
        side = _sidecar_prefix(rocq, environ)
        found = _in_prefix(side, name)
        if found:
            return found, side, f"sidecar switch {sidecar_switch_name(rocq)}", []
    candidates: list[tuple[str | None, str]] = [(shutil.which(name, path=environ.get("PATH")), "PATH")]
    candidates.append((_in_prefix(penv.switch_prefix(), name), "pinned switch"))
    rejected: list[str] = []
    for found, how in candidates:
        if not found:
            continue
        other = prefix_of(found)
        built_for = rocq_version_of(other)
        if rocq is None or built_for is None or built_for == rocq:
            return found, other, how, rejected
        rejected.append(f"{found} ({how}, built for Rocq {built_for})")
    return None, None, "none", rejected


def _sidecar_prefix(rocq: str, environ: Mapping[str, str]) -> Path | None:
    raw = environ.get(penv.OPAMROOT)
    root = Path(raw).expanduser() if raw else penv.opam_root()
    prefix = root / sidecar_switch_name(rocq)
    return prefix if (prefix / "bin").is_dir() else None


def resolve(start: str | Path | None = None, environ: Mapping[str, str] | None = None) -> Toolchain:
    """The toolchain for the project containing ``start`` (a file or directory; default:
    the cwd).  Not memoised: it is a handful of ``stat`` calls, and a cache would go
    stale the moment ``pcp setup`` builds a switch."""
    environ = os.environ if environ is None else environ
    here = Path(start).resolve() if start is not None else Path.cwd()
    coqc, source, prefix = _pick_coqc(here, environ)
    rocq = rocq_version_of(prefix)
    pet, pet_prefix, pet_source, rejected = _pick_pet("pet", penv.PET, prefix, rocq, environ)
    server, server_prefix, server_source, rejected_servers = _pick_pet("pet-server", penv.PET_SERVER, prefix, rocq, environ)
    if pet is None and server is not None:
        pet_prefix, pet_source = server_prefix, server_source
    chain = Toolchain(
        coqc=coqc,
        source=source,
        prefix=prefix,
        rocq_version=rocq,
        pet=pet,
        pet_server=server,
        pet_prefix=pet_prefix,
        pet_source=pet_source,
        project=project_root(here),
        rejected_pets=tuple(rejected + rejected_servers),
    )
    ignored = tuple(e for e in _search_path(environ) if chain._foreign(e))
    return dataclasses.replace(chain, ignored_paths=ignored)

