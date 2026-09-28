"""``pcp setup``, ``pcp env`` -- the Rocq/Iris toolchain, for an installed pcp.

The opam scripts and the pins ship inside the package (``pcp/assets/``), so an install
from a wheel has everything a checkout has.  ``pcp setup`` builds pcp's pinned switch
(its tested default); ``pcp setup --for-project`` builds only a petanque for a
project's own Rocq, in a sidecar switch (:mod:`pcp.config.toolchain`), because
installing coq-lsp into the project's switch lets opam rebuild that switch's Rocq and
Iris under the project's ``.vo`` files.  ``pcp env`` prints the shell exports for the
toolchain in use.  pcp itself does not need ``pcp env``: it resolves the toolchain on
its own (:func:`pcp.config.toolchain.resolve`), which matters because Claude Code and
Codex start ``pcp`` without a login shell.
"""

from __future__ import annotations

import argparse
import os
import re
import shlex
import shutil
import sys
from dataclasses import dataclass
from pathlib import Path

from pcp.cli.common import absolute, err
from pcp.config import env as penv
from pcp.config import toolchain as tc
from pcp.errors import ToolchainError, UsageError
from pcp.util.assets import pins_path, setup_script, sidecar_script, toolchain_pins
from pcp.util.proc import run

#: The opam packages ``setup-toolchain.sh`` installs, and the pin each must match.
#: ``rocq-equations`` is optional there and so absent here.
PINNED_PACKAGES: dict[str, str] = {
    "rocq-core": "PCP_ROCQ_VERSION",
    "rocq-stdlib": "PCP_ROCQ_STDLIB_VERSION",
    "coq-lsp": "PCP_COQLSP_VERSION",
    "rocq-stdpp": "PCP_STDPP_VERSION",
    "rocq-iris": "PCP_IRIS_VERSION",
    "rocq-iris-heap-lang": "PCP_IRIS_VERSION",
}
#: What pcp needs of each component (``toolchain.env``'s floors); unlisted ones
#: (``rocq-stdlib``) pcp does not need at any particular version.
REQUIRED_MINIMUM: dict[str, str] = {
    "rocq-core": "PCP_MIN_ROCQ",
    "coq-lsp": "PCP_MIN_COQLSP",
    "rocq-stdpp": "PCP_MIN_STDPP",
    "rocq-iris": "PCP_MIN_IRIS",
    "rocq-iris-heap-lang": "PCP_MIN_IRIS",
}
#: Coq-era opam names of the same components, tried after the Rocq name.
PACKAGE_ALIASES: dict[str, tuple[str, ...]] = {
    "rocq-core": ("coq-core", "coq"),
    "rocq-stdlib": ("coq-stdlib",),
    "rocq-stdpp": ("coq-stdpp",),
    "rocq-iris": ("coq-iris",),
    "rocq-iris-heap-lang": ("coq-iris-heap-lang",),
}
#: Where coq-lsp's release branches live; ``v<major>.<minor>`` tracks each Rocq.
COQLSP_GIT = "git+https://github.com/ejgallego/coq-lsp"
_ROCQ_BANNER = re.compile(r"version\s+(\S+)")


@dataclass(frozen=True)
class PinCheck:
    """One component: what is installed, against the version pcp's own switch pins
    (its tested default) and the floor pcp needs (``minimum``; ``None``: any)."""

    name: str
    pinned: str
    installed: str | None
    minimum: str | None = None

    @property
    def ok(self) -> bool:
        """Exactly the pinned version -- what ``pcp setup`` checks of its own switch."""
        return self.installed == self.pinned

    @property
    def meets(self) -> bool | None:
        """At least :attr:`minimum` -- what ``pcp doctor`` requires of any toolchain.
        ``None``: not installed."""
        if self.minimum is None:
            return None if self.installed is None else True
        return tc.meets_minimum(self.installed, self.minimum)


def coqc_version(coqc: str | None = None) -> str | None:
    """The version in ``coqc --version`` (``9.1.1``), or ``None``."""
    binary = coqc or penv.coqc_binary()
    if binary is None:
        return None
    done = run([binary, "--version"], timeout=60)
    match = _ROCQ_BANNER.search(done.stdout) if done.ok else None
    return match.group(1) if match else None


def switch_packages(prefix: Path | None, pet_prefix: Path | None = None) -> dict[str, str]:
    """``{pinned package: version}`` installed at ``prefix`` (a Coq-era name counts as
    its Rocq successor), read from opam's own bookkeeping (:func:`tc.packages`, no
    ``opam`` binary needed).  ``coq-lsp`` is read from ``pet_prefix`` when given: a
    sidecar's petanque is not in the compiler's switch."""
    installed = tc.packages(prefix)
    beside = tc.packages(pet_prefix) if pet_prefix is not None else installed
    out: dict[str, str] = {}
    for name in PINNED_PACKAGES:
        source = beside if name == "coq-lsp" else installed
        for candidate in (name, *PACKAGE_ALIASES.get(name, ())):
            if candidate in source:
                out[name] = source[candidate]
                break
    return out


def check_pins(chain: tc.Toolchain | None = None) -> list[PinCheck]:
    """Every pin against one toolchain, all read from the *same* place: ``chain``'s
    ``coqc`` and prefix (and its petanque's prefix for ``coq-lsp``), default pcp's
    pinned switch.  (Reading the packages of the pinned switch while another
    ``coqc`` runs reported "ok" for libraries that were never loaded.)"""
    pins = toolchain_pins()
    if chain is None:
        prefix = penv.switch_prefix()
        coqc = tc.in_prefix(prefix, "coqc", "rocq")
        installed = switch_packages(prefix)
    else:
        coqc = chain.coqc
        installed = switch_packages(chain.prefix, chain.pet_prefix)
    floor = {name: pins.get(key) for name, key in REQUIRED_MINIMUM.items()}
    checks = [PinCheck("coqc --version", pins["PCP_ROCQ_VERSION"], coqc_version(coqc) if coqc else None, floor["rocq-core"])]
    for package, key in PINNED_PACKAGES.items():
        checks.append(PinCheck(package, pins[key], installed.get(package), floor.get(package)))
    return checks


# ---------------------------------------------------------------- pcp setup


def setup_environment(switch: str | None, *, dry_run: bool, jobs: int | None) -> dict[str, str]:
    env = dict(os.environ)
    env[penv.OPAM_SWITCH] = switch or penv.opam_switch()
    env["PCP_SETUP_DRY_RUN"] = "1" if dry_run else "0"
    if jobs is not None:
        env["PCP_JOBS"] = str(int(jobs))
    return env


def cmd_setup(args: argparse.Namespace) -> int:
    bash = shutil.which("bash")
    if bash is None:
        raise ToolchainError("`pcp setup` needs bash on PATH")
    if args.jobs is not None and args.jobs < 1:
        raise UsageError("--jobs must be at least 1")
    if getattr(args, "for_project", None) is not None:
        return _setup_sidecar(args, bash)
    script = setup_script()
    env = setup_environment(args.switch, dry_run=args.dry_run, jobs=args.jobs)
    switch = env[penv.OPAM_SWITCH]
    print(f"toolchain script: {script}\npins:             {pins_path()}\nswitch:           {switch} (opam root {penv.opam_root()})")
    if not args.dry_run and not args.force and args.switch in (None, penv.opam_switch()):
        stale = [c for c in check_pins() if not c.ok]
        if not stale and penv.switch_prefix() is not None:
            print("the switch already matches every pin; nothing to do (--force re-runs the script)")
            return 0
    if args.dry_run:
        done = run([bash, str(script)], env=env, timeout=600)
        sys.stdout.write(done.stdout)
        if done.stderr:
            err(done.stderr.rstrip())
        return 0 if done.ok else 1
    return _exec(bash, script, env)


def _exec(bash: str, script: Path, env: dict[str, str]) -> int:
    sys.stdout.flush()
    # Hand the terminal to the script: a switch build is long and its output is the
    # progress bar; its exit status is ours.
    os.execve(bash, [bash, str(script)], env)
    return 1  # unreachable


# ---------------------------------------------------------------- pcp setup --for-project


@dataclass(frozen=True)
class SidecarPlan:
    """What ``setup-sidecar.sh`` is asked to build -- all derived from the project's
    prefix, which the script itself is never given."""

    chain: tc.Toolchain
    switch: str
    ocaml: str
    #: The project's Rocq core packages at their exact versions (``rocq-core.9.2.0``).
    core: tuple[str, ...]
    coqlsp_git: str

    def environment(self, *, dry_run: bool, jobs: int | None) -> dict[str, str]:
        env = {k: v for k, v in os.environ.items() if k not in ("OPAMSWITCH", "OPAM_SWITCH_PREFIX")}
        env.update(
            PCP_SIDECAR_SWITCH=self.switch,
            PCP_SIDECAR_OCAML=self.ocaml,
            PCP_SIDECAR_CORE=" ".join(self.core),
            PCP_SIDECAR_COQLSP_GIT=self.coqlsp_git,
            PCP_SETUP_DRY_RUN="1" if dry_run else "0",
        )
        if jobs is not None:
            env["PCP_JOBS"] = str(int(jobs))
        return env


def sidecar_plan(start: str | Path) -> SidecarPlan:
    """The sidecar for the project toolchain at ``start``; :class:`UsageError` when
    ``start`` has no project toolchain (``pcp setup`` is the command for pcp's own)."""
    chain = tc.resolve(start)
    if chain.prefix is None or not chain.project_toolchain:
        raise UsageError(
            f"no project toolchain at {start}: pcp would use {chain.describe()}. --for-project builds a "
            "petanque for a project's own opam switch (a local `_opam`, or PCP_COQC / PCP_OPAM_SWITCH); "
            "for pcp's pinned toolchain run `pcp setup`"
        )
    rocq, ocaml = chain.rocq_version, chain.ocaml_version
    if rocq is None or ocaml is None:
        raise ToolchainError(f"cannot read the Rocq/OCaml versions of the switch at {chain.prefix} (no .opam-switch/packages)")
    switch = tc.sidecar_switch_name(rocq)
    if (penv.opam_root() / switch).resolve() == chain.prefix.resolve():
        raise UsageError(f"the toolchain in use is already the sidecar {switch}; point --for-project at the project")
    installed = chain.packages
    core = tuple(f"{name}.{installed[name]}" for name in ("rocq-runtime", "rocq-core", "coq-core", "coq") if name in installed)
    major_minor = ".".join(rocq.split(".")[:2])
    return SidecarPlan(chain, switch, ocaml, core, f"{COQLSP_GIT}#v{major_minor}")


def _setup_sidecar(args: argparse.Namespace, bash: str) -> int:
    plan = sidecar_plan(absolute(args.for_project) or Path.cwd())
    chain = plan.chain
    side = penv.opam_root() / plan.switch
    print(
        f"project toolchain: {chain.describe()}, OCaml {plan.ocaml}\n"
        f"sidecar switch:    {plan.switch} (opam root {penv.opam_root()}), pinned to {' '.join(plan.core)}\n"
        "                   the project's own switch is never passed to opam"
    )
    if chain.pet_source == "same switch as coqc":
        print(f"note: the project switch has its own pet ({chain.pet}); pcp prefers it over the sidecar")
    if not args.dry_run and not args.force and tc.in_prefix(side, "pet", "pet-server"):
        print(f"{plan.switch} already has petanque; nothing to do (--force re-runs the script)")
        return 0
    script = sidecar_script()
    env = plan.environment(dry_run=args.dry_run, jobs=args.jobs)
    if args.dry_run:
        done = run([bash, str(script)], env=env, timeout=600)
        sys.stdout.write(done.stdout)
        if done.stderr:
            err(done.stderr.rstrip())
        return 0 if done.ok else 1
    os.chdir("/")  # no `_opam` above the cwd: opam must not select the project's switch
    return _exec(bash, script, env)


# ---------------------------------------------------------------- pcp env


def env_exports(switch: str | None = None, start: str | Path | None = None) -> list[str]:
    """POSIX ``export`` lines activating a switch: ``opam env`` when opam is there
    (it knows the switch's full environment), else the essentials computed from the
    prefix; then ``ROCQPATH`` (and ``PCP_OPAM_SWITCH`` for a named switch).

    Without ``switch``: the local ``_opam`` of the project at ``start`` (default the
    cwd) when there is one -- the toolchain pcp itself uses there -- else the pinned
    switch, with a ``#`` comment saying why (comments are inert under ``eval``)."""
    lines: list[str] = []
    if switch is None:
        chain = tc.resolve(start)
        local = tc.local_switch(start if start is not None else Path.cwd())
        if chain.source == "project switch" and local is not None:
            pet = f"; pet: {chain.pet} ({chain.pet_source})" if chain.pet else "; no petanque (`pcp setup --for-project`)"
            lines.append(f"# project toolchain: {chain.describe()}{pet}")
            return lines + _switch_exports(str(local.parent), local, chain.user_contrib, named=False)
        if chain.project_toolchain:
            lines.append(f"# pcp uses {chain.describe()} here (explicit); the lines below are pcp's pinned switch")
        elif chain.project is not None:
            lines.append(f"# no project-local _opam above {chain.project}; pcp's pinned switch:")
    name = switch or penv.opam_switch()
    prefix, contrib = penv.switch_prefix(name), penv.switch_user_contrib(name)
    if prefix is None:
        raise ToolchainError(f"no opam switch {name!r} under {penv.opam_root()}; run `pcp setup` first")
    return lines + _switch_exports(name, prefix, contrib, named=True)


def _switch_exports(name: str, prefix: Path, contrib: Path | None, *, named: bool) -> list[str]:
    lines: list[str] = []
    opam = shutil.which("opam")
    done = run([opam, "env", f"--switch={name}", "--set-switch", "--shell=sh"], timeout=60) if opam else None
    if done is not None and done.ok and done.stdout.strip():
        lines += [ln for ln in done.stdout.splitlines() if ln.strip()]
    else:
        q = shlex.quote
        lines += [
            f"OPAM_SWITCH_PREFIX={q(str(prefix))}; export OPAM_SWITCH_PREFIX;",
            f"CAML_LD_LIBRARY_PATH={q(str(prefix / 'lib' / 'stublibs'))}; export CAML_LD_LIBRARY_PATH;",
            f'PATH={q(str(prefix / "bin"))}:"$PATH"; export PATH;',
        ]
    if named:
        lines.append(f"{penv.OPAM_SWITCH}={shlex.quote(name)}; export {penv.OPAM_SWITCH};")
    if contrib is not None:
        lines.append(f"{penv.ROCQPATH}={shlex.quote(str(contrib))}; export {penv.ROCQPATH};")
    return lines


def cmd_env(args: argparse.Namespace) -> int:
    print("\n".join(env_exports(args.switch)))
    return 0


def pins_summary() -> str:
    pins = toolchain_pins()
    return (
        f"Rocq {pins['PCP_ROCQ_VERSION']}, Iris {pins['PCP_IRIS_VERSION']}, std++ {pins['PCP_STDPP_VERSION']}, "
        f"coq-lsp {pins['PCP_COQLSP_VERSION']}, OCaml {pins['PCP_OCAML_VERSION']}"
    )

