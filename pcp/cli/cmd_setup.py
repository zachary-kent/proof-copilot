"""``pcp setup``, ``pcp env`` -- the pinned Rocq/Iris toolchain, for an installed pcp.

The opam script and its pins ship inside the package (``pcp/assets/``), so an install
from a wheel has everything a checkout has.  ``pcp setup`` runs that script; ``pcp env``
prints the shell exports for the switch.  pcp itself does not need ``pcp env``: it
finds the switch through ``PCP_OPAM_SWITCH``/``OPAMROOT`` (:mod:`pcp.config.env`), which
matters because Claude Code and Codex start ``pcp`` without a login shell.
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

from pcp.cli.common import err
from pcp.config import env as penv
from pcp.errors import ToolchainError, UsageError
from pcp.util.assets import pins_path, setup_script, toolchain_pins
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
_ROCQ_BANNER = re.compile(r"version\s+(\S+)")


@dataclass(frozen=True)
class PinCheck:
    """One pinned component: what is installed against what is pinned."""

    name: str
    pinned: str
    installed: str | None

    @property
    def ok(self) -> bool:
        return self.installed == self.pinned


def coqc_version(coqc: str | None = None) -> str | None:
    """The version in ``coqc --version`` (``9.1.1``), or ``None``."""
    binary = coqc or penv.coqc_binary()
    if binary is None:
        return None
    done = run([binary, "--version"], timeout=60)
    match = _ROCQ_BANNER.search(done.stdout) if done.ok else None
    return match.group(1) if match else None


def switch_packages(prefix: Path) -> dict[str, str]:
    """``{package: version}`` installed in the switch at ``prefix``, read from opam's
    own bookkeeping (``.opam-switch/packages/<name>.<version>/``) -- no ``opam`` binary
    needed, so it works from a shell that never ran ``opam env``."""
    out: dict[str, str] = {}
    packages = prefix / ".opam-switch" / "packages"
    if packages.is_dir():
        for entry in packages.iterdir():
            name, sep, version = entry.name.partition(".")
            if sep and name in PINNED_PACKAGES:
                out[name] = version
    return out


def check_pins() -> list[PinCheck]:
    """Every pin against the machine: the Rocq that pcp will actually run (the
    ``coqc`` it resolves, which may not be the switch's) and the switch's packages."""
    pins = toolchain_pins()
    checks = [PinCheck("coqc --version", pins["PCP_ROCQ_VERSION"], coqc_version())]
    prefix = penv.switch_prefix()
    installed = switch_packages(prefix) if prefix is not None else {}
    for package, key in PINNED_PACKAGES.items():
        checks.append(PinCheck(package, pins[key], installed.get(package)))
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
    sys.stdout.flush()
    # Hand the terminal to the script: a switch build is long and its output is the
    # progress bar; its exit status is ours.
    os.execve(bash, [bash, str(script)], env)
    return 1  # unreachable


# ---------------------------------------------------------------- pcp env


def env_exports(switch: str | None = None) -> list[str]:
    """POSIX ``export`` lines activating the switch: ``opam env`` when opam is there
    (it knows the switch's full environment), else the essentials computed from the
    prefix; then ``ROCQPATH`` and ``PCP_OPAM_SWITCH``."""
    name = switch or penv.opam_switch()
    prefix, contrib = penv.switch_prefix(name), penv.switch_user_contrib(name)
    if prefix is None:
        raise ToolchainError(f"no opam switch {name!r} under {penv.opam_root()}; run `pcp setup` first")
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

