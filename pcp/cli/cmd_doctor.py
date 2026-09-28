"""``pcp doctor``, ``pcp models``, ``pcp docs`` -- the environment, not a proof."""

from __future__ import annotations

import argparse
import importlib.util
import os
import re
from pathlib import Path

from pcp.cli.common import absolute, err
from pcp.config import env as penv
from pcp.config.load import DEFAULT_CONFIG, EXAMPLE_CONFIG, load
from pcp.config.providers import describe_bindings
from pcp.errors import UsageError


def _config(args: argparse.Namespace):
    path = getattr(args, "config", None)
    return load(absolute(path) if path else None)


def cmd_models(args: argparse.Namespace) -> int:
    if args.example:
        print(EXAMPLE_CONFIG)
        return 0
    cfg = _config(args)
    print(describe_bindings(cfg))
    print(f"\nsource: {cfg.source}")
    print(
        "override per run with --decomposer / --prover-model, or pin them in "
        f'{DEFAULT_CONFIG} ([tiers] decomposer = "anthropic/claude-fable-5").'
    )
    return 0


#: The live probe: the smallest document that makes petanque load the Rocq prelude
#: (every ``.vo`` compatibility problem surfaces there) and run one tactic.
PROBE_LEMMA = "pcp_probe"
PROBE_TEXT = f"Lemma {PROBE_LEMMA} : True.\nProof.\n  exact I.\nQed.\n"
PROBE_TIMEOUT_S = 120.0


#: Vernacular that opens a proof pcp can step into.
_LEMMA_KEYWORDS = frozenset({"Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark"})
_LEMMA_NAME = re.compile(r"\s*(?:#\[[^\]]*\]\s*)*[A-Za-z]+\s+([A-Za-z_][A-Za-z0-9_']*)")
#: Never searched for a probe file: switches, build trees, pcp's own state and twins.
_PROBE_SKIP = frozenset({"_opam", "_build", ".git", ".pcp", "node_modules", "__pycache__", ".venv"})


def first_lemma(file: Path) -> str | None:
    """The name of the first ``Lemma``/``Theorem``/... in ``file``, if any."""
    from pcp.rocq.lexer import split_sentences

    try:
        sentences = split_sentences(file.read_text(encoding="utf-8", errors="replace"))
    except OSError:
        return None
    for sentence in sentences:
        if sentence.first_word in _LEMMA_KEYWORDS:
            found = _LEMMA_NAME.match(sentence.code)
            if found:
                return found.group(1)
    return None


def pick_probe_lemma(project: Path) -> tuple[Path, str] | None:
    """A real lemma of ``project`` to open: the first of the smallest ``.v`` file that
    has one, preferring files already compiled (a ``.vo`` beside them) -- a small built
    file isolates "can this toolchain load this project" from "is this file slow"."""
    candidates: list[tuple[bool, int, Path]] = []
    for dirpath, dirnames, files in os.walk(project):
        dirnames[:] = [d for d in dirnames if d not in _PROBE_SKIP and not d.startswith(".")]
        for name in files:
            if name.endswith(".v") and "__pcp" not in name:
                path = Path(dirpath) / name
                try:
                    candidates.append((not path.with_suffix(".vo").exists(), path.stat().st_size, path))
                except OSError:
                    continue
    for _unbuilt, _size, path in sorted(candidates):
        lemma = first_lemma(path)
        if lemma:
            return path, lemma
    return None


def probe_petanque(chain, *, lemma: tuple[Path, str] | None = None, timeout: float = PROBE_TIMEOUT_S) -> tuple[bool, str]:
    """Open a lemma through ``chain``'s petanque and run one tactic -- the only check
    that holds across Rocq versions (no version string tells a pet that refuses the
    project's ``Corelib``, or a ``-Q`` that coq-lsp does not see).  ``lemma`` is a real
    ``(file, name)`` of the project, opened with the project root as the workspace;
    ``None`` opens ``Lemma pcp_probe : True.`` in a temporary file.  Returns
    ``(ok, detail)``; a failure's detail is petanque's own error text."""
    import tempfile
    import time

    from pcp.state.petanque import PetProcess

    # Pinned through the environment -- the same values a sandboxed worker gets --
    # because a temporary directory has no ``_opam`` above it.
    env = chain.worker_env()
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="pcp-probe-") as tmp:
        if lemma is None:
            file, name, tactic, workspace = Path(tmp) / "PcpProbe.v", PROBE_LEMMA, "exact I.", Path(tmp)
            file.write_text(PROBE_TEXT, encoding="utf-8")
        else:
            (file, name), tactic = lemma, "idtac."
            workspace = chain.project or file.parent
        proc = None
        try:
            proc = PetProcess(workspace, env=env, mode="stdio" if chain.pet else "socket", start_timeout=timeout, call_timeout=timeout)
            proc.spawn()
            state = proc.start(file, name)
            done = proc.run(state, tactic, timeout=min(timeout, 30.0))
            if lemma is None and not done.proof_finished:
                return False, f"`{tactic}` ran but did not close the goal"
        except Exception as exc:  # noqa: BLE001 -- every failure is the report
            tail = proc.stderr_tail().strip() if proc is not None else ""
            detail = f"{type(exc).__name__}: {exc}"
            return False, detail + (f"\n      pet stderr: {tail[-800:]}" if tail else "")
        finally:
            if proc is not None:
                proc.stop()
    where = f"{name} in {file}" if lemma is not None else f"{name} (a temporary file)"
    return True, f"opened {where} and ran `{tactic}` ({time.monotonic() - started:.1f}s)"


def _toolchain_report(chain, *, probe: bool, lemma: tuple[Path, str] | None = None) -> bool:
    """Print the toolchain pcp will actually run, every value read from *its* prefix;
    ``True`` when it is usable.  A component fails only below what pcp needs
    (``PCP_MIN_*``); pcp's exact pins are its tested default, a difference from them
    is information.  The verdict is the live probe: can a lemma be opened here?"""
    from pcp.cli.cmd_setup import check_pins, pins_summary

    where = chain.project or Path.cwd()
    print(f"toolchain in use (for {where})")
    why = {
        penv.COQC: f"${penv.COQC}",
        "project switch": "the project's local opam switch (nearest `_opam` above it)",
        penv.OPAM_SWITCH: f"${penv.OPAM_SWITCH} names this switch",
        "PATH": "first coqc/rocq on PATH",
        "pinned switch": f"pcp's pinned switch `{penv.opam_switch()}` (built by `pcp setup`)",
    }.get(chain.source, chain.source)
    print(f"  {'coqc / rocq':24} {chain.coqc or '— missing'}")
    print(f"  {'  chosen because':24} {why}")
    print(f"  {'  prefix':24} {chain.prefix or '— not an opam switch'}")
    print(f"  {'  Rocq':24} {chain.rocq_version or '?'}" + (f", OCaml {chain.ocaml_version}" if chain.ocaml_version else ""))
    pet = chain.pet or chain.pet_server
    print(f"  {'pet (stdio petanque)':24} {chain.pet or '— missing'}")
    print(f"  {'pet-server (socket)':24} {chain.pet_server or '— missing' + (' (pcp uses stdio pet)' if chain.pet else '')}")
    if pet:
        built = chain.pet_rocq_version
        print(f"  {'  from':24} {chain.pet_source}" + (f" ({chain.pet_prefix})" if chain.pet_prefix and chain.sidecar else ""))
        print(f"  {'  built for':24} Rocq {built or '? (not in an opam switch)'}")
        if chain.sidecar:
            spawned = chain.env()
            print(f"  {'  sidecar env':24} ROCQLIB={spawned.get('ROCQLIB')} (the project's Corelib); "
                  f"OCAMLPATH={spawned.get('OCAMLPATH')}")
    for rejected in chain.rejected_pets:
        print(f"  {'  passed over':24} {rejected}")
    print(f"  {'bwrap (sandbox)':24} {penv.bwrap_binary() or '— missing'}")
    for var in (penv.COQPATH, penv.ROCQPATH):
        print(f"  {var:24} {os.environ.get(var, '— unset')}")
    for entry in chain.ignored_paths:
        print(f"  {'  ignored':24} {entry} (another opam switch's libraries)")
    roots = chain.library_roots()
    print(f"  {'library roots':24} {', '.join(str(r) for r in roots) or '— none'}")

    blocking = chain.blocking()
    where_from = f"read from {chain.prefix}" + (f"; coq-lsp from {chain.pet_prefix}" if chain.sidecar else "")
    print(f"\npackages ({where_from})")
    print(f"  {'':24} installed / pcp needs / pcp's tested default ({pins_summary()})")
    ok = not blocking
    for check in check_pins(chain):
        need = f">= {check.minimum}" if check.minimum else "any"
        if check.meets is False:
            mark = "— TOO OLD"
            blocking.append(f"{check.name} {check.installed} is older than pcp needs ({need})")
            ok = False
        elif check.installed is None:
            mark = "— absent" if check.minimum is None or check.name == "coqc --version" else "— absent (needed only for Iris proofs)"
        else:
            mark = "ok" + ("" if check.ok else "  (differs from the tested default)")
        print(f"  {check.name:24} {check.installed or '—'} / {need} / {check.pinned}  {mark}")

    pinned = penv.switch_prefix()
    print(f"\npinned switch            {penv.opam_switch()} at {pinned or f'{penv.opam_root()} — missing (`pcp setup`)'}"
          + ("" if chain.source == "pinned switch" else "  (not in use here)"))

    if probe and chain.petanque_available and chain.coqc:
        if lemma is None and chain.project is not None:
            lemma = pick_probe_lemma(chain.project)
        ok_probe, detail = probe_petanque(chain, lemma=lemma)
        print(f"\ncan pcp open a lemma here?  {'yes' if ok_probe else '— NO'}: {detail}")
        if not ok_probe:
            blocking.append(f"petanque cannot open a lemma with this toolchain: {detail.splitlines()[0]}")
            ok = False
    elif probe:
        print("\ncan pcp open a lemma here?  — NO: no coqc or no petanque (see problems)")

    if chain.problems() or blocking:
        print("\nproblems")
        for problem in dict.fromkeys([*blocking, *chain.problems()]):
            print(f"  - {problem}")
    return ok


def cmd_doctor(args: argparse.Namespace) -> int:
    from pcp.config.toolchain import resolve
    from pcp.util.assets import check_assets

    start = absolute(getattr(args, "project", None)) or Path.cwd()
    lemma = None
    spec = getattr(args, "lemma", None)
    if spec:
        file, sep, name = str(spec).rpartition(":")
        path = absolute(file) if sep else None
        if path is None or not name or not path.is_file():
            raise UsageError(f"--lemma {spec}: expected FILE:NAME with an existing FILE")
        lemma = (path, name)
        if getattr(args, "project", None) is None:
            start = path
    chain = resolve(start)
    ok = _toolchain_report(chain, probe=getattr(args, "probe", True), lemma=lemma)

    print("\npackaged assets")
    for rel, problem in check_assets():
        print(f"  {rel:24} {'ok' if problem is None else '— ' + problem}")
        if problem is not None:
            ok = False

    print("\nlibraries")
    if importlib.util.find_spec("pytanque") is not None:
        print("  pytanque                 ok")
    else:
        print("  pytanque                 — missing (pip install 'pytanque @ git+https://github.com/LLM4Rocq/pytanque@4092b1238b56468fdc1b3d100e078791c9690fd4')")
    try:
        from pcp.mcp.server import make_mcp

        make_mcp("probe")
        print("  mcp server API           ok")
    except Exception as exc:  # noqa: BLE001 -- report, do not crash the doctor
        print(f"  mcp server API           — unusable ({exc})")

    print("\nmodels by role")
    for line in describe_bindings(_config(args)).splitlines():
        print("  " + line)

    print("\nrunners")
    from pcp.orch.runners.base import RUNNER_NAMES, RunnerSpec, build_runner

    for name in RUNNER_NAMES:
        if name == "mock":
            continue
        try:
            runner = build_runner(RunnerSpec(runner=name))
            mark = "ok" if runner.available() else "— unavailable"
        except Exception as exc:  # noqa: BLE001
            mark = f"— unavailable ({exc})"
        print(f"  {name:24} {mark}")
    print(
        "\nLogin is delegated: run `codex login` or Claude Code's `/login` yourself. "
        "Inside a Claude Code session, `! codex login` runs it without leaving the session."
    )
    if not ok:
        if chain.project_toolchain:
            err(
                f"\nThis project uses its own toolchain ({chain.describe()}). For a missing or mismatched "
                "petanque run `pcp setup --for-project` (a sidecar switch; the project's switch is never "
                "touched; `--dry-run` shows the commands). A missing packaged asset means a broken install: "
                "reinstall proof-copilot."
            )
        else:
            err(
                "\nRun `pcp setup` to build or repair the pinned switch (`pcp setup --dry-run` shows what it "
                'would do). pcp finds the switch itself; `eval "$(pcp env)"` also puts rocq/coqc on your '
                "shell's PATH. A missing packaged asset means a broken install: reinstall proof-copilot."
            )
    return 0 if ok else 1


def cmd_docs(args: argparse.Namespace) -> int:
    from pcp.rocq.library import build_index

    roots = penv.library_roots()
    if not roots:
        raise UsageError("no Rocq library root found; set ROCQPATH")
    out = absolute(args.out) or Path(".pcp/docs/index.txt").resolve()
    n, found = build_index(out, libraries=tuple(args.libraries), roots=roots)
    print(f"{n} declarations from {', '.join(found or args.libraries)} → {out}")
    return 0
