"""The toolchain resolver (pcp.config.toolchain) and what reads it: ``pcp doctor``,
``pcp setup --for-project``, ``pcp env`` and the environment workers get.

Fake opam switches (a ``bin/`` and ``.opam-switch/packages/<name>.<version>/``) stand
in for real ones, so these run anywhere; the live checks at the end are marked.
"""

from __future__ import annotations

import argparse
import os
import shutil
from pathlib import Path

import pytest

from pcp.config import env as penv
from pcp.config import toolchain as tc
from pcp.errors import UsageError
from tests.conftest import needs_petanque

ROCQ_VARS = (penv.COQC, penv.PET, penv.PET_SERVER, penv.OPAM_SWITCH, penv.ROCQPATH, penv.COQPATH, "ROCQLIB", "OCAMLPATH")


def fake_switch(prefix: Path, packages: dict[str, str], binaries: tuple[str, ...] = ("coqc", "pet")) -> Path:
    """An opam prefix with ``binaries`` (a ``coqc`` that prints its Rocq version) and
    opam's package bookkeeping for ``packages``."""
    (prefix / "bin").mkdir(parents=True)
    (prefix / "lib" / "coq" / "user-contrib").mkdir(parents=True)
    for name, version in packages.items():
        (prefix / ".opam-switch" / "packages" / f"{name}.{version}").mkdir(parents=True)
    rocq = packages.get("rocq-core", "?")
    for b in binaries:
        exe = prefix / "bin" / b
        exe.write_text(f"#!/bin/sh\necho 'The Rocq Prover, version {rocq}'\n")
        exe.chmod(0o755)
    return prefix


ROCQ_92 = {"rocq-core": "9.2.0", "rocq-runtime": "9.2.0", "ocaml-base-compiler": "4.14.2", "rocq-stdlib": "9.2.0",
           "rocq-stdpp": "dev.2026-07-16.0.dec47225", "rocq-iris": "dev.2026-07-19.0.5b67fadf",
           "rocq-iris-heap-lang": "dev.2026-07-19.0.5b67fadf"}
ROCQ_911 = {"rocq-core": "9.1.1", "ocaml-base-compiler": "5.2.1", "rocq-stdlib": "9.1.0", "coq-lsp": "0.2.5+9.1",
            "rocq-stdpp": "1.13.0", "rocq-iris": "4.5.0", "rocq-iris-heap-lang": "4.5.0"}


@pytest.fixture
def machine(tmp_path: Path, monkeypatch):
    """A clean machine: an opam root holding pcp's pinned switch (Rocq 9.1.1), an empty
    PATH, none of the toolchain variables set, and a project with a ``_CoqProject``."""
    for var in ROCQ_VARS:
        monkeypatch.delenv(var, raising=False)
    root = tmp_path / "opam"
    monkeypatch.setenv("OPAMROOT", str(root))
    empty = tmp_path / "empty-path"
    empty.mkdir()
    monkeypatch.setenv("PATH", f"{empty}{os.pathsep}/usr/bin{os.pathsep}/bin")
    if shutil.which("coqc", path=os.environ["PATH"]) or shutil.which("pet", path=os.environ["PATH"]):
        pytest.skip("a coqc/pet in /usr/bin would shadow the fake switches")
    pinned = fake_switch(root / "pcp", ROCQ_911)
    project = tmp_path / "proj"
    (project / "theories" / "sub").mkdir(parents=True)
    (project / "_CoqProject").write_text("-Q theories proj\n")
    return argparse.Namespace(root=root, pinned=pinned, project=project, empty=empty, tmp=tmp_path)


# ---------------------------------------------------------------- resolution order


def test_resolution_order_explicit_then_local_then_named_then_path_then_pinned(machine, monkeypatch) -> None:
    start = machine.project / "theories" / "sub"
    assert tc.resolve(start).source == "pinned switch"

    onpath = fake_switch(machine.tmp / "onpath", {"rocq-core": "9.0.0"}, ("coqc",))
    monkeypatch.setenv("PATH", f"{onpath / 'bin'}{os.pathsep}{os.environ['PATH']}")
    assert tc.resolve(start).source == "PATH"

    monkeypatch.setenv(penv.OPAM_SWITCH, "pcp")  # the default name (env.sh exports it): no signal
    assert tc.resolve(start).source == "PATH"
    named = fake_switch(machine.root / "other", {"rocq-core": "8.20.0"}, ("coqc",))
    monkeypatch.setenv(penv.OPAM_SWITCH, "other")
    chain = tc.resolve(start)
    assert (chain.source, chain.prefix) == (penv.OPAM_SWITCH, named)

    local = fake_switch(machine.project / "_opam", ROCQ_92)
    chain = tc.resolve(start / "Foo.v")
    assert (chain.source, chain.prefix, chain.rocq_version) == ("project switch", local, "9.2.0")
    assert chain.project == machine.project and chain.project_toolchain

    explicit = fake_switch(machine.tmp / "explicit", {"rocq-core": "9.1.0"}, ("coqc",))
    monkeypatch.setenv(penv.COQC, str(explicit / "bin" / "coqc"))
    chain = tc.resolve(start)
    assert (chain.source, chain.prefix, chain.rocq_version) == (penv.COQC, explicit, "9.1.0")


# ---------------------------------------------------------------- which pet


def test_pet_comes_from_the_compilers_own_switch_first(machine) -> None:
    local = fake_switch(machine.project / "_opam", ROCQ_92)
    chain = tc.resolve(machine.project)
    assert chain.pet == str(local / "bin" / "pet") and chain.pet_source == "same switch as coqc"
    assert not chain.sidecar and chain.blocking() == []


def test_a_sidecar_pet_is_used_when_the_project_switch_has_none(machine) -> None:
    local = fake_switch(machine.project / "_opam", ROCQ_92, ("coqc",))
    side = fake_switch(machine.root / tc.sidecar_switch_name("9.2.0"), {"rocq-core": "9.2.0", "coq-lsp": "0.2.5+9.1"}, ("pet",))
    chain = tc.resolve(machine.project)
    assert chain.pet == str(side / "bin" / "pet") and chain.sidecar
    assert chain.pet_source == "sidecar switch pcp-pet-rocq-9.2.0" and chain.pet_rocq_version == "9.2.0"
    assert chain.prefixes() == [local, side]
    env = chain.env({"PATH": "/usr/bin"})
    assert env["ROCQLIB"] == str(local / "lib" / "coq"), "a sidecar pet loads the project's Corelib"
    assert env["OCAMLPATH"].split(os.pathsep)[:2] == [str(side / "lib"), str(local / "lib")]


def test_rocqlib_is_set_only_for_a_sidecar(machine) -> None:
    fake_switch(machine.project / "_opam", ROCQ_92)
    env = tc.resolve(machine.project).env({"PATH": "/usr/bin"})
    assert "ROCQLIB" not in env and "OCAMLPATH" not in env


def test_a_pet_on_path_built_for_another_rocq_is_passed_over(machine, monkeypatch) -> None:
    """The project has Rocq 9.2 and no pet; the only pets are 9.1 builds (PATH, pinned)."""
    fake_switch(machine.project / "_opam", ROCQ_92, ("coqc",))
    other = fake_switch(machine.tmp / "other91", {"rocq-core": "9.1.1"}, ("pet",))
    monkeypatch.setenv("PATH", f"{other / 'bin'}{os.pathsep}{os.environ['PATH']}")
    chain = tc.resolve(machine.project)
    assert chain.pet is None and not chain.petanque_available
    assert any(str(other / "bin" / "pet") in r and "9.1.1" in r for r in chain.rejected_pets)
    assert any("pinned switch" in r for r in chain.rejected_pets)
    [problem] = chain.blocking()
    assert "no petanque" in problem and "pcp setup --for-project" in problem

    same = fake_switch(machine.tmp / "same92", {"rocq-core": "9.2.0"}, ("pet",))
    monkeypatch.setenv("PATH", f"{same / 'bin'}{os.pathsep}{os.environ['PATH']}")
    assert tc.resolve(machine.project).pet == str(same / "bin" / "pet"), "a PATH pet for the same Rocq is fine"


def test_an_explicit_pet_for_another_rocq_is_a_blocking_problem(machine, monkeypatch) -> None:
    fake_switch(machine.project / "_opam", ROCQ_92, ("coqc",))
    monkeypatch.setenv(penv.PET, str(machine.pinned / "bin" / "pet"))
    chain = tc.resolve(machine.project)
    assert chain.pet_source == penv.PET
    assert any("built for Rocq 9.1.1 but coqc is Rocq 9.2.0" in p for p in chain.blocking())


# ---------------------------------------------------------------- library paths


def test_foreign_rocqpath_entries_are_dropped_from_env_and_library_roots(machine, monkeypatch) -> None:
    local = fake_switch(machine.project / "_opam", ROCQ_92)
    mine = machine.tmp / "my-lib"
    mine.mkdir()
    foreign = machine.pinned / "lib" / "coq" / "user-contrib"
    monkeypatch.setenv(penv.ROCQPATH, f"{foreign}{os.pathsep}{mine}")
    monkeypatch.setenv(penv.COQPATH, str(foreign))
    chain = tc.resolve(machine.project)
    assert chain.ignored_paths == (foreign,)
    assert chain.library_roots() == [mine, local / "lib" / "coq" / "user-contrib"]
    env = chain.env()
    assert env[penv.ROCQPATH] == str(mine) and penv.COQPATH not in env
    assert env["PATH"].split(os.pathsep)[0] == str(local / "bin")
    assert chain.blocking() == [] and any("ignoring" in p for p in chain.problems())


# ---------------------------------------------------------------- discovery


def test_a_dune_project_using_rocq_is_a_project_root(tmp_path: Path) -> None:
    (tmp_path / "a" / "theories").mkdir(parents=True)
    (tmp_path / "a" / "dune-project").write_text("(lang dune 3.8)\n(using rocq 0.11)\n")
    (tmp_path / "b" / "src").mkdir(parents=True)
    (tmp_path / "b" / "dune-project").write_text("(lang dune 3.8)\n(name ocaml_only)\n")
    assert tc.project_root(tmp_path / "a" / "theories" / "X.v") == tmp_path / "a"
    assert tc.project_file(tmp_path / "a" / "theories") == tmp_path / "a" / "dune-project"
    assert tc.project_root(tmp_path / "b" / "src") is None, "a dune project without rocq/coq is not one"
    (tmp_path / "a" / "_CoqProject").write_text("-Q theories a\n")
    assert tc.project_file(tmp_path / "a") == tmp_path / "a" / "_CoqProject", "the -Q flags live there"


def test_version_floors_ignore_suffixes_and_rank_dev_newest() -> None:
    assert tc.meets_minimum("9.2.0", "9.0") and not tc.meets_minimum("8.20.1", "9.0")
    assert tc.meets_minimum("0.2.5+9.1", "0.2.5") and not tc.meets_minimum("0.2.4+9.0", "0.2.5")
    assert tc.meets_minimum("dev.2026-07-19.0.5b67fadf", "4.3.0") and not tc.meets_minimum("4.2.0", "4.3.0")
    assert tc.meets_minimum(None, "1.0") is None


# ---------------------------------------------------------------- pcp doctor (issue 2)


def test_doctor_reads_the_packages_of_the_toolchain_in_use_not_the_pinned_switch(machine, capsys) -> None:
    """Regression: doctor printed `rocq-iris 4.5.0 ok` from the pinned switch while the
    project's own Iris dev was what loaded."""
    from pcp.cli.cmd_doctor import _toolchain_report

    fake_switch(machine.project / "_opam", {**ROCQ_92, "coq-lsp": "0.2.5+9.1"})
    ok = _toolchain_report(tc.resolve(machine.project), probe=False)
    out = capsys.readouterr().out
    assert ok, "differences from the tested pins are informational for a project toolchain"
    iris = next(line for line in out.splitlines() if line.strip().startswith("rocq-iris "))
    assert "dev.2026-07-19" in iris and "ok" in iris
    assert f"read from {machine.project / '_opam'}" in out
    assert "project's local opam switch" in out and "Rocq                   9.2.0" in out
    assert "MISMATCH" not in out


def test_doctor_fails_below_what_pcp_needs_and_without_petanque(machine, capsys) -> None:
    from pcp.cli.cmd_doctor import _toolchain_report

    fake_switch(machine.project / "_opam", {**ROCQ_92, "rocq-iris": "4.1.0"}, ("coqc",))
    assert not _toolchain_report(tc.resolve(machine.project), probe=False)
    out = capsys.readouterr().out
    assert "TOO OLD" in out and "no petanque" in out and "passed over" in out


def test_doctor_explains_a_sidecar(machine, capsys) -> None:
    from pcp.cli.cmd_doctor import _toolchain_report

    local = fake_switch(machine.project / "_opam", ROCQ_92, ("coqc",))
    side = fake_switch(machine.root / "pcp-pet-rocq-9.2.0", {"rocq-core": "9.2.0", "coq-lsp": "0.2.5+9.2"}, ("pet",))
    assert _toolchain_report(tc.resolve(machine.project), probe=False)
    out = capsys.readouterr().out
    assert "sidecar switch pcp-pet-rocq-9.2.0" in out and f"ROCQLIB={local / 'lib' / 'coq'}" in out
    assert "0.2.5+9.2" in out and f"coq-lsp from {side}" in out, "coq-lsp is read from the pet's switch"


def test_doctor_lemma_picker_prefers_a_small_built_file(tmp_path: Path) -> None:
    from pcp.cli.cmd_doctor import first_lemma, pick_probe_lemma

    big = tmp_path / "theories" / "Big.v"
    big.parent.mkdir(parents=True)
    big.write_text("(* a comment *)\nLemma big_one : True.\nProof. exact I. Qed.\n" + "(* pad *)\n" * 50)
    big.with_suffix(".vo").write_text("")
    small = tmp_path / "theories" / "Small.v"
    small.write_text("Theorem small : True.\nProof. exact I. Qed.\n")  # smaller, but not built
    (tmp_path / "_opam" / "lib").mkdir(parents=True)
    (tmp_path / "_opam" / "lib" / "Tiny.v").write_text("Lemma tiny : True. Admitted.\n")
    (tmp_path / "theories" / "Big__pcpfast.v").write_text("Lemma twin : True. Admitted.\n")
    assert pick_probe_lemma(tmp_path) == (big, "big_one")
    assert first_lemma(small) == "small"
    (tmp_path / "theories" / "Defs.v").write_text("#[local] Definition x := 1.\n#[global] Lemma  attr_lemma' {A} : True.\n")
    assert first_lemma(tmp_path / "theories" / "Defs.v") == "attr_lemma'"


# ---------------------------------------------------------------- pcp setup --for-project (issue 3)


def _setup_args(**kw) -> argparse.Namespace:
    base = dict(dry_run=True, force=False, jobs=4, switch=None, for_project=None)
    base.update(kw)
    return argparse.Namespace(**base)


@pytest.mark.skipif(shutil.which("bash") is None, reason="needs bash")
def test_setup_for_project_dry_run_never_names_the_project_switch(machine, capsys, monkeypatch) -> None:
    from pcp.cli.cmd_setup import cmd_setup

    local = fake_switch(machine.project / "_opam", ROCQ_92, ("coqc",))
    monkeypatch.setenv("OPAMSWITCH", str(machine.project))  # a shell that ran `opam env` in the project
    monkeypatch.chdir(machine.project)
    assert cmd_setup(_setup_args(for_project=Path("."))) == 0
    out = capsys.readouterr().out
    commands = [ln for ln in out.splitlines() if "opam " in ln and ("would" in ln or "then:" in ln)]
    assert commands and "would run: opam switch create pcp-pet-rocq-9.2.0 ocaml-base-compiler.4.14.2" in out
    for line in commands:
        assert str(machine.project) not in line and str(local) not in line and "_opam" not in line, line
        assert "--all-switches" not in line and "--this-switch" not in line, line
        if "--switch" in line:
            assert "--switch=pcp-pet-rocq-9.2.0" in line, line
    assert "opam pin add --switch=pcp-pet-rocq-9.2.0 -n -y rocq-core 9.2.0" in out
    assert "opam pin add --switch=pcp-pet-rocq-9.2.0 -n -y rocq-runtime 9.2.0" in out
    # Every coq-lsp request names the exact core packages, so the solver cannot swap Rocq out.
    for line in (ln for ln in commands if "coq-lsp" in ln and "install" in ln):
        assert "rocq-core.9.2.0" in line and "rocq-runtime.9.2.0" in line, line
    assert "coq-lsp git+https://github.com/ejgallego/coq-lsp#v9.2" in out
    assert "nothing was changed" in out and not (machine.root / "pcp-pet-rocq-9.2.0").exists()


def test_setup_for_project_refuses_outside_a_project_toolchain(machine) -> None:
    from pcp.cli.cmd_setup import sidecar_plan

    with pytest.raises(UsageError, match="no project toolchain"):
        sidecar_plan(machine.project)  # no _opam: pcp would use its pinned switch


def test_sidecar_plan_takes_versions_from_the_project_switch(machine) -> None:
    from pcp.cli.cmd_setup import sidecar_plan

    fake_switch(machine.project / "_opam", ROCQ_92, ("coqc",))
    plan = sidecar_plan(machine.project / "theories")
    assert (plan.switch, plan.ocaml, plan.core) == ("pcp-pet-rocq-9.2.0", "4.14.2", ("rocq-runtime.9.2.0", "rocq-core.9.2.0"))
    env = plan.environment(dry_run=True, jobs=None)
    assert "OPAMSWITCH" not in env and env["PCP_SIDECAR_COQLSP_GIT"].endswith("#v9.2")
    assert not any(str(machine.project) in v for k, v in env.items() if k.startswith("PCP_SIDECAR"))


# ---------------------------------------------------------------- pcp env


def test_env_exports_the_project_switch_inside_a_project(machine, monkeypatch) -> None:
    from pcp.cli.cmd_setup import env_exports

    monkeypatch.setenv("PATH", str(machine.empty))  # no opam: the computed essentials
    local = fake_switch(machine.project / "_opam", ROCQ_92)
    lines = env_exports(start=machine.project / "theories")
    assert lines[0].startswith("# project toolchain: Rocq 9.2.0")
    text = "\n".join(lines)
    assert f"PATH={local / 'bin'}" in text and f"ROCQPATH={local / 'lib' / 'coq' / 'user-contrib'}" in text
    assert "PCP_OPAM_SWITCH" not in text, "the local switch is found without it"
    shutil.rmtree(local)
    lines = env_exports(start=machine.project)
    assert lines[0].startswith("# no project-local _opam") and any(str(machine.pinned) in ln for ln in lines)


# ---------------------------------------------------------------- workers


def test_workers_get_the_toolchain_pinned(machine, monkeypatch) -> None:
    """A worker's cwd is a scratch packet: without the exports it would re-resolve
    pcp's pinned 9.1 switch instead of the project's 9.2 ``_opam``."""
    local = fake_switch(machine.project / "_opam", ROCQ_92)
    chain = tc.resolve(machine.project)
    monkeypatch.setenv(penv.ROCQPATH, str(machine.pinned / "lib" / "coq" / "user-contrib"))
    env = penv.with_runner_defaults(toolchain=chain)
    assert env[penv.COQC] == str(local / "bin" / "coqc") and env[penv.PET] == str(local / "bin" / "pet")
    assert penv.ROCQPATH not in env
    packet = machine.tmp / "packet"
    packet.mkdir()
    again = tc.resolve(packet, environ=env)
    assert (again.prefix, again.pet, again.rocq_version) == (local, chain.pet, "9.2.0")
    assert tc.resolve(packet).prefix == machine.pinned, "what the worker would get without the pin"


def test_toolchain_for_resolves_the_development_file(machine) -> None:
    from pcp.cli.runners import toolchain_for

    local = fake_switch(machine.project / "_opam", ROCQ_92)
    dev = machine.project / "theories" / "sub" / "Dev.v"
    dev.write_text("")
    assert toolchain_for(argparse.Namespace(file=str(dev))).prefix == local
    assert toolchain_for(argparse.Namespace(), machine.project).prefix == local


def test_petanque_process_resolves_from_the_environment_it_is_given(machine) -> None:
    from pcp.state.petanque import PetProcess

    local = fake_switch(machine.project / "_opam", ROCQ_92)
    elsewhere = machine.tmp / "elsewhere"
    elsewhere.mkdir()
    proc = PetProcess(elsewhere, env={**os.environ, **tc.resolve(machine.project).exports()}, mode="stdio")
    assert proc.toolchain.prefix == local and proc.toolchain.pet == str(local / "bin" / "pet")


# ---------------------------------------------------------------- live


@needs_petanque
def test_live_probe_opens_a_trivial_lemma_with_the_resolved_toolchain(tmp_path: Path) -> None:
    from pcp.cli.cmd_doctor import probe_petanque

    ok, detail = probe_petanque(tc.resolve(tmp_path))
    assert ok, detail
    assert "exact I." in detail


@needs_petanque
def test_live_probe_reports_petanques_error_text(tmp_path: Path) -> None:
    from pcp.cli.cmd_doctor import probe_petanque

    bad = tmp_path / "Bad.v"
    bad.write_text("Lemma bad : True.\nProof. exact I. Qed.\n")
    ok, detail = probe_petanque(tc.resolve(tmp_path), lemma=(bad, "not_there"))
    assert not ok and "not_there" in detail
