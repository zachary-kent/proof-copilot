"""An installed pcp behaves like the checkout: every packaged file is reachable.

The legacy lookups went through the checkout (``repo_root() / "skills"``) and returned
nothing from a wheel -- workers then ran without their norms and nothing said so.  The
fast tests pin the loader and its failure mode; the ``slow`` one builds a real wheel,
installs it non-editable into a fresh venv and loads everything *from site-packages*
(``make install-check``; the ``install`` CI job runs the same thing).
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

from pcp.util import assets
from pcp.util.proc import run

ROOT = Path(__file__).resolve().parents[1]
PACKAGED = ROOT / "pcp" / "assets"

#: What the installed interpreter runs: every asset from the installed package, and
#: the paths it came from, so the test can assert none of it is the checkout.
PROBE = """
import pcp, pcp.util.assets as a
from pcp.cli.cmd_prove import load_skills
from pcp.state.ipm.reflect import idump_source
assert load_skills()[0].strip(), "empty prover skill"
assert set(a.skill_names()) >= {"prover.md", "decomposer.md", "invariants.md", "logatom.md"}, a.skill_names()
assert "iDump" in idump_source().read_text()
assert a.toolchain_pins()["PCP_ROCQ_VERSION"]
assert a.setup_script().is_file()
assert all(problem is None for _, problem in a.check_assets())
print(pcp.__file__)
print(idump_source())
"""


def test_every_packaged_asset_is_reachable_through_the_loader() -> None:
    assert assets.skill_names() == sorted(p.name for p in (PACKAGED / "skills").glob("*.md"))
    assert assets.skill_text("prover.md") == (PACKAGED / "skills" / "prover.md").read_text(encoding="utf-8")
    assert assets.idump_path() == PACKAGED / "coq" / "IDump.v"
    assert assets.setup_script() == PACKAGED / "setup-toolchain.sh"
    assert all(problem is None for _, problem in assets.check_assets())


def test_nothing_is_left_at_the_old_checkout_paths() -> None:
    """One copy of each asset: the packaged one (a stale ``skills/`` would drift)."""
    assert not (ROOT / "skills").exists() and not (ROOT / "coq").exists()
    assert not (ROOT / "scripts" / "setup-toolchain.sh").exists()


def test_a_missing_asset_is_an_error_never_an_empty_default() -> None:
    from pcp.errors import ToolchainError

    with pytest.raises(assets.MissingAsset, match="reinstall"):
        assets.asset_path("skills/nope.md")
    with pytest.raises(ToolchainError):
        assets.skill_text("../toolchain.env")


def test_prover_skill_reaches_every_packet() -> None:
    from pcp.cli.cmd_prove import load_skills

    skills = load_skills()
    assert len(skills) == 1 and skills[0] == assets.skill_text("prover.md") and skills[0].strip()


def test_pins_are_single_sourced_and_the_script_reads_them() -> None:
    pins = assets.toolchain_pins()
    assert {"PCP_DEFAULT_OPAM_SWITCH", "PCP_OCAML_VERSION", "PCP_ROCQ_VERSION", "PCP_IRIS_VERSION", "PCP_STDPP_VERSION"} <= set(pins)
    script = assets.setup_script().read_text(encoding="utf-8")
    assert "toolchain.env" in script
    # No version literal is repeated in the script or the developer env.sh.
    for text in (script, (ROOT / "env.sh").read_text(encoding="utf-8")):
        assert not re.search(r"PCP_\w+_VERSION=\S", text), "a pin was duplicated outside toolchain.env"


def test_setup_dry_run_prints_the_opam_plan_and_changes_nothing(tmp_path: Path) -> None:
    if shutil.which("bash") is None:
        pytest.skip("no bash")
    env = {**os.environ, "PCP_SETUP_DRY_RUN": "1", "PCP_OPAM_SWITCH": "pcp-test-nonexistent", "OPAMROOT": str(tmp_path / "opam")}
    done = run(["bash", str(assets.setup_script())], env=env, timeout=120)
    assert done.ok, done.output
    pins = assets.toolchain_pins()
    assert f"rocq-iris.{pins['PCP_IRIS_VERSION']}" in done.stdout and "would run: opam switch create pcp-test-nonexistent" in done.stdout
    assert "nothing was changed" in done.stdout and not (tmp_path / "opam").exists()


# ---------------------------------------------------------------- a real wheel


@pytest.mark.slow
def test_a_wheel_installed_non_editable_carries_every_asset(tmp_path: Path) -> None:
    uv = shutil.which("uv")
    if uv is None:
        pytest.skip("needs uv to build and install a wheel")
    dist = tmp_path / "dist"
    # sdist first, then the wheel from the sdist: what `uv tool install git+...` does, and
    # it proves the sdist carries the assets too.  Never the checkout's stale build/.
    built = subprocess.run([uv, "build", "--out-dir", str(dist), str(ROOT)], capture_output=True, text=True, check=False)
    assert built.returncode == 0, built.stderr[-3000:]
    wheel = next(dist.glob("*.whl"))
    venv = tmp_path / "venv"
    assert subprocess.run([uv, "venv", "--python", sys.executable, str(venv)], capture_output=True, check=False).returncode == 0
    python = venv / "bin" / "python"
    # --no-deps: the probe needs nothing beyond the package (pytanque is a git dep).
    inst = subprocess.run([uv, "pip", "install", "--python", str(python), "--no-deps", str(wheel)], capture_output=True, text=True, check=False)
    assert inst.returncode == 0, inst.stderr[-3000:]
    elsewhere = tmp_path / "elsewhere"  # not the checkout: nothing may resolve through cwd
    elsewhere.mkdir()
    probe = subprocess.run([str(python), "-c", PROBE], cwd=str(elsewhere), capture_output=True, text=True, check=False,
                           env={k: v for k, v in os.environ.items() if k != "PYTHONPATH"})
    assert probe.returncode == 0, probe.stderr[-3000:]
    package_file, idump = probe.stdout.split()
    assert str(venv) in package_file and str(ROOT) not in package_file, package_file
    assert str(venv) in idump and "site-packages" in idump
    pcp = venv / "bin" / "pcp"
    version = subprocess.run([str(pcp), "--version"], cwd=str(elsewhere), capture_output=True, text=True, check=False)
    assert version.returncode == 0 and version.stdout.startswith("pcp "), version.stderr
    init = subprocess.run([str(pcp), "init"], cwd=str(elsewhere), capture_output=True, text=True, check=False)
    assert init.returncode == 0 and (elsewhere / ".pcp" / "config.toml").exists(), init.stderr
