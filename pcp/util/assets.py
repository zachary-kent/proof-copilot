"""The files that ship inside the package, found the same way in a checkout and a wheel.

Everything a run needs besides Python lives under ``pcp/assets/`` and is reached only
through this module (importlib.resources), never through a path relative to the repo:
an installed package has no repo, and a ``repo_root() / "skills"`` style lookup would
silently return nothing there, leaving workers without their norms.  A missing asset
is therefore an error (:class:`MissingAsset`), never an empty default.

* ``skills/*.md`` -- worker norms carried in every packet (docs/ARCHITECTURE.md 8);
* ``coq/IDump.v`` -- the reflected dump (PLAN.md 3.1);
* ``setup-toolchain.sh`` + ``toolchain.env`` -- ``pcp setup`` and the pins it installs,
  which ``pcp doctor`` / ``pcp env`` read too, so the pins exist exactly once.
"""

from __future__ import annotations

import functools
from importlib import resources
from pathlib import Path

from pcp.errors import ToolchainError

PACKAGE = "pcp.assets"
SKILLS_DIR = "skills"
IDUMP = "coq/IDump.v"
SETUP_SCRIPT = "setup-toolchain.sh"
PINS = "toolchain.env"
#: The skill every prover packet carries (``pcp prove``).
PROVER_SKILL = "prover.md"


class MissingAsset(ToolchainError):
    """A packaged file is absent: a broken install, not a user error."""


def asset_path(rel: str) -> Path:
    """The on-disk path of ``pcp/assets/<rel>``; :class:`MissingAsset` if it is absent.

    A path, not a ``Traversable``: ``coqc`` and ``bash`` need a real file.  pcp is never
    installed zipped (setuptools unpacks wheels), so the resource is always a file.
    """
    ref = resources.files(PACKAGE).joinpath(rel)
    path = Path(str(ref))
    if not ref.is_file() or not path.is_file():
        raise MissingAsset(
            f"packaged file pcp/assets/{rel} is missing from this installation ({path}); "
            "reinstall proof-copilot (`uv tool install --force ...`)"
        )
    return path


def read_asset(rel: str) -> str:
    return asset_path(rel).read_text(encoding="utf-8")


def skill_names() -> list[str]:
    """Every packaged skill file name, sorted."""
    root = resources.files(PACKAGE).joinpath(SKILLS_DIR)
    return sorted(e.name for e in root.iterdir() if e.name.endswith(".md")) if root.is_dir() else []


def skill_text(name: str) -> str:
    """The text of ``skills/<name>`` (a file *name*, e.g. ``prover.md``)."""
    if "/" in name or not name.endswith(".md"):
        raise MissingAsset(f"not a skill file name: {name!r}")
    return read_asset(f"{SKILLS_DIR}/{name}")


def idump_path() -> Path:
    return asset_path(IDUMP)


def setup_script() -> Path:
    return asset_path(SETUP_SCRIPT)


def pins_path() -> Path:
    return asset_path(PINS)


@functools.cache
def toolchain_pins() -> dict[str, str]:
    """``toolchain.env`` as a dict (``PCP_ROCQ_VERSION`` -> ``9.1.1``, ...)."""
    out: dict[str, str] = {}
    for raw in read_asset(PINS).splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        key, sep, value = line.partition("=")
        if not sep or not key.strip().isidentifier():
            raise MissingAsset(f"pcp/assets/{PINS}: malformed line {raw!r}")
        out[key.strip()] = value.strip()
    return out


def check_assets() -> list[tuple[str, str | None]]:
    """``(asset, problem-or-None)`` for every required asset -- ``pcp doctor``'s view."""
    required = [f"{SKILLS_DIR}/{PROVER_SKILL}", IDUMP, SETUP_SCRIPT, PINS]
    out: list[tuple[str, str | None]] = []
    for rel in required:
        try:
            asset_path(rel)
            out.append((rel, None))
        except MissingAsset as exc:
            out.append((rel, str(exc)))
    return out
