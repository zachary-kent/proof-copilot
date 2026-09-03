from __future__ import annotations

import os
import shutil
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SCRATCH = ROOT / "eval" / "corpus" / "scratch"
CANARY = ROOT / "eval" / "corpus" / "canary"


def _rocq_available() -> bool:
    return bool(os.environ.get("PCP_COQC") or shutil.which("coqc") or shutil.which("rocq"))


def _petanque_available() -> bool:
    return bool(os.environ.get("PCP_PET") or shutil.which("pet") or shutil.which("pet-server"))


needs_rocq = pytest.mark.skipif(not _rocq_available(), reason="no Rocq toolchain (run ./scripts/setup-toolchain.sh)")
needs_petanque = pytest.mark.skipif(not _petanque_available(), reason="no petanque binary")


@pytest.fixture(scope="session")
def scratch_dir() -> Path:
    return SCRATCH


@pytest.fixture(scope="session")
def canary_dir() -> Path:
    return CANARY


@pytest.fixture(scope="session")
def pool():
    """One shared pet-server for the whole session.

    Deliberately shared: a pet-server with Iris loaded costs 1-2 GB and `start`
    re-elaborates the file prefix, so a fixture per test would make the suite
    unusable.  This mirrors how the real session pool is meant to be used.
    """
    from pcp.core.session import SessionPool

    p = SessionPool(SCRATCH, size=1)
    yield p
    p.close()
