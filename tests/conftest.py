"""Shared fixtures and markers.

Rocq-dependent tests skip cleanly without a toolchain; that is itself a tested property
(``tests/test_layering.py``).  One pet-server is shared by the whole session: a pet with
Iris loaded costs 1-2 GB and ``start`` re-elaborates the file prefix.
"""

from __future__ import annotations

import os
import shutil
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SCRATCH = ROOT / "eval" / "corpus" / "scratch"
CANARY = ROOT / "eval" / "corpus" / "canary"
BENCH = ROOT / "eval" / "corpus" / "bench"
GOLDENS = ROOT / "tests" / "goldens" / "ipm_states.jsonl"


def rocq_available() -> bool:
    return bool(os.environ.get("PCP_COQC") or shutil.which("coqc") or shutil.which("rocq"))


def petanque_available() -> bool:
    return bool(os.environ.get("PCP_PET") or shutil.which("pet") or shutil.which("pet-server"))


def bwrap_available() -> bool:
    return bool(os.environ.get("PCP_BWRAP") or shutil.which("bwrap"))


needs_rocq = pytest.mark.skipif(not rocq_available(), reason="no Rocq toolchain (run ./scripts/setup-toolchain.sh)")
needs_petanque = pytest.mark.skipif(not petanque_available(), reason="no petanque binary")
needs_bwrap = pytest.mark.skipif(not bwrap_available(), reason="no bubblewrap")
needs_goldens = pytest.mark.skipif(not GOLDENS.exists(), reason="no golden corpus (python eval/extract_goldens.py)")


@pytest.fixture(scope="session")
def scratch_dir() -> Path:
    return SCRATCH


@pytest.fixture(scope="session")
def canary_dir() -> Path:
    return CANARY


@pytest.fixture(scope="session")
def bench_dir() -> Path:
    return BENCH


@pytest.fixture(scope="session")
def pool():
    """One shared petanque process for the whole session."""
    if not petanque_available():
        pytest.skip("no petanque binary")
    from pcp.state.pool import SessionPool

    p = SessionPool(SCRATCH, size=1)
    yield p
    p.close()


@pytest.fixture(autouse=True)
def _isolate_cwd(tmp_path, monkeypatch):
    """Tests never write into the repo: every test runs in its own directory."""
    monkeypatch.chdir(tmp_path)
