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

from pcp.config import env as penv

ROOT = Path(__file__).resolve().parents[1]
SCRATCH = ROOT / "eval" / "corpus" / "scratch"
CANARY = ROOT / "eval" / "corpus" / "canary"
BENCH = ROOT / "eval" / "corpus" / "bench"
GOLDENS = ROOT / "tests" / "goldens" / "ipm_states.jsonl"


def rocq_available() -> bool:
    """The lookup pcp itself uses: ``PCP_COQC``, ``PATH``, then the pinned opam switch."""
    return penv.coqc_binary() is not None


def petanque_available() -> bool:
    return penv.petanque_available()


def bwrap_available() -> bool:
    return bool(os.environ.get("PCP_BWRAP") or shutil.which("bwrap"))


#: Markers, not bare skips: ``-m "not rocq and not petanque"`` deselects these tests, and
#: ``pytest_collection_modifyitems`` skips them when the toolchain is missing.
needs_rocq = pytest.mark.rocq
needs_petanque = pytest.mark.petanque
needs_bwrap = pytest.mark.skipif(not bwrap_available(), reason="no bubblewrap")
needs_goldens = pytest.mark.skipif(not GOLDENS.exists(), reason="no golden corpus (python eval/extract_goldens.py)")


@pytest.hookimpl(tryfirst=True)
def pytest_collection_modifyitems(config, items) -> None:
    """Mark every test that needs the shared pet-server (the ``pool`` fixture) as
    ``petanque``, then skip ``rocq``/``petanque`` tests whose toolchain is missing.
    Runs before ``-m`` deselection so the fixture-derived marker is honoured."""
    skips = {
        "rocq": None if rocq_available() else pytest.mark.skip(reason="no Rocq toolchain (run `pcp setup`)"),
        "petanque": None if petanque_available() else pytest.mark.skip(reason="no petanque binary"),
    }
    for item in items:
        if "pool" in getattr(item, "fixturenames", ()) and item.get_closest_marker("petanque") is None:
            item.add_marker(pytest.mark.petanque)
        for name, skip in skips.items():
            if skip is not None and item.get_closest_marker(name) is not None:
                item.add_marker(skip)


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
