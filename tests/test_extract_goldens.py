"""``eval/extract_goldens.py`` stays runnable: one file, one lemma, real petanque."""

from __future__ import annotations

import importlib.util
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest
from conftest import ROOT, SCRATCH, needs_petanque

SCRIPT = ROOT / "eval" / "extract_goldens.py"


def _module():
    spec = importlib.util.spec_from_file_location("extract_goldens", SCRIPT)
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_file_selection_is_seeded_and_sharded(tmp_path: Path) -> None:
    mod = _module()
    for i in range(6):
        (tmp_path / f"f{i}.v").write_text("", encoding="utf-8")
    assert mod.parse_shard("1/3") == (1, 3)
    with pytest.raises(SystemExit):
        mod.parse_shard("3/3")
    a = mod.select_files(tmp_path, "*.v", seed=0, shard=(0, 1), limit=6)
    assert sorted(a) == sorted(tmp_path.glob("*.v")) and a == mod.select_files(tmp_path, "*.v", seed=0, shard=(0, 1), limit=6)
    shards = [mod.select_files(tmp_path, "*.v", seed=0, shard=(i, 2), limit=6) for i in range(2)]
    assert sorted(shards[0] + shards[1]) == sorted(a) and not set(shards[0]) & set(shards[1])
    blocks = mod.proof_blocks((SCRATCH / "Basic.v").read_text(encoding="utf-8"))
    assert {b.name for b in blocks} >= {"sep_comm", "exists_pure", "inv_open"}
    assert all(b.ender == "Qed" for b in blocks)
    # Comments never fuse with a bullet or a tactic: the lexer hands over sentences.
    assert all("(*" not in t for b in blocks for t in b.tactics())


@needs_petanque
def test_extract_one_file_one_lemma_writes_golden_rows(tmp_path: Path) -> None:
    ws = tmp_path / "ws"
    ws.mkdir()
    for name in ("Basic.v", "Blame.v", "_CoqProject"):
        shutil.copy(SCRATCH / name, ws / name)
    out = tmp_path / "x.jsonl"
    proc = subprocess.run(
        [sys.executable, str(SCRIPT), "--root", str(ws), "--pattern", "*.v", "--limit-files", "1",
         "--limit-lemmas", "1", "--limit-steps", "3", "--out", str(out)],
        capture_output=True, text=True, timeout=600, env=dict(os.environ), check=False,
    )
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout.startswith("wrote ") and "from 1 lemmas" in proc.stdout
    rows = [json.loads(line) for line in out.read_text(encoding="utf-8").splitlines()]
    assert rows and rows[0]["step"] == 0 and rows[0]["tactic"] == "<start>"
    assert set(rows[0]) == {"file", "thm", "step", "tactic", "goal_index", "ty", "hyps"}
    assert rows[0]["file"] in ("Basic.v", "Blame.v") and rows[0]["goal_index"] == 0
    assert all(isinstance(r["ty"], str) and r["ty"] for r in rows)
    assert all(set(h) == {"names", "ty"} for r in rows for h in r["hyps"])
    assert max(r["step"] for r in rows) <= 3 and not out.with_name(out.name + ".partial").exists()
    assert not (SCRATCH / "Basic__pcpfast.v").exists()
