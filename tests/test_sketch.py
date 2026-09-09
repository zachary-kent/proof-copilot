"""The CSL sketch compiler (PLAN.md 9.3)."""

from __future__ import annotations

from pathlib import Path

from pcp.cli.main import main
from pcp.orch.sketch import compile_sketch
from pcp.rocq.assemble import parse_plan


def test_canary_sketch_compiles_to_a_plan(canary_dir: Path, tmp_path: Path, capsys) -> None:
    sketch = compile_sketch((canary_dir / "counter.sketch").read_text(encoding="utf-8"))
    names = [n for n, _ in sketch.obligations()]
    assert names == ["Icount_alloc", "incr_spec", "incr_seg_load", "incr_seg_cmpxchg", "incr_glue_load_cmpxchg"]
    assert sketch.ghost == [("gamma", "authR natUR")]
    plan = sketch.render_plan()
    specs = parse_plan(plan)
    assert [s.name for s in specs] == names
    assert all(s.body is None for s in specs)
    summary = sketch.render_summary()
    assert "commit point: the CmpXchg that succeeds" in summary
    assert not sketch.warnings

    out = tmp_path / "plan.v"
    assert main(["sketch", str(canary_dir / "counter.sketch"), "--out", str(out)]) == 0
    captured = capsys.readouterr().out
    assert "Lemma Icount_alloc" in plan and f"wrote {out}" in captured


def test_logatom_without_commit_point_warns() -> None:
    sketch = compile_sketch("function pop\n  spec: <<< ∀ x, α x >>> pop #s <<< β, RET v >>>\n")
    assert any("no commit point" in w for w in sketch.warnings)
    assert any("no invariant" in w for w in sketch.warnings)
    assert "! logically atomic spec" in sketch.render_summary()


def test_trailing_comment_does_not_eat_wands() -> None:
    sketch = compile_sketch("invariant I : P -∗ Q -- the wand survives\n  alloc: ⊢ |==> ∃ γ, I γ\n")
    assert sketch.invariants[0].body == "P -∗ Q"
    assert sketch.invariants[0].alloc == "⊢ |==> ∃ γ, I γ"


def test_json_shape(canary_dir: Path) -> None:
    d = compile_sketch((canary_dir / "counter.sketch").read_text(encoding="utf-8")).to_json()
    assert set(d) == {"context", "ghost", "invariants", "functions", "obligations", "warnings"}
    assert d["functions"][0]["segments"][0] == {"name": "load", "assertion": "⌜True⌝"}
