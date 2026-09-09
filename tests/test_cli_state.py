"""``pcp trace`` / ``state`` / ``ledger`` / ``destruct`` (contract 1.7-1.10).

``destruct`` and the trace readers are exercised offline on a synthetic trace; the
petanque-backed tests run ``pcp trace`` on the scratch corpus (no ``--fast`` twin is
written, so the fixture directory stays clean) and read the JSONL back.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

from conftest import SCRATCH, needs_petanque, needs_rocq

from pcp.cli.cmd_trace import TraceRun, script_tactics
from pcp.cli.main import main
from pcp.state.ipm.model import Hyp, IrisGoal, Step
from pcp.state.ledger.events import Event
from pcp.state.trace import Trace

BASIC = SCRATCH / "Basic.v"
BLAME = SCRATCH / "Blame.v"


# ------------------------------------------------------------------- destruct


def test_destruct_synthesises_the_pattern_and_shows_the_skeleton(capsys) -> None:
    assert main(["destruct", "∃ γ, own γ (◯ n) ∗ ⌜n = 3⌝"]) == 0
    out = capsys.readouterr().out
    assert 'iDestruct "H" as (γ) "[H1 %H2]"' in out and "\nprop skeleton:\n" in out and "exists γ" in out
    assert main(["destruct", "P ∗ Q", "--name", "Hx"]) == 0
    assert 'iDestruct "Hx" as "[Hx1 Hx2]".' in capsys.readouterr().out


def test_destruct_pattern_mismatch_exits_1_with_a_fitting_pattern(capsys) -> None:
    assert main(["destruct", "P ∗ Q", "--pattern", "[H1|H2]"]) == 1
    out = capsys.readouterr().out
    assert "disjunction" in out and "a pattern that fits: [H1 H2]" in out
    assert main(["destruct", "P ∗ Q", "--pattern", "[H1 H2]"]) == 0
    assert "pattern aligns" in capsys.readouterr().out
    assert main(["destruct", "P ∗ Q", "--pattern", "[H1"]) == 2
    assert "does not parse" in capsys.readouterr().err


# ---------------------------------------------------------------- readers, offline


def _synthetic_trace(path: Path, *, failed: bool = False) -> Path:
    hp, hq = Hyp(id="HP", prop="P"), Hyp(id="HQ", prop="Q")
    trace = Trace(file="x.v", thm="t")
    trace.steps.append(Step(step=0, state_id=1, tactic="<start>", goals=[IrisGoal(goal_id="g0", goal="P ∗ Q -∗ P")]))
    trace.steps.append(Step(step=1, state_id=2, tactic='iIntros "[HP HQ]".', goals=[IrisGoal(goal_id="g0", spatial=[hp, hq], goal="P")]))
    trace.events.append(Event(step=1, kind="Intro", tactic='iIntros "[HP HQ]".', hyp="HP", targets=["HP"]))
    trace.events.append(Event(step=1, kind="Intro", tactic='iIntros "[HP HQ]".', hyp="HQ", targets=["HQ"]))
    if failed:
        trace.steps.append(Step(step=2, state_id=-1, tactic="done.", ok=False, error="Coq: no", goals=[IrisGoal(goal_id="g0", spatial=[hp, hq], goal="P")]))
        trace.failed_at, trace.error = 2, "Coq: no"
    for s in trace.steps:
        trace.store.update(s.goals)
    return trace.to_jsonl(path)


def test_state_renders_diff_only_by_default_and_all_on_request(tmp_path: Path, capsys) -> None:
    t = _synthetic_trace(tmp_path / "t.jsonl")
    assert main(["state", str(t)]) == 0
    out = capsys.readouterr().out
    assert out.startswith("goal g0") and '"HP" : P' in out and "rendered 2/2" in out  # both new at step 1
    assert main(["state", str(t), "--step", "0"]) == 0
    assert "⊢ P ∗ Q -∗ P" in capsys.readouterr().out
    assert main(["state", str(t), "--all", "--select", "HQ", "--mode", "hash-only"]) == 0
    out = capsys.readouterr().out
    assert '"HQ"' in out and '"HP" : P' not in out and "not shown: HP" in out
    assert main(["state", str(t), "--step", "9"]) == 2
    assert "no goals at that step" in capsys.readouterr().err
    assert main(["state", str(tmp_path / "missing.jsonl")]) == 2


def test_ledger_queries_read_the_trace_back(tmp_path: Path, capsys) -> None:
    t = _synthetic_trace(tmp_path / "t.jsonl", failed=True)
    assert main(["ledger", str(t), "events"]) == 0
    assert 'step 1 · Intro · "HP"' in capsys.readouterr().out
    assert main(["ledger", str(t), "where"]) == 2 and "--hyp is required" in capsys.readouterr().err
    assert main(["ledger", str(t), "where", "--hyp", "HP"]) == 0
    assert "HP" in capsys.readouterr().out
    assert main(["ledger", str(t), "blame", "--hyp", "HP"]) == 0
    out = capsys.readouterr().out
    assert "not available at step 2?" in out and "repair class:" in out  # the failed step, not len(steps)
    assert main(["ledger", str(t), "leftovers"]) == 0
    assert capsys.readouterr().out.splitlines() == ['  "HP" : P', '  "HQ" : Q']
    assert main(["ledger", str(t), "unused"]) == 0
    assert capsys.readouterr().out.strip() in ("every resource was consumed", '"HP", "HQ"')


def test_script_tactics_lexes_wrapped_tactics_and_drops_comments() -> None:
    text = '(* a comment line *)\niDestruct "H" as (x)\n  "[H1 H2]".\n- iFrame. (* trailing *)\n'
    assert script_tactics(text) == ['iDestruct "H" as (x)\n  "[H1 H2]".', "-", "iFrame."]


def test_trace_without_a_proof_is_a_usage_error(capsys) -> None:
    assert main(["trace", str(BASIC), "no_such_lemma"]) == 2
    assert "no_such_lemma has no proof to trace; pass --script" in capsys.readouterr().err
    assert main(["trace", "missing.v", "x"]) == 2


# ---------------------------------------------------------------------- live


def _rows(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


@needs_petanque
def test_trace_writes_jsonl_and_state_and_ledger_read_it_back(tmp_path: Path, capsys) -> None:
    out = tmp_path / "exists_pure.jsonl"
    assert main(["trace", str(BASIC), "exists_pure", "-o", str(out)]) == 0
    captured = capsys.readouterr()
    m = re.match(r"(\d+) steps, (\d+) ledger events → (.*)", captured.out)
    assert m and m.group(3) == str(out) and "stopped at" not in captured.err
    rows = _rows(out)
    assert rows[0]["rec"] == "header" and rows[0]["finished"] is True and rows[0]["failed_at"] is None
    steps = [r for r in rows if r["rec"] == "step"]
    events = [r for r in rows if r["rec"] == "event"]
    assert [s["tactic"] for s in steps][:2] == ["<start>", 'iIntros "H".'] and len(steps) == int(m.group(1))
    assert len(events) == int(m.group(2)) > 0 and {e["hyp"] for e in events if e["kind"] == "Intro"} >= {"H"}
    assert not (SCRATCH / "Basic__pcpfast.v").exists()

    assert main(["state", str(out), "--step", "2"]) == 0
    text = capsys.readouterr().out
    assert text.startswith("goal g0") and "rendered" in text
    assert main(["state", str(out), "--step", "2", "--select", "HΦ"]) == 0
    assert '"HΦ"' in capsys.readouterr().out
    assert main(["ledger", str(out), "leftovers"]) == 0
    assert capsys.readouterr().out.strip() == "the spatial context is empty"
    assert main(["ledger", str(out), "blame", "--hyp", "H"]) == 0
    blamed = capsys.readouterr().out
    assert "repair class:" in blamed and "step 2" in blamed
    assert main(["ledger", str(out), "unused"]) == 0
    assert capsys.readouterr().out.strip() == "every resource was consumed"
    assert main(["ledger", str(out), "where", "--hyp", "H"]) == 0
    assert '"H"' in capsys.readouterr().out
    assert main(["ledger", str(out), "events"]) == 0
    assert "step 1 · Intro" in capsys.readouterr().out


@needs_petanque
def test_trace_default_output_and_a_script_that_stops(tmp_path: Path, capsys) -> None:
    script = tmp_path / "script.txt"
    script.write_text('(* wrapped on purpose *)\niIntros\n  "[HP HQ]".\niSplitL "HP".\ndone.\n', encoding="utf-8")
    assert main(["trace", str(BASIC), "sep_comm", "--script", str(script)]) == 0
    captured = capsys.readouterr()
    default = tmp_path / ".pcp" / "traces" / "Basic.sep_comm.jsonl"
    assert default.exists() and captured.out.startswith("4 steps,")
    assert captured.err.startswith("stopped at step 3: ")
    rows = _rows(default)
    steps = [r for r in rows if r["rec"] == "step"]
    assert [s["tactic"] for s in steps] == ["<start>", 'iIntros\n  "[HP HQ]".', 'iSplitL "HP".', "done."]
    assert steps[3]["ok"] is False and steps[3]["state_id"] == -1 and rows[0]["failed_at"] == 3
    assert len(steps[3]["goals"]) == 2  # the goals before the failing tactic: both halves of the split
    assert main(["state", str(default)]) == 0
    assert "step 3 failed" in capsys.readouterr().err


@needs_petanque
def test_trace_oracle_probes_each_step_at_its_own_state(tmp_path: Path, capsys) -> None:
    out = tmp_path / "exists_pure.jsonl"
    assert main(["trace", str(BASIC), "exists_pure", "--oracle", "-o", str(out)]) == 0
    steps = [r for r in _rows(out) if r["rec"] == "step"]
    # "H" exists only at step 1: a probe at the final state (v1) would have answered
    # "no such hypothesis" and left `persistent` unknown.
    assert [h["id"] for h in steps[1]["goals"][0]["spatial"]] == ["H"]
    assert steps[1]["goals"][0]["spatial"][0]["persistent"] is False
    assert steps[2]["goals"][0]["spatial"][0]["id"] == "HΦ" and steps[2]["goals"][0]["spatial"][0]["persistent"] is False
    assert steps[-1]["goals"] == []


@needs_petanque
@needs_rocq
def test_trace_reflect_really_reads_through_idump(tmp_path: Path, monkeypatch, capsys) -> None:
    import os

    root = tmp_path / "coqroot"
    before = dict(os.environ)
    run = TraceRun.open(BASIC, "load_twice", reflect=True, coq_root=root)
    try:
        assert dict(os.environ) == before and (root / "pcp" / "IDump.vo").exists()
        run.tracer.start()
        step = run.tracer.step('iIntros "Hl".')
        assert step.ok and run.reflector is not None and run.reflector.available is True
        state = run.session.state(step.state_id)
        # Only a session that loaded IDump can answer a per-hypothesis `Set Printing All` probe.
        verbose = run.reflector.dump_hyp("Hl", state=state, printing="Set Printing All.")
        assert verbose is not None and "pointsto" in verbose.body
        assert step.goals[0].spatial[0].prop == "l ↦ v"
    finally:
        run.close()
    monkeypatch.setattr("pcp.cli.cmd_trace.DEFAULT_COQ_ROOT", root)
    out = tmp_path / "reflect.jsonl"
    assert main(["trace", str(BASIC), "load_twice", "--reflect", "-o", str(out)]) == 0
    assert capsys.readouterr().out.startswith("7 steps,")
    assert dict(os.environ) == before
    steps = [r for r in _rows(out) if r["rec"] == "step"]
    assert steps[1]["goals"][0]["spatial"][0]["prop"] == "l ↦ v" and steps[-1]["goals"] == []
