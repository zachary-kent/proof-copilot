"""`pcp check` explains a failing compile with the proof state at the failing tactic.

The alternative was shadowing `coqc`.  These tests pin the two properties that made
`pcp check` the better host: the gate still means `coqc`, and the enrichment is
withheld from a run that was not granted the state layer.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import pytest

from pcp.cli.main import _wants_diagnosis
from pcp.mcp.explain import locate_failure

SOURCE = """\
From iris.proofmode Require Import proofmode.

Lemma first : True.
Proof.
  exact I.
Qed.

Lemma second : True.
Proof.
  iIntros "[H1 H2]".
  exact I.
Qed.
"""


def _args(**kw):
    ns = argparse.Namespace(diagnose=None, full=False, json=False)
    for k, v in kw.items():
        setattr(ns, k, v)
    return ns


# ------------------------------------------------------------------ locating it

def test_the_failing_block_is_found_from_the_error_line() -> None:
    output = 'File "./X.v", line 10, characters 2-21:\nError: cannot destruct\n'
    block = locate_failure(SOURCE, output, prefer="first")
    assert block is not None
    # `prefer` names the node under test; the *line* names where it actually broke.
    assert block.name == "second"


def test_an_error_outside_every_proof_body_is_not_diagnosed() -> None:
    output = 'File "./X.v", line 1, characters 0-10:\nError: cannot find library\n'
    assert locate_failure(SOURCE, output, prefer="second") is None


def test_with_no_location_it_falls_back_to_the_node_under_test() -> None:
    block = locate_failure(SOURCE, "Error: something unlocated", prefer="second")
    assert block is not None and block.name == "second"


def test_with_no_location_and_no_preference_it_says_nothing() -> None:
    assert locate_failure(SOURCE, "Error: something unlocated") is None


def test_a_statement_only_declaration_is_never_replayed() -> None:
    text = "Lemma bare : True.\nAdmitted.\n"
    assert locate_failure(text, "Error: nope", prefer="bare") is None


# --------------------------------------------------------------------- gating

def test_the_packet_decides_by_default() -> None:
    assert _wants_diagnosis({"diagnose": True}, _args()) is True
    assert _wants_diagnosis({"diagnose": False}, _args()) is False
    assert _wants_diagnosis({}, _args()) is False


def test_an_explicit_flag_overrides_the_packet() -> None:
    assert _wants_diagnosis({"diagnose": False}, _args(diagnose=True)) is True
    assert _wants_diagnosis({"diagnose": True}, _args(diagnose=False)) is False


def test_the_control_arm_does_not_get_the_state_layer_through_the_checker(tmp_path: Path) -> None:
    """Granting no state tools must grant no replay: otherwise the ablation is void."""
    from pcp.orch.assemble import Development
    from pcp.orch.graph import Node
    from pcp.orch.packet import NODE_FILE, build_packet

    dev_path = tmp_path / "X.v"
    dev_path.write_text(SOURCE, encoding="utf-8")
    dev = Development(dev_path)
    node = Node(id="second", name="second", statement="Lemma second : True.", parent=None)

    off = build_packet(None, node, dev, [], anchor="second",
                       root=tmp_path / "off", state_tools=None)
    on = build_packet(None, node, dev, [], anchor="second",
                      root=tmp_path / "on", state_tools=["proof_step"])

    assert json.loads((off.workdir / NODE_FILE).read_text())["diagnose"] is False
    assert json.loads((on.workdir / NODE_FILE).read_text())["diagnose"] is True
    # ... and the arm that has it is told it has it.
    assert "replays that proof" in on.task.read_text(encoding="utf-8")
    assert "replays that proof" not in off.task.read_text(encoding="utf-8")


# ------------------------------------------------------------------- layering

def test_the_daily_loop_still_runs_without_petanque() -> None:
    """`pcp/orch` must not acquire a state-layer dependency through this feature."""
    import inspect

    from pcp.orch import packet

    source = inspect.getsource(packet)
    assert "pcp.mcp.explain" not in source
    assert "pytanque" not in source


def test_explain_is_silent_when_the_toolchain_is_absent(monkeypatch, tmp_path: Path) -> None:
    from pcp.mcp import explain as explain_mod

    monkeypatch.setattr(explain_mod, "available", lambda: False)
    assert explain_mod.explain(SOURCE, workdir=tmp_path, compile_output='File "./X.v", line 10, characters 2-21:\nError: x') == ""


def test_a_broken_replay_never_breaks_the_check(monkeypatch, tmp_path: Path) -> None:
    from pcp.mcp import explain as explain_mod

    monkeypatch.setattr(explain_mod, "available", lambda: True)
    monkeypatch.setattr(explain_mod, "_replay", lambda *a, **k: 1 / 0)
    out = explain_mod.explain(
        SOURCE, workdir=tmp_path, compile_output='File "./X.v", line 10, characters 2-21:\nError: x'
    )
    assert out == ""
    assert not list(tmp_path.glob("*.v"))  # and it cleans up after itself


def test_a_leftover_replay_twin_is_never_taken_for_the_workers_file(tmp_path: Path) -> None:
    """A killed replay leaves a `.v` behind; the checker must still find the real one."""
    from pcp.cli.main import _body_from_scratch, _candidate_file, _worker_files
    from pcp.mcp.explain import TWIN_STEM

    (tmp_path / "X.v").write_text(SOURCE, encoding="utf-8")
    (tmp_path / f"{TWIN_STEM}.v").write_text("Lemma second : False.\nProof.\nQed.\n", encoding="utf-8")
    (tmp_path / f"{TWIN_STEM}__pcpfast.v").write_text("Lemma second : False.\n", encoding="utf-8")

    assert [p.name for p in _worker_files(tmp_path)] == ["X.v"]
    assert "exact I" in (_body_from_scratch(tmp_path, {"target": "second"}) or "")

    class _Dev:
        path = Path("Nowhere.v")

    assert _candidate_file(tmp_path, _Dev()) == SOURCE


def test_the_replay_stops_at_its_budget_rather_than_eating_the_node_clock(monkeypatch, tmp_path) -> None:
    """A diagnosis that costs more than it is worth has done harm, not help."""
    import time as _time

    from pcp.mcp import explain as explain_mod

    class _Step:
        ok = True

    class _Tracer:
        def __init__(self, session):
            self.trace = type("T", (), {"failed_at": None, "finished": False})()
            self.n = 0

        def step(self, tactic):
            self.n += 1
            clock["t"] += 100.0  # each tactic blows the whole budget
            return _Step()

    clock = {"t": 0.0}
    monkeypatch.setattr(explain_mod, "available", lambda: True)
    monkeypatch.setattr("pcp.core.session.SessionPool", lambda *a, **k: type(
        "P", (), {"close": lambda self: None})())
    monkeypatch.setattr("pcp.core.session.ProofSession", lambda *a, **k: None)
    monkeypatch.setattr("pcp.core.trace.Tracer", _Tracer)
    monkeypatch.setattr(_time, "monotonic", lambda: clock["t"])

    source = "Lemma l : True.\nProof.\n" + "  idtac.\n" * 40 + "Qed.\n"
    out = explain_mod.explain(
        source, workdir=tmp_path,
        compile_output='File "./X.v", line 20, characters 2-8:\nError: boom',
        budget_seconds=1.0,
    )
    assert "of 40 tactics" in out and "within the budget" in out
    assert "replayed the first 1 " in out
