"""`pcp check` replay diagnosis (pcp.state.explain): locating offline, replaying live."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest
from conftest import needs_petanque, needs_rocq

from pcp.errors import StateError, UsageError
from pcp.rocq.assemble import Development
from pcp.rocq.project import CompileResult, compile_text
from pcp.state.explain import (
    TWIN_INFIX,
    Located,
    _no_tactic_failed,
    error_offsets,
    explain,
    locate_failure,
    twin_path,
)
from tests._orch_fixtures import write_plain

ONE_LINE = 'Lemma x : True.\nProof. iIntros "[H]". exact I. Qed.\n'
TWO = (
    "Lemma a : True.\nProof.\n  exact I.\nQed.\n\n"
    "Lemma b (P Q : Prop) : P → Q.\nProof.\n  intros HP.\n  apply HP.\nQed.\n"
)


def test_one_line_proof_is_located_by_char_offset() -> None:
    out = 'File "./x.v", line 2, characters 7-20:\nError: iIntros: ...'
    loc = locate_failure(ONE_LINE, out)
    assert loc is not None and loc.name == "x" and not loc.at_qed
    assert ONE_LINE[loc.body_start : loc.body_end].strip() == 'iIntros "[H]". exact I.'


def test_a_located_warning_before_the_error_does_not_fool_the_locator() -> None:
    out = (
        'File "./x.v", line 1, characters 0-15:\nWarning: deprecated [deprecated]\n'
        'File "./x.v", line 9, characters 2-11:\nError: Unable to unify.'
    )
    loc = locate_failure(TWO, out)
    assert loc is not None and loc.name == "b"
    assert locate_failure(TWO, CompileResult(False, stdout=out)).name == "b"


def test_qed_time_incomplete_proof_maps_to_the_body_before_it() -> None:
    out = 'File "./x.v", line 10, characters 0-4:\nError: Attempt to save an incomplete proof'
    loc = locate_failure(TWO, out)
    assert loc is not None and loc.name == "b" and loc.at_qed
    assert TWO[loc.body_start : loc.body_end].strip() == "intros HP.\n  apply HP."


def test_spans_and_target_fallbacks() -> None:
    spans = {"b": (TWO.index("intros HP"), TWO.index("Qed.", 40))}
    out = 'File "./x.v", line 9, characters 2-11:\nError: x'
    assert locate_failure(TWO, out, spans=spans).name == "b"
    assert locate_failure(TWO, "Error: no location at all", target="a").name == "a"
    assert locate_failure(TWO, "Error: no location at all") is None
    assert locate_failure(TWO, 'File "./x.v", line 1, characters 0-5:\nError: x') is None, "outside every body"


def test_error_offsets_try_code_points_and_bytes() -> None:
    text = "∗ ∗ x\nab\n"
    assert error_offsets(text, 2, 1) == [len("∗ ∗ x\n") + 1]
    assert len(error_offsets(text, 1, 4)) == 2


def test_explain_never_raises_and_is_quiet_by_default(tmp_path: Path) -> None:
    assert explain(assembly_text=TWO, assembled_path_name="x.v", compile_output_or_result="Error: boom", root=tmp_path) == ""
    verbose = explain(assembly_text=TWO, assembled_path_name="x.v", compile_output_or_result="Error: boom",
                      root=tmp_path, verbose=True)
    assert verbose.startswith("(no diagnosis:")
    assert twin_path(tmp_path, "Basic.v").name == f"Basic{TWIN_INFIX}.v"


def _workdir(tmp_path: Path, scratch_dir: Path) -> Path:
    work = tmp_path / "w"
    work.mkdir()
    shutil.copy(scratch_dir / "_CoqProject", work / "_CoqProject")
    return work


def _assemble(scratch_dir: Path, body: str) -> str:
    dev = Development(scratch_dir / "Basic.v")
    return dev.assemble("destruct_nested", [], anchor_body=body, truncate=True).text


@needs_rocq
@needs_petanque
def test_wrong_pattern_is_located_by_char_offset_and_diagnosed(tmp_path: Path, scratch_dir: Path) -> None:
    pytest.importorskip("pcp.state.trace")
    work = _workdir(tmp_path, scratch_dir)
    text = _assemble(scratch_dir, 'iIntros "[HP|HQ]". iFrame.')
    result = compile_text(text, filename="Basic.v", root=work)
    assert not result.ok and result.error_location() is not None
    out = explain(assembly_text=text, assembled_path_name="Basic.v", compile_output_or_result=result,
                  root=work, target="destruct_nested", verbose=True)
    assert "diagnosis: replayed `destruct_nested`; tactic 1 of 2 is where it stops." in out, out
    assert "disjunction" in out
    assert not list(work.glob(f"*{TWIN_INFIX}*")), "the twin is removed afterwards"


@needs_rocq
@needs_petanque
def test_qed_time_error_gets_the_goals_remain_diagnosis(tmp_path: Path, scratch_dir: Path) -> None:
    pytest.importorskip("pcp.state.trace")
    work = _workdir(tmp_path, scratch_dir)
    text = _assemble(scratch_dir, 'iIntros "[HP [HQ HR]]". iSplitL "HR".')
    result = compile_text(text, filename="Basic.v", root=work)
    assert not result.ok
    out = explain(assembly_text=text, assembled_path_name="Basic.v", compile_output_or_result=result,
                  root=work, target="destruct_nested", verbose=True)
    assert "goals remain" in out, out


# ------------------------------------------------------------------ pcp check, from the command line


def _pcp(*args: str, cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, "-m", "pcp.cli.main", *args], cwd=str(cwd), capture_output=True, text=True, check=False)


def test_pcp_check_reports_a_missing_body_or_development_without_a_traceback(tmp_path):
    dev_path, _ = write_plain(tmp_path, plan=None)
    packet = tmp_path / "packet"
    packet.mkdir()
    meta = {"target": "root", "anchor": "root", "file": str(dev_path), "statement": "Lemma root (P Q : Prop) : P -> Q -> P.", "siblings": [], "scratch": "Plain.v"}
    (packet / "pcp-node.json").write_text(json.dumps(meta), encoding="utf-8")
    missing = _pcp("check", "--body", str(tmp_path / "nope.v"), cwd=packet)
    assert missing.returncode == 2 and "no such body file" in missing.stderr and "Traceback" not in missing.stderr
    meta["file"] = str(tmp_path / "gone" / "Plain.v")
    (packet / "pcp-node.json").write_text(json.dumps(meta), encoding="utf-8")
    gone = _pcp("check", "--body", str(dev_path), cwd=packet)
    assert gone.returncode == 2 and "is gone" in gone.stderr and "Traceback" not in gone.stderr


def test_usage_errors_from_the_body_argument_are_usage_errors():
    from pcp.cli.common import read_body_arg

    with pytest.raises(UsageError, match="no such body file"):
        read_body_arg(Path("/nonexistent/body.v"))


# ------------------------------------------------------------------ diagnosis wording and the replay budget


def test_a_shelved_existential_is_not_blamed_on_a_bullet() -> None:
    located = Located("ev2", 0, 10)
    shelved = _no_tactic_failed(located, ["a.", "b."], False, True, no_goals_shown=True)
    assert "shelved" in shelved and "Unshelve" in shelved and "bullet" not in shelved
    open_goal = _no_tactic_failed(located, ["a.", "b."], False, True, no_goals_shown=False)
    assert "bullet or brace" in open_goal


def test_explain_bounds_petanque_start_by_its_budget(monkeypatch, tmp_path: Path) -> None:
    """`pcp check`'s replay builds its own pool: `petanque/start` sits under the wall
    budget too, not under the 600 s default."""
    seen: dict[str, object] = {}

    class FakePool:
        def __init__(self, workspace, size=2, **cfg) -> None:
            seen.update(cfg)

        def open(self, *args, **kwargs):
            raise StateError("no pet in this test")

        def close(self) -> None:
            seen["closed"] = True

    monkeypatch.setattr("pcp.state.pool.SessionPool", FakePool)
    monkeypatch.setattr("pcp.state.explain.petanque_available", lambda: True)
    text = "Lemma x : True.\nProof. exact I. exact I. Qed.\n"
    output = 'File "./X.v", line 2, characters 16-24:\nError: No such goal.'
    out = explain(assembly_text=text, assembled_path_name="X.v", compile_output_or_result=output, root=tmp_path,
                  target="x", budget_seconds=7, verbose=True)
    assert "could not run" in out and seen.get("closed") is True
    assert isinstance(seen["start_timeout"], float) and 7 <= seen["start_timeout"] <= 60
    assert not list(tmp_path.glob("*__pcp*"))
