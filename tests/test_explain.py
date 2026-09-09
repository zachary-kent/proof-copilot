"""`pcp check` replay diagnosis (pcp.state.explain): locating offline, replaying live."""

from __future__ import annotations

import shutil
from pathlib import Path

import _ipm_standin  # noqa: F401
import pytest
from conftest import needs_petanque, needs_rocq

from pcp.rocq.assemble import Development
from pcp.rocq.project import CompileResult, compile_text
from pcp.state.explain import TWIN_INFIX, error_offsets, explain, locate_failure, twin_path

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
