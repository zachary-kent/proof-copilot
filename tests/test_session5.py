"""Regression tests for pcp-issues.md "Session 5" (issues 35-42), offline with fakes."""

from __future__ import annotations

import os
import threading
import time
import weakref
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from pcp.errors import WallClockExceeded
from pcp.rocq import deps
from pcp.state.diagnose import diagnose_structured
from pcp.state.ipm.model import Hyp, IrisGoal, Step
from pcp.state.ledger.diff import step_warnings
from pcp.state.ledger.effects import step_effects
from pcp.state.pool import SessionPool
from pcp.state.printing import GoalHidden, Hidden, atom_mismatches
from pcp.state.render import render_goal
from pcp.state.session import StepResult
from pcp.state.trace import Tracer

pytest.importorskip("pytanque")

from pcp.mcp.server import PcpServer, SessionRecord  # noqa: E402


def _goal(text: str, *, spatial=(), pure=(), intuit=(), gid: str = "g0", ipm: bool = True) -> IrisGoal:
    return IrisGoal(goal_id=gid, goal=text, is_ipm=ipm,
                    spatial=[Hyp(i, p) for i, p in spatial],
                    pure=[Hyp(i, p, klass="pure") for i, p in pure],
                    intuitionistic=[Hyp(i, p, klass="intuitionistic") for i, p in intuit])


# ----------------------------------------- 35: atoms that differ in implicit arguments


GOAL_35 = "pred (size fm) + S n = size fm + n"
IMPLICIT_35 = "pred (@size (gmap nat V) (map_size_delete fm) fm) + S n = @size (gmap nat V) (gmap_size nat V) fm + n"


def test_atoms_that_print_alike_but_differ_in_implicit_arguments_are_found() -> None:
    found = atom_mismatches([("the goal", GOAL_35, IMPLICIT_35), ('"Hne"', "size fm ≠ 0", "@size (gmap nat V) (gmap_size nat V) fm ≠ 0")])
    assert [m.atom for m in found] == ["size fm"]  # not `pred (size fm)`: only the smallest atom
    assert len(found[0].variants) == 2 and found[0].variants[1][1] == ("the goal", '"Hne"')
    assert atom_mismatches([("g", "size fm = size fm", "@size A i fm = @size A i fm")]) == []


def test_lia_on_such_atoms_says_so_with_confidence() -> None:
    goal = _goal(GOAL_35, pure=[("Hne", "size fm ≠ 0")], ipm=False)
    hidden = GoalHidden(goal=Hidden(implicit=IMPLICIT_35))
    dx = diagnose_structured("lia.", "Tactic failure: Cannot find witness.", goal, hidden=hidden)
    assert dx.repair == "implicit-mismatch" and dx.confidence == "high"
    assert "`size fm` prints the same everywhere but is 2 different terms" in dx.text
    assert diagnose_structured("lia.", "Tactic failure: Cannot find witness.", goal).repair == "unknown"


def test_select_goal_prints_the_goals_implicit_arguments() -> None:
    goal = _goal(GOAL_35, ipm=False)
    hidden = GoalHidden(goal=Hidden(implicit=IMPLICIT_35))
    assert "with implicit arguments" in render_goal(goal, select="goal", hidden=hidden).text
    assert "with implicit arguments" not in render_goal(goal, hidden=hidden).text


# ------------------------------------------------------ 36: an unfinished `{ }` block


def test_a_brace_that_closes_an_unfinished_block_is_not_called_no_focused_goal() -> None:
    error = "This proof is focused, but cannot be unfocused this way."
    open_block = diagnose_structured("}", error, _goal("m + n = m + n + ε", ipm=False), n_goals=1)
    assert open_block.repair == "finish-block" and open_block.confidence == "high"
    assert "still open inside it" in open_block.text and "no goal is focused" not in open_block.text
    nothing = diagnose_structured("}", "No focused proof.", None, n_goals=0)
    assert nothing.repair == "bullet" and nothing.confidence == "high" and "no goal is focused" in nothing.text


# ----------------------------------------------- 38: case_bool_decide in a hypothesis


def test_case_bool_decide_on_a_hypothesis_warns_when_the_goal_has_its_own() -> None:
    goal = "WP if: #(bool_decide (s = H)) then e1 else e2 {{ v, Φ v }}"
    hphi = ("HΦ", "∀ v, ⌜bool_decide (#p ∈ drop s snap) = true⌝ -∗ Φ v")
    prev = [_goal(goal, spatial=[hphi])]
    after = [_goal(goal, gid="g1", spatial=[hphi], pure=[("Heq", "#p ∈ drop s snap")]),
             _goal(goal, gid="g2", spatial=[hphi], pure=[("Heq", "¬ #p ∈ drop s snap")])]
    events = step_effects(prev, after, step=4, tactic="case_bool_decide as Heq.")
    warnings = step_warnings(events)
    assert len(warnings) == 1 and 'from "HΦ"' in warnings[0]
    assert "destruct_decide (bool_decide_reflect (s = H)) as Heq" in warnings[0]
    # Splitting on the goal's own decision is what was meant: no warning.
    fine = [_goal(goal, gid="g1", spatial=[hphi], pure=[("Heq", "s = H")]),
            _goal(goal, gid="g2", spatial=[hphi], pure=[("Heq", "s ≠ H")])]
    assert step_warnings(step_effects(prev, fine, step=4, tactic="case_bool_decide as Heq.")) == []


# ------------------------------------------------------- 40: iFrame through evars


def test_a_timed_out_iframe_on_evars_says_instantiate_first() -> None:
    goal = _goal("l ↦∗ ?snap' ∗ ⌜length ?snap' = n⌝ ∗ ([∗ list] x ∈ ?snap', P x)", spatial=[("Hl", "l ↦∗ snap")])
    dx = diagnose_structured("iFrame.", "Coq: Timeout!", goal)
    assert dx.repair == "split-before-frame" and dx.confidence == "high"
    assert dx.text.index("?snap'") < dx.text.index("ran out of time")  # the structural cause leads
    unfold = diagnose_structured('iFrame "Hn".', "Coq: Timeout!", _goal("Retirer γd t ∗ ♢ n", spatial=[("Hn", "♢ n")]))
    assert unfold.repair == "split-before-frame" and unfold.confidence == "low" and "`Retirer`" in unfold.text


# ------------------------------------------------ 41: an applied evar is not a mask


def test_an_applied_evar_unification_failure_asks_for_the_predicate() -> None:
    error = ('Tactic failure: iMod: Unable to unify "?P pn.1 s\'" with "s\' < s ∧ (|={E ∖ ↑hpInvN,E}=> own γ s\')".')
    goal = _goal("|={E ∖ ↑hpInvN,E}=> Q")
    dx = diagnose_structured('iMod (entries_take _ _ _ _ L _ s w with "H") as "H".', error, goal)
    assert dx.repair == "give-predicate" and dx.confidence == "high" and "`?P`" in dx.text
    assert "opening an invariant" not in dx.text


# ---------------------------------------- 42: a runaway sentence, and early answers


class _RunawaySession:
    source_file = file = "x.v"
    thm = "t"
    step_timeout = 30.0

    def run(self, tactic: str, *, timeout: float | None = None, **_: Any) -> StepResult:
        raise WallClockExceeded("petanque call `run` exceeded its 75 s wall clock; the process was killed",
                                fn="run", limit=75.0)


def test_a_sentence_that_outruns_the_wall_clock_is_a_timed_out_step() -> None:
    tracer = Tracer(_RunawaySession())  # type: ignore[arg-type]
    tracer.trace.steps.append(Step(step=0, state_id=1, tactic="<start>", goals=[_goal("P ∗ ?x")]))
    tracer.retry_budget = lambda n, tactic, run: 60.0  # never retried: the process is gone
    step = tracer.step("iFrame.")
    assert not step.ok and "wall clock" in (step.error or "") and "Timeout!" in (step.error or "")
    assert tracer.lost and tracer.last_result is not None and tracer.last_result.timed_out
    assert tracer.running is None and tracer.retries == []


def test_proof_step_on_a_runaway_sentence_says_the_session_is_gone(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    tracer = Tracer(_RunawaySession())  # type: ignore[arg-type]
    tracer.trace.steps.append(Step(step=0, state_id=1, tactic="<start>", goals=[_goal("l ↦∗ ?snap ∗ P", spatial=[("Hl", "l ↦∗ s")])]))
    tracer.hidden_at = lambda step: None  # type: ignore[method-assign]
    session = SimpleNamespace(source_file=str(tmp_path / "x.v"), thm="t", pool=None, close=lambda: None)
    server._sessions["s1"] = SessionRecord("s1", session=session, tracer=tracer)  # type: ignore[arg-type]
    out = server.proof_step("s1", "iFrame")
    assert out["ok"] is False and out["timed_out"] is True and out["diagnosis_class"] == "split-before-frame"
    assert "wall clock" in out["next"][0] and "do not rerun it as is" in " ".join(out["next"])
    server.close()


def test_an_early_answer_names_the_sentence_it_is_on(tmp_path: Path, monkeypatch) -> None:
    server = PcpServer(tmp_path)
    (tmp_path / "x.v").write_text("Lemma t : True.\nProof.\n  exact I.\nQed.\n", encoding="utf-8")
    release = threading.Event()

    def slow(path: Path, lemma: str, tactics: list[str], places: Any, **kw: Any) -> dict[str, Any]:
        tracer = SimpleNamespace(running=(10, "iFrame.", time.monotonic() - 40))
        kw["job"].rec = SimpleNamespace(id="s28", trace=SimpleNamespace(final=SimpleNamespace(step=9)), tracer=tracer)
        release.wait(10)
        return {"ok": True, "what": "done"}

    monkeypatch.setattr(server, "_trace", slow)
    out = server.proof_trace("x.v", "t", wait_s=0.05)
    assert "now on step 10, `iFrame.`, for 4" in out["what"] and out["progress"]["running"]["step"] == 10
    assert out["where"]["sentence"] == "iFrame."
    assert any("wait_s=0" in h for h in out["next"]) and "past the default per-sentence budget" in out["next"][0]
    release.set()
    server.close()


# ------------------------------------------------- 37: a library rebuilt under a worker


def _project(tmp_path: Path) -> Path:
    (tmp_path / "_CoqProject").write_text("-Q theories smr\n", encoding="utf-8")
    lang = tmp_path / "theories" / "lang"
    lang.mkdir(parents=True)
    (lang / "primitive_laws.v").write_text("Inductive t := NoSpace.\n", encoding="utf-8")
    (lang / "primitive_laws.vo").write_bytes(b"old")
    (lang / "lifting.v").write_text("From smr.lang Require Import primitive_laws.\n", encoding="utf-8")
    (lang / "lifting.vo").write_bytes(b"old")
    (lang / "adequacy.v").write_text(
        "(* Require Import nothing. *)\nFrom iris Require Import prelude.\nFrom smr Require Export lifting.\n", encoding="utf-8")
    return lang


def test_the_project_libraries_a_file_loads_are_found_transitively(tmp_path: Path) -> None:
    lang = _project(tmp_path)
    assert deps.requires("From smr Require Import a b.\nRequire Export smr.c.\n(* Require d. *)") == ["smr.a", "smr.b", "smr.c"]
    got = deps.library_files(lang / "adequacy.v")
    assert sorted(p.name for p in got) == ["lifting.vo", "primitive_laws.vo"]


class _FakeProcess:
    def __init__(self, pid: int) -> None:
        self.id, self.files, self.lock, self.restarts = pid, set(), threading.RLock(), []

    def alive(self) -> bool:
        return True

    def restart(self, reason: str = "") -> int:
        self.restarts.append(reason)
        self.files.clear()
        return len(self.restarts)


class _FakeSession:
    def __init__(self, process: _FakeProcess) -> None:
        self.process, self.started, self.lost = process, True, None

    def mark_lost(self, reason: str) -> None:
        self.lost = reason


def test_a_worker_whose_library_was_rebuilt_is_not_reused(tmp_path: Path) -> None:
    lang = _project(tmp_path)
    pool = SessionPool(tmp_path, size=1)
    proc = _FakeProcess(1)
    pool._processes.append(proc)  # type: ignore[arg-type]
    pool._sessions[1] = []
    target = lang / "adequacy.v"
    proc.files.add(str(target.resolve()))
    old = _FakeSession(proc)
    pool.note_libraries(old, target)  # type: ignore[arg-type]
    pool._sessions[1].append(weakref.ref(old))
    assert pool.process_for(target) is proc and proc.restarts == []  # nothing changed: warm reuse
    vo = lang / "primitive_laws.vo"
    vo.write_bytes(b"new")
    stamp = vo.stat().st_mtime + 5
    os.utime(vo, (stamp, stamp))
    assert [p.name for p in pool.changed_libraries(old)] == ["primitive_laws.vo"]  # type: ignore[arg-type]
    assert pool.process_for(target) is proc
    assert proc.restarts and "primitive_laws.vo changed on disk" in proc.restarts[0]
    assert old.lost and "primitive_laws.vo" in old.lost
    assert pool._changed(1) == []  # a fresh process starts a fresh record
    pool._closed = True


# ------------------------------------------------------------------ against Rocq

LIVE = """From Stdlib Require Import Lia.
Class Size (A : Type) := size : A -> nat.
#[local] Instance size_a : Size nat := fun n => n.
Definition size_b : Size nat := fun n => n.

Lemma atoms (m : nat) (Hm : @size nat size_b m <> 0) : pred (@size nat size_a m) + 1 = @size nat size_b m.
Proof.
  lia.
Qed.

Lemma block (m : nat) : m = m /\\ True.
Proof.
  split.
  { idtac. }
  exact I.
Qed.
"""


@pytest.mark.petanque
def test_implicit_atoms_and_open_blocks_against_rocq(tmp_path: Path) -> None:
    (tmp_path / "_CoqProject").write_text("-Q . ws\n", encoding="utf-8")
    (tmp_path / "L.v").write_text(LIVE, encoding="utf-8")
    server = PcpServer(tmp_path, pool_size=1)
    try:
        atoms = server.proof_trace("L.v", "atoms", wait_s=0)
        assert atoms["ok"] is False, atoms["what"]
        assert atoms["failure"]["diagnosis_class"] == "implicit-mismatch", atoms["failure"]["diagnosis"]
        assert "size m" in atoms["failure"]["diagnosis"]
        shown = server.proof_state(atoms["session"], select="goal")
        assert "with implicit arguments" in "\n".join(shown["goal"])
        block = server.proof_trace("L.v", "block", wait_s=0)
        assert block["ok"] is False and block["failure"]["diagnosis_class"] == "finish-block", block["failure"]
    finally:
        server.close()


def _compile(root: Path, name: str) -> None:
    import subprocess

    from pcp.config import toolchain

    tc = toolchain.resolve(root)
    out = subprocess.run([*tc.compiler_argv(), "-Q", ".", "ws", f"{name}.v"], cwd=root, env=tc.env(),
                         capture_output=True, text=True, timeout=120, check=False)
    assert out.returncode == 0, out.stderr


@pytest.mark.petanque
def test_a_rebuilt_library_is_reloaded_against_rocq(tmp_path: Path) -> None:
    (tmp_path / "_CoqProject").write_text("-Q . ws\n", encoding="utf-8")
    (tmp_path / "Lib.v").write_text("Inductive t := A.\n", encoding="utf-8")
    _compile(tmp_path, "Lib")
    (tmp_path / "Use.v").write_text(
        "From ws Require Import Lib.\nLemma a : exists x : t, x = x.\nProof. exists A. reflexivity. Qed.\n"
        "Lemma b : True.\nProof. exact I. Qed.\n", encoding="utf-8")
    server = PcpServer(tmp_path, pool_size=1)
    try:
        assert server.proof_trace("Use.v", "a", wait_s=0)["ok"] is True
        (tmp_path / "Lib.v").write_text("Inductive t := A | NoSpace.\n", encoding="utf-8")
        time.sleep(1.1)  # a new mtime even on a coarse filesystem clock
        _compile(tmp_path, "Lib")
        opened = server.proof_open("Use.v", "b")
        assert opened["ok"] is True and "Lib.vo changed on disk" in opened.get("worker_restarted", ""), opened
        step = server.proof_step(opened["session"], "assert (NoSpace = NoSpace) by reflexivity")
        assert step["ok"] is True, step["what"]  # the new constructor is visible
    finally:
        server.close()
