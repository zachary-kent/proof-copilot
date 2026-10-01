"""Regression tests for pcp-issues.md "Session 4" (issues 28-34), offline with fakes."""

from __future__ import annotations

import json
import threading
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from pcp.rocq.errors import is_timeout
from pcp.state import budget as budgets
from pcp.state.compound import branch_command, split_compound
from pcp.state.diagnose import _points_to, diagnose_structured
from pcp.state.ipm.model import Hyp, IrisGoal, Step
from pcp.state.petanque import GoalStack
from pcp.state.session import StepResult
from pcp.state.trace import Trace, Tracer

pytest.importorskip("pytanque")

from pcp.mcp.server import PcpServer, SessionRecord, _event_json  # noqa: E402


def _goal(text: str, *hyps: Hyp) -> IrisGoal:
    return IrisGoal(goal=text, spatial=list(hyps))


# ------------------------------------------------- 28, 29, 33: time budgets


def test_every_way_rocq_says_timeout_is_a_timeout() -> None:
    assert is_timeout("Coq: Timeout!") and is_timeout("petanque call `run` timed out")
    assert is_timeout('Anomaly "Uncaught exception Fun.Finally_raised: Control.Timeout."')
    assert not is_timeout("No applicable tactic.")


def test_a_timeout_is_a_budget_problem_before_it_is_a_proof_problem() -> None:
    wp = _goal("WP ! #l {{ v, Φ v }}")  # no `l ↦` in the context
    plain = diagnose_structured("wp_load.", "Tactic failure: wp_load: cannot find 'Load'.", wp)
    assert plain.repair == "wp-next-step" and plain.confidence == "high" and "there is no `l ↦ …`" in plain.text
    slow = diagnose_structured("wp_load.", "Coq: Timeout!", wp)
    assert slow.repair == "budget" and slow.confidence == "low"
    assert "there is no" not in slow.text and "larger `timeout`" in slow.text
    known = diagnose_structured("set_solver.", "Coq: Timeout!", _goal("x ∈ dom m"), known_good=True)
    assert known.repair == "budget" and known.confidence == "high" and "has passed before" in known.text
    # A β-redex is still named with confidence: that timeout has a structural cause.
    beta = diagnose_structured('iApply ("HQ" with "[$]").', "Timeout!", _goal("(λ b, if b then P else Q) false"))
    assert beta.repair == "beta-reduce" and beta.confidence == "high"


def test_a_points_to_is_found_through_a_coercion() -> None:
    assert _points_to("(l +ₗ 1%nat) ↦ #0", "Some (l +ₗ 1%nat) &ₜ 0")
    assert _points_to("(l +ₗ 1%nat) ↦{#1/2} v", "(l +ₗ 1%nat)")
    assert _points_to("l ↦ v", "l") and not _points_to("ll ↦ v", "l")
    assert not _points_to("l ↦ v", "l +ₗ 1")  # location arithmetic is not a coercion
    goal = _goal("WP ! #(l +ₗ 1) {{ v, Φ v }}", Hyp("Hbackup", "(l +ₗ 1) ↦ #0"))
    dx = diagnose_structured("wp_load.", "Tactic failure: wp_load: cannot find 'Load'.", goal)
    assert "there is no" not in dx.text


def test_one_retry_only_on_a_busy_machine_or_a_known_good_sentence(monkeypatch) -> None:
    assert budgets.retry_budget(30, busy=False, known_good=False) is None
    assert budgets.retry_budget(30, busy=True, known_good=False) == 60
    assert budgets.retry_budget(30, busy=False, known_good=True) == 60
    assert budgets.retry_budget(100, busy=True, known_good=False) == budgets.MAX_RETRY_S
    assert budgets.retry_budget(budgets.MAX_RETRY_S, busy=True, known_good=True) is None
    assert budgets.step_budget(None) == 30 and budgets.step_budget(0) == 30 and budgets.step_budget(90) == 90
    assert budgets.step_budget(10_000) == budgets.MAX_TIMEOUT_S
    monkeypatch.setattr(budgets.os, "getloadavg", lambda: (95.0, 50.0, 20.0))
    monkeypatch.setattr(budgets, "cpus", lambda: 64)
    assert budgets.load() == {"load_1m": 95.0, "cpus": 64, "busy": True}


class _SlowSession:
    """A session whose first run of a sentence times out and whose second passes."""

    source_file = "x.v"
    file = "x.v"
    thm = "t"

    def __init__(self) -> None:
        self.budgets: list[float | None] = []

    def run(self, tactic: str, *, timeout: float | None = None, **_: Any) -> StepResult:
        self.budgets.append(timeout)
        if len(self.budgets) == 1:
            return StepResult(ok=False, error="Coq: Timeout!", timed_out=True, budget_s=30.0, tactic=tactic)
        state = SimpleNamespace(st=2, state_hash=7, messages=(), proof_finished=False)
        return StepResult(ok=True, state=state, budget_s=float(timeout or 30), tactic=tactic)  # type: ignore[arg-type]


def test_the_tracer_retries_a_timeout_once_at_the_budget_it_is_given() -> None:
    session = _SlowSession()
    tracer = Tracer(session)  # type: ignore[arg-type]
    tracer.trace.steps.append(Step(step=0, state_id=1, tactic="<start>", goals=[_goal("P")]))
    tracer.goals_at = lambda state: [_goal("Q")]  # type: ignore[method-assign]
    tracer.retry_budget = lambda n, tactic, run: 60.0
    step = tracer.step("set_solver.")
    assert step.ok and session.budgets == [None, 60.0]
    assert tracer.last_result is not None and tracer.last_result.retried_from_s == 30.0
    assert tracer.retries == [{"step": 1, "sentence": "set_solver.", "first_s": 30.0, "retry_s": 60.0, "ok": True}]


# ------------------------------------------------------------ fakes for the tools


class _Tracer:
    """Steps like ``Tracer.step``; ``fail`` maps a sentence to its error."""

    def __init__(self, goals: list[IrisGoal], fail: dict[str, str] | None = None) -> None:
        self.trace = Trace(file="x.v", thm="t")
        self.trace.steps.append(Step(step=0, state_id=1, tactic="<start>", goals=goals))
        self.fail = fail or {}
        self.last_result: StepResult | None = None
        self.retries: list[dict[str, Any]] = []

    def step(self, tactic: str, *, timeout: float | None = None) -> Step:
        n = len(self.trace.steps)
        prev = self.trace.steps[-1].goals
        error = self.fail.get(tactic)
        if error is not None:
            step = Step(step=n, state_id=-1, tactic=tactic, goals=prev, ok=False, error=error)
            self.trace.failed_at, self.trace.error = n, error
            self.last_result = StepResult(ok=False, error=error, timed_out=is_timeout(error), budget_s=timeout or 30.0,
                                          elapsed_ms=30_500, tactic=tactic)
        else:
            step = Step(step=n, state_id=n + 1, tactic=tactic, goals=[])
            self.last_result = StepResult(ok=True, tactic=tactic)
        self.trace.steps.append(step)
        return step

    def goals_at(self, state: Any) -> list[IrisGoal]:
        return list(state.goals)

    def hidden_at(self, step: Step) -> None:
        return None


class _Session:
    """Speculative runs answered from a table: sentence -> ``(ok, error, goals)``."""

    def __init__(self, table: dict[str, tuple[bool, str | None, list[IrisGoal]]], **extra: Any) -> None:
        self.table, self.ran = table, []
        self.source_file, self.thm, self.pool = "x.v", "t", None
        self.__dict__.update(extra)

    def close(self) -> None:
        pass

    def run(self, tactic: str, *, commit: bool = True, from_state: Any = None, timeout: float | None = None) -> StepResult:
        self.ran.append(tactic)
        ok, error, goals = self.table.get(tactic, (True, None, []))
        state = SimpleNamespace(st=9, goals=goals, proof_finished=False, state_hash=None, messages=())
        return StepResult(ok=ok, error=error, state=state if ok else None, tactic=tactic)  # type: ignore[arg-type]


def _record(server: PcpServer, tracer: Any, session: Any, sid: str = "s1") -> SessionRecord:
    session.source_file = str(server.workspace / "x.v")
    rec = SessionRecord(sid, session=session, tracer=tracer)
    server._sessions[sid] = rec
    return rec


# ------------------------------------------------------ 30, 32: compound tails


def test_compound_sentences_are_taken_apart() -> None:
    c = split_compound('iMod (foo with "H") as "[A B]"; [done|done| | |done|by iFrame].')
    assert c is not None and c.kind == "dispatch" and c.head == 'iMod (foo with "H") as "[A B]".'
    assert c.branches == ("done", "done", "", "", "done", "by iFrame")
    first = split_compound('wp_alloc lw as "Hlw" "†Hlw"; first lia.')
    assert first is not None and first.kind == "first" and first.branches == ("lia",)
    assert split_compound("intros; lia.").kind == "each"  # type: ignore[union-attr]
    for whole in ('iDestruct "H" as "[A|B]".', "t; try lia.", "2: t; lia.", "t; [a|b]; c.", "by t; lia."):
        assert split_compound(whole) is None, whole
    assert branch_command(5, "by iFrame") == "5: (by iFrame)."


def test_a_tail_that_fails_is_named_with_its_goal(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    sentence = 'iMod (foo with "H") as "HX"; [done|done| | |done|by iFrame].'
    made = [_goal(f"side {i}") for i in range(1, 6)] + [_goal("|={⊤}=> Φ #()")]
    made[4] = _goal("st = SPend j → st = SInst j0 → False")
    session = _Session({'iMod (foo with "H") as "HX".': (True, None, made),
                        "5: (done).": (False, "No applicable tactic.", [])})
    _record(server, _Tracer([_goal("|={⊤}=> P")], {sentence: "No applicable tactic."}), session)
    out = server.proof_step("s1", sentence)
    assert out["ok"] is False and out["compound"]["part"] == "tail" and out["compound"]["branch"] == 5
    assert "`done` fails on goal 5 of the 6 it makes" in out["what"]
    assert "st = SPend j" in out["goal"][0]
    assert session.ran[:4] == ['iMod (foo with "H") as "HX".', "1: (done).", "2: (done).", "5: (done)."]
    json.dumps(out)
    server.close()


def test_a_first_tail_that_meets_the_main_goal_says_the_side_goal_is_gone(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    sentence = 'wp_alloc lw as "Hlw" "†Hlw"; first lia.'
    session = _Session({'wp_alloc lw as "Hlw" "†Hlw".': (True, None, [_goal("WP #lw {{ v, Φ v }}")]),
                        "1: (lia).": (False, "Tactic failure: Cannot find witness.", [])})
    _record(server, _Tracer([_goal("WP AllocN #3 #0 {{ v, Φ v }}")], {sentence: "Tactic failure: Cannot find witness."}),
            session)
    out = server.proof_step("s1", sentence)
    assert out["compound"]["part"] == "tail" and out["compound"]["made"] == 1
    assert "already solved -- drop the tail" in out["next"][0]
    assert "there is no" not in out["diagnosis"]  # not the head's wp diagnosis
    server.close()


def test_a_head_that_fails_alone_is_diagnosed_as_the_head(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    sentence = 'iMod "AU" as (vs) "[H1 H2]"; first wndisj.'
    session = _Session({'iMod "AU" as (vs) "[H1 H2]".': (False, "iMod: 1 binder names were given", [])})
    _record(server, _Tracer([_goal("P")], {sentence: "iMod: 1 binder names were given"}), session)
    out = server.proof_step("s1", sentence)
    assert out["compound"]["part"] == "head" and "its head" in out["what"] and "fails on its own" in out["what"]
    server.close()


def test_a_dispatch_of_the_wrong_length_says_so(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    sentence = "split; [done|done]."
    session = _Session({"split.": (True, None, [_goal("A"), _goal("B"), _goal("C")])})
    _record(server, _Tracer([_goal("A ∧ B ∧ C")], {sentence: "Incorrect number of goals (expected 3 tactics, was given 2)."}),
            session)
    out = server.proof_step("s1", sentence)
    assert out["compound"]["part"] == "dispatch" and "makes 3 goals, the `[…]` gives 2 tactics" in out["what"]
    server.close()


# -------------------------------------------------- 31: "0 goals" that aren't


def test_no_focused_goal_but_an_open_bullet_sibling(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    session = _Session({"Qed.": (False, "Coq:  (in proof t): Attempt to save an incomplete proof\n"
                                        "(there are remaining open goals).", [])},
                       goal_stack=lambda: GoalStack(focused=0, unfocused=1), query=lambda cmd: [])
    _record(server, _Tracer([_goal("A ∧ B ∧ C")]), session)
    out = server.proof_step("s1", "exact I.")
    assert out["ok"] is True and "not finished: 1 unfocused goal under a bullet or brace" in out["what"]
    assert out["open_ends"]["unfocused"] == 1 and "Attempt to save an incomplete proof" in out["open_ends"]["qed"]
    assert "bullet sibling is still open" in out["next"][0]
    server.close()


def test_no_goal_but_an_uninstantiated_evar(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    tracer = _Tracer([_goal("∃ γ, own ?γ x ∨ True")])
    session = _Session({"Qed.": (False, "Coq: (in proof t): Attempt to save an incomplete proof\n"
                                        "(the proof term is not complete).", [])},
                       goal_stack=GoalStack,
                       query=lambda cmd: ["Existential 1 = ?γ : [ H : True |- gname]"])
    _record(server, tracer, session)
    out = server.proof_step("s1", "iRight.")
    ends = out["open_ends"]
    assert ends["evars"] == [{"evar": "?γ", "type": "gname", "step": 0}]
    assert "the proof term is not complete" in ends["qed"] and "uninstantiated evar `?γ` (step 0)" in out["what"]
    server.close()


def test_a_finished_proof_has_no_open_ends(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    session = _Session({"Qed.": (True, None, [])}, goal_stack=GoalStack, query=lambda cmd: [])
    _record(server, _Tracer([_goal("True")]), session)
    out = server.proof_step("s1", "exact I.")
    assert "open_ends" not in out and "not finished" not in out["what"]
    server.close()


# ---------------------------------------------------- 28: timeouts in results


def test_a_timeout_carries_its_budget_and_the_load(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(budgets, "load", lambda: {"load_1m": 95.0, "cpus": 64, "busy": True})
    server = PcpServer(tmp_path)
    _record(server, _Tracer([_goal("WP ! #l {{ v, Φ v }}")], {"wp_load.": "Coq: Timeout!"}), _Session({}))
    out = server.proof_step("s1", "wp_load", timeout=45)
    assert out["timed_out"] is True and out["diagnosis_class"] == "budget"
    assert out["timeout"]["budget_s"] == 45 and out["timeout"]["elapsed_s"] == 30.5 and out["timeout"]["busy"] is True
    assert "timeout=180" in out["next"][0] and "compound" not in out
    server.close()


def test_a_long_replay_answers_before_the_client_gives_up(tmp_path: Path, monkeypatch) -> None:
    server = PcpServer(tmp_path)
    (tmp_path / "x.v").write_text("Lemma t : True.\nProof.\n  exact I.\nQed.\n", encoding="utf-8")
    release = threading.Event()
    calls: list[int] = []

    def slow(path: Path, lemma: str, tactics: list[str], places: Any, **kw: Any) -> dict[str, Any]:
        calls.append(1)
        job = kw["job"]
        job.rec = SimpleNamespace(id="s9", trace=SimpleNamespace(final=SimpleNamespace(step=1)))
        release.wait(10)
        return {"ok": True, "what": "replayed 1 sentence: proof finished"}

    monkeypatch.setattr(server, "_trace", slow)
    first = server.proof_trace("x.v", "t", wait_s=0.05)
    assert first["ok"] is True and first["replaying"] is True and first["progress"] == {"steps": 1, "of": 1}
    assert first["session"] == "s9" and 'proof_trace("x.v", "t") again collects it' in first["next"][0]
    release.set()
    second = server.proof_trace("x.v", "t", wait_s=5)
    assert second["what"] == "replayed 1 sentence: proof finished" and calls == [1]  # joined, not rerun
    assert not server._replays
    server.close()


def test_a_busy_session_says_it_is_replaying(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    rec = _record(server, _Tracer([_goal("P")]), _Session({}))
    rec.busy = "x.v t"
    out = server.proof_state("s1")
    assert out["ok"] is False and "still replaying" in out["what"]
    server.close()


# ------------------------------------------------------------ 34: answer size


def test_step_results_cut_rewrite_sites_and_keep_the_error_out_of_the_diagnosis(tmp_path: Path) -> None:
    long = "x" * 5000
    event = SimpleNamespace(to_json=lambda: {"kind": "Rewrite", "detail": long, "hyp": None,
                                             "data": {"target": "goal", "sites": [{"old": long, "new": long}] * 9}})
    d = _event_json(event)
    assert len(d["detail"]) <= 300 and len(d["data"]["sites"]) == 3 and len(d["data"]["sites"][0]["old"]) <= 160
    server = PcpServer(tmp_path)
    env = "Cannot infer this placeholder of type nat in environment:\n" + "\n".join(f"H{i} : P{i}" for i in range(200))
    _record(server, _Tracer([_goal("P")], {"apply foo.": env}), _Session({}))
    out = server.proof_step("s1", "apply foo.")
    assert "H150 : P150" not in out["diagnosis"]
    server.close()


# ------------------------------------------------------------- against Rocq

LIVE = """Lemma three : True /\\ True /\\ True.
Proof.
  split; [|split].
  - exact I.
  - exact I.
Admitted.

Lemma shelved : exists n : nat, n = n.
Proof.
  eexists. reflexivity.
Admitted.

Lemma tails : True /\\ (1 = 1 /\\ 2 = 3).
Proof.
  split; [exact I|split; [reflexivity|reflexivity]].
Admitted.

Lemma firsts : 2 = 3 /\\ True.
Proof.
  split; first reflexivity.
Admitted.
"""


@pytest.mark.petanque
def test_open_ends_and_compound_tails_against_rocq(tmp_path: Path) -> None:
    (tmp_path / "_CoqProject").write_text("-Q . ws\n", encoding="utf-8")
    (tmp_path / "L.v").write_text(LIVE, encoding="utf-8")
    server = PcpServer(tmp_path, pool_size=1)
    try:
        three = server.proof_trace("L.v", "three", wait_s=0)
        assert three["ok"] is True and "no focused goal, but not finished" in three["what"], three["what"]
        assert three["open_ends"]["unfocused"] == 1 and "incomplete proof" in three["open_ends"]["qed"]
        shelf = server.proof_trace("L.v", "shelved", wait_s=0)
        assert shelf["open_ends"]["shelved"] == 1 and shelf["open_ends"]["evars"][0]["evar"] == "?n"
        tails = server.proof_trace("L.v", "tails", wait_s=0)
        assert tails["ok"] is False and tails["failure"]["compound"]["part"] == "tail", tails["what"]
        assert "fails on goal 2 of the 2 it makes" in tails["what"]
        first = server.proof_trace("L.v", "firsts", wait_s=0)
        assert first["failure"]["compound"] == {**first["failure"]["compound"], "part": "tail", "branch": 1, "made": 2}
        assert "2 = 3" in first["goal"][0]
    finally:
        server.close()
