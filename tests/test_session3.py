"""Regression tests for pcp-issues.md "Session 3" (issues 19-26), offline with fakes."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from pcp.config.load import INNER_IGNORE, state_dir
from pcp.config.toolchain import workspace_for
from pcp.state.candidates import closest_survivor, compare
from pcp.state.diagnose import beta_redexes, diagnose_structured
from pcp.state.diagnosis_log import record_diagnosis
from pcp.state.ipm.model import Hyp, IrisGoal, Step
from pcp.state.trace import Trace

pytest.importorskip("pytanque")

from pcp.mcp.server import PcpServer, SessionRecord  # noqa: E402


def _repo(tmp_path: Path) -> tuple[Path, Path]:
    """A git root holding the pcp project one level down, as smr-verification is laid out."""
    repo = tmp_path / "repo"
    proj = repo / "proj"
    (repo / ".git").mkdir(parents=True)
    (proj / ".pcp").mkdir(parents=True)
    (proj / ".pcp" / "config.toml").write_text("", encoding="utf-8")
    (proj / "_CoqProject").write_text("-Q theories smr\n", encoding="utf-8")
    (proj / "theories").mkdir()
    (proj / "theories" / "a.v").write_text("Lemma t : True. Proof. exact I. Qed.\n", encoding="utf-8")
    (repo / "README.md").write_text("", encoding="utf-8")
    return repo, proj


# ---------------------------------------------------- 19, 24, 26: the workspace


def test_the_mcp_workspace_is_the_project_below_the_git_root(tmp_path: Path) -> None:
    repo, proj = _repo(tmp_path)
    server = PcpServer(repo)
    try:
        assert server.workspace == proj.resolve() and server.launch_dir == repo.resolve()
        # Relative to the project (what `next` suggests), and to the launch dir (what the host lists).
        assert server._file("theories/a.v") == (proj / "theories" / "a.v").resolve()
        assert server._file("proj/theories/a.v") == (proj / "theories" / "a.v").resolve()
        assert server._rel(proj / "theories" / "a.v") == "theories/a.v"
        with pytest.raises(Exception, match="resolved against .*proj and .*repo"):
            server._file("theories/missing.v")
    finally:
        server.close()


def test_the_cli_daemon_and_the_mcp_server_pick_the_same_workspace(tmp_path: Path, monkeypatch) -> None:
    from pcp.cli.cmd_tools import workspace_of

    repo, proj = _repo(tmp_path)
    assert workspace_of(argparse.Namespace(workspace=str(repo))) == proj.resolve()
    monkeypatch.chdir(repo)
    assert workspace_of(argparse.Namespace(workspace=None)) == proj.resolve()
    monkeypatch.chdir(proj / "theories")
    assert workspace_of(argparse.Namespace(workspace=None)) == proj.resolve()


def test_workspace_for_prefers_the_configured_project_and_else_stays_put(tmp_path: Path) -> None:
    repo, proj = _repo(tmp_path)
    other = repo / "vendor" / "lib"
    other.mkdir(parents=True)
    (other / "_CoqProject").write_text("", encoding="utf-8")
    (repo / "_opam" / "x").mkdir(parents=True)
    (repo / "_opam" / "x" / "_CoqProject").write_text("", encoding="utf-8")  # a switch is never a project
    assert workspace_for(repo) == proj.resolve()  # shallowest level: proj only
    two = tmp_path / "two"
    for name in ("a", "b"):
        (two / name).mkdir(parents=True)
        (two / name / "_CoqProject").write_text("", encoding="utf-8")
    assert workspace_for(two) == two.resolve()  # ambiguous and none configured: where we were started
    (two / "b" / ".pcp").mkdir()
    (two / "b" / ".pcp" / "config.toml").write_text("", encoding="utf-8")
    assert workspace_for(two) == (two / "b").resolve()
    plain = tmp_path / "plain"
    plain.mkdir()
    assert workspace_for(plain) == plain.resolve()


def test_run_state_goes_to_the_project_and_is_ignored(tmp_path: Path) -> None:
    repo, proj = _repo(tmp_path)
    server = PcpServer(repo)
    try:
        dx = diagnose_structured("done.", "No such goal.", IrisGoal(goal="True"))
        assert record_diagnosis(server.workspace, dx)
    finally:
        server.close()
    assert (proj / ".pcp" / "diagnoses.jsonl").is_file() and not (repo / ".pcp").exists()
    assert (proj / ".pcp" / ".gitignore").read_text(encoding="utf-8") == INNER_IGNORE
    # Never clobbers an ignore file the user wrote.
    mine = tmp_path / "mine"
    (mine / ".pcp").mkdir(parents=True)
    (mine / ".pcp" / ".gitignore").write_text("custom\n", encoding="utf-8")
    assert state_dir(mine) == mine / ".pcp"
    assert (mine / ".pcp" / ".gitignore").read_text(encoding="utf-8") == "custom\n"


# ------------------------------------------------------------ fakes for the tools


def _goal(text: str, *hyps: Hyp) -> IrisGoal:
    return IrisGoal(goal=text, spatial=list(hyps))


class _ChainTracer:
    """Steps like ``Tracer.step``: a failure records the goals it met and stays put."""

    def __init__(self, fail_on: str | None, error: str = "No applicable tactic.") -> None:
        self.trace = Trace(file="x.v", thm="t")
        self.trace.steps.append(Step(step=0, state_id=1, tactic="<start>", goals=[_goal("WP e {{ v, Φ v }}")]))
        self.fail_on, self.error = fail_on, error
        self.ran: list[str] = []
        self.last_result = None

    def step(self, tactic: str) -> Step:
        self.ran.append(tactic)
        n = len(self.trace.steps)
        prev = self.trace.steps[-1].goals
        if tactic == self.fail_on:
            step = Step(step=n, state_id=-1, tactic=tactic, goals=prev, ok=False, error=self.error)
            self.trace.failed_at, self.trace.error = n, self.error
        else:
            step = Step(step=n, state_id=n + 1, tactic=tactic, goals=[_goal(f"G after {tactic}")])
            self.trace.failed_at = self.trace.error = None
        self.trace.steps.append(step)
        return step

    def hidden_at(self, step: Step) -> None:
        return None


def _session(server: PcpServer, tracer: Any, sid: str = "s1", **attrs: Any) -> SessionRecord:
    session = SimpleNamespace(source_file=str(server.workspace / "x.v"), thm="t", pool=None, close=lambda: None, **attrs)
    rec = SessionRecord(sid, session=session, tracer=tracer)  # type: ignore[arg-type]
    server._sessions[sid] = rec
    return rec


# ------------------------------------------------ 23: a chain names its failure


def test_a_multi_sentence_step_reports_the_failing_sentence(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    tracer = _ChainTracer(fail_on="wp_pures.")
    _session(server, tracer)
    out = server.proof_step("s1", "rewrite /f. wp_store. wp_pures. iApply \"HΦ\"")
    assert tracer.ran == ["rewrite /f.", "wp_store.", "wp_pures."]  # stops at the failure
    assert out["ok"] is False and out["chain"] == {"sentences": 4, "failed": 3, "committed": 2, "sentence": "wp_pures."}
    assert out["what"].startswith("sentence 3/4 of the chain: `wp_pures.` failed at step 3")
    assert out["where"]["sentence"] == "wp_pures." and out["step"] == 3
    # The goal it met is the one after `wp_store`, not the one before the chain.
    assert "G after wp_store." in out["goal"][0]
    assert "sentences 1-2 were committed (steps 1-2)" in out["next"][0]
    server.close()


def test_a_multi_sentence_step_that_succeeds_commits_every_sentence(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    tracer = _ChainTracer(fail_on=None)
    _session(server, tracer)
    out = server.proof_step("s1", "- wp_store. wp_pures.")
    assert tracer.ran == ["-", "wp_store.", "wp_pures."]
    assert out["ok"] is True and out["chain"] == {"sentences": 3, "committed": 3, "steps": [1, 3]}
    assert out["step"] == 3 and "G after wp_pures." in out["goal"][0]
    one = _ChainTracer(fail_on=None)
    _session(server, one, "s2")
    assert "chain" not in server.proof_step("s2", "wp_store.") and one.ran == ["wp_store."]
    server.close()


# ------------------------------------------------------- 20: trace answer size


def _long_trace(n: int, *, fail: bool) -> _ChainTracer:
    tracer = _ChainTracer(fail_on=f"t{n}." if fail else None)
    for i in range(1, n + 1):
        tracer.step(f"t{i}.")
        tracer.trace.events.append(SimpleNamespace(step=i, detail="", render=lambda i=i: f"step {i} · intro"))
    return tracer


def test_a_trace_answer_keeps_only_the_events_near_its_end(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    f = tmp_path / "x.v"
    f.write_text("Lemma t : True. Proof. exact I. Qed.\n", encoding="utf-8")
    rec = _session(server, _long_trace(40, fail=True))
    out = server._trace_result(rec, f, "t", reused=None, saved_ms=0)
    assert out["ok"] is False and out["events_total"] == 40
    assert out["events"] == [f"step {i} · intro" for i in range(36, 41)]
    # The goal and the error are the block's; `failure` does not repeat them.
    assert "goal" not in out["failure"] and "error" not in out["failure"] and out["goal"] and out["error"]
    assert any('proof_ledger("s1", "events")' in n for n in out["next"])
    assert len(server._trace_result(rec, f, "t", reused=None, saved_ms=0, events="all")["events"]) == 40
    assert server._trace_result(rec, f, "t", reused=None, saved_ms=0, events="none")["events"] == []
    done = _session(server, _long_trace(12, fail=False), "s2")
    ok = server._trace_result(done, f, "t", reused=None, saved_ms=0)
    assert ok["ok"] is True and [e.split()[1] for e in ok["events"]] == ["8", "9", "10", "11", "12"]
    bad = server.proof_trace("x.v", "t", events="most")
    assert bad["ok"] is False and "one of near, all, none" in bad["what"]
    server.close()


# --------------------------------------------------------- 22: proof_try rows


def test_a_failed_candidate_says_how_it_differs_from_a_survivor() -> None:
    failed = 'iAssert (P) with "AU" as "AU"; first (rewrite /AU_sc; iExact "AU").'
    good = 'iAssert (P) with "[AU]" as "AU"; first (rewrite /AU_sc /=; iExact "AU").'
    c = compare(failed, good)
    assert c is not None and c["differs"] == '`"AU"` → `"[AU]"`; adds `/=`'
    assert any("up to `simpl`" in w for w in c["why"]) and any("spec pattern" in w for w in c["why"])
    assert compare("lia.", "iFrame. iApply foo. done. by eauto.") is None  # not variants
    assert compare("lia.", "rewrite array_cons.") is None  # two different attempts, not a variant
    assert closest_survivor("iExact \"H\".", ["lia.", "iExact \"H\" //."])["differs"] == "adds `//`"


def test_proof_try_rows_carry_the_difference(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    no = SimpleNamespace(ok=False, error="iExact: \"AU\" : P does not match", proof_finished=False, state_id=-1,
                         timed_out=False, state=None)
    yes = SimpleNamespace(ok=True, error=None, proof_finished=True, state_id=5, timed_out=False, state=None)
    _session(server, _ChainTracer(None), try_many=lambda batch: [no, yes])
    out = server.proof_try("s1", ['iExact "AU"', 'rewrite /= ; iExact "AU"'])
    row = out["results"][0]
    assert row["vs_survivor"]["survivor"] == 'rewrite /= ; iExact "AU".' and "up to `simpl`" in row["vs_survivor"]["why"][0]
    assert "vs_survivor" not in out["results"][1]
    json.dumps(out)
    server.close()


# ------------------------------------------------------------ 21: diagnoses


def test_a_hypothesis_under_a_later_over_a_match_is_named() -> None:
    hm = Hyp("HM", "▷ match o with Some p => Managed γ p | None => True end")
    dx = diagnose_structured('iApply (shield_validate with "HM").', "Unable to unify \"Managed γ ?p\" with ...",
                             _goal("|={⊤}=> Φ #()", hm))
    assert dx.repair == "strip-later" and dx.confidence == "high"
    assert '"HM" is under a later' in dx.text and "destruct its scrutinee" in dx.text
    plain = diagnose_structured('iApply (shield_validate with "HM").', "Unable to unify",
                                _goal("|={⊤}=> Φ #()", Hyp("HM", "▷ Managed γ p")))
    assert plain.repair == "strip-later" and "strip it first" in plain.text
    # Destructing a later over a sep is fine: no later diagnosis.
    split = diagnose_structured('iDestruct "HM" as "[A B]".', "some other failure",
                                _goal("P", Hyp("HM", "▷ (A ∗ B)")))
    assert split.repair != "strip-later"


def test_a_timeout_against_a_beta_redex_is_diagnosed() -> None:
    assert beta_redexes("WP e {{ v, (λ b : bool, if b then P else Q) false }}") == [
        "(λ b : bool, if b then P else Q) false"]
    assert beta_redexes("(λ x, x) ∗ P") == []
    dx = diagnose_structured('iApply ("HQ" with "[$]").', "Timeout!", _goal("(λ b, if b then P else Q) false"))
    assert dx.repair == "beta-reduce" and dx.confidence == "high" and "`cbn beta`" in dx.text and "$!" in dx.text


def test_the_previous_tactic_already_did_it() -> None:
    wp = diagnose_structured("wp_pures.", "No applicable tactic.", _goal("|={⊤}=> Φ #()"))
    assert wp.repair == "already-simplified" and "no longer contains a WP" in wp.text and "`iModIntro`" in wp.text
    rw = diagnose_structured("rewrite Nat.add_0_r.", 'Found no subterm matching "?n + 0" in the current goal.',
                             _goal("x = y"))
    assert rw.repair == "already-simplified" and "no longer contains `?n + 0`" in rw.text
    gone = diagnose_structured("lia.", "No such goal.", _goal("x = y"))
    assert gone.repair == "bullet" and "already discharged this side goal" in gone.text


def test_a_timed_out_step_surfaces_a_confident_diagnosis(tmp_path: Path) -> None:
    server = PcpServer(tmp_path)
    tracer = _ChainTracer(fail_on='iApply ("HQ" with "[$]").', error="Timeout!")
    tracer.trace.steps[0].goals[:] = [_goal("(λ b, if b then P else Q) false")]
    _session(server, tracer)
    out = server.proof_step("s1", 'iApply ("HQ" with "[$]")')
    assert out["timed_out"] is True and out["diagnosis_class"] == "beta-reduce"
    assert out["next"][0].startswith("`diagnosis` names the likely cause (beta-reduce")
    server.close()
