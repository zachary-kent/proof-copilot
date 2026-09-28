"""Failure reporting against real Rocq and petanque (issues 4, 10, 11, 15; D4).

Small documents in a temp workspace, so nothing touches the corpus: a broken
``Require`` before the lemma, a statement that does not elaborate, a prefix that
diverges, a ``Z`` equality that prints like a ``nat`` one.
"""

from __future__ import annotations

import time
from pathlib import Path

import pytest
from conftest import needs_petanque, needs_rocq

from pcp.rocq.errors import check_prefix

pytest.importorskip("pytanque")

BROKEN_REQUIRE = """From Stdlib Require Import ZArith.

Lemma before : True.
Proof.
  exact I.
Qed.

From ws Require Import Missing.

Lemma after : Missing.foo = 1.
Proof. reflexivity. Qed.
"""

BAD_STATEMENT = """Lemma ok : True.
Proof. exact I. Qed.

Lemma bad {A B : Type} (x : list A) (f : list B -> Prop) : f x.
Proof. Admitted.
"""

#: A definition before the lemma that takes hours to elaborate (10^12 iterations in
#: constant memory): statements-only twins keep it, so ``start`` cannot end in time.
DIVERGES = """From Stdlib Require Import PArith.
Definition spin := Eval vm_compute in Pos.iter (fun b : bool => negb b) true 1000000000000%positive.

Lemma target : spin = spin.
Proof. reflexivity. Qed.
"""

COERCED = """From Stdlib Require Import ZArith.
Open Scope Z_scope.
Coercion Z.of_nat : nat >-> Z.  (* as std++ declares it *)

Lemma coe (sq2 k : nat) (Heq : Z.of_nat sq2 = Z.of_nat k) (Hn : (sq2 = k)%nat) : (sq2 + 0 = k)%nat.
Proof.
  rewrite Nat.add_0_r.
  exact Heq.
Qed.

Lemma other : True.
Proof. exact I. Qed.
"""


@pytest.fixture
def ws(tmp_path: Path) -> Path:
    (tmp_path / "_CoqProject").write_text("-Q . ws\n", encoding="utf-8")
    for name, text in (("Req.v", BROKEN_REQUIRE), ("Stmt.v", BAD_STATEMENT), ("Spin.v", DIVERGES), ("Coe.v", COERCED)):
        (tmp_path / name).write_text(text, encoding="utf-8")
    return tmp_path


@needs_rocq
def test_check_prefix_names_the_failing_require_and_the_bad_statement(ws: Path) -> None:
    req = check_prefix(ws / "Req.v", "after")
    assert req is not None and not req.ok and req.line == 8 and not req.in_statement
    assert req.sentence == "From ws Require Import Missing." and "Missing" in req.message
    assert req.render().startswith("the document does not check before after: Req.v:8 `From ws Require Import Missing.`")
    stmt = check_prefix(ws / "Stmt.v", "bad")
    assert stmt is not None and stmt.in_statement and stmt.line == 4 and 'expected to have type "list B"' in stmt.message
    assert check_prefix(ws / "Req.v", "before").ok


@needs_rocq
def test_check_prefix_timeout_names_the_running_sentence(ws: Path) -> None:
    spin = check_prefix(ws / "Spin.v", "target", timeout=3)
    assert spin is not None and spin.timed_out and spin.line == 2 and spin.sentence.startswith("Definition spin")


@needs_petanque
def test_proof_open_reports_the_first_error_before_the_lemma(ws: Path) -> None:
    from pcp.mcp.server import PcpServer

    server = PcpServer(ws, pool_size=1)
    try:
        out = server.proof_open("Req.v", "after")
        assert out["ok"] is False and out["timed_out"] is False
        assert out["error"].startswith("the document does not check before after: Req.v:8 `From ws Require Import Missing.`")
        assert "petanque said:" in out["error"]  # the original symptom is kept
        stmt = server.proof_open("Stmt.v", "bad")
        assert stmt["error"].startswith("the statement of bad does not elaborate: Stmt.v:4")
        assert server.proof_open("Coe.v", "missing")["error"].startswith("Coe.v declares no `missing`")
    finally:
        server.close()


@needs_petanque
def test_a_diverging_prefix_is_a_timeout_result_and_never_wedges_the_pool(ws: Path) -> None:
    """D4: a start that hits its wall clock is reported, and the next open just works."""
    from pcp.state.pool import SessionPool
    from pcp.state.trace import Tracer

    pool = SessionPool(ws, size=1, start_timeout=4.0)
    try:
        started = time.monotonic()
        with pytest.raises(Exception) as exc:
            Tracer(pool.open(ws / "Spin.v", "target", stub_prefix=True)).start()
        message = str(exc.value)
        assert getattr(exc.value, "timed_out", False), message
        assert message.startswith("the document does not check up to target within 4 s")
        assert "coqc was still checking Spin.v:2 `Definition spin" in message
        assert time.monotonic() - started < 60
        fresh = Tracer(pool.open(ws / "Coe.v", "other", stub_prefix=True))
        assert fresh.start() and pool.processes[0].alive()
    finally:
        pool.close()


@needs_petanque
def test_trace_failure_and_hidden_coercions_end_to_end(ws: Path) -> None:
    from pcp.mcp.server import PcpServer

    server = PcpServer(ws, pool_size=1)
    try:
        out = server.proof_trace("Coe.v", "coe")
        failure = out["failure"]
        assert out["steps"] == 2 and failure["step"] == 2
        assert (failure["sentence"], failure["line"], failure["column"], failure["file"]) == ("exact Heq.", 8, 3, "Coe.v")
        assert "@eq Z (Z.of_nat sq2) (Z.of_nat k)" in failure["error"]
        # The goal it was applied to, with the coercion that made `exact Heq` wrong spelled out.
        (goal,) = failure["goal"]
        assert '"Heq" : sq2 = k   [= at Z]' in goal and "↳ with coercions (Z.of_nat): Z.of_nat sq2 =@{Z} Z.of_nat k" in goal
        assert '"Hn" : sq2 = k   [= at nat]' in goal and goal.count("↳") == 1
        state = server.proof_state(out["session"])
        assert state["step"] == failure["step"] and state["ok"] is False
        picked = server.proof_state(out["session"], select="Heq", diff_only=False)["goals"][0]
        assert "↳ with coercions (Z.of_nat)" in picked and '"Hn"' not in picked
        opened = server.proof_open("Coe.v", "coe")
        step = server.proof_step(opened["session"], "rewrite Nat.add_0_r.")
        assert step["ok"] and "Heq=unchanged" in step["goal"][0]  # diff-only is untouched by the marks
    finally:
        server.close()
