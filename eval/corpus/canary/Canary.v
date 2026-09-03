(** The permanent canary (PLAN.md 8.11).

    One golden end-to-end run: a known lemma, a known plan, scripted workers.  It
    executes in CI and before every release, and speculative features are not allowed
    to break it.  The proofs are deliberately trivial -- what is under test is the
    *loop* (freeze, parallel dispatch, gate, retry, resume, integrate), not Iris. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import base_logic.

Set Default Proof Using "Type".

Section canary.
  Context {PROP : bi}.
  Implicit Types P Q R : PROP.

  Lemma canary_main P Q R : P ∗ Q ∗ R -∗ R ∗ Q ∗ P.
  Proof.
    iIntros "[HP [HQ HR]]". iFrame.
  Qed.

End canary.
