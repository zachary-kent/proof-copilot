(* Failure mode #1, premature consumption, in its smallest honest form.

   `iDestruct "H" as "[H1 H2]"` splits a resource early; a later step needs the
   whole of it back.  The agent sees "H is gone" and starts guessing.  The ledger
   is supposed to answer *when* it went away and *what* it became. *)
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import lang proofmode notation.

Set Default Proof Using "Type".

Section blame.
  Context `{!heapGS Σ}.

  (* The prover destructs, frames one half, and then needs it again. *)
  Lemma premature_consumption (P Q R : iProp Σ) :
    (P ∗ Q) ∗ R -∗ (P ∗ Q) ∗ R.
  Proof.
    iIntros "[[HP HQ] HR]". iFrame.
  Qed.

  Lemma persistent_is_not_consumed (P Q : iProp Σ) :
    □ P ∗ Q -∗ P ∗ P ∗ Q.
  Proof.
    iIntros "[#HP HQ]". iFrame "HP". iFrame.
  Qed.

  Lemma leftover_spatial (P Q : iProp Σ) :
    P ∗ Q -∗ P.
  Proof.
    iIntros "[HP HQ]". iFrame.
  Qed.

End blame.
