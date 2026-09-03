(* A scratch Iris development: the smallest thing that exercises every shape
   pcp's state layer has to read -- spatial and intuitionistic contexts, masks,
   laters, existentials, heap_lang weakest preconditions. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import lang proofmode notation.

Set Default Proof Using "Type".

Section basics.
  Context `{!heapGS Σ}.
  Implicit Types l : loc.

  Lemma sep_comm (P Q : iProp Σ) : P ∗ Q -∗ Q ∗ P.
  Proof. iIntros "[HP HQ]". iFrame. Qed.

  Lemma destruct_nested (P Q R : iProp Σ) : P ∗ (Q ∗ R) -∗ R ∗ Q ∗ P.
  Proof. iIntros "[HP [HQ HR]]". iFrame. Qed.

  Lemma exists_pure (Φ : nat → iProp Σ) :
    (∃ n, ⌜n = 3⌝ ∗ Φ n) -∗ Φ 3.
  Proof. iIntros "H". iDestruct "H" as (n) "[%Hn HΦ]". subst. iFrame. Qed.

  Lemma persist_dup (P : iProp Σ) : □ P -∗ P ∗ P.
  Proof. iIntros "#HP". iFrame "HP". Qed.

  Lemma load_twice l (v : val) :
    l ↦ v -∗ WP (! #l);; (! #l) {{ w, ⌜w = v⌝ ∗ l ↦ v }}.
  Proof.
    iIntros "Hl". wp_load. wp_seq. wp_load. iFrame. done.
  Qed.

  Lemma inv_open (N : namespace) (P : iProp Σ) :
    inv N P ={⊤}=∗ True.
  Proof.
    iIntros "#Hinv". iInv "Hinv" as "HP" "Hclose".
    iMod ("Hclose" with "HP") as "_". done.
  Qed.

End basics.

Section overstrong.
  Context `{!heapGS Σ}.

  (* An over-strong statement: `Hn` is never needed.  The gate's unused-premise
     report is meant to catch exactly this, before it becomes a `weaken` fight. *)
  Lemma over_strong (n : nat) (Hn : n > 0) (P : iProp Σ) : P -∗ P.
  Proof. iIntros "HP". iFrame. Qed.

End overstrong.
