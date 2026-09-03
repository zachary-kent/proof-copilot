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
Proof.
admit.
Qed.
End basics.
