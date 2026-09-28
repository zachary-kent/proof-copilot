(* Invariants and WP goals for the shape assertions and the invariant-opening helper
   (tests/test_shape.py, tests/test_invariant.py).  Every lemma stops right after
   `iIntros`; the tests step that one tactic and probe from there. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import lang proofmode notation.

Section inv.
  Context `{!heapGS Σ}.
  Let N := nroot .@ "cnt".

  (* Two timeless points-to, two pure facts, and one non-timeless wand.  (Only notation
     shared by Iris 4.5 and Iris dev: `ghost_var`'s fraction changed type in between.) *)
  Definition cnt_inv (k l : loc) : iProp Σ :=
    ∃ (n : Z) (m : nat), l ↦ #n ∗ k ↦{#1/2} #n ∗ ⌜0 ≤ n⌝%Z ∗ ▷ (True -∗ True) ∗ ⌜m = m⌝.

  Definition is_cnt (k l : loc) : iProp Σ := inv N (cnt_inv k l).

  (* The address-offset form an agent restates wrong: `l +ₗ (0 + 1)`, not `l +ₗ 1`. *)
  Lemma offset_goal k l :
    inv N (cnt_inv k l) -∗ WP ! #(l +ₗ (0 + 1)) ;; ! #l {{ v, True }}.
  Proof. iIntros "#Hinv". Admitted.

  Lemma load_goal k l :
    inv N (cnt_inv k l) -∗ WP ! #l {{ v, True }}.
  Proof. iIntros "#Hinv". Admitted.

  (* `n` is taken by the lemma and `"Hl"` by a hypothesis: the pattern must avoid both. *)
  Lemma raw_goal k l (n : Z) :
    inv N (∃ n : Z, l ↦ #n ∗ k ↦{#1/2} #n) -∗ l ↦ #n -∗ |={⊤}=> True.
  Proof. iIntros "#Hinv Hl". Admitted.

  Lemma named_goal k l :
    is_cnt k l -∗ |={⊤}=> True.
  Proof. iIntros "#Hc". Admitted.

  Lemma opaque_goal (P : iProp Σ) :
    inv N P -∗ |={⊤}=> True.
  Proof. iIntros "#HI". Admitted.
End inv.
