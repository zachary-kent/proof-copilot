(* The user's plan: the children the root is proved from.

   A plan is not prose -- it is Rocq, so the no-gap rule has something to check.
   These statements are inserted into the development inside the root's section, so
   they inherit its `Context`; they carry no section of their own. *)

Lemma canary_swap (A B : PROP) : A ∗ B -∗ B ∗ A.
Proof. Admitted.

Lemma canary_assoc (A B C : PROP) : A ∗ (B ∗ C) -∗ (A ∗ B) ∗ C.
Proof. Admitted.
