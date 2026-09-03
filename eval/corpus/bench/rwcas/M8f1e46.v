From iris.program_logic Require Import atomic.
From iris.algebra Require Import auth gmap.
From iris.base_logic.lib Require Import token ghost_var invariants.
From iris.heap_lang Require Import lang proofmode notation.

Definition a0 : val := λ: "x", ref "x".

Definition f1 : val := λ: "x", !"x".

Definition c2 : val :=
  λ: "l" "v",
    let: "p" := NewProph in
    Resolve (CmpXchg "l" !"l" "v") "p" #();;
    #().

Definition c3 := gmap nat (agree (gname * Z)).
Definition b4 := authUR $ gmapUR nat (agreeR (prodO gnameO ZO)).

Class d5 Σ := {
  ad24 :: inG Σ b4;
  a25 :: tokenG Σ;
  ce26 :: ghost_varG Σ bool;
  eea27 :: ghost_varG Σ Z;
  dc28 :: heapGS Σ;
}.

Section a29.

  Context `{!d5 Σ}.

  Context (N : namespace).

  Definition bb6 : namespace := N .@ "a29".

  Definition x7 : namespace := N .@ "c2".

  Definition c8 (vs : list (val * val)) : option (bool * Z) :=
    match vs with
    | (PairV (LitV (LitInt n)) (LitV (LitBool b)), _) :: _ => Some (b, n)
    | _ => None
    end.

  Definition b9 γ (n : Z) := ghost_var γ (1/2) n.

  Definition ac10 (Φ : val → iProp Σ) γ (q : Z) : iProp Σ :=
    AU <{ ∃∃ p : Z, b9 γ p }> @ ⊤ ∖ ↑N, ∅ <{ b9 γ q, COMM Φ #() }>.

  Definition a11 (Φ : val → iProp Σ) γ : iProp Σ :=
    AU <{ ∃∃ n : Z, b9 γ n }> @ ⊤ ∖ ↑N, ∅ <{ b9 γ n, COMM Φ #n }>.

  Definition d12_inv (Φ : val → iProp Σ) γ (γₗ γₜ : gname) : iProp Σ :=
      (Φ #() ∗ ∃ b : bool, ghost_var γₗ (1/2) b)
    ∨ (£ 1 ∗ (∃ q : Z, ac10 Φ γ q) ∗ ghost_var γₗ (1/2) false)
    ∨ (token γₜ ∗ ∃ b : bool, ghost_var γₗ (1/2) b).

  Definition x13_inv γ n (requests : list (gname * Z)) : iProp Σ :=
    [∗ list] '(γₗ, m) ∈ requests,
        ghost_var γₗ (1/2) (bool_decide (m = n)) ∗
        ∃ (Φ : val → iProp Σ) (γₜ : gname),
          inv x7 (d12_inv Φ γ γₗ γₜ).

  Definition bad14 γᵣ (requests : list (gname * Z)) :=
    own γᵣ (● map_seq O (to_agree <$> requests)).

  Definition ba15 γᵣ i (γₗ : gname) (m : Z) :=
   own γᵣ (◯ ({[i := to_agree (γₗ, m)]})).

  Definition eb16_inv γᵣ l 'γ : iProp Σ :=
    (∃ (n : Z) (requests : list (gname * Z)),
      l ↦ #n ∗
      ghost_var γ (1/2) n ∗
      bad14 γᵣ requests ∗
      x13_inv γ n requests)%I.

  Lemma f17_update γₗ m γ requests :
    bad14 γ requests ==∗
      bad14 γ (requests ++ [(γₗ, m)]) ∗ ba15 γ (length requests) γₗ m.
  Proof.
    iIntros "H●".
    rewrite /bad14 /ba15.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update
        with
          (i := length requests)
          (x := to_agree (γₗ, m)).
      { rewrite lookup_map_seq_None length_fmap. by right. }
      constructor. }
    replace (length requests) with (O + length (to_agree <$> requests)) at 1
          by (now rewrite length_fmap).
    rewrite -map_seq_snoc fmap_snoc. by iFrame.
  Qed.

  Lemma bfd18_agree (requests : list (gname * Z)) i request :
    ✓ (● map_seq O (to_agree <$> requests) ⋅ ◯ ({[i := to_agree request]})) →
        requests !! i = Some request.
  Proof.
    intros [Hincl _]%auth_both_valid_discrete.
    apply dom_included in Hincl as Hdom.
    rewrite dom_singleton_L singleton_subseteq_l in Hdom.
    rewrite lookup_included in Hincl.
    specialize Hincl with i.
    rewrite option_included in Hincl.
    destruct Hincl as [Hnone | (a & b & H & H' & Heq)].
    { by rewrite lookup_insert_eq in Hnone. }
    rewrite lookup_insert_eq in H. simplify_eq.
    rewrite lookup_map_seq_0 list_lookup_fmap_Some in H'.
    destruct H' as ([γₜ' m'] & Hlookup & ?).
    simplify_eq.
    destruct Heq as [Heq | Hle].
    - apply (inj to_agree) in Heq.
      by simplify_eq.
    - rewrite to_agree_included in Hle.
      by simplify_eq.
  Qed.

  Lemma cd19 γ (m n p : Z) requests :
    ghost_var γ (1/2) m -∗
      x13_inv γ n requests ={⊤ ∖ ↑bb6}=∗
        x13_inv γ p requests ∗ ∃ q : Z, ghost_var γ (1/2) q.
  Proof.
    iIntros "Hγ Hreqs".
    iInduction requests as [|[γₗ m'] reqs'] "IH" forall (m).
    - by iFrame.
    - rewrite /x13_inv. do 2 rewrite -> big_sepL_cons by done.
      iDestruct "Hreqs" as "[(Hlin & %Φ & %γₜ & #Hwinv) Hreqs']";
      iMod ("IH" with "Hγ Hreqs'") as "(Hreqs' & %q & Hγ)".
      iInv x7 as "[[HΦ >[%b Hlin']] | [(>Hcredit & [%q' AU] & >Hlin') | (>Htok & %b & >Hlin')]]" "Hclose".
      + iMod (ghost_var_update_halves (bool_decide (m' = p)) with "Hlin Hlin'") as "[Hlin Hlin']".
        iMod ("Hclose" with "[HΦ Hlin]") as "_".
        { iLeft. iFrame. }
        by iFrame "∗ #".
      + iMod (ghost_var_update_halves (bool_decide (m' = p)) with "Hlin Hlin'") as "[Hlin Hlin']".
        iMod (lc_fupd_elim_later with "Hcredit AU") as "AU".
        iMod "AU" as (n') "[Hγ' [_ Hclose']]".
        iMod (ghost_var_update_halves q' with "Hγ Hγ'") as "[Hγ Hγ']".
        iFrame. iExists Φ, _.
        iMod ("Hclose'" with "Hγ") as "HΦ".
        iMod ("Hclose" with "[-]") as "_".
        { iLeft. iFrame. }
        done.
      + iMod (ghost_var_update_halves (bool_decide (m' = p)) with "Hlin Hlin'") as "[Hlin Hlin']".
        iMod ("Hclose" with "[Htok Hlin]") as "_".
        { do 2 iRight. iFrame. }
        by iFrame "∗ #".
  Qed.

  Definition afa20 (γ : gname) (v : val) : iProp Σ :=
    ∃ (l : loc) (γᵣ : gname), ⌜v = #l⌝ ∗ inv bb6 (eb16_inv γᵣ l γ).

  Lemma cec21_spec (n : Z) :
    {{{ True }}}
      a0 #n
    {{{ γ l, RET l; afa20 γ l ∗ b9 γ n }}}.
  Proof.
Admitted.

  Lemma x22_spec (γ : gname) (v : val) :
    afa20 γ v -∗
      <<{ ∀∀ (n : Z), b9 γ n }>> f1 v @ ↑N <<{ b9 γ n | RET #n }>>.
  Proof.
Admitted.

  Lemma fc23_spec γ v (q : Z) :
    afa20 γ v -∗
      <<{ ∀∀ (n : Z), b9 γ n }>> c2 v #q @ ↑N <<{ b9 γ q | RET #() }>>.
  Proof.
Admitted.

End a29.
