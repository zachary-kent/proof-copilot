From iris.program_logic Require Import atomic.
From iris.algebra Require Import auth gmap list lib.mono_nat.
From iris.base_logic.lib Require Import token ghost_var mono_nat invariants.
From iris.heap_lang Require Import lang proofmode notation lib.array.
Import derived_laws.bi.
Require Import Stdlib.ZArith.Zquot.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Require Import Arith ZArith ZifyClasses ZifyInst Lia.

Global Program Instance da0 : BinOp Nat.modulo :=
  {| TBOp := Z.modulo ; TBOpInj := Nat2Z.inj_mod |}.
Add Zify BinOp da0.

Global Program Instance cb1 : BinOp Nat.div :=
  {| TBOp := Z.div ; TBOpInj := Nat2Z.inj_div |}.
Add Zify BinOp cb1.

Require Import stdpp.sorting.

Definition bcaf2 (n : nat) : val :=
  λ: "src",
    let: "dst" := AllocN #(S n) #0 in
    array_copy_to ("dst" +ₗ #1) "src" #n;;
    "dst".

Definition x3 : val :=
  rec: "loop" "l" "v" :=
    if: !"l" = "v" then "loop" "l" "v"
    else #().

Definition c4 (n : nat) : val :=
  λ: "l" "src",
    let: "ver" := !"l" in
    if: "ver" `rem` #2 = #1 then

      x3 "l" "ver"
    else
      let: "res" := CmpXchg "l" "ver" (#1 + "ver") in
      if: Snd "res" then

        array_copy_to ("l" +ₗ #1) "src" #n;;

        "l" <- #2 + "ver"
      else

        let: "ver'" := Fst "res" in
        if: "ver'" = #1 + "ver" then

          x3 "l" "ver'"
        else

          #().

Definition f5 (n : nat) : val :=
  rec: "f5" "l" :=
    let: "ver" := !"l" in
    if: "ver" `rem` #2 = #1 then

      "f5" "l"
    else

      let: "data" := array_clone ("l" +ₗ #1) #n in
      if: !"l" = "ver" then

        "data"
      else

        "f5" "l".

Definition d6 := gmap nat $ agree $ list val.

Definition x7 := authUR $ gmapUR nat $ agreeR $ listO valO.

Definition c8 := gmap nat $ agree (gname * nat).
Definition b9 := authUR $ gmapUR nat $ agreeR $ prodO gnameO natO.

Class fbe10 (Σ : gFunctors) := {
  x52 :: heapGS Σ;
  e53 :: inG Σ x7;
  ba54 :: inG Σ b9;
  fbc55 :: mono_natG Σ;
  b56 :: ghost_varG Σ (list val);
  d57 :: ghost_varG Σ bool;
  dea58 :: tokenG Σ;
}.

Section a59.
  Context `{!fbe10 Σ, !heapGS Σ}.

  Context (N : namespace).

  Definition fb11 := N .@ "a59".

  Definition x12 := N .@ "c4".

  Definition x13_own γᵥ (q : Qp) (d6 : list (list val)) := own γᵥ (●{#q} map_seq 0 (to_agree <$> d6)).

  Definition b14 γᵥ (vs : list val) : iProp Σ := ghost_var γᵥ (1/2) vs.

  Definition a15_own γₕ i (b14 : list val) := own γₕ (◯ {[i := to_agree b14]}).

  Lemma ef16_update (b14 : list val) γₕ (d6 : list (list val)) :
    x13_own γₕ 1 d6 ==∗
      x13_own γₕ 1 (d6 ++ [b14]) ∗ a15_own γₕ (length d6) b14.
  Proof.
    iIntros "H●".
    rewrite /x13_own /a15_own.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update
        with
          (i := length d6)
          (x := to_agree b14).
      { rewrite lookup_map_seq_None length_fmap. by right. }
      constructor. }
    replace (length d6) with (O + length (to_agree <$> d6)) at 1
          by (now rewrite length_fmap).
    rewrite -map_seq_snoc fmap_snoc. by iFrame.
  Qed.

  Lemma ff17_alloc i b14 γₕ d6 q :
    d6 !! i = Some b14 →
      x13_own γₕ q d6 ==∗
        x13_own γₕ q d6 ∗ a15_own γₕ i b14.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[i := to_agree b14]}).
      { apply _. }
      apply singleton_included_l with (i := i).
      exists (to_agree b14). split; last done.
      rewrite lookup_map_seq_0 list_lookup_fmap Hlookup //. }
    by iFrame.
  Qed.

  Lemma c18_agree γₕ q d6 i b14 :
    x13_own γₕ q d6 -∗
      a15_own γₕ i b14 -∗
        ⌜d6 !! i = Some b14⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    rewrite -list_lookup_fmap /= -lookup_map_seq_0 Hvs'' //.
  Qed.

  Definition bad19 γᵣ (requests : list (gname * nat)) :=
    own γᵣ (● map_seq O (to_agree <$> requests)).

  Definition ba20 γᵣ i (γₗ : gname) (ver : nat) :=
   own γᵣ (◯ ({[i := to_agree (γₗ, ver)]})).

  Lemma f21_update γₗ ver γ requests :
    bad19 γ requests ==∗
      bad19 γ (requests ++ [(γₗ, ver)]) ∗ ba20 γ (length requests) γₗ ver.
  Proof.
    iIntros "H●".
    rewrite /bad19 /ba20.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update
        with
          (i := length requests)
          (x := to_agree (γₗ, ver)).
      { rewrite lookup_map_seq_None length_fmap. by right. }
      constructor. }
    replace (length requests) with (O + length (to_agree <$> requests)) at 1
          by (now rewrite length_fmap).
    rewrite -map_seq_snoc fmap_snoc. by iFrame.
  Qed.

  Lemma bfd22_agree γᵣ (requests : list (gname * nat)) (i : nat) γₗ ver :
    bad19 γᵣ requests -∗
      ba20 γᵣ i γₗ ver -∗
        ⌜requests !! i = Some (γₗ, ver)⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    rewrite -list_lookup_fmap /= -lookup_map_seq_0 Hvs'' //.
  Qed.

  Definition ac23 (Φ : val → iProp Σ) γ (vs' : list val) (src : loc) dq : iProp Σ :=
       AU <{ ∃∃ vs : list val, b14 γ vs }>
            @ ⊤ ∖ ↑N, ∅
          <{ b14 γ vs', COMM src ↦∗{dq} vs' -∗ Φ #() }>.

  Definition d24_inv (Φ : val → iProp Σ) (γ γₗ γₜ : gname) (src : loc) (dq : dfrac) (vs' : list val) : iProp Σ :=
      ((src ↦∗{dq} vs' -∗ Φ #()) ∗ ghost_var γₗ (1/2) false)
    ∨ (£ 1 ∗ ac23 Φ γ vs' src dq ∗ ghost_var γₗ (1/2) true)
    ∨ (token γₜ ∗ ∃ b : bool, ghost_var γₗ (1/2) b).

  Definition ad25_inv γ γₗ ver ver' : iProp Σ :=
    ghost_var γₗ (1/2) (bool_decide (ver < ver')) ∗
    ∃ (Φ : val → iProp Σ) (γₜ : gname) (src : loc) (dq : dfrac) (vs : list val),
      inv x12 (d24_inv Φ γ γₗ γₜ src dq vs).

  Definition x26_inv γ ver (requests : list (gname * nat)) : iProp Σ :=
    [∗ list] '(γₗ, ver') ∈ requests, ad25_inv γ γₗ ver ver'.

  Lemma cd27 γ (ver : nat) (vs : list val) requests :
    ghost_var γ (1/2) vs -∗
      x26_inv γ ver requests ={⊤ ∖ ↑fb11}=∗
        x26_inv γ (S ver) requests ∗ ∃ vs' : list val, ghost_var γ (1/2) vs'.
  Proof.
    iIntros "Hγ Hreqs".
    iInduction requests as [|[γₗ ver'] reqs'] "IH" forall (vs).
    - by iFrame.
    - rewrite /x26_inv. do 2 rewrite -> big_sepL_cons by done.
      iDestruct "Hreqs" as "[(Hlin & %Φ & %γₜ & %src & %dq & %vs' & #Hwinv) Hreqs']";
      iMod ("IH" with "Hγ Hreqs'") as "(Hreqs' & %vs'' & Hγ)".
      iInv x12 as "[[HΦ >Hlin'] | [(>Hcredit & AU & >Hlin') | (>Htok & %b & >Hlin')]]" "Hclose".
      + iCombine "Hlin Hlin'" gives %[_ Hless].
        iMod ("Hclose" with "[HΦ Hlin]") as "_".
        { iLeft. rewrite Hless. iFrame. }
        rewrite bool_decide_eq_false in Hless.
        assert (ver ≥ ver') as Hge by lia.
        iFrame "∗ #".
        by case_bool_decide; first lia.
      + iCombine "Hlin Hlin'" gives %[_ Hless].
        destruct (decide (ver' = S ver)) as [-> | Hne].
        * iMod (ghost_var_update_halves false with "Hlin Hlin'") as "[Hlin Hlin']".
          iMod (lc_fupd_elim_later with "Hcredit AU") as "AU".
          iMod "AU" as (n') "[Hγ' [_ Hconsume]]".
          iMod (ghost_var_update_halves vs' with "Hγ Hγ'") as "[Hγ Hγ']".
          iFrame.
          rewrite /ad25_inv.
          rewrite -> bool_decide_eq_false_2 by lia.
          iFrame "∗ #".
          iMod ("Hconsume" with "Hγ") as "HΦ".
          iMod ("Hclose" with "[-]") as "_".
          { iLeft. iFrame. }
          done.
        * iMod ("Hclose" with "[Hcredit AU Hlin']") as "_".
          { iRight. iLeft. iFrame. }
          iFrame.
          rewrite Hless.
          rewrite bool_decide_eq_true in Hless.
          rewrite /ad25_inv.
          rewrite -> bool_decide_eq_true_2 by lia.
          by iFrame "∗ #".
      + iCombine "Hlin Hlin'" gives %[_ <-].
        iMod (ghost_var_update_halves (bool_decide (S ver < ver')) with "Hlin Hlin'") as "[Hlin Hlin']".
        iMod ("Hclose" with "[Htok Hlin]") as "_".
        { do 2 iRight. iFrame. }
        by iFrame "∗ #".
  Qed.

  Definition e28_inv (γ γᵥ γₕ γᵣ : gname) (l : loc) (len : nat) : iProp Σ :=
    ∃ (ver : nat) (d6 : list (list val)) (vs : list val) requests,
      bad19 γᵣ requests ∗

      x26_inv γ (Nat.div2 ver) requests ∗

      l ↦ #ver ∗

      ⌜length vs = len⌝ ∗

      ⌜length d6 = S (Nat.div2 ver)⌝ ∗
      if Nat.even ver then

        ghost_var γ (1/2) vs ∗ x13_own γₕ 1 d6 ∗ mono_nat_auth_own γᵥ 1 ver ∗ (l +ₗ 1) ↦∗ vs ∗ ⌜last d6 = Some vs⌝
      else

        x13_own γₕ (1/2) d6 ∗ mono_nat_auth_own γᵥ (1/2) ver ∗ (l +ₗ 1) ↦∗{# 1/2} vs.

  Lemma wp_array_copy_to' γ γᵥ γₕ γᵣ (dst src : loc) (n i : nat) vdst ver :

    i ≤ n → length vdst = n - i →
      inv fb11 (e28_inv γ γᵥ γₕ γᵣ src n) -∗

        mono_nat_lb_own γᵥ ver -∗
          {{{ (dst +ₗ i) ↦∗ vdst }}}
            array_copy_to #(dst +ₗ i) #(src +ₗ 1 +ₗ i) #(n - i)
          {{{ vers vdst', RET #();

              (dst +ₗ i) ↦∗ vdst' ∗
              ⌜length vdst' = n - i⌝ ∗

              ⌜StronglySorted Nat.le vers⌝ ∗

              ⌜Forall (Nat.le ver) vers⌝ ∗

              ([∗ list] j ↦ ver' ; v ∈ vers ; vdst',
                  mono_nat_lb_own γᵥ ver' ∗

                  (⌜Nat.Even ver'⌝ →

                    ∃ vs,
                      a15_own γₕ (Nat.div2 ver') vs ∗

                      ⌜vs !! (i + j)%nat = Some v⌝)) }}}.
  Proof.
    iIntros "%Hle %Hvdst #Hinv #Hlb !> %Φ Hdst HΦ".
    iLöb as "IH" forall (i vdst ver Hle Hvdst) "Hlb".
    wp_rec.
    wp_pures.
    case_bool_decide as Hdone.
    - wp_pures.
      assert (i = n)%Z as -> by lia. clear Hdone. simplify_eq/=.
      rewrite Nat.sub_diag length_zero_iff_nil in Hvdst.
      clear Hle. subst.
      iApply ("HΦ" $! [] []). iFrame.
      iModIntro.
      iSplit; first rewrite Nat.sub_diag //.
      by repeat (iSplit; first by iPureIntro; constructor).
    - wp_pures.
      destruct vdst as [| v vdst].
      { simplify_list_eq. lia. }
      clear Hdone. simpl in *. rewrite array_cons.
      iDestruct "Hdst" as "[Hhd Htl]".
      wp_bind (! _)%E.
      iInv fb11 as "(%ver' & %d6 & %vs & %bad19 & Hreg & Hreginv & >Hver' & >%Hlen & >%Hhistory & Hlock)" "Hcl". simplify_eq.
      destruct (Nat.even ver') eqn:Hparity.
      + iDestruct "Hlock" as ">(Hγ & Hγₕ & Hγᵥ & Hsrc & %Hcons)".
        wp_apply (wp_load_offset with "Hsrc").
        { apply list_lookup_lookup_total_lt. lia. }
        iMod (ff17_alloc with "Hγₕ") as "[H● #H◯]".
        { by rewrite last_lookup in Hcons. }
        rewrite Hhistory /=.
        iIntros "Hsrc".
        iPoseProof (mono_nat_lb_own_valid with "Hγᵥ Hlb") as "[%Ha %Hord]".
        iPoseProof (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb'".
        iMod ("Hcl" with "[-Hhd Htl HΦ]") as "_".
        { iExists ver', d6, vs. rewrite Hparity. by iFrame "∗ %".  }
        iModIntro.
        wp_store.
        wp_pures.
        rewrite -Z.sub_add_distr.
        do 2 rewrite Loc.add_assoc.
        change 1%Z with (Z.of_nat 1).
        rewrite -Nat2Z.inj_add Nat.add_1_r.
        wp_apply ("IH" $! _ vdst ver' with "[] [] [$] [-] [//]").
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        iIntros (vers vdst') "!> (Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
        iApply "HΦ".
        replace (S i) with (i + 1) by lia.
        rewrite Nat2Z.inj_add -Loc.add_assoc.
        iCombine "Hhd Hdst" as "Hdst".
        rewrite -array_cons.
        iFrame. repeat iSplit.
        { iIntros "!% /=". lia. }
        { iPureIntro. by eapply SSorted_cons. }
        { iPureIntro. constructor; first done.
          eapply Forall_impl; eauto. lia. }
        { simpl. iSplitR "Hcons".
          - iSplitR; first done.
            iIntros "%Heven".
            iExists vs. iFrame "#".
            rewrite Nat.add_0_r.
            by rewrite <- list_lookup_lookup_total_lt by lia.
          - rewrite big_sepL2_mono; first done.
            iIntros (k ver''' v') "_ _ H".
            rewrite -Nat.add_1_r -Nat.add_assoc Nat.add_1_r //.  }
      + iDestruct "Hlock" as ">(Hγₕ & Hγᵥ & Hsrc)".
        wp_apply (wp_load_offset with "Hsrc").
        { apply list_lookup_lookup_total_lt. lia. }
        iIntros "Hsrc".
        iPoseProof (mono_nat_lb_own_valid with "Hγᵥ Hlb") as "[%Ha %Hord]".
        iPoseProof (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb'".
        iMod ("Hcl" with "[-Hhd Htl HΦ]") as "_".
        { iExists _, _, _. iFrame.
          repeat iSplit; try done.
          rewrite Hparity. by iFrame. }
        iModIntro.
        wp_store.
        wp_pures.
        rewrite -Z.sub_add_distr.
        do 2 rewrite Loc.add_assoc.
        change 1%Z with (Z.of_nat 1).
        rewrite -Nat2Z.inj_add Nat.add_1_r.
        wp_apply ("IH" $! _ vdst ver' with "[] [] [$] [-] [//]").
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        iIntros (vers vdst') "!> (Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
        iApply "HΦ".
        replace (S i) with (i + 1) by lia.
        rewrite Nat2Z.inj_add -Loc.add_assoc.
        iCombine "Hhd Hdst" as "Hdst".
        rewrite -array_cons.
        iFrame. repeat iSplit.
        { iIntros "!% /=". lia. }
        { iPureIntro. by eapply SSorted_cons. }
        { iPureIntro. constructor; first done.
          eapply Forall_impl; eauto. lia. }
        { simpl. iSplitR "Hcons".
          - rewrite -Nat.even_spec.
            iSplitR; first done.
            iIntros "%Heven". congruence.
          - rewrite big_sepL2_mono; first done.
            iIntros (k ver''' v') "_ _ H".
            rewrite -Nat.add_1_r -Nat.add_assoc Nat.add_1_r //.  }
  Qed.

  Lemma ff30_agree γₕ p q d6 d6' :
    x13_own γₕ p d6 -∗
      x13_own γₕ q d6'  -∗
        ⌜d6 = d6'⌝.
  Proof.
    iIntros "H H'".
    iCombine "H H'" gives %Hagree%auth_auth_dfrac_op_inv.
    iPureIntro.
    apply list_eq.
    intros i.
    apply leibniz_equiv.
    apply (inj (fmap to_agree)).
    repeat rewrite -list_lookup_fmap.
    by do 2 rewrite -lookup_map_seq_0.
  Qed.

  Lemma c31 γ γᵥ γₕ γᵣ (dst src : loc) (n : nat) vdst ver :

    length vdst = n →
      inv fb11 (e28_inv γ γᵥ γₕ γᵣ src n) -∗

        mono_nat_lb_own γᵥ ver -∗
          {{{ dst ↦∗ vdst }}}
            array_copy_to #dst #(src +ₗ 1) #n
          {{{ vers vdst', RET #();

              dst ↦∗ vdst' ∗
              ⌜length vdst' = n⌝ ∗

              ⌜StronglySorted Nat.le vers⌝ ∗

              ⌜Forall (Nat.le ver) vers⌝ ∗

              ([∗ list] i ↦ ver' ; v ∈ vers ; vdst',
                  mono_nat_lb_own γᵥ ver' ∗

                  (⌜Nat.Even ver'⌝ →

                    ∃ vs,
                      own γₕ (◯ {[Nat.div2 ver' := to_agree vs]}) ∗

                      ⌜vs !! i = Some v⌝)) }}}.
  Proof.
     iIntros "%Hvdst #Hinv #Hlb !> %Φ Hdst HΦ".
     rewrite -(Loc.add_0 (src +ₗ 1)).
     rewrite -(Loc.add_0 dst).
     replace (Z.of_nat n) with (n - 0)%Z by lia.
     change 0%Z with (Z.of_nat O).
     wp_smart_apply (wp_array_copy_to' _ _ _ _ _ _ _ _ vdst _ with "[//] [//] [$] [-]"); try lia.
     iIntros "!> %vers %vdst' /=".
     rewrite Nat.sub_0_r //.
  Qed.

  Lemma de32 γ γᵥ γₕ γᵣ (src : loc) (n : nat) ver :
    n > 0 →
      inv fb11 (e28_inv γ γᵥ γₕ γᵣ src n) -∗

        mono_nat_lb_own γᵥ ver -∗
          {{{ True }}}
            array_clone #(src +ₗ 1) #n
          {{{ vers vdst (dst : loc), RET #dst;

              dst ↦∗ vdst ∗
              ⌜length vdst = n⌝ ∗

              ⌜StronglySorted Nat.le vers⌝ ∗

              ⌜Forall (Nat.le ver) vers⌝ ∗

              ([∗ list] i ↦ ver' ; v ∈ vers ; vdst,
                  mono_nat_lb_own γᵥ ver' ∗

                  (⌜Nat.Even ver'⌝ →

                    ∃ vs,
                      own γₕ (◯ {[Nat.div2 ver' := to_agree vs]}) ∗

                      ⌜vs !! i = Some v⌝)) }}}.
  Proof.
    iIntros "%Hpos #Hinv #Hlb %Φ !# _ HΦ".
    rewrite /array_clone.
    wp_pures.
    wp_alloc dst as "Hdst".
    { lia. }
    wp_pures.
    wp_apply (c31 with "[//] [//] [$]").
    { rewrite length_replicate. lia. }
    iIntros (vers vdst') "(Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
    wp_pures.
    iModIntro.
    iApply ("HΦ" with "[$Hdst $Hcons]").
    by iPureIntro.
  Qed.

  Lemma cbf33 n : Z.Even (Z.of_nat n) ↔ Nat.Even n.
  Proof.
    split.
    - intros [k H]. exists (Z.to_nat k). lia.
    - intros [k H]. exists k. lia.
  Qed.

  Lemma af34 n : Nat.Odd n ↔ Z.Odd (Z.of_nat n).
  Proof.
    split.
    - intros [k H]. exists k. lia.
    - intros [k H]. exists (Z.to_nat k). lia.
  Qed.

  Lemma a36' γ γᵥ γₕ γᵣ dst src (vs vs' : list val) i n dq :
    i ≤ n → length vs = n - i → length vs = length vs' →
        inv fb11 (e28_inv γ γᵥ γₕ γᵣ dst n) -∗
          {{{ (dst +ₗ 1 +ₗ i) ↦∗{#1 / 2} vs ∗ (src +ₗ i) ↦∗{dq} vs' }}}
            array_copy_to #(dst +ₗ 1 +ₗ i) #(src +ₗ i) #(n - i)%nat
          {{{ RET #(); (dst +ₗ 1 +ₗ i) ↦∗{#1 / 2} vs' ∗ (src +ₗ i) ↦∗{dq} vs' }}}.
  Proof.
    iIntros (Hle Hlen Hmatch) "#Hinv %Φ !> [Hdst Hsrc] HΦ".
    iLöb as "IH" forall (i vs vs' Hlen Hle Hmatch).
    wp_rec.
    wp_pures.
    case_bool_decide.
    - wp_pures.
      simpl in *.
      assert (i = n) as -> by lia.
      rewrite Nat.sub_diag in Hlen.
      rewrite Hlen in Hmatch.
      symmetry in Hmatch.
      rewrite length_zero_iff_nil in Hlen.
      rewrite length_zero_iff_nil in Hmatch.
      subst.
      repeat rewrite array_nil.
      by iApply "HΦ".
    - wp_pures.
      assert (length vs > 0) by lia.
      destruct vs as [| v vs].
      { simplify_list_eq. lia. }
      destruct vs' as [| v' vs']; first simplify_list_eq.
      do 2 rewrite array_cons.
      iDestruct "Hdst" as "[Hdst Hdst']".
      iDestruct "Hsrc" as "[Hsrc Hsrc']".
      wp_load.
      wp_bind (_ <- _)%E.
      iInv fb11 as "(%ver & %d6 & %vs'' & %bad19 & Hreg & Hreginv & >Hversion & >%Hlen' & >%Hhistory & Hlock)" "Hcl".
      assert (i < length vs'') as [v'' Hv'']%lookup_lt_is_Some by lia.
      destruct (Nat.even ver) eqn:Heven.
      + iMod "Hlock" as "(Hγ & Hγₕ & Hγᵥ & Hdst'' & %Hcons') /=".
        iPoseProof (update_array _ _ _ i v'' with "Hdst''") as "[Hdst'' _]".
        { done. }

        by iCombine "Hdst Hdst''" gives %[Hfrac%dfrac_valid_own_r <-].
      + iMod "Hlock" as "(Hγₕ & Hγᵥ & Hdst'')".
        iPoseProof (update_array _ _ _ i v'' with "Hdst''") as "[Hdst'' Hacc]".
        { done. }
        iCombine "Hdst Hdst''" as "Hdst".
        rewrite dfrac_op_own Qp.half_half.
        wp_store.
        iDestruct "Hdst" as "[Hdst Hdst'']".
        iPoseProof ("Hacc" with "Hdst''") as "Hdst''".
        iMod ("Hcl" with "[$Hreg $Hreginv $Hversion Hγₕ Hγᵥ Hdst'']") as "_".
        { iExists d6, (<[i:=v']> vs''). rewrite Heven. iFrame "∗ %".
          iPureIntro. by rewrite length_insert. }
        iModIntro.
        wp_pures.
        rewrite -> Nat2Z.inj_sub by done.
        rewrite -Z.sub_add_distr.
        rewrite Loc.add_assoc /=.
        rewrite (Loc.add_assoc src) /=.
        change 1%Z with (Z.of_nat 1).
        rewrite -Nat2Z.inj_add Nat.add_comm /=.
        rewrite <- Nat2Z.inj_sub by lia.
        simplify_list_eq.
        wp_apply ("IH" $! (S i) vs vs' with "[] [] [//] [$] [$]").
        * iPureIntro. lia.
        * iPureIntro. lia.
        * iIntros "[Hdst' Hsrc']".
          iApply "HΦ". iFrame.
          rewrite (Loc.add_assoc (dst +ₗ 1)) /=.
          change 1%Z with (Z.of_nat 1).
          by rewrite -Nat2Z.inj_add Nat.add_comm /=.
  Qed.

  Lemma a36 γ γᵥ γₕ γᵣ dst src (vs vs' : list val) n dq :
    length vs = n → length vs = length vs' →
        inv fb11 (e28_inv γ γᵥ γₕ γᵣ dst n) -∗
          {{{ (dst +ₗ 1) ↦∗{#1 / 2} vs ∗ src ↦∗{dq} vs' }}}
            array_copy_to #(dst +ₗ 1) #src #n
          {{{ RET #(); (dst +ₗ 1) ↦∗{#1 / 2} vs' ∗ src↦∗ {dq} vs' }}}.
  Proof.
    iIntros (Hlen Hlen') "#Hinv %Φ !> [Hdst Hsrc] HΦ".
    rewrite -(Loc.add_0 (dst +ₗ 1)).
    rewrite -(Loc.add_0 src).
    change 0%Z with (Z.of_nat 0).
    rewrite -{2}(Nat.sub_0_r n).
    wp_apply (a36' _ _ _ _ _ _ vs vs' with "[$] [$] [$]").
    - lia.
    - lia.
    - done.
  Qed.

  Lemma b37 n : Nat.Even n ↔ ¬ (Nat.Odd n).
  Proof.
    split.
    - rewrite /not. apply Nat.Even_Odd_False.
    - intros Hnotodd. by pose proof Nat.Even_or_Odd n as [Heven | Hodd].
  Qed.

  Lemma eefe38 n : Nat.Odd n ↔ ¬ (Nat.Even n).
  Proof.
    split.
    - rewrite /not. intros. by eapply Nat.Even_Odd_False.
    - intros Hnotodd. by pose proof Nat.Even_or_Odd n as [Heven | Hodd].
  Qed.

  Lemma ec39 n : Nat.div2 (S (S n)) = S (Nat.div2 n).
  Proof. done. Qed.

  Lemma d40 l dq dq' vs vs' : length vs = length vs' → l ↦∗{dq} vs -∗ l ↦∗{dq'} vs' -∗ l ↦∗{dq ⋅ dq'} vs ∗ ⌜vs = vs'⌝.
  Proof.
    iIntros (Hlen) "Hl Hl'".
    iInduction vs as [|v vs] "IH" forall (l vs' Hlen).
    - symmetry in Hlen. rewrite length_zero_iff_nil in Hlen. simplify_list_eq. by iSplit.
    - destruct vs' as [|v' vs']; simplify_list_eq.
      repeat rewrite array_cons.
      iDestruct "Hl" as "[Hl Hls]".
      iDestruct "Hl'" as "[Hl' Hls']".
      iCombine "Hl Hl'" as "Hl" gives %[_ <-].
      iFrame.
      iPoseProof ("IH" with "[//] [$] [$]") as "[Hl <-]".
      by iFrame.
  Qed.

  Definition efd41 (v : val) (γ : gname) (n : nat) : iProp Σ :=
    ∃ (dst : loc) (γₕ γᵥ γᵣ : gname),
      ⌜v = #dst⌝ ∗ inv fb11 (e28_inv γ γᵥ γₕ γᵣ dst n).

  Lemma bd42_spec (n : nat) (src : loc) dq vs :
    length vs = n → n > 0 →
      {{{ src ↦∗{dq} vs }}}
        bcaf2 n #src
      {{{ v γ, RET v; src ↦∗{dq} vs ∗ efd41 v γ n ∗ b14 γ vs  }}}.
  Proof.
Admitted.

  Lemma da43 γ γᵥ γₕ γᵣ (l : loc) (n ver : nat) :
    inv fb11 (e28_inv γ γᵥ γₕ γᵣ l n) -∗
      {{{ mono_nat_lb_own γᵥ ver }}}
        x3 #l #ver
      {{{ ver', RET #(); ⌜ver < ver'⌝ ∗ mono_nat_lb_own γᵥ ver' }}}.
  Proof.
    iIntros "#Hinv %Φ !# #Hlb HΦ".
    iLöb as "IH".
    wp_rec.
    wp_pures.
    wp_bind (! _)%E.
    iInv fb11 as "(%ver' & %d6 & %vs & %bad19 & Hreg & Hreginv & >Hver' & >%Hlen & >%Hhistory & Hlock)" "Hcl".
    wp_load.
    destruct (Nat.even ver') eqn:Heven.
    - iDestruct "Hlock" as "(Hγ & Hγₕ & Hγᵥ & Hl & %Hcons)".
      iDestruct (mono_nat_lb_own_valid with "Hγᵥ Hlb") as %[_ Hle].
      iClear "Hlb".
      iPoseProof (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb".
      iMod ("Hcl" with "[-HΦ]") as "_".
      { iFrame. rewrite Heven. by iFrame. }
      iModIntro.
      wp_pures.
      destruct (decide (ver = ver')) as [-> | Hne].
      + rewrite -> bool_decide_eq_true_2 by congruence.
        wp_pures.
        iApply ("IH" with "[$]").
      + rewrite -> bool_decide_eq_false_2 by (intros Heq; simplify_eq).
        wp_pures.
        iModIntro.
        iApply ("HΦ" with "[$Hlb]").
        iPureIntro. lia.
    - iDestruct "Hlock" as "(Hγₕ & Hγᵥ & Hl)".
      iDestruct (mono_nat_lb_own_valid with "Hγᵥ Hlb") as %[_ Hle].
      iClear "Hlb".
      iPoseProof (mono_nat_lb_own_get with "Hγᵥ") as "#Hlb".
      iMod ("Hcl" with "[-HΦ]") as "_".
      { iFrame. rewrite Heven. by iFrame. }
      iModIntro.
      wp_pures.
      destruct (decide (ver = ver')) as [-> | Hne].
      + rewrite -> bool_decide_eq_true_2 by congruence.
        wp_pures.
        iApply ("IH" with "[$]").
      + rewrite -> bool_decide_eq_false_2 by (intros Heq; simplify_eq).
        wp_pures.
        iModIntro.
        iApply ("HΦ" with "[$Hlb]").
        iPureIntro. lia.
  Qed.

  Lemma c44 x y : x ≤ y → Nat.div2 x ≤ Nat.div2 y.
  Proof.
    intros Hle. induction Hle as [| y Hle IH].
    - done.
    - destruct (Nat.Even_Odd_dec y).
      + by rewrite -Nat.Even_div2.
      + rewrite <- Nat.Odd_div2 by done. by constructor.
  Qed.

  Lemma be45 n b : Nat.even n = b ↔ Nat.odd n = negb b.
  Proof.
    split; destruct b; simpl.
    - intros Heven%Nat.even_spec.
      apply dec_stable.
      rewrite not_false_iff_true.
      intros Hodd%Nat.odd_spec.
      by eapply Nat.Even_Odd_False.
    - rewrite -not_true_iff_false Nat.even_spec Nat.odd_spec.
      intros Hnoteven.
      destruct (Nat.Even_Odd_dec n).
      + contradiction.
      + done.
    - rewrite -not_true_iff_false Nat.even_spec Nat.odd_spec.
      intros Hnoteven.
      destruct (Nat.Even_Odd_dec n).
      + done.
      + contradiction.
    - intros Hodd%Nat.odd_spec.
      apply dec_stable.
      rewrite not_false_iff_true.
      intros Heven%Nat.even_spec.
      by eapply Nat.Even_Odd_False.
  Qed.

  Lemma fc46 n b : Nat.odd n = b ↔ Nat.even n = negb b.
  Proof.
    rewrite be45 negb_involutive //.
  Qed.

  Lemma x47 n : Z.even (Z.of_nat n) = Nat.even n.
  Proof.
    destruct (Z.even n) eqn:H, (Nat.even n) eqn:H'; auto.
    - rewrite Z.even_spec cbf33 in H.
      by rewrite -not_true_iff_false Nat.even_spec in H'.
    - rewrite Nat.even_spec in H'.
      by rewrite -not_true_iff_false Z.even_spec cbf33 in H.
  Qed.

  Lemma fbe48 n : Z.odd (Z.of_nat n) = Nat.odd n.
  Proof.
    destruct (Z.odd n) eqn:H, (Nat.odd n) eqn:H'; auto.
    - rewrite Z.odd_spec -af34 in H.
      by rewrite -not_true_iff_false Nat.odd_spec in H'.
    - rewrite Nat.odd_spec in H'.
      by rewrite -not_true_iff_false Z.odd_spec -af34 in H.
  Qed.

  Lemma x49 Φ γ γₗ γᵥ γᵣ γₕ γₜ l n src dq vs' ver i :
    inv fb11 (e28_inv γ γᵥ γₕ γᵣ l n) -∗
      inv x12 (d24_inv Φ γ γₗ γₜ src dq vs') -∗
        ba20 γᵣ i γₗ (S (Nat.div2 ver)) -∗
          mono_nat_lb_own γᵥ (S (S ver)) -∗
            token γₜ -∗
              £ 2 -∗
                src ↦∗{dq} vs'
                  ={⊤}=∗ Φ #().
  Proof.
    iIntros "#Hinv #Hwinv #◯Hreg #Hlb Hγₜ [Hcredit Hcredit'] Hsrc".
    iInv fb11 as "(%ver' & %d6 & %vs'' & %bad19 & >Hreg & Hreginv & >Hver & >%Hlen & >%Hhistory & Hlock)" "Hcl".
    iMod (lc_fupd_elim_later with "Hcredit Hreginv") as "Hreginv".
    iPoseProof (bfd22_agree with "Hreg ◯Hreg") as "%Hagree".

    iPoseProof (big_sepL_lookup_acc _ _ _ _ Hagree with "Hreginv") as "[[Hlin _] Hrest]".
    iInv x12 as "[[HΦ >Hlin'] | [(>Hcredit & AU & >Hlin') | (>Htok & >Hlin')]]" "Hclose".
    { iMod ("Hclose" with "[Hγₜ Hlin']") as "_".
      { do 2 iRight. iFrame. }
      iMod ("Hcl" with "[-HΦ Hsrc Hcredit']") as "_".
      { iFrame. iSplit; last done. iApply "Hrest". iFrame "∗ #". }
      iMod (lc_fupd_elim_later with "Hcredit' HΦ") as "HΦ".
      iModIntro.
      iApply ("HΦ" with "Hsrc"). }
    { destruct (Nat.even ver') eqn:Heven''.
      - iMod "Hlock" as "(Hγ & Hγₕ & Hγᵥ & Hdst & %Hcons')".
        iDestruct (mono_nat_lb_own_valid with "Hγᵥ Hlb") as %[_ Hless].

        iCombine "Hlin Hlin'" gives %[_ Heq%bool_decide_eq_true].
        assert (S (S ver) ≤ ver') as Htight%c44 by lia. simpl in Htight. lia.
      - iMod "Hlock" as "(Hγₕ & Hγᵥ & Hdst)".
        iDestruct (mono_nat_lb_own_valid with "Hγᵥ Hlb") as %[_ Hless''].

        iCombine "Hlin Hlin'" gives %[_ Heq%bool_decide_eq_true].
        assert (S (S ver) ≤ ver') as Htight%c44 by lia.
        simpl in Htight. lia. }
    {

      iCombine "Hγₜ Htok" gives %[]. }
  Qed.

  Lemma fc50_spec (γ : gname) (v : val) (src : loc) dq (vs' : list val) :
    efd41 v γ (length vs') -∗
      src ↦∗{dq} vs' -∗
        <<{ ∀∀ vs, b14 γ vs  }>>
          c4 (length vs') v #src @ ↑N
        <<{ b14 γ vs' | RET #(); src ↦∗{dq} vs' }>>.
  Proof.
Admitted.

  Lemma x51_spec (γ : gname) (v : val) (n : nat) :
    n > 0 →
      efd41 v γ n -∗
        <<{ ∀∀ vs, b14 γ vs  }>>
          f5 n v @ ↑N
        <<{ ∃∃ copy : loc, b14 γ vs | RET #copy; copy ↦∗ vs }>>.
  Proof.
Admitted.

End a59.
