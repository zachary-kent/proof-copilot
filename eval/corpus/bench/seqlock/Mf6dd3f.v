From iris.program_logic Require Import atomic.
From iris.algebra Require Import auth gmap list lib.mono_nat.
From iris.base_logic.lib Require Import token ghost_var mono_nat invariants.
From iris.heap_lang Require Import lang proofmode notation lib.array.
Import derived_laws.bi.

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
  λ: "src", (ref #0, array_clone "src" #n).

Definition c3 (n : nat) : val :=
  rec: "c3" "l" "src" :=
    let: "version" := Fst "l" in
    let: "ver" := !"version" in
    if: "ver" `rem` #2 = #1 then

      "c3" "l" "src"
    else
      if: CAS "version" "ver" (#1 + "ver") then

        array_copy_to (Snd "l") "src" #n;;

        "version" <- #2 + "ver"
      else

        "c3" "l" "src".

Definition f4 (n : nat) : val :=
  rec: "f4" "l" :=
    let: "version" := Fst "l" in
    let: "ver" := !"version" in
    if: "ver" `rem` #2 = #1 then

      "f4" "l"
    else

      let: "data" := array_clone (Snd "l") #n in
      if: !"version" = "ver" then

        "data"
      else

        "f4" "l".

Definition d5 := gmap nat $ agree $ list val.

Definition x6 := authUR $ gmapUR nat $ agreeR $ listO valO.

Class fbe7 (Σ : gFunctors) := {
  x35 :: heapGS Σ;
  e36 :: inG Σ x6;
  fbc37 :: mono_natG Σ;
}.

Section a38.
  Context `{!fbe7 Σ, !heapGS Σ}.

  Context (N : namespace).

  Definition fb8 := N .@ "a38".

  Definition x9_own γ (q : Qp) d5 := own γ (●{#q} map_seq 0 (to_agree <$> d5)).

  Definition b10 γ (vs : list val) : iProp Σ :=
    ∃ d5,
      x9_own γ (1/2) d5 ∗ ⌜last d5 = Some vs⌝.

  Definition a11_own γₕ i b10 := own γₕ (◯ {[i := to_agree b10]}).

  Lemma ef12_update b10 γₕ d5 :
    x9_own γₕ 1 d5 ==∗
      x9_own γₕ 1 (d5 ++ [b10]) ∗ a11_own γₕ (length d5) b10.
  Proof.
    iIntros "H●".
    rewrite /x9_own /a11_own.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update
        with
          (i := length d5)
          (x := to_agree b10).
      { rewrite lookup_map_seq_None length_fmap. by right. }
      constructor. }
    replace (length d5) with (O + length (to_agree <$> d5)) at 1
          by (now rewrite length_fmap).
    rewrite -map_seq_snoc fmap_snoc. by iFrame.
  Qed.

  Lemma ff13_alloc i b10 γₕ d5 q :
    d5 !! i = Some b10 →
      x9_own γₕ q d5 ==∗
        x9_own γₕ q d5 ∗ a11_own γₕ i b10.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[i := to_agree b10]}).
      { apply _. }
      apply singleton_included_l with (i := i).
      exists (to_agree b10). split; last done.
      by rewrite lookup_map_seq_0 list_lookup_fmap Hlookup. }
    by iFrame.
  Qed.

  Lemma c14_agree γₕ q d5 i b10 :
    x9_own γₕ q d5 -∗
      a11_own γₕ i b10 -∗
        ⌜d5 !! i = Some b10⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    by rewrite -list_lookup_fmap /= -lookup_map_seq_0 Hvs''.
  Qed.

  Definition a15 γ Φ : iProp Σ :=
    AU <{ ∃∃ (vs : list val), b10 γ vs }> @ ⊤ ∖ ↑N, ∅
       <{ ∃ l : loc, b10 γ vs, COMM Φ #() }>.

  Definition e16_inv (γ γₕ : gname) (version l : loc) (len : nat) : iProp Σ :=
    ∃ (ver : nat) (d5 : list (list val)) (vs : list val),

      version ↦ #ver ∗

      ⌜length vs = len⌝ ∗

      ⌜length d5 = S (Nat.div2 ver)⌝ ∗
      if Nat.even ver then

        x9_own γₕ (1/2) d5 ∗ mono_nat_auth_own γ 1 ver ∗ l ↦∗ vs ∗ ⌜last d5 = Some vs⌝
      else

        x9_own γₕ (1/4) d5 ∗ mono_nat_auth_own γ (1/2) ver ∗ l ↦∗{# 1/2} vs.

  Lemma ac19' γ γₕ (version dst src : loc) (n i : nat) vdst ver :

    i ≤ n → length vdst = n - i →
      inv fb8 (e16_inv γ γₕ version src n) -∗

        mono_nat_lb_own γ ver -∗
          {{{ (dst +ₗ i) ↦∗ vdst }}}
            array_copy_to #(dst +ₗ i) #(src +ₗ i) #(n - i)
          {{{ vers vdst', RET #();

              (dst +ₗ i) ↦∗ vdst' ∗
              ⌜length vdst' = n - i⌝ ∗

              ⌜StronglySorted Nat.le vers⌝ ∗

              ⌜Forall (Nat.le ver) vers⌝ ∗

              ([∗ list] j ↦ ver' ; v ∈ vers ; vdst',
                  mono_nat_lb_own γ ver' ∗

                  (⌜Nat.Even ver'⌝ →

                    ∃ vs,
                      a11_own γₕ (Nat.div2 ver') vs ∗

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
      iSplit; first by rewrite Nat.sub_diag.
      by repeat (iSplit; first by iPureIntro; constructor).
    - wp_pures.
      destruct vdst as [| v vdst].
      { assert (@List.length val [] > 0) as Hlen by lia. inv Hlen.  }
      clear Hdone. simpl in *. rewrite array_cons.
      iDestruct "Hdst" as "[Hhd Htl]".
      wp_bind (! _)%E.
      iInv fb8 as "(%ver' & %d5 & %vs & >Hver' & >%Hlen & >%Hhistory & Hlock)" "Hcl". simplify_eq.
      destruct (Nat.even ver') eqn:Hparity.
      + iDestruct "Hlock" as ">(Hγₕ & Hγ & Hsrc & %Hcons)".
        wp_apply (wp_load_offset with "Hsrc").
        { apply list_lookup_lookup_total_lt. lia. }
        iMod (ff13_alloc with "Hγₕ") as "[H● #H◯]".
        { by rewrite last_lookup in Hcons. }
        rewrite Hhistory /=.
        iIntros "Hsrc".
        iPoseProof (mono_nat_lb_own_valid with "Hγ Hlb") as "[%Ha %Hord]".
        iPoseProof (mono_nat_lb_own_get with "Hγ") as "#Hlb'".
        iMod ("Hcl" with "[-Hhd Htl HΦ]") as "_".
        { iExists ver', d5, vs. rewrite Hparity. by iFrame "∗ %".  }
        iModIntro.
        wp_store.
        wp_pures.
        rewrite -Z.sub_add_distr.
        repeat rewrite Loc.add_assoc.
        change 1%Z with (Z.of_nat 1).
        rewrite -Nat2Z.inj_add Nat.add_1_r.
        wp_apply ("IH" $! _ vdst ver' with "[] [] [$] [-] [//]").
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        iIntros (vers vdst') "!> (Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
        iApply "HΦ".
        rewrite -{1}Nat.add_1_r.
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
            by rewrite -Nat.add_1_r -Nat.add_assoc Nat.add_1_r.  }
      + iDestruct "Hlock" as ">(Hγₕ & Hγ & Hsrc)".
        wp_apply (wp_load_offset with "Hsrc").
        { apply list_lookup_lookup_total_lt. lia. }
        iIntros "Hsrc".
        iPoseProof (mono_nat_lb_own_valid with "Hγ Hlb") as "[%Ha %Hord]".
        iPoseProof (mono_nat_lb_own_get with "Hγ") as "#Hlb'".
        iMod ("Hcl" with "[-Hhd Htl HΦ]") as "_".
        { iExists _, _, _. iFrame.
          repeat iSplit; try done.
          rewrite Hparity. by iFrame. }
        iModIntro.
        wp_store.
        wp_pures.
        rewrite -Z.sub_add_distr.
        repeat rewrite Loc.add_assoc.
        change 1%Z with (Z.of_nat 1).
        rewrite -Nat2Z.inj_add Nat.add_1_r.
        wp_apply ("IH" $! _ vdst ver' with "[] [] [$] [-] [//]").
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        iIntros (vers vdst') "!> (Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
        iApply "HΦ".
        rewrite -{1}Nat.add_1_r.
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
            by rewrite -Nat.add_1_r -Nat.add_assoc Nat.add_1_r.  }
  Qed.

  Lemma ff18_agree γₕ p q d5 d5' :
    x9_own γₕ p d5 -∗
      x9_own γₕ q d5'  -∗
        ⌜d5 = d5'⌝.
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

  Lemma ac19 γ γₕ (version dst src : loc) (n : nat) vdst ver :

    length vdst = n →
      inv fb8 (e16_inv γ γₕ version src n) -∗

        mono_nat_lb_own γ ver -∗
          {{{ dst ↦∗ vdst }}}
            array_copy_to #dst #src #n
          {{{ vers vdst', RET #();

              dst ↦∗ vdst' ∗
              ⌜length vdst' = n⌝ ∗

              ⌜StronglySorted Nat.le vers⌝ ∗

              ⌜Forall (Nat.le ver) vers⌝ ∗

              ([∗ list] i ↦ ver' ; v ∈ vers ; vdst',
                  mono_nat_lb_own γ ver' ∗

                  (⌜Nat.Even ver'⌝ →

                    ∃ vs,
                      own γₕ (◯ {[Nat.div2 ver' := to_agree vs]}) ∗

                      ⌜vs !! i = Some v⌝)) }}}.
  Proof.
     iIntros "%Hvdst #Hinv #Hlb !> %Φ Hdst HΦ".
     replace dst with (dst +ₗ 0) by apply Loc.add_0.
     replace src with (src +ₗ 0) at 2 by apply Loc.add_0.
     replace (Z.of_nat n) with (n - 0)%Z by lia.
     change 0%Z with (Z.of_nat O).
     wp_smart_apply (ac19' γ γₕ version dst src n 0 vdst ver with "[//] [//] [$] [-]"); try lia.
     iIntros "!> %vers %vdst' /=".
     by rewrite Nat.sub_0_r.
  Qed.

  Lemma de20 γ γₕ (version src : loc) (n : nat) ver :
    n > 0 →
      inv fb8 (e16_inv γ γₕ version src n) -∗

        mono_nat_lb_own γ ver -∗
          {{{ True }}}
            array_clone #src #n
          {{{ vers vdst (dst : loc), RET #dst;

              dst ↦∗ vdst ∗
              ⌜length vdst = n⌝ ∗

              ⌜StronglySorted Nat.le vers⌝ ∗

              ⌜Forall (Nat.le ver) vers⌝ ∗

              ([∗ list] i ↦ ver' ; v ∈ vers ; vdst,
                  mono_nat_lb_own γ ver' ∗

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
    wp_apply (ac19 with "[//] [//] [$]").
    { rewrite length_replicate. lia. }
    iIntros (vers vdst') "(Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
    wp_pures.
    iModIntro.
    iApply ("HΦ" with "[$Hdst $Hcons]").
    by iPureIntro.
  Qed.

  Lemma cbf21 n : Z.Even (Z.of_nat n) ↔ Nat.Even n.
  Proof.
    split.
    - intros [k H]. exists (Z.to_nat k). lia.
    - intros [k H]. exists k. lia.
  Qed.

  Lemma af22 n : Nat.Odd n ↔ Z.Odd (Z.of_nat n).
  Proof.
    split.
    - intros [k H]. exists k. lia.
    - intros [k H]. exists (Z.to_nat k). lia.
  Qed.

  Lemma x23 n : Z.even (Z.of_nat n) = Nat.even n.
  Proof.
    destruct (Z.even n) eqn:H, (Nat.even n) eqn:H'; auto.
    - rewrite Z.even_spec cbf21 in H.
      by rewrite -not_true_iff_false Nat.even_spec in H'.
    - rewrite Nat.even_spec in H'.
      by rewrite -not_true_iff_false Z.even_spec cbf21 in H.
  Qed.

  Lemma a25' γ γₕ version dst src (vs vs' : list val) i n dq :
    i ≤ n → length vs = n - i → length vs = length vs' →
        inv fb8 (e16_inv γ γₕ version dst n) -∗
          {{{ (dst +ₗ i) ↦∗{#1 / 2} vs ∗ (src +ₗ i) ↦∗{dq} vs' }}}
            array_copy_to #(dst +ₗ i) #(src +ₗ i) #(n - i)%nat
          {{{ RET #(); (dst +ₗ i) ↦∗{#1 / 2} vs' ∗ (src +ₗ i) ↦∗{dq} vs' }}}.
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
      iInv fb8 as "(%ver & %d5 & %vs'' & >Hversion & >%Hlen' & >%Hhistory & Hlock)" "Hcl".
      assert (i < length vs'') as [v'' Hv'']%lookup_lt_is_Some by lia.
      destruct (Nat.even ver) eqn:Heven.
      + iMod "Hlock" as "(Hγₕ & Hγ & Hdst'' & %Hcons') /=".
        iPoseProof (update_array _ _ _ i v'' with "Hdst''") as "[Hdst'' _]".
        { done. }
        by iCombine "Hdst Hdst''" gives %[Hfrac%dfrac_valid_own_r <-].
      + iMod "Hlock" as "(Hγₕ & Hγ & Hdst'')".
        iPoseProof (update_array _ _ _ i v'' with "Hdst''") as "[Hdst'' Hacc]".
        { done. }
        iCombine "Hdst Hdst''" as "Hdst".
        rewrite dfrac_op_own Qp.half_half.
        wp_store.
        iDestruct "Hdst" as "[Hdst Hdst'']".
        iPoseProof ("Hacc" with "Hdst''") as "Hdst''".
        iMod ("Hcl" with "[$Hversion Hγₕ Hγ Hdst'']") as "_".
        { iExists d5, (<[i:=v']> vs''). rewrite Heven. iFrame "∗ %".
          iPureIntro. by rewrite length_insert. }
        iModIntro.
        wp_pures.
        rewrite -> Nat2Z.inj_sub by done.
        rewrite -Z.sub_add_distr.
        repeat rewrite Loc.add_assoc /=.
        change 1%Z with (Z.of_nat 1).
        rewrite -Nat2Z.inj_add Nat.add_comm /=.
        rewrite <- Nat2Z.inj_sub by lia.
        simplify_list_eq.
        wp_apply ("IH" $! (S i) vs vs' with "[] [] [//] [$] [$]").
        * iPureIntro. lia.
        * iPureIntro. lia.
        * iIntros "[Hdst' Hsrc']".
          iApply "HΦ". iFrame.
          rewrite Loc.add_assoc /=.
          change 1%Z with (Z.of_nat 1).
          by rewrite -Nat2Z.inj_add Nat.add_comm /=.
  Qed.

  Lemma a25 γ γₕ version dst src (vs vs' : list val) n dq :
    length vs = n → length vs = length vs' →
        inv fb8 (e16_inv γ γₕ version dst n) -∗
          {{{ dst ↦∗{#1 / 2} vs ∗ src ↦∗{dq} vs' }}}
            array_copy_to #dst #src #n
          {{{ RET #(); dst ↦∗{#1 / 2} vs' ∗ src↦∗ {dq} vs' }}}.
  Proof.
    iIntros (Hlen Hlen') "#Hinv %Φ !> [Hdst Hsrc] HΦ".
    replace dst with (dst +ₗ O) by now rewrite Loc.add_0.
    replace src with (src +ₗ O) by now rewrite Loc.add_0.
    replace n with (n - O) at 2 by lia.
    wp_apply (a25' _ _ _ _ _ vs vs' with "[#] [$] [$]").
    - lia.
    - lia.
    - done.
    - by rewrite Loc.add_0.
  Qed.

  Lemma b26 n : Nat.Even n ↔ ¬ (Nat.Odd n).
  Proof.
    split.
    - rewrite /not. apply Nat.Even_Odd_False.
    - intros Hnotodd. by pose proof Nat.Even_or_Odd n as [Heven | Hodd].
  Qed.

  Lemma eefe27 n : Nat.Odd n ↔ ¬ (Nat.Even n).
  Proof.
    split.
    - rewrite /not. intros. by eapply Nat.Even_Odd_False.
    - intros Hnotodd. by pose proof Nat.Even_or_Odd n as [Heven | Hodd].
  Qed.

  Lemma ec28 n : Nat.div2 (S (S n)) = S (Nat.div2 n).
  Proof. done. Qed.

  Lemma d29 l dq dq' vs vs' : length vs = length vs' → l ↦∗{dq} vs -∗ l ↦∗{dq'} vs' -∗ l ↦∗{dq ⋅ dq'} vs ∗ ⌜vs = vs'⌝.
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

  Definition efd30 (v : val) (γₕ : gname) (n : nat) : iProp Σ :=
    ∃ (version dst : loc) (γ : gname),
      ⌜v = (#version, #dst)%V⌝ ∗ inv fb8 (e16_inv γ γₕ version dst n).

  Lemma bd31_spec (n : nat) (src : loc) dq vs :
    length vs = n → n > 0 →
      {{{ src ↦∗{dq} vs }}}
        bcaf2 n #src
      {{{ v γ, RET v; src ↦∗{dq} vs ∗ efd30 v γ n ∗ b10 γ vs  }}}.
  Proof.
Admitted.

  Lemma fc32_spec (γₕ : gname) (v : val) (src : loc) dq (vs' : list val) :
    efd30 v γₕ (length vs') -∗
      src ↦∗{dq} vs' -∗
        <<{ ∀∀ vs, b10 γₕ vs  }>>
          c3 (length vs') v #src @ ↑N
        <<{ b10 γₕ vs' | RET #(); src ↦∗{dq} vs' }>>.
  Proof.
Admitted.

  Lemma e33_inv {A B} (f : A → B) x y : f x ≠ f y → x ≠ y.
  Proof.
    intros Hne Heq. simplify_eq.
  Qed.

  Lemma x34_spec (γₕ : gname) (v : val) (n : nat) :
    n > 0 →
      efd30 v γₕ n -∗
        <<{ ∀∀ vs, b10 γₕ vs  }>>
          f4 n v @ ↑N
        <<{ ∃∃ copy : loc, b10 γₕ vs | RET #copy; copy ↦∗ vs }>>.
  Proof.
Admitted.

End a38.
