Require Import iris.program_logic.atomic.

From iris.program_logic Require Import atomic.
From iris.algebra Require Import auth gmap gset list lib.mono_nat.
From iris.heap_lang Require Import lang proofmode notation lib.array.
From iris.base_logic.lib Require Import token ghost_var mono_nat invariants.

Import derived_laws.bi.
Require Import Stdlib.ZArith.Zquot.
Require Import iris.bi.interface.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

From Stdlib Require Import Arith ZArith ZifyClasses ZifyInst Lia.

Global Program Instance da0 : BinOp Nat.modulo :=
  {| TBOp := Z.modulo ; TBOpInj := Nat2Z.inj_mod |}.
Add Zify BinOp da0.

Global Program Instance cb1 : BinOp Nat.div :=
  {| TBOp := Z.div ; TBOpInj := Nat2Z.inj_div |}.
Add Zify BinOp cb1.

From stdpp Require Import base tactics option list gmap sorting.

Definition bcaf2 (n : nat) : val :=
  λ: "src",
    let: "dst" := AllocN #(S (S n)) #0 in
    "dst" +ₗ #1 <- InjR (array_clone "src" #n);;
    array_copy_to ("dst" +ₗ #2) "src" #n;;
    "dst".

Definition bff3_valid : val :=
  λ: "l",
    match: "l" with
      InjL "_" => #false
    | InjR "_" => #true
    end.

Definition dae4 : val :=
  λ: "l",
    match: "l" with
      InjL "p" => "p"
    | InjR "p" => "p"
    end.

Definition f6' (n : nat) : val :=
  λ: "l",
    let: "ver" := !"l" in
    let: "data" := array_clone ("l" +ₗ #2) #n in
    let: "backup" := !("l" +ₗ #1) in
    if: bff3_valid "backup" && (!"l" = "ver") then (
      ("data", "backup", "ver")
    ) else (
      array_copy_to "data" (dae4 "backup") #n;;
      ("data", "backup", "ver")
    ).

Definition f6 (n : nat) : val := λ: "l", Fst (Fst (f6' n "l")).

Definition dcb7 : val :=
  rec: "dcb7" "l" "l'" "n" :=
    if: "n" ≤ #0 then #true
    else
      (!"l" = !"l'") && ("dcb7" ("l" +ₗ #1) ("l'" +ₗ #1) ("n" - #1)).

Definition fa8 (n : nat) : val :=
  λ: "l" "ver" "desired" "backup'",
    if: ("ver" `rem` #2 = #0) && (CAS "l" "ver" (#1 + "ver")) then

      array_copy_to ("l" +ₗ #2) "desired" #n;;

      "l" <- #2 + "ver";;
      CmpXchg ("l" +ₗ #1) (InjL "backup'") (InjR "backup'");;
      #()
    else #().

Definition x9 (n : nat) : val :=
  λ: "l" "expected" "desired",
    let: "old" := f6' n "l" in
    if: dcb7 (Fst (Fst "old")) "expected" #n then
      if: dcb7 "expected" "desired" #n then #true
      else
        let: "backup'" := array_clone "desired" #n in
        let: "backup" := (Snd (Fst "old")) in
        if: (CAS ("l" +ₗ #1) "backup" (InjL "backup'")) || (CAS ("l" +ₗ #1) (InjR (dae4 "backup")) (InjL "backup'")) then
          fa8 n "l" (Snd "old") "desired" "backup'";;
          #true
        else #false
    else #false.

Definition x10 := gmap nat $ agree $ (loc * list val)%type.

Definition fde11 := gmap nat $ agree nat.

Definition x12 := authUR $ gmapUR nat (agreeR locO).

Definition x13 := authUR $ gmapUR loc $ agreeR $ (prodO gnameO (listO valO)).

Definition c14 := gmap nat $ agree (gname * gname * loc).
Definition b15 := authUR $ gmapUR nat $ agreeR $ prodO (prodO gnameO gnameO) locO.

Definition bbf16 := authUR $ gsetUR $ locO.
Definition c17 := authUR $ gmapUR locO $ agreeR natO.
Definition cfb18 := authUR $ gmapUR locO $ agreeR natO.

Class fe19 (Σ : gFunctors) := {
  acee130 :: heapGS Σ;
  c131 :: inG Σ x13;
  d132 :: inG Σ x12;
  b133 :: inG Σ b15;
  ea134 :: mono_natG Σ;
  f135 :: ghost_varG Σ bool;
  d136 :: ghost_varG Σ (loc * list val);
  da137 :: tokenG Σ;
  a138 :: inG Σ c17;
  adf139 :: inG Σ cfb18;
  bf140 :: inG Σ bbf16;
}.

Section ecb141_wf.
  Context `{!fe19 Σ, !heapGS Σ}.

  Lemma eaa20 (l l' : loc) (dq dq' : dfrac) (vs vs' : list val) :
    length vs = length vs' → Forall2 vals_compare_safe vs vs' →
    {{{ l ↦∗{dq} vs ∗ l' ↦∗{dq'} vs' }}}
      dcb7 #l #l' #(length vs)
    {{{ RET #(bool_decide (vs = vs')); l ↦∗{dq} vs ∗ l' ↦∗{dq'} vs' }}}.
    iIntros (Hlen Hsafe Φ) "[Hl Hl'] HΦ".
    Proof.
    iInduction vs as [|v vs] "IH" forall (l l' vs' Hsafe Hlen) "HΦ".
    - wp_rec. wp_pures.
      apply symmetry, length_zero_iff_nil in Hlen as ->.
      iModIntro.
      rewrite bool_decide_eq_true_2; last done.
      iApply "HΦ". iFrame.
    - wp_rec. wp_pures.
      destruct vs' as [| v' vs']; first discriminate.
      inv Hlen. inv Hsafe.
      repeat rewrite array_cons.
      iDestruct "Hl" as "[Hl Hlrest]".
      iDestruct "Hl'" as "[Hl' Hlrest']".
      do 2 wp_load.
      wp_pures.
      destruct (decide (v = v')) as [-> | Hne].
      + rewrite (bool_decide_eq_true_2 (v' = v')); last done.
        wp_pures.
        rewrite Z.sub_1_r.
        rewrite -Nat2Z.inj_pred /=; last lia.
        iApply ("IH" $! _ _ vs' with "[//] [//] [$] [$]").
        iIntros "!> [Hlrest Hlrest']".
        iSpecialize ("HΦ" with "[$]").
        destruct (decide (vs = vs')) as [-> | Hne].
        * rewrite bool_decide_eq_true_2; last done.
          by rewrite bool_decide_eq_true_2.
        * rewrite bool_decide_eq_false_2.
          -- by rewrite bool_decide_eq_false_2.
          -- by intros [=].
      + rewrite (bool_decide_eq_false_2 (v = v')); last done.
        iSpecialize ("HΦ" with "[$]").
        wp_pures.
        destruct (decide (vs = vs')) as [-> | Hne'];
        rewrite bool_decide_eq_false_2; auto; by intros [=].
  Qed.

  Context (N : namespace).

  Definition a21 := N .@ "ecb141_wf".

  Definition x22 := N .@ "x9".

  Definition e23 := N .@ "f6".

  Definition ab24_own γᵢ (q : Qp) (fde11 : list loc) := own γᵢ (●{#q} map_seq 0 (to_agree <$> fde11)).

  Definition c31_own' γ (fde11 : list loc) := own γ (◯ map_seq 0 (to_agree <$> fde11)).

  Definition x26_own γᵥ (q : Qp) (x10 : gmap loc (gname * list val)) := own γᵥ (●{#q} fmap (M:=gmap loc) to_agree x10).

  Definition a27_own γᵥ (q : Qp) (x10 : gmap loc nat) := own γᵥ (●{#q} fmap (M:=gmap loc) to_agree x10).

  Definition b28 γ (backup : loc) (vs : list val) : iProp Σ := ghost_var γ (1/2) (backup, vs).

  Definition ec29_own γₕ l γ (b28 : list val) := own γₕ (◯ {[l := to_agree (γ, b28)]}).

  Definition eee30_own γ (l : loc) (ver : nat) := own γ (◯ {[l := to_agree ver]}).

  Definition c31_own γᵢ (i : nat) (l : loc) := own γᵢ (◯ {[i := to_agree l]}).

  Definition ca32_own γ (q : Qp) (validated : gset loc) := own γ (●{#q} validated).

  Definition a33_own γ (l : loc) := own γ (◯ {[ l ]}).

  Definition x34 `{Countable K} (m : gmap K nat) : nat :=
    map_fold (λ _ ver acc, max ver acc) 0 m.

  Lemma dd35 (x y z : nat) :
    x ≤ Nat.max y z ↔ x ≤ y ∨ x ≤ z.
  Proof.
    split.
    - intros H.
      destruct (le_ge_dec y z) as [Hyz|Hzy].
      + rewrite (Nat.max_r y z) // in H. auto.
      + rewrite (Nat.max_l y z) in H; auto with lia.
    - intros [Hy|Hz].
      + eapply Nat.le_trans; first done. apply Nat.le_max_l.
      + eapply Nat.le_trans; first done. apply Nat.le_max_r.
  Qed.

  Lemma be36_spec {K} `{Countable K} (m : gmap K nat) k v :
    m !! k = Some v → v ≤ x34 m.
  Proof.
    unfold x34.
    intros Hlookup.
    induction m using map_first_key_ind.
    - done.
    - rewrite map_fold_insert_first_key //.
      destruct (decide (i = k)) as [<- | Hne].
      + rewrite lookup_insert_eq in Hlookup.
        simplify_eq. rewrite dd35. auto.
      + rewrite lookup_insert_ne // in Hlookup.
        rewrite dd35. auto.
  Qed.

  Lemma ba37_update (l : loc) γ (fde11 : list loc) :
    ab24_own γ 1 fde11 ==∗
      ab24_own γ 1 (fde11 ++ [l]) ∗ c31_own γ (length fde11) l.
  Proof.
    iIntros "H●".
    rewrite /ab24_own /c31_own.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update
        with
          (i := length fde11)
          (x := to_agree l).
      { rewrite lookup_map_seq_None length_fmap. by right. }
      constructor. }
    replace (length fde11) with (O + length (to_agree <$> fde11)) at 1
          by (now rewrite length_fmap).
    rewrite -map_seq_snoc fmap_snoc. by iFrame.
  Qed.

  Lemma c38_alloc i l γ fde11 q :
    fde11 !! i = Some l →
      ab24_own γ q fde11 ==∗
        ab24_own γ q fde11 ∗ c31_own γ i l.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[i := to_agree l]}).
      { apply _. }
      apply singleton_included_l with (i := i).
      exists (to_agree l). split; last done.
      rewrite lookup_map_seq_0 list_lookup_fmap Hlookup //. }
    by iFrame.
  Qed.

  Lemma c38_alloc' i l γ fde11 q :
    fde11 !! i = Some l →
      ab24_own γ q fde11 ==∗ c31_own γ i l.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[i := to_agree l]}).
      { apply _. }
      apply singleton_included_l with (i := i).
      exists (to_agree l). split; last done.
      rewrite lookup_map_seq_0 list_lookup_fmap Hlookup //. }
    by iFrame.
  Qed.

  Lemma bde40_update (l : loc) (γ : gname) (validated : gset loc) :
    ca32_own γ 1 validated ==∗
      ca32_own γ 1 ({[ l ]} ∪ validated) ∗ a33_own γ l.
  Proof.
    iIntros "H●".

    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply (gset_local_update _ _ ({[ l ]} ∪ validated)). set_solver. }
    iFrame. iModIntro.
    rewrite /a33_own.
    iPoseProof (own_mono with "H◯") as "H"; last done.
    apply auth_frag_mono. set_solver.
  Qed.

  Lemma cf41_alloc (l : loc) (γ : gname) (q : Qp) (validated : gset loc) :
    l ∈ validated →
      ca32_own γ q validated ==∗ ca32_own γ q validated ∗ a33_own γ l.
  Proof.
    iIntros (Hfresh) "H●".
    iMod (own_update with "H●") as "[H● H◯]".
    { apply (auth_update_dfrac_alloc _ _ {[ l ]}). set_solver. }
    by iFrame.
  Qed.

  Lemma e42 (γ : gname) (q : Qp) (validated : gset loc) :
    ca32_own γ q validated ==∗ ca32_own γ q validated ∗ own γ (◯ validated).
  Proof.
    iIntros "H●".
    iMod (own_update with "H●") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := validated).
      - apply _.
      - reflexivity. }
    by iFrame.
  Qed.

  Lemma x43_agree γ dq l validated :
    ca32_own γ dq validated -∗
      a33_own γ l -∗
        ⌜l ∈ validated⌝.
  Proof.
    iIntros "●H ◯H".
    iCombine "●H ◯H" gives %(_ & H & _)%auth_both_dfrac_valid_discrete.
    set_solver.
  Qed.

  Lemma x44_update (l : loc) (b28 : list val) (γ γₕ : gname) (x10 : gmap loc (gname * list val)) :
    x10 !! l = None →
      x26_own γₕ 1 x10 ==∗
        x26_own γₕ 1 (<[l := (γ, b28)]>x10) ∗ ec29_own γₕ l γ b28.
  Proof.
    iIntros (Hfresh) "H●".
    rewrite /x26_own /ec29_own.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update
        with
          (i := l)
          (x := to_agree (γ, b28)).
      { by rewrite lookup_fmap fmap_None. }
      constructor. }
    rewrite fmap_insert.
    by iFrame.
  Qed.

  Lemma ea45_update (l : loc) (ver : nat) (γ : gname) (x10 : gmap loc nat) :
    x10 !! l = None →
      a27_own γ 1 x10 ==∗
        a27_own γ 1 (<[l := ver]>x10) ∗ eee30_own γ l ver.
  Proof.
    iIntros (Hfresh) "H●".
    rewrite /x26_own /ec29_own.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update
        with
          (i := l)
          (x := to_agree ver).
      { by rewrite lookup_fmap fmap_None. }
      constructor. }
    rewrite -fmap_insert.
    by iFrame.
  Qed.

  Lemma dc46 vers l i γ q :
    vers !! l = Some i →
      a27_own γ q vers ==∗
        a27_own γ q vers ∗ eee30_own γ l i.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[ l := to_agree i ]}).
      { apply _. }
      apply singleton_included_l with (i := l).
      exists (to_agree i). split; last done.
      rewrite lookup_fmap Hlookup //.
    }
    by iFrame.
  Qed.

  Lemma b47_alloc i γ b28 γₕ x10 q :
    x10 !! i = Some (γ, b28) →
      x26_own γₕ q x10 ==∗
        x26_own γₕ q x10 ∗ ec29_own γₕ i γ b28.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[i := to_agree (γ, b28)]}).
      { apply _. }
      apply singleton_included_l with (i := i).
      exists (to_agree (γ, b28)). split; last done.
      rewrite lookup_fmap Hlookup //.
    }
    by iFrame.
  Qed.

  Lemma d48_agree γₕ q x10 i γ b28 :
    x26_own γₕ q x10 -∗
      ec29_own γₕ i γ b28 -∗
        ⌜x10 !! i = Some (γ, b28)⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    rewrite -lookup_fmap /= Hvs'' //.
  Qed.

  Lemma aee49_agree (γ : gname) (i : nat) (l : loc) (fde11 : list loc) (q : Qp) :
    ab24_own γ q fde11 -∗
      c31_own γ i l -∗
        ⌜fde11 !! i = Some l⌝.
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

  Lemma af50_lookup {A} (xs ys : list A) :
    (∀ i x, xs !! i = Some x → ys !! i = Some x) → xs `prefix_of` ys.
  Proof.
    rewrite /prefix. generalize dependent ys.
    induction xs as [| x xs IH].
    - eauto.
    - intros ys Hpoint. simpl.
      destruct ys as [| y ys].
      { specialize (Hpoint 0 x). intuition. discriminate. }
      epose proof (IH ys _) as [ys' ->]. Unshelve.
      + specialize (Hpoint 0 x). simpl in *.
        intuition. simplify_eq. eauto.
      + intros i x' Hlookup.
        specialize (Hpoint (S i) x').
        auto.
  Qed.

  Lemma cf51 {A} (l l' : list A) :
    map_seq (M := gmap nat A) O l ⊆ map_seq O l' →
      l `prefix_of` l'.
  Proof.
    intros Hincl.
    rewrite map_subseteq_spec in Hincl.
    apply af50_lookup.
    intros i x.
    do 2 rewrite -lookup_map_seq_0.
    apply Hincl.
  Qed.

  Lemma e52 (m m' : gmap loc (gname * list val)) :
          (to_agree <$> m) ≼ (to_agree <$> m') → m ⊆ m'.
  Proof.
    intros Hincl. apply map_subseteq_spec.
    intros i x Hix.
    rewrite lookup_included in Hincl.
    specialize (Hincl i).
    do 2 rewrite lookup_fmap in Hincl.
    rewrite Hix /= in Hincl.
    apply Some_included_is_Some in Hincl as H.
    destruct H as [y Hsome].
    rewrite Hsome Some_included_total in Hincl.
    rewrite -lookup_fmap lookup_fmap_Some in Hsome.
    destruct Hsome as (x' & <- & Hix').
    by apply to_agree_included, leibniz_equiv in Hincl as <-.
  Qed.

  Lemma e52' (m m' : gmap loc nat) :
          (to_agree <$> m) ≼ (to_agree <$> m') → m ⊆ m'.
  Proof.
    intros Hincl. apply map_subseteq_spec.
    intros i x Hix.
    rewrite lookup_included in Hincl.
    specialize (Hincl i).
    do 2 rewrite lookup_fmap in Hincl.
    rewrite Hix /= in Hincl.
    apply Some_included_is_Some in Hincl as H.
    destruct H as [y Hsome].
    rewrite Hsome Some_included_total in Hincl.
    rewrite -lookup_fmap lookup_fmap_Some in Hsome.
    destruct Hsome as (x' & <- & Hix').
    by apply to_agree_included, leibniz_equiv in Hincl as <-.
  Qed.

  Lemma e52'' (m m' : gmap nat loc) :
          (to_agree <$> m) ≼ (to_agree <$> m') → m ⊆ m'.
  Proof.
    intros Hincl. apply map_subseteq_spec.
    intros i x Hix.
    rewrite lookup_included in Hincl.
    specialize (Hincl i).
    do 2 rewrite lookup_fmap in Hincl.
    rewrite Hix /= in Hincl.
    apply Some_included_is_Some in Hincl as H.
    destruct H as [y Hsome].
    rewrite Hsome Some_included_total in Hincl.
    rewrite -lookup_fmap lookup_fmap_Some in Hsome.
    destruct Hsome as (x' & <- & Hix').
    by apply to_agree_included, leibniz_equiv in Hincl as <-.
  Qed.

  Lemma aee49_agree' (γ : gname) (q : Qp) (fde11 fde11' : list loc) :
    ab24_own γ q fde11 -∗
      c31_own' γ fde11' -∗
        ⌜fde11' `prefix_of` fde11⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & Hvalid & _)%auth_both_dfrac_valid_discrete.
    iPureIntro.
    apply cf51, e52''.
    by repeat rewrite fmap_map_seq.
  Qed.

  Definition bad56 γᵣ (requests : list (gname * gname * loc)) :=
    own γᵣ (● map_seq O (to_agree <$> requests)).

  Definition ba57 γᵣ i (γₗ γₑ : gname) (l : loc) :=
   own γᵣ (◯ ({[i := to_agree (γₗ, γₑ, l)]})).

  Lemma f58_update γₗ γₑ l γ requests :
    bad56 γ requests ==∗
      bad56 γ (requests ++ [(γₗ, γₑ, l)]) ∗ ba57 γ (length requests) γₗ γₑ l.
  Proof.
    iIntros "H●".
    rewrite /bad56 /ba57.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update
        with
          (i := length requests)
          (x := to_agree (γₗ, γₑ, l)).
      { rewrite lookup_map_seq_None length_fmap. by right. }
      constructor. }
    replace (length requests) with (O + length (to_agree <$> requests)) at 1
          by (now rewrite length_fmap).
    rewrite -map_seq_snoc fmap_snoc. by iFrame.
  Qed.

  Lemma bfd59_agree γᵣ (requests : list (gname * gname * loc)) (i : nat) γₗ γₑ ver :
    bad56 γᵣ requests -∗
      ba57 γᵣ i γₗ γₑ ver -∗
        ⌜requests !! i = Some (γₗ, γₑ, ver)⌝.
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

  Definition f60 (Φ : val → iProp Σ) γ (expected desired : list val) (lexp ldes : loc) dq dq' : iProp Σ :=
       AU <{ ∃∃ backup actual, b28 γ backup actual }>
            @ ⊤ ∖ ↑N, ∅
          <{ if bool_decide (actual = expected) then ∃ backup', b28 γ backup' desired else b28 γ backup actual,
             COMM lexp ↦∗{dq} expected ∗ ldes ↦∗{dq'} desired -∗ Φ #(bool_decide (actual = expected)) }>.

  Definition ad61_inv (Φ : val → iProp Σ) (γ γₑ γₗ γₜ : gname) (lexp ldes : loc) (dq dq' : dfrac) (expected desired : list val) : iProp Σ :=
      ((lexp ↦∗{dq} expected ∗ ldes ↦∗{dq'} desired -∗ Φ #false) ∗ (∃ b : bool, ghost_var γₑ (1/2) b) ∗ ghost_var γₗ (1/2) false)
    ∨ (£ 1 ∗ f60 Φ γ expected desired lexp ldes dq dq' ∗ ghost_var γₑ (1/2) true ∗ ghost_var γₗ (1/2) true)
    ∨ (token γₜ ∗ (∃ b : bool, ghost_var γₑ (1/2) b) ∗ ∃ b : bool, ghost_var γₗ (1/2) b).

  Definition ac62 (x10 : gmap loc (gname * list val)) : iProp Σ :=
    ([∗ map] backup ↦ '(γ, vs) ∈ x10, token γ ∗ backup ↦∗□ vs)%I.

  Lemma adc63 x10 l γ b28 :
    x10 !! l = Some (γ, b28) → ac62 x10 -∗ token γ ∗ l ↦∗□ b28.
  Proof.
    iIntros (Hbound) "Hlog".
    iPoseProof (big_sepM_lookup with "Hlog") as "H /=".
    { done. }
    done.
  Qed.

  Lemma bdc64 l γ b28 :
    ac62 {[ l := (γ, b28) ]} ⊣⊢ token γ ∗ l ↦∗□ b28.
  Proof.
    rewrite /ac62 big_sepM_singleton //.
  Qed.

  Definition ad65_inv γ γₗ γₑ (lactual lexp : loc) (actual : list val) (used : gset loc) : iProp Σ :=
    ⌜lexp ∈ used⌝ ∗
    ghost_var γₗ (1/2) (bool_decide (lactual = lexp)) ∗
    ∃ (Φ : val → iProp Σ) (γₜ : gname) (lexp ldes : loc) (dq dq' : dfrac) (expected desired : list val),
      ghost_var γₑ (1/2) (bool_decide (actual = expected)) ∗
      inv x22 (ad61_inv Φ γ γₑ γₗ γₜ lexp ldes dq dq' expected desired).

  Definition x66_inv γ lactual actual (requests : list (gname * gname * loc)) (used : gset loc) : iProp Σ :=
    [∗ list] '(γₗ, γₑ, lexp) ∈ requests, ad65_inv γ γₗ γₑ lactual lexp actual used.

  Lemma d67 γ backup expected requests used used' :
    used ⊆ used' →
      x66_inv γ backup expected requests used -∗
        x66_inv γ backup expected requests used'.
  Proof.
    iIntros (Hsub) "Hreginv".
    iInduction requests as [|[[γₗ γₑ] lexp] requests] "IH".
    - done.
    - rewrite /x66_inv /=.
      iDestruct "Hreginv" as "[Hreqinv Hreginv]".
      iPoseProof ("IH" with "Hreginv") as "$".
      rewrite /ad65_inv.
      iDestruct "Hreqinv" as "(%Hin & $ & $)".
      iPureIntro. set_solver.
  Qed.

  Lemma d68 l dq dq' vs vs' : length vs = length vs' → l ↦∗{dq} vs -∗ l ↦∗{dq'} vs' -∗ l ↦∗{dq ⋅ dq'} vs ∗ ⌜vs = vs'⌝.
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

  Lemma c69_valid l dq vs : length vs > 0 → l ↦∗{dq} vs -∗ ⌜✓ dq⌝.
  Proof.
    iIntros (Hpos) "Hl".
    destruct vs as [|v vs].
    { inv Hpos. }
    rewrite array_cons.
    iDestruct "Hl" as "[Hl _]".
    iApply (pointsto_valid with "Hl").
  Qed.

  Lemma ec70 l vs vs' :
    length vs = length vs' → length vs > 0 →
      l ↦∗ vs -∗ l ↦∗□ vs' -∗ False.
  Proof.
    iIntros (Hlensame Hlenpos) "Hl Hl'".
    iPoseProof (d68 with "Hl Hl'") as "[Hl %HJ]".
    { done. }
    by iDestruct (c69_valid with "Hl") as %Hvalid.
  Qed.

  Definition dbc71 {K A} `{Countable K} (m : gmap K A) :=
    ∀ i j v, m !! i = Some v → m !! j = Some v → i = j.

  Definition caf72_inv (γ γᵥ γₕ γᵢ γ_val : gname) (l : loc) (len : nat) : iProp Σ :=
    ∃ (ver : nat) (x10 : gmap loc (gname * list val)) (actual cache : list val) (marked_backup : val) (backup backup' : loc) (fde11 : list loc) (validated : gset loc),

      l ↦ #ver ∗

      (l +ₗ 1) ↦{# 1/2} marked_backup ∗

      ghost_var γ (1/4) (backup, actual) ∗

      ⌜Forall val_is_unboxed actual⌝ ∗

      backup ↦∗□ actual ∗

      ⌜last fde11 = Some backup'⌝ ∗

      ⌜marked_backup = InjLV #backup ∨ marked_backup = InjRV #backup ∧ Nat.Even ver ∧ actual = cache ∧ backup = backup'⌝ ∗

      ⌜length actual = len⌝ ∗
      ⌜length cache = len⌝ ∗

      ⌜map_Forall (λ _ '(_, b28), length b28 = len) x10⌝ ∗

      ac62 x10 ∗

      ⌜snd <$> x10 !! backup = Some actual⌝ ∗

      x26_own γₕ (1/2) x10 ∗

      ⌜length fde11 = S (Nat.div2 (S ver))⌝ ∗

      ⌜NoDup fde11⌝ ∗

      ⌜Forall (.∈ dom x10) fde11⌝ ∗

      ab24_own γᵢ (1/4) fde11 ∗

      mono_nat_auth_own γᵥ (1/4) ver ∗

      (l +ₗ 2) ↦∗{# 1/2} cache ∗

      ⌜if Nat.even ver then snd <$> x10 !! backup' = Some cache else marked_backup = InjLV #backup⌝ ∗

      (if Nat.even ver then ab24_own γᵢ (1/4) fde11 ∗ mono_nat_auth_own γᵥ (1/4) ver ∗(l +ₗ 2) ↦∗{# 1/2} cache else True) ∗

      ca32_own γ_val 1 validated ∗

      ⌜if bool_decide (backup ∈ validated) then marked_backup = InjRV #backup else marked_backup = InjLV #backup⌝ ∗

      ⌜validated ⊆ dom x10⌝.

  Definition a73 (order : gmap loc nat) (loc loc' : loc) :=
    ∀ i j,
      order !! loc = Some i →
        order !! loc' = Some j →
          i < j.

  Lemma f74_alloc (l : loc) (i : nat) (order : gmap loc nat) (fde11 : list loc) :
    l ∉ fde11 →
      StronglySorted (a73 order) fde11 →
        StronglySorted (a73 (<[l := i]>order)) fde11.
  Proof.
    induction fde11 as [|loc' fde11 IH].
    - intros. constructor.
    - intros [Hne Hnmem]%not_elem_of_cons Hsorted.
      inv Hsorted.
      constructor.
      + auto.
      + clear IH H1.
        induction fde11 as [| loc'' fde11 IH'].
        * constructor.
        * inv H2. rewrite not_elem_of_cons in Hnmem.
          destruct Hnmem as [Hne' Hnmem].
          constructor.
          { rewrite /a73.
            intros j k.
            do 2 rewrite lookup_insert_ne //. auto. }
          { auto. }
  Qed.

  Lemma ca75 (order order' : gmap loc nat) (fde11 : list loc) :
    order ⊆ order' →
      Forall (.∈ dom order) fde11 →
        StronglySorted (a73 order) fde11 →
          StronglySorted (a73 order') fde11.
  Proof.
    intros Hsub Hdom Hssorted.
    induction fde11 as [| l fde11 IH].
    - constructor.
    - inv Hdom. inv Hssorted. constructor.
      + auto.
      + clear IH H3.
        induction fde11 as [| l' fde11 IH].
        * constructor.
        * inv H2. inv H4.
          constructor.
          { intros i j Hi Hj.
            apply elem_of_dom in H1 as [i' Hi'].
            apply elem_of_dom in H3 as [j' Hj'].
            rewrite map_subseteq_spec in Hsub.
            apply Hsub in Hi' as Hi''.
            apply Hsub in Hj' as Hj''.
            simplify_eq.
            by apply H2. }
          { auto. }
  Qed.

  Lemma ee76 {A} (Q R : A → A → Prop) (l : list A) :
    (∀ x y, Q x y → R x y) →
      StronglySorted Q l →
        StronglySorted R l.
  Proof.
    intros Hweak Hsorted.
    induction Hsorted.
    - constructor.
    - constructor.
      + done.
      + eapply Forall_impl; eauto.
  Qed.

  Lemma x77_snoc {A} (R : A → A → Prop) (xs : list A) (y : A) :
    StronglySorted R xs →
      Forall (λ x, R x y) xs →
        StronglySorted R (xs ++ [y]).
  Proof.
    induction xs as [|x xs IH]; intros Hssorted Hord.
    - repeat constructor.
    - inv Hssorted. inv Hord. simpl. constructor.
      + by apply IH.
      + rewrite Forall_app; auto.
  Qed.

  Definition c78_inv (γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ : gname) (l : loc) : iProp Σ :=
    ∃ (ver : nat) x10 (actual : list val) (marked_backup : val) (backup : loc) requests (vers : gmap loc nat) (fde11 : list loc) (order : gmap loc nat) (idx : nat),

      mono_nat_auth_own γᵥ (1/2) ver ∗

      (l +ₗ 1) ↦{# 1/2} marked_backup ∗

      ghost_var γ (1/4) (backup, actual) ∗

      ⌜snd <$> x10 !! backup = Some actual⌝ ∗

      x26_own γₕ (1/2) x10 ∗

      bad56 γᵣ requests ∗

      x66_inv γ backup actual requests (dom x10) ∗

      a27_own γ_vers 1 vers ∗

      ⌜dom vers ⊂ dom x10⌝ ∗

      ⌜if bool_decide (1 < size x10) then
        (∃ ver' : nat,

          vers !! backup = Some ver' ∧

          ver' ≤ ver ∧

          map_Forall (λ _ ver'', ver'' ≤ ver') vers ∧

          if bool_decide (ver = ver') then marked_backup = InjLV #backup else True)
      else vers = ∅⌝ ∗

      ab24_own γᵢ (1/2) fde11 ∗

      a27_own γₒ 1 order ∗

      ⌜dom order = dom x10⌝ ∗

      ⌜dbc71 order⌝ ∗

      ⌜order !! backup = Some idx⌝ ∗

      ⌜StronglySorted (a73 order) fde11⌝ ∗

      ⌜map_Forall (λ _ idx', idx' ≤ idx) order⌝.

  Global Instance df79_persistent l vs : Persistent (l ↦∗□ vs).
  Proof.
    rewrite /Persistent.
    iIntros "P".
    iInduction vs as [|v vs] "IH" forall (l).
    - rewrite array_nil. by iModIntro.
    - rewrite array_cons.
      iDestruct "P" as "[#Hl Hrest]".
      iPoseProof ("IH" with "Hrest") as "Hvs".
      by iFrame "#".
  Qed.

  Lemma x80 `{Countable K} {V} (x10 : gmap K V) (fde11 : list K) (backup' : K) : Forall (.∈ dom x10) fde11 → last fde11 = Some backup' → is_Some (x10 !! backup').
  Proof.
    rewrite Forall_lookup last_lookup.
    intros Hrange Hindex.
    by eapply elem_of_dom, Hrange.
  Qed.

  Lemma wp_array_copy_to' γ γᵥ γₕ γᵢ γ_val (dst src : loc) (n i : nat) vdst ver :

    i ≤ n → length vdst = n - i →
      inv e23 (caf72_inv γ γᵥ γₕ γᵢ γ_val src n) -∗

        mono_nat_lb_own γᵥ ver -∗
          {{{ (dst +ₗ i) ↦∗ vdst }}}
            array_copy_to #(dst +ₗ i) #(src +ₗ 2 +ₗ i) #(n - i)
          {{{ vers vdst', RET #();

              (dst +ₗ i) ↦∗ vdst' ∗
              ⌜length vdst' = n - i⌝ ∗

              ⌜StronglySorted Nat.le vers⌝ ∗

              ⌜Forall (Nat.le ver) vers⌝ ∗

              ([∗ list] j ↦ ver' ; v ∈ vers ; vdst',
                  mono_nat_lb_own γᵥ ver' ∗

                  (⌜Nat.Even ver'⌝ →

                    ∃ l γₜ vs,

                      c31_own γᵢ (Nat.div2 ver') l ∗

                      ec29_own γₕ l γₜ vs ∗

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
      iInv e23 as "(%ver' & %x10 & %actual & %cache & %marked_backup & %backup & %backup' & %fde11 & %validated & >Hver & >Hbackup & >Hγ & >%Hunboxed & >#□Hbackup & >%Hindex & >%Hvalidated & >%Hlenactual & >%Hlencache & >%Hloglen & Hlog & >%Hlogged & >●Hlog & >%Hlenᵢ & >%Hnodup & >%Hrange & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons & Hlock)" "Hcl".
      wp_apply (wp_load_offset with "Hcache").
      { apply list_lookup_lookup_total_lt. lia. }
      iMod (c38_alloc with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ]".
      { by rewrite last_lookup Hlenᵢ in Hindex. }
      iIntros "Hsrc".
      iPoseProof (mono_nat_lb_own_valid with "●Hγᵥ Hlb") as "[%Ha %Hord]".
      iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#Hlb'".
      eapply x80 in Hrange as Hbackup_logged; last done.
      destruct Hbackup_logged as [[γₜ backup'vs] Hbackup'vs].
      iMod (b47_alloc backup' with "●Hlog") as "[●Hlog #◯Hlog]".
      { done. }
      iMod ("Hcl" with "[-Hhd Htl HΦ]") as "_".
      { iExists ver', x10, actual, cache, marked_backup, backup, backup', fde11. iFrame "∗ # %". }
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
      { iSplitR "Hcons".
        - iSplitR; first done.
          iIntros "%Heven'".
          rewrite Nat.Odd_div2; first last.
          { rewrite Nat.Odd_succ //. }
          rewrite -Nat.even_spec in Heven'.
          rewrite Heven' in Hcons.
          iExists backup', _.
          iFrame "∗ # %".
          rewrite Nat.add_0_r.
          rewrite list_lookup_lookup_total_lt //.
          * iPureIntro. do 2 f_equal.
            rewrite -lookup_fmap lookup_fmap_Some in Hcons.
            destruct Hcons as ([γₜ' vs] & Heq & Hlookup).
            simpl in *. congruence.
          * rewrite /map_Forall in Hloglen.
            apply Hloglen in Hbackup'vs as ->. lia.
        - rewrite big_sepL2_mono; first done.
          iIntros (k ver''' v') "_ _ H".
          rewrite -Nat.add_1_r -Nat.add_assoc Nat.add_1_r //.  }
  Qed.

  Lemma ad82_agree γₕ p q (x10 x10' : gmap loc (gname * list val)) :
    x26_own γₕ p x10 -∗
      x26_own γₕ q x10'  -∗
        ⌜x10 = x10'⌝.
  Proof.
    iIntros "H H'".
    iCombine "H H'" gives %Hagree%auth_auth_dfrac_op_inv.
    iPureIntro.
    apply map_eq.
    intros i.
    apply leibniz_equiv, (inj (fmap to_agree)).
    repeat rewrite -lookup_fmap //.
  Qed.

  Lemma c83_agree γₕ p q (fde11 fde11' : list loc) :
    ab24_own γₕ p fde11 -∗
      ab24_own γₕ q fde11'  -∗
        ⌜fde11 = fde11'⌝.
  Proof.
    iIntros "H H'".
    iCombine "H H'" gives %Hagree%auth_auth_dfrac_op_inv.
    iPureIntro.
    apply list_eq.
    intros i.
    apply leibniz_equiv, (inj (fmap to_agree)).
    do 2 rewrite -lookup_map_seq_0 -lookup_fmap fmap_map_seq //.
  Qed.

  Lemma c84_agree γₕ p q (x10 x10' : gmap loc nat) :
    a27_own γₕ p x10 -∗
      a27_own γₕ q x10'  -∗
        ⌜x10 = x10'⌝.
  Proof.
    iIntros "H H'".
    iCombine "H H'" gives %Hagree%auth_auth_dfrac_op_inv.
    iPureIntro.
    apply map_eq.
    intros i.
    apply leibniz_equiv, (inj (fmap to_agree)).
    repeat rewrite -lookup_fmap //.
  Qed.

  Lemma d85_agree γₕ q x10 i b28 :
    a27_own γₕ q x10 -∗
      eee30_own γₕ i b28 -∗
        ⌜x10 !! i = Some b28⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    rewrite -lookup_fmap /= Hvs'' //.
  Qed.

  Lemma c86 γ γᵥ γₕ γᵢ γ_val (dst src : loc) (n : nat) vdst ver :

    length vdst = n →
      inv e23 (caf72_inv γ γᵥ γₕ γᵢ γ_val src n) -∗

        mono_nat_lb_own γᵥ ver -∗
          {{{ dst ↦∗ vdst }}}
            array_copy_to #dst #(src +ₗ 2) #n
          {{{ vers vdst', RET #();

              dst ↦∗ vdst' ∗
              ⌜length vdst' = n⌝ ∗

              ⌜StronglySorted Nat.le vers⌝ ∗

              ⌜Forall (Nat.le ver) vers⌝ ∗

              ([∗ list] i ↦ ver' ; v ∈ vers ; vdst',
                  mono_nat_lb_own γᵥ ver' ∗

                  (⌜Nat.Even ver'⌝ →

                    ∃ l γₜ vs,

                      c31_own γᵢ (Nat.div2 ver') l ∗

                      ec29_own γₕ l γₜ vs ∗

                      ⌜vs !! i = Some v⌝ ))}}}.
  Proof.
     iIntros "%Hvdst #Hinv #Hlb !> %Φ Hdst HΦ".
     rewrite -(Loc.add_0 (src +ₗ 2)).
     rewrite -(Loc.add_0 dst).
     replace (Z.of_nat n) with (n - 0)%Z by lia.
     change 0%Z with (Z.of_nat O).
     wp_smart_apply (wp_array_copy_to' _ _ _ _ _ _ _ _ _ vdst _ with "[//] [//] [$] [-]"); try lia.
     iIntros "!> %vers %vdst' /=".
     rewrite Nat.sub_0_r //.
  Qed.

  Lemma de87 γ γᵥ γₕ γᵢ γ_val (src : loc) (n : nat) ver :
    n > 0 →
      inv e23 (caf72_inv γ γᵥ γₕ γᵢ γ_val src n) -∗

        mono_nat_lb_own γᵥ ver -∗
          {{{ True }}}
            array_clone #(src +ₗ 2) #n
          {{{ vers vdst (dst : loc), RET #dst;

              dst ↦∗ vdst ∗
              ⌜length vdst = n⌝ ∗

              ⌜StronglySorted Nat.le vers⌝ ∗

              ⌜Forall (Nat.le ver) vers⌝ ∗

              ([∗ list] i ↦ ver' ; v ∈ vers ; vdst,
                  mono_nat_lb_own γᵥ ver' ∗

                  (⌜Nat.Even ver'⌝ →

                    ∃ l γₜ vs,

                      c31_own γᵢ (Nat.div2 ver') l ∗

                      ec29_own γₕ l γₜ vs ∗

                      ⌜vs !! i = Some v⌝)) }}}.
  Proof.
    iIntros "%Hpos #Hinv #Hlb %Φ !# _ HΦ".
    rewrite /array_clone.
    wp_pures.
    wp_alloc dst as "Hdst".
    { lia. }
    wp_pures.
    wp_apply (c86 with "[//] [//] [$]").
    { rewrite length_replicate. lia. }
    iIntros (vers vdst') "(Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
    wp_pures.
    iModIntro.
    iApply ("HΦ" with "[$Hdst $Hcons]").
    by iPureIntro.
  Qed.

  Lemma cbf88 n : Z.Even (Z.of_nat n) ↔ Nat.Even n.
  Proof.
    split.
    - intros [k H]. exists (Z.to_nat k). lia.
    - intros [k H]. exists k. lia.
  Qed.

  Lemma af89 n : Nat.Odd n ↔ Z.Odd (Z.of_nat n).
  Proof.
    split.
    - intros [k H]. exists k. lia.
    - intros [k H]. exists (Z.to_nat k). lia.
  Qed.

  Lemma a91' γ γᵥ γₕ γᵢ γ_val dst src (vs vs' : list val) i n dq :
    i ≤ n → length vs = n - i → length vs = length vs' →
        inv e23 (caf72_inv γ γᵥ γₕ γᵢ γ_val dst n) -∗
            {{{ (dst +ₗ 2 +ₗ i) ↦∗{#1 / 2} vs ∗ (src +ₗ i) ↦∗{dq} vs' }}}
              array_copy_to #(dst +ₗ 2 +ₗ i) #(src +ₗ i) #(n - i)%nat
            {{{ RET #(); (dst +ₗ 2 +ₗ i) ↦∗{#1 / 2} vs' ∗ (src +ₗ i) ↦∗{dq} vs' }}}.
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
      iInv e23 as "(%ver & %x10 & %actual & %cache & %marked_backup & %backup & %backup' & %fde11 & %validated & >Hver & >Hbackup & >Hγ & >%Hunboxed & >#□Hbackup & >%Hindex & >%Hvalidated & >%Hlenactual & >%Hlencache & >%Hloglen & Hlog & >%Hlogged & >●Hlog & >%Hlenᵢ & >%Hnodup & >%Hrange & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons & Hlock & Hval)" "Hcl".
      assert (i < length cache) as [v'' Hv'']%lookup_lt_is_Some by lia.
      destruct (Nat.even ver) eqn:Heven.
      + iMod "Hlock" as "(Hγᵢ' & Hγᵥ' & Hcache') /=".
        iCombine "Hcache Hcache'" as "Hcache".
        iPoseProof (update_array _ _ _ i v'' with "Hcache") as "[Hcache _]".
        { done. }
        by iCombine "Hdst Hcache" gives %[Hfrac%dfrac_valid_own_r <-].
      + simplify_eq.
        iPoseProof (update_array _ _ _ i v'' with "Hcache") as "[Hcache Hacc]".
        { done. }
        iCombine "Hdst Hcache" as "Hcache".
        rewrite dfrac_op_own Qp.half_half.
        wp_store.
        iDestruct "Hcache" as "[Hcache Hcache']".
        iPoseProof ("Hacc" with "Hcache") as "Hcache".

        simplify_eq.
        iMod ("Hcl" with "[-Hcache' Hdst' Hsrc Hsrc' HΦ]") as "_".
        { iExists ver, x10, actual, (<[i:=v']> cache), (InjLV #backup), backup, backup', fde11.
          iFrame "∗ # %".
          rewrite Heven. iFrame.
          iNext. repeat iSplit; try done.
          { iPureIntro. auto. }
          by rewrite length_insert. }
        iModIntro.
        wp_pures.
        rewrite -> Nat2Z.inj_sub by done.
        rewrite -Z.sub_add_distr.
        rewrite (Loc.add_assoc (dst +ₗ 2)) /=.
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
          rewrite (Loc.add_assoc (dst +ₗ 2)) /=.
          change 1%Z with (Z.of_nat 1).
          by rewrite -Nat2Z.inj_add Nat.add_comm /=.
  Qed.

  Lemma a91 γ γᵥ γₕ γᵢ γ_val dst src (vs vs' : list val) n dq :
    length vs = n → length vs = length vs' →
        inv e23 (caf72_inv γ γᵥ γₕ γᵢ γ_val dst n) -∗
          {{{ (dst +ₗ 2) ↦∗{#1 / 2} vs ∗ src ↦∗{dq} vs' }}}
            array_copy_to #(dst +ₗ 2) #src #n
          {{{ RET #(); (dst +ₗ 2) ↦∗{#1 / 2} vs' ∗ src↦∗ {dq} vs' }}}.
  Proof.
    iIntros (Hlen Hlen') "#Hinv %Φ !> [Hdst Hsrc] HΦ".
    rewrite -(Loc.add_0 (dst +ₗ 2)).
    rewrite -(Loc.add_0 src).
    change 0%Z with (Z.of_nat 0).
    rewrite -{2}(Nat.sub_0_r n).
    wp_apply (a91' _ _ _ _ _ _ _ vs vs' with "[$] [$] [$]").
    - lia.
    - lia.
    - done.
  Qed.

  Lemma b92 n : Nat.Even n ↔ ¬ (Nat.Odd n).
  Proof.
    split.
    - rewrite /not. apply Nat.Even_Odd_False.
    - intros Hnotodd. by pose proof Nat.Even_or_Odd n as [Heven | Hodd].
  Qed.

  Lemma eefe93 n : Nat.Odd n ↔ ¬ (Nat.Even n).
  Proof.
    split.
    - rewrite /not. intros. by eapply Nat.Even_Odd_False.
    - intros Hnotodd. by pose proof Nat.Even_or_Odd n as [Heven | Hodd].
  Qed.

  Lemma ec94 n : Nat.div2 (S (S n)) = S (Nat.div2 n).
  Proof. done. Qed.

  Definition ff95_wf (v : val) (γ : gname) (n : nat) : iProp Σ :=
    ∃ (dst : loc) (γₕ γᵥ γᵣ γᵢ γₒ γ_vers γ_val : gname),
      ⌜v = #dst⌝ ∗
      inv e23 (caf72_inv γ γᵥ γₕ γᵢ γ_val dst n) ∗
      inv a21 (c78_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ dst).

  Lemma x96 l vs : l ↦∗ vs ==∗ l ↦∗□ vs.
  Proof.
    iInduction vs as [| v vs] "IH" forall (l).
    - by iIntros.
    - do 2 rewrite array_cons. iIntros "[Hl Hrest]".
      iSplitL "Hl".
      + iApply (pointsto_persist with "Hl").
      + iApply ("IH" with "Hrest").
  Qed.

  Lemma cd97 `{Countable K} {V} (k : K) (v : V) :
    dbc71 {[k := v]}.
  Proof.
    rewrite /dbc71.
    intros i j v'. do 2 rewrite lookup_singleton_Some.
    by intros [<- <-] [<- _].
  Qed.

Lemma acbd98_insert `{Countable K, Countable V} (k : K) (v : V) (m : gmap K V) :
  v ∉ map_img (SA:=gset V) m →
    dbc71 m →
      dbc71 (<[k := v]>m).
  Proof.
    rewrite /dbc71. intros Hfresh Hinj.
    intros i j v'.
    destruct (decide (i = k)) as [-> | Hne]; destruct (decide (j = k)) as [-> | Hne'].
    - rewrite lookup_insert_eq //.
    - rewrite lookup_insert_eq lookup_insert_ne //.
      intros [=<-] Hmj. by apply not_elem_of_map_img_1 with (i := j) in Hfresh.
    - rewrite lookup_insert_eq lookup_insert_ne //.
      intros Hsome [=<-]. by apply not_elem_of_map_img_1 with (i := i) in Hfresh.
    - do 2 rewrite lookup_insert_ne //. apply Hinj.
  Qed.

  Lemma bd99_spec (n : nat) (src : loc) dq vs :
    length vs = n → n > 0 → Forall val_is_unboxed vs →
      {{{ src ↦∗{dq} vs }}}
        bcaf2 n #src
      {{{ v γ, RET v; src ↦∗{dq} vs ∗ ff95_wf v γ n ∗ ∃ backup, b28 γ backup vs  }}}.
  Proof.
Admitted.

  Lemma c100 x y : x ≤ y → Nat.div2 x ≤ Nat.div2 y.
  Proof.
    intros Hle. induction Hle as [| y Hle IH].
    - done.
    - destruct (Nat.Even_Odd_dec y).
      + by rewrite -Nat.Even_div2.
      + rewrite <- Nat.Odd_div2 by done. by constructor.
  Qed.

  Lemma be101 n b : Nat.even n = b ↔ Nat.odd n = negb b.
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

  Lemma fc102 n b : Nat.odd n = b ↔ Nat.even n = negb b.
  Proof.
    rewrite be101 negb_involutive //.
  Qed.

  Lemma x103 n : Z.even (Z.of_nat n) = Nat.even n.
  Proof.
    destruct (Z.even n) eqn:H, (Nat.even n) eqn:H'; auto.
    - rewrite Z.even_spec cbf88 in H.
      by rewrite -not_true_iff_false Nat.even_spec in H'.
    - rewrite Nat.even_spec in H'.
      by rewrite -not_true_iff_false Z.even_spec cbf88 in H.
  Qed.

  Lemma fbe104 n : Z.odd (Z.of_nat n) = Nat.odd n.
  Proof.
    destruct (Z.odd n) eqn:H, (Nat.odd n) eqn:H'; auto.
    - rewrite Z.odd_spec -af89 in H.
      by rewrite -not_true_iff_false Nat.odd_spec in H'.
    - rewrite Nat.odd_spec in H'.
      by rewrite -not_true_iff_false Z.odd_spec -af89 in H.
  Qed.

  Lemma x105_persistent stk E (dst src : loc) vdst vsrc (n : Z) :
    Z.of_nat (length vdst) = n → Z.of_nat (length vsrc) = n →
      [[{ dst ↦∗ vdst ∗ src ↦∗□ vsrc }]]
        array_copy_to #dst #src #n @ stk; E
      [[{ RET #(); dst ↦∗ vsrc }]].
  Proof.
    iIntros (Hvdst Hvsrc Φ) "[Hdst Hsrc] HΦ".
    iInduction vdst as [|v1 vdst] "IH" forall (n dst src vsrc Hvdst Hvsrc);
      destruct vsrc as [|v2 vsrc]; simplify_eq/=; try lia; wp_rec; wp_pures.
    { iApply "HΦ". auto with iFrame. }
    iDestruct (array_cons with "Hdst") as "[Hv1 Hdst]".
    iDestruct (array_cons with "Hsrc") as "[Hv2 #Hsrc]".
    wp_load; wp_store.
    wp_smart_apply ("IH" with "[%] [%] Hdst Hsrc") as "Hvdst"; [ lia .. | ].
    iApply "HΦ". by iFrame.
  Qed.

  Lemma d106_persistent stk E (dst src : loc) vdst vsrc (n : Z) :
    Z.of_nat (length vdst) = n → Z.of_nat (length vsrc) = n →
    {{{ dst ↦∗ vdst ∗ src ↦∗□ vsrc }}}
      array_copy_to #dst #src #n @ stk; E
    {{{ RET #(); dst ↦∗ vsrc }}}.
  Proof.
    iIntros (? ? Φ) "H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (x105_persistent with "H"); [auto..|]; iIntros "H HΦ". by iApply "HΦ".
  Qed.

  Lemma a107_persistent stk E l vl n :
    Z.of_nat (length vl) = n → (0 < n)%Z →
      [[{ l ↦∗□ vl }]]
        array_clone #l #n @ stk; E
      [[{ l', RET #l'; l' ↦∗ vl }]].
  Proof.
    iIntros (Hvl Hn Φ) "Hvl HΦ".
    wp_lam.
    wp_alloc dst as "Hdst"; first by auto.
    wp_smart_apply (x105_persistent with "[$Hdst $Hvl]") as "Hdst".
    - rewrite length_replicate Z2Nat.id; lia.
    - auto.
    - wp_pures.
      iApply "HΦ". by iFrame.
  Qed.

  Definition df108 (vs : list (val * val)) : option bool :=
    match vs with
    | (LitV (LitBool b), _) :: _ => Some b
    | _ => None
    end.

  Definition ef109 (vs : list (val * val)) : option loc :=
    match vs with
    | (_, LitV (LitLoc l)) :: _ => Some l
    | _ => None
    end.

  Lemma ee110_persistent stk E l vl n :
    Z.of_nat (length vl) = n →
    (0 < n)%Z →
    {{{ l ↦∗□ vl }}}
      array_clone #l #n @ stk; E
    {{{ l', RET #l'; l' ↦∗ vl }}}.
  Proof.
    iIntros (? ? Φ) "H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (a107_persistent with "H"); [auto..|]; iIntros (l') "H HΦ". by iApply "HΦ".
  Qed.

  Lemma f111_spec (γ γᵥ γₕ γᵢ γ_val : gname) (l : loc) (n : nat) :
    n > 0 →
      inv e23 (caf72_inv γ γᵥ γₕ γᵢ γ_val l n) -∗
        <<{ ∀∀ backup vs, b28 γ backup vs  }>>
          f6' n #l @ ↑e23
        <<{ ∃∃ (marked_backup : val) (copy backup : loc) (ver : nat) (γₜ : gname), b28 γ backup vs |
            RET (#copy, marked_backup, #ver)%V;
            copy ↦∗ vs ∗ ⌜Forall val_is_unboxed vs⌝ ∗ ⌜length vs = n⌝ ∗ ec29_own γₕ backup γₜ vs ∗ mono_nat_lb_own γᵥ ver ∗ ((⌜marked_backup = InjRV #backup⌝ ∗ a33_own γ_val backup ∗ ∃ ver', mono_nat_lb_own γᵥ ver' ∗ ⌜ver ≤ ver'⌝ ∗ c31_own γᵢ (Nat.div2 ver') backup) ∨ ⌜marked_backup = InjLV #backup⌝) }>>.
  Proof.
Admitted.

  Lemma d112 γ (lactual lactual' : loc) (actual actual' : list val) requests (x10 : gmap loc (gname * list val)) (γₜ : gname) :
    length actual > 0 →

    actual ≠ actual' →

    length actual = length actual' →

    fst <$> x10 !! lactual' = None →

    ac62 x10 -∗

    ghost_var γ (1/2) (lactual', actual') -∗

    x66_inv γ lactual actual requests (dom x10)

    ={⊤ ∖ ↑e23 ∖ ↑a21}=∗

      ac62 x10 ∗

      ghost_var γ (1/2) (lactual', actual') ∗

      x66_inv γ lactual' actual' requests (dom x10).
  Proof.
    iIntros (Hpos Hne Hlen Hlogged) "Hlog Hγ Hreqs".
    iInduction requests as [|[[γₗ γₑ] lexp] reqs'] "IH".
    - by iFrame.
    - rewrite /x66_inv. do 2 rewrite -> big_sepL_cons by done.
      iDestruct "Hreqs" as "[(%Hfresh & Hlin & %Φ & %γₜ' & %lexp' & %ldes & %dq & %dq' & %expected & %desired & Hγₑ & #Hwinv) Hreqs']".
      iMod ("IH" with "Hlog Hγ Hreqs'") as "(Hlog & Hγ & Hreqinv)".
      iInv x22 as "[(HΦ & [%b >Hγₑ'] & >Hlin') | [(>Hcredit & AU & >Hγₑ' & >Hlin') | (>Htok & [%b >Hγₑ'] & [%b' >Hlin'])]]" "Hclose".
      + iCombine "Hlin Hlin'" gives %[_ ->].
        iMod (ghost_var_update_halves (bool_decide (actual' = expected)) with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']".

        iMod ("Hclose" with "[HΦ Hγₑ Hlin]") as "_".
        { iLeft. iFrame. }
        destruct (decide (lactual' = lexp)) as [-> | Hneq].
        * apply elem_of_dom in Hfresh as [[γₜ'' b28] Hvalue].
          by destruct (x10 !! lexp).
        * iFrame "∗ # %".
          rewrite /ad65_inv.
          replace (bool_decide (lactual' = lexp)) with false.
          { by iFrame. }
          { by rewrite bool_decide_eq_false_2. }
      + iCombine "Hlin Hlin'" gives %[_ ->%bool_decide_eq_true].
        iCombine "Hγₑ Hγₑ'" gives %[_ ->%bool_decide_eq_true].
        iMod (ghost_var_update_halves false with "Hlin Hlin'") as "[Hlin Hlin']".
        iMod (lc_fupd_elim_later with "Hcredit AU") as "AU".
        iMod "AU" as (backup'' actual'') "[Hγ' [_ Hconsume]]".
        iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
        rewrite (bool_decide_eq_false_2 (actual' = expected)); last done.
        destruct (decide (lactual' = lexp)) as [-> | Hdiff].
        * apply elem_of_dom in Hfresh as [[γₜ'' b28] Hvalue].
          iPoseProof (adc63 with "Hlog") as "[Hactual' _]".
          { done. }
          by destruct (x10 !! lexp).
        * iFrame "∗ # %".
          rewrite (bool_decide_eq_false_2 (lactual' = lexp)); last done.
          iMod (ghost_var_update_halves (bool_decide (actual' = expected)) with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']".
          iMod ("Hconsume" with "[$]") as "HΦ".
          iFrame.
          iMod ("Hclose" with "[-]") as "_".
          { iLeft. iFrame. }
          done.
      + iMod (ghost_var_update_halves (bool_decide (lactual' = lexp)) with "Hlin Hlin'") as "[Hlin Hlin']".
        iMod (ghost_var_update_halves (bool_decide (actual' = expected)) with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']".
        iFrame "∗ # %".
        iMod ("Hclose" with "[-]") as "_".
        { do 2 iRight. iFrame. }
        done.
  Qed.

  Lemma e113_update x10 l γ vs :
    x10 !! l = None →
      ac62 x10 -∗
        token γ -∗
          l ↦∗□ vs -∗
            ac62 (<[l := (γ, vs)]> x10).
  Proof.
    iIntros (Hlog) "Hlogtokens Htok #Hl".
    rewrite /ac62.
    rewrite big_sepM_insert; last done.
    iFrame "∗ #".
  Qed.

  Lemma a114 (dq : dfrac) (γ : gname) (m : gmap loc (agree (gname * list val))) :
    own γ (●{dq} m) ==∗ own γ (●{dq} m) ∗ own γ (◯ m).
  Proof.
    iIntros "H●".
    iMod (own_update with "H●") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := m).
      - apply _.
      - reflexivity. }
    by iFrame.
  Qed.

  Lemma a114' (dq : dfrac) (γ : gname) (m : gmap loc (agree nat)) :
    own γ (●{dq} m) ==∗ own γ (●{dq} m) ∗ own γ (◯ m).
  Proof.
    iIntros "H●".
    iMod (own_update with "H●") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := m).
      - apply _.
      - reflexivity. }
    by iFrame.
  Qed.

  Lemma a114'' (dq : dfrac) (γ : gname) (m : gmap nat (agree loc)) :
    own γ (●{dq} m) ==∗ own γ (●{dq} m) ∗ own γ (◯ m).
  Proof.
    iIntros "H●".
    iMod (own_update with "H●") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := m).
      - apply _.
      - reflexivity. }
    by iFrame.
  Qed.

  Lemma x117 `{Countable K} {V} (m m' : gmap K V) P :
    m ⊆ m' → map_Forall P m' → map_Forall P m.
  Proof.
    rewrite /map_Forall.
    intros Hsub HP k v Hsome.
    by eapply HP, lookup_weaken.
  Qed.

  Lemma f118 k : Nat.even (S k) = negb (Nat.even k).
  Proof.
    destruct (Nat.even (S k)) eqn:Hsucc; destruct (Nat.even k) eqn:H.
    - exfalso. apply (Nat.Even_Odd_False k).
      + rewrite -Nat.even_spec //.
      + rewrite -Nat.Even_succ -Nat.even_spec //.
    - done.
    - done.
    - exfalso. apply (Nat.Even_Odd_False k).
      + rewrite -Nat.Odd_succ -Nat.odd_spec fc102 //.
      + rewrite -Nat.odd_spec fc102 //.
  Qed.

Lemma x119_ne {A} (l : list A) i j x y :
  NoDup l →
  i ≠ j →
  l !! i = Some x →
  l !! j = Some y →
  x ≠ y.
Proof.
  intros Hnd Hij Hi Hj ->. eapply Hij, NoDup_lookup; eauto.
Qed.

  Lemma eb120 n : Nat.odd n = negb (Nat.even n).
  Proof.
    by apply be101.
  Qed.

  Lemma d121 {A} (R : A → A → Prop) l i j x y :
    StronglySorted R l →
    i < j →
    l !! i = Some x →
    l !! j = Some y →
    R x y.
  Proof.
    revert i j x y.
    induction l as [|a l IH]; intros i j x y Hsorted Hij Hix Hjy.
    - now rewrite lookup_nil in Hix.
    - destruct i as [| i], j as [| j].
      + lia.
      + simpl in *. simplify_eq. inv Hsorted.
        eapply Forall_lookup_1; eauto.
      + lia.
      + simpl in *. inv Hsorted. apply (IH i j); auto. lia.
  Qed.

  Lemma x122 Φ γ γₗ γₑ γᵣ γₜ (backup lexp lexp' ldes : loc) expected desired actual (dq dq' : dfrac) i used :
    lexp' ≠ backup →

      inv x22 (ad61_inv Φ γ γₑ γₗ γₜ lexp ldes dq dq' expected desired) -∗
        lexp ↦∗{dq} expected -∗
          ldes ↦∗{dq'} desired -∗
            ba57 γᵣ i γₗ γₑ lexp' -∗
              ad65_inv γ γₗ γₑ backup lexp' actual used -∗
                token γₜ -∗
                  £ 1 ={⊤ ∖ ↑e23 ∖ ↑a21}=∗
                    Φ #false ∗ ad65_inv γ γₗ γₑ backup lexp' actual used.
  Proof.
    iIntros (Hne) "#Hcasinv Hlexp Hldes #Hregistered Hreqinv Hγₜ Hcredit".
    rewrite /ad65_inv.
    iDestruct "Hreqinv" as "(%Hused & Hlin & %Φ' & %γₜ' & %lexp'' & %ldes' & %dq₁ & %dq₁' & %expected' & %desired' & Hγₑ & _)".
    iInv x22 as "[(HΦ & [%b >Hγₑ'] & >Hlin') | [(>Hcredit' & AU & >Hγₑ' & >Hlin') | (>Htok & [%b >Hγₑ'] & [%b' >Hlin'])]]" "Hclose".
    + iCombine "Hlin Hlin'" gives %[_ Heq].
      iMod (ghost_var_update_halves (bool_decide (actual = expected)) with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']".
      iMod ("Hclose" with "[Hγₜ Hγₑ Hlin]") as "_".
      { rewrite /ad61_inv. do 2 iRight. iFrame. }
      iMod (lc_fupd_elim_later with "Hcredit HΦ") as "HΦ".
      iModIntro.
      iPoseProof ("HΦ" with "[$]") as "HΦ".
      iFrame "∗ # %".
      rewrite bool_decide_eq_false_2 //.
    + rewrite bool_decide_eq_false_2 //.
      iCombine "Hlin Hlin'" gives %[_ [=]].
    + iCombine "Hγₜ Htok" gives %[].
  Qed.

  Global Instance ad123`{EqDecision K, Countable K} `{V} : FMap (gmap K).
  Proof. apply _. Qed.

  Lemma fcc124 (γ γᵥ γₕ γᵣ γᵢ γ_val γ_vers γₒ γₚ' : gname) (l ldes ldes' : loc) (dq : dfrac)
                        (expected desired : list val) (ver ver₂ idx₂ : nat) (index₂ : list loc)
                        (order₂ : gmap loc nat) :
    length expected > 0 → length expected = length desired → ver ≤ ver₂ → length index₂ = S (Nat.div2 (S ver₂)) →
      StronglySorted (a73 order₂) index₂ → Forall (.∈ dom order₂) index₂ → map_Forall (λ _ idx, idx ≤ idx₂) order₂ →
        order₂ !! ldes' = None →
          inv e23 (caf72_inv γ γᵥ γₕ γᵢ γ_val l (length expected)) -∗
            inv a21 (c78_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ l) -∗
              mono_nat_lb_own γᵥ ver₂ -∗
                own γᵢ (◯ map_seq O (to_agree <$> index₂)) -∗
                  ec29_own γₕ ldes' γₚ' desired -∗
                    eee30_own γₒ ldes' (S idx₂) -∗
                      own γₒ (◯ (fmap (M := gmap loc) to_agree order₂)) -∗
                        eee30_own γ_vers ldes' ver₂ -∗
                          {{{ ldes ↦∗{dq} desired }}}
                            fa8 (length expected) #l #ver #ldes #ldes'
                          {{{ RET #(); ldes ↦∗{dq} desired }}}.
  Proof.
    iIntros (Hlenexp Hlenmatch Hle Hlenᵢ₂ Hindexordered Hmono Hubord₂ Hldes'fresh) "#Hreadinv #Hinv #◯Hγᵥ #◯Hγᵢ #◯Hγₕ #◯Hγₒ #◯Hγₒcopy #◯Hγ_vers %Φ !# Hldes HΦ".
    rewrite /fa8. wp_pures.
    destruct (Nat.even ver) eqn:Heven.
    - rewrite Zrem_even x103 Heven /=.
      wp_pures.
      wp_bind (CmpXchg _ _ _).
      iInv e23 as "(%ver₃ & %log₃ & %actual₃ & %cache₃ & %marked_backup₃ & %backup₃ & %backup₃' & %index₃ & %validated₃ & >Hver & >Hbackup & >Hγ & >%Hunboxed & >#□Hbackup₃ & >%Hindex₃ & >%Hvalidated₃ & >%Hlenactual₃ & >%Hlencache₃ & >%Hloglen₃ & Hlogtokens & >%Hlogged₃ & >●Hγₕ & >%Hlenᵢ₃ & >%Hnodup₃ & >%Hrange₃ & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons₃ & Hlock & >●Hγ_val & >%Hval₃ & >%Hvallogged₃)" "Hcl".
      iInv a21 as "(%ver'' & %log₃' & %actual₃' & %marked_backup₃' & %backup₃'' & %requests₃ & %vers₃ & %index₃' & %order₃ & %idx₃ & >●Hγᵥ' & >Hbackup₃' & >Hγ' & >%Hcons₃' & >●Hγₕ' & >●Hγᵣ & Hreginv & >●Hγ_vers & >%Hdomvers₃ & >%Hvers₃ & >●Hγᵢ' & >●Hγₒ & >%Hdomord₃ & >%Hinj₃ & >%Hidx₃ & >%Hmono₃ & >%Hubord₃)" "Hcl'".
      iDestruct (ad82_agree with "●Hγₕ ●Hγₕ'") as %<-.
      iDestruct (c83_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
      iCombine "●Hγₕ ●Hγₕ'" gives %G.
      destruct (decide (ver₃ = ver)) as [-> | Hneq]; first last.
      { wp_cmpxchg_fail.
        { intros [=]. lia. }
        iMod ("Hcl'" with "[$Hγ' $●Hγₕ' $Hreginv $●Hγᵣ $●Hγᵥ' $●Hγ_vers $Hbackup₃' $●Hγᵢ' $●Hγₒ]") as "_".
        { iFrame "%". }
        iMod ("Hcl" with "[$Hγ $Hlogtokens $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hbackup $Hver $●Hγₕ $□Hbackup₃ $●Hγ_val]") as "_".
        { iFrame "%". }
        iApply fupd_mask_intro.
        { set_solver. }
        iIntros ">_ !>".
        wp_pures.
        iModIntro.
        iApply ("HΦ" with "[$]"). }
      wp_cmpxchg_suc.
      iDestruct (mono_nat_lb_own_valid with "●Hγᵥ ◯Hγᵥ") as %[_ Hle₃].

      assert (ver₂ = ver) as -> by lia.
      rewrite Heven.
      iDestruct "Hlock" as "(●Hγᵢ'' & ●Hγᵥ'' & Hcache₂)".
      iCombine "●Hγᵥ ●Hγᵥ''" as "●Hγᵥ". rewrite Qp.quarter_quarter.
      iDestruct (mono_nat_auth_own_agree with "●Hγᵥ ●Hγᵥ'") as %[_ <-].
      iCombine "●Hγᵥ ●Hγᵥ'" as "●Hγᵥ".
      iPoseProof (d85_agree with "●Hγ_vers ◯Hγ_vers") as "%Hagreevers".

      destruct (decide (1 < size log₃)) as [Hless | Hge]; first last.
      { rewrite bool_decide_eq_false_2 // in Hvers₃. simplify_eq. }
      rewrite bool_decide_eq_true_2 // in Hvers₃.
      iMod (mono_nat_own_update (S ver) with "●Hγᵥ") as "[(●Hγᵥ & ●Hγᵥ' & ●Hγᵥ'') #Hlb']".
      { lia. }

      destruct Hvers₃ as (ver'' & Hvers₃lookup & Hlevers₃ & Hub₃ & Hinvalid).
      eapply map_Forall_lookup_1 in Hagreevers as Hvalid; eauto.
      simpl in Hvalid.
      assert (ver'' = ver) as -> by lia.
      rewrite bool_decide_eq_true_2 // in Hinvalid.
      simplify_eq.
      iCombine "●Hγᵢ ●Hγᵢ''" as "●Hγᵢ".
      rewrite Qp.quarter_quarter.
      iCombine "●Hγᵢ ●Hγᵢ'" as "●Hγᵢ".

      iPoseProof (aee49_agree' with "●Hγᵢ ◯Hγᵢ") as "%Hprefix".
      apply prefix_length_eq in Hprefix as <-; last lia.

      iCombine "●Hγₒ ◯Hγₒcopy" gives %(_ & Hvalidₒ'%e52' & _)%auth_both_dfrac_valid_discrete.

      iMod (ba37_update ldes' with "●Hγᵢ") as "[(●Hγᵢ & ●Hγᵢ' & ●Hγᵢ'') ◯Hγᵢ₃]".
      iCombine "Hbackup Hbackup₃'" gives %[_ ->].
      replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done.
      iPoseProof (d85_agree with "●Hγₒ ◯Hγₒ") as "%Hagreeₒ".

      iMod ("Hcl'" with "[$Hbackup₃' $Hγ' $●Hγₕ' $Hreginv $●Hγᵣ $●Hγ_vers $●Hγᵥ $●Hγᵢ $●Hγₒ]") as "_".
      { iFrame "%". iSplit; first last.
        { iPureIntro. apply x77_snoc.
          - apply (ca75 order₂).
            { done. }
            { done. }
            { done. }
          - rewrite Forall_forall.
            intros l' Hmem i j Hts Hts'.
            simplify_eq.
            rewrite Forall_forall in Hmono.
            apply Hmono in Hmem.
            rewrite elem_of_dom in Hmem.
            destruct Hmem as [ts' Hts''].
            rewrite map_subseteq_spec in Hvalidₒ'.
            apply Hvalidₒ' in Hts'' as ?.
            simplify_eq.
            apply Hubord₂ in Hts''. lia. }
        rewrite bool_decide_eq_true_2 //.
        iPureIntro. exists ver. repeat split; auto.
        rewrite bool_decide_eq_false_2 //. }
      change 1%Z with (Z.of_nat 1).
      rewrite -Nat2Z.inj_add /=.

      destruct Hvalidated₃ as [-> | ([=] & _ & _ & _)].

      iModIntro.
      iMod ("Hcl" with "[$Hγ $Hlogtokens $●Hγᵢ' $●Hγᵥ'' $Hcache $Hbackup $Hver $●Hγₕ $□Hbackup₃ $●Hγ_val]") as "_".
      { rewrite f118 Heven /= last_snoc.
        iExists ldes'. iFrame "%". iPureIntro.
        repeat split; auto.
        - rewrite length_app /= Nat.add_1_r Hlenᵢ₃. do 2 f_equal. rewrite -Nat.Even_div2 // -Nat.even_spec //.
        - apply NoDup_app. repeat split; first done.
          + intros l' Hl'. intros ->%list_elem_of_singleton.
            rewrite Forall_forall in Hmono.
            apply Hmono in Hl'.
            rewrite elem_of_dom in Hl'.
            destruct Hl' as [ts Hts]. simplify_eq.
          + apply NoDup_singleton.
        - rewrite Forall_app. split; first done. rewrite Forall_singleton.
          rewrite -Hdomord₃ elem_of_dom. eauto.
        - destruct (decide (backup₃ ∈ validated₃)) as [Hval' | Hnval].
          { rewrite bool_decide_eq_true_2 // in Hval₃. }
          rewrite bool_decide_eq_false_2 //. }
      iModIntro.
      wp_pures.
      wp_bind (array_copy_to _ _ _).
      wp_apply (a91 _ _ _ _ _ _ _ cache₃ desired with "[//] [$] [-]"); try done.
      { lia. }
      iIntros "!> [Hdst Hsrc]".
      wp_pures.
      wp_bind (_ <- _)%E.
      iInv e23 as "(%ver₄ & %log₄ & %actual₄ & %cache₄ & %marked_backup₄ & %backup₄ & %backup₄' & %index₄ & %validated₄ & >Hver & >Hbackup & >Hγ & >%Hunboxed₄ & >#□Hbackup₄ & >%Hindex₄ & >%Hvalidated₄ & >%Hlenactual₄ & >%Hlencache₄ & >%Hloglen₄ & Hlogtokens & >%Hlogged₄ & >●Hγₕ & >%Hlenᵢ₄ & >%Hnodup₄ & >%Hrange₄ & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons₄ & Hlock & >●Hγ_val & >%Hvallogged₄)" "Hcl".
      iInv a21 as "(%ver'' & %log₄' & %actual₄' & %marked_backup₄' & %backup₄'' & %requests₄ & %vers₄ & %index₄' & %order₄ & %idx₄ & >●Hγᵥ'' & >Hbackup₄' & >Hγ' & >%Hcons₄' & >●Hγₕ' & >●Hγᵣ & Hreginv & >●Hγ_vers & >%Hdomvers₄ & >%Hvers₄ & >●Hγᵢ' & >●Hγₒ & >%Hdomord₄ & >%Hinj₄ & >%Hidx₄ & >%Hmono₄ & >%Hubord₄)" "Hcl'".
      wp_store.
      change 2%Z with (Z.of_nat 2). simplify_eq.
      iDestruct (mono_nat_auth_own_agree with "●Hγᵥ ●Hγᵥ'") as %[_ ->].
      iDestruct (mono_nat_auth_own_agree with "●Hγᵥ' ●Hγᵥ''") as %[_ <-].
      iCombine "●Hγᵥ ●Hγᵥ'" as "●Hγᵥ".
      rewrite Qp.quarter_quarter.
      iCombine "●Hγᵥ ●Hγᵥ''" as "●Hγᵥ".
      iMod (mono_nat_own_update (S (S ver)) with "●Hγᵥ") as "[(●Hγᵥ & ●Hγᵥ' & ●Hγᵥ'') #Hlb₃]".
      { lia. }
      iDestruct (c83_agree with "●Hγᵢ ●Hγᵢ''") as %<-.
      iDestruct (c83_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
      replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done.
      iPoseProof (d68 with "Hcache Hdst") as "[Hcache ->]".
      { lia. }
      rewrite dfrac_op_own Qp.half_half.
      iDestruct (ad82_agree with "●Hγₕ ●Hγₕ'") as %<-.
      iMod ("Hcl'" with "[$Hbackup₄' $Hγ' $●Hγₕ' $Hreginv $●Hγᵣ $●Hγ_vers $●Hγᵥ $●Hγᵢ' $●Hγₒ]") as "_".
      { iFrame "%". iPureIntro.
        destruct (decide (1 < size log₄)).
        - rewrite bool_decide_eq_true_2 //.
          rewrite bool_decide_eq_true_2 // in Hvers₄.
          destruct Hvers₄ as (ver₄' & Hver₄' & Hle₄ & Hub₄ & Hinvalid₄).
          exists ver₄'. repeat split; auto.
          rewrite bool_decide_eq_false_2 //. lia.
        - rewrite bool_decide_eq_false_2 //.
          rewrite bool_decide_eq_false_2 // in Hvers₄. }
      rewrite -Nat2Z.inj_add /=.
      destruct Hvalidated₄ as [-> | (_ & HOdd%Nat.Even_succ & _ & _)]; first last.
      { exfalso. apply (Nat.Even_Odd_False ver).
        - rewrite -Nat.even_spec //.
        - done. }
      iDestruct "Hcache" as "[Hcache Hcache']".
      simpl in Hlenᵢ₄.
      iPoseProof (aee49_agree with "●Hγᵢ ◯Hγᵢ₃") as "%Hagreeᵢ".
      iPoseProof (d48_agree with "●Hγₕ ◯Hγₕ") as "%Hbackup₃".
      iMod ("Hcl" with "[$Hγ $Hlogtokens $●Hγᵢ ●Hγᵢ'' $●Hγᵥ' ●Hγᵥ'' $Hcache Hcache' $Hbackup $Hver $●Hγₕ $□Hbackup₄ $●Hγ_val]") as "_".
      { iFrame "%".
        iSplit; first auto.
        rewrite Nat.Odd_div2; first last.
        { rewrite Nat.Odd_succ Nat.Even_succ Nat.Odd_succ -Nat.even_spec //. }
        simpl.
        simpl in Hlenᵢ₄.
        rewrite last_lookup Hlenᵢ₄ /= in Hindex₄.
        rewrite Hlenᵢ₃ -Nat.Even_div2 // in Hagreeᵢ; first last.
        { rewrite -Nat.even_spec //. }
        simplify_eq. iFrame "%".
        rewrite Heven.
        iFrame. rewrite Hbackup₃ //. }
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros ">_ !>".
      rewrite /dae4.
      wp_pures.
      wp_bind (CmpXchg _ _ _)%E.
      iClear "Hlock".
      iInv e23 as "(%ver₅ & %log₅ & %actual₅ & %cache₅ & %marked_backup₅ & %backup₅ & %backup₅' & %index₅ & %validated₅ & >Hver & >Hbackup & >Hγ & >%Hunboxed₅ & >#□Hbackup₅ & >%Hindex₅ & >%Hvalidated₅ & >%Hlenactual₅ & >%Hlencache₅ & >%Hloglen₅ & Hlogtokens & >%Hlogged₅ & >●Hγₕ & >%Hlenᵢ₅ & >%Hnodup₅ & >%Hrange₅ & >●Hγᵢ & >●Hγᵥ & >Hcache & >%Hcons₅ & Hlock & ●Hγ_val & >%Hvallogged₅)" "Hcl".
      iInv a21 as "(%ver'' & %log₅' & %actual₅' & %marked_backup₅' & %backup₅'' & %requests₅ & %vers₅ & %index₅' & %order₅ & %idx₅ & >●Hγᵥ'' & >Hbackup₅' & >Hγ' & >%Hcons₅' & >●Hγₕ' & >●Hγᵣ & Hreginv & >●Hγ_vers & >%Hdomvers₅ & >%Hvers₅ & >●Hγᵢ' & >●Hγₒ & >%Hdomord₅ & >%Hinj₅ & >%Hidx₅ & >%Hmono₅ & >%Hubord₅)" "Hcl'".
      iCombine "Hbackup Hbackup₅'" gives %[_ <-].
      destruct (decide (marked_backup₅ = InjLV #ldes')) as [-> | Hneq]; first last.
      { wp_cmpxchg_fail.
        iMod ("Hcl'" with "[$Hbackup₅' $Hγ' $●Hγₕ' $●Hγᵣ $●Hγᵥ'' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
        { iFrame "%". }
        iMod ("Hcl" with "[$Hγ $□Hbackup₅ $●Hγₕ $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup $●Hγ_val]") as "_".
        { iFrame "%". }
        iApply fupd_mask_intro.
        { set_solver. }
        iIntros ">_ !>".
        rewrite /dae4.
        wp_pures.
        iModIntro.
        iApply ("HΦ" with "[$]"). }
      iCombine "Hbackup Hbackup₅'" as "Hbackup".
      wp_cmpxchg_suc.
      iDestruct (mono_nat_auth_own_agree with "●Hγᵥ ●Hγᵥ''") as %[_ <-].
      iDestruct (c83_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
      iDestruct (ad82_agree with "●Hγₕ ●Hγₕ'") as %<-.
      iCombine "Hγ Hγ'" gives %[_ [=->->]].
      destruct Hvalidated₅ as [[=<-] | ([=] & _ & _)].
      iPoseProof (d85_agree with "●Hγₒ ◯Hγₒ") as "%Hagreeₒ₄". simplify_eq.
      iDestruct (mono_nat_lb_own_valid with "●Hγᵥ Hlb₃") as %[_ Hless₃].
      iPoseProof (aee49_agree with "●Hγᵢ ◯Hγᵢ₃") as "%Hagreeᵢ₂₄".
      rewrite Hlenᵢ₂ -Nat.Even_div2 in Hagreeᵢ₂₄; first last.
      { rewrite -Nat.even_spec //. }
      destruct (decide (S (S ver) = ver₅)) as [<- | Hneq]; first last.
      { iExFalso.
        destruct ver₅ as [|[|[|ver₄]]]; try lia.
        simpl in Hlenᵢ₅.
        rewrite last_lookup Hlenᵢ₅ /= in Hindex₅.
        assert (Nat.div2 ver < S (Nat.div2 ver₄)) as Hnever.
        { assert (ver ≤ ver₄) as Hmono'%c100 by lia. lia. }

        eapply d121 with (i := S (Nat.div2 ver)) (j := S (S (Nat.div2 ver₄))) in Hmono₅; eauto; last lia.
        rewrite /a73 in Hmono₄.
        assert (is_Some (order₅ !! backup₅')) as [ts₅ Hts₅].
        { rewrite -elem_of_dom Hdomord₅.
          rewrite Forall_forall in Hrange₅.
          apply Hrange₅. rewrite list_elem_of_lookup.
          eauto. }
        pose proof (Hmono₅ _ _ Hidx₅ Hts₅) as Hle'.
        rewrite map_Forall_lookup in Hubord₄.
        apply Hubord₅ in Hts₅. lia. }
      iDestruct "Hbackup" as "[Hbackup Hbackup']".
      iPoseProof (d85_agree with "●Hγ_vers ◯Hγ_vers") as "%Hagreever".
      iMod ("Hcl'" with "[$Hbackup $Hγ' $●Hγₕ' $Hreginv $●Hγᵣ $●Hγ_vers $●Hγᵥ'' $●Hγᵢ' $●Hγₒ]") as "_".
      { iFrame "%". iPureIntro.
        destruct (decide (1 < size log₅)).
        { rewrite bool_decide_eq_true_2 //.
          rewrite bool_decide_eq_true_2 // in Hvers₅.
          destruct Hvers₅ as (ver'' & Hvers₅ & Hlever' & Hubvers₅ & Hinvalid).
          simplify_eq.
          exists ver. repeat split; auto.
          rewrite bool_decide_eq_false_2 //. lia. }
        { rewrite bool_decide_eq_false_2 //.
          rewrite bool_decide_eq_false_2 // in Hvers₅. } }
      iPoseProof (d48_agree with "●Hγₕ ◯Hγₕ") as "%Hldes₅".
      rewrite Hldes₅ /= in Hlogged₅.
      simplify_eq.
      simpl in Hcons₅.
      rewrite Heven in Hcons₅.
      pose proof Hindex₅ as Hindex₅'.
      rewrite last_lookup Hlenᵢ₅ Nat.Odd_div2 /= in Hindex₅; first last.
      { rewrite Nat.Odd_succ Nat.Even_succ Nat.Odd_succ -Nat.even_spec //. }
      simplify_eq.
      rewrite Hldes₅ /= in Hcons₅.
      simplify_eq.
      iMod (bde40_update ldes' with "●Hγ_val") as "[●Hγ_val _]".
      iMod ("Hcl" with "[$Hγ $Hlogtokens $●Hγᵢ $●Hγᵥ $Hcache $Hbackup' $Hver $●Hγₕ $□Hbackup₅ $Hlock $●Hγ_val]") as "_".
      { iFrame "%". iPureIntro.
        - repeat split; auto.
          + right. rewrite Nat.Even_succ Nat.Odd_succ -Nat.even_spec //.
          + rewrite Hldes₅ //=.
          + simpl. rewrite Heven Hldes₅ //=.
          + rewrite bool_decide_eq_true_2 //. set_solver.
          + assert (ldes' ∈ dom log₅).
            { rewrite elem_of_dom //. }
            set_solver. }
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros ">_ !>".
      rewrite /dae4.
      wp_pures.
      iModIntro.
      iApply ("HΦ" with "[$]").
    - rewrite Zrem_odd fbe104 eb120 Heven /=.
      destruct ver as [|ver].
      { done. }
      simpl. wp_pures.
      iApply ("HΦ" with "[$]").
  Qed.

  Lemma cd125 `{!invGS Σ} (E1 E2 E3 : coPset) (P : iProp Σ) :
    E2 ⊆ E3 →
    (|={E1,E3}=> P) ⊢ |={E1,E2}=> |={E2,E3}=> P.
  Proof.
    iIntros (HE) "H".
    iApply (fupd_trans E1 E3 E2).

    iApply (fupd_mono with "H").
    iIntros "HP".
    iApply (fupd_mask_intro_subseteq E3 E2); first done.
    iExact "HP".
  Qed.

  Lemma d126
    (γ γᵥ γₕ γᵣ γᵢ γ_val γ_vers γₒ : gname)
    (l lexp ldes ldes' : loc)
    (dq dq' : dfrac)
    (expected desired cache : list val)
    (Φ : val → iProp Σ)
    (log₁ : gmap loc (gname * list val))
    (backup backup' copy : loc)
    (requests₁ : list (gname * gname * loc))
    (vers₁ order₁ : gmap loc nat)
    (index₁ : list loc)
    (validated : gset loc)
    (idx₁ ver ver₁ ver' i : nat)
    (γₚ γₑ γₗ γₜ : gname) :
    length expected > 0 →
    length expected = length desired →
    length cache = length expected →
    expected ≠ desired →
    last index₁ = Some backup' →
    (if Nat.even ver₁ then snd <$> log₁ !! backup' = Some cache else True) →
    map_Forall (λ _ '(_, b28), length b28 = length expected) log₁ →
    length index₁ = S (Nat.div2 (S ver₁)) →
    NoDup index₁ →
    Forall (.∈ dom log₁) index₁ →
    validated ⊆ dom log₁ →
    dom order₁ = dom log₁ →
    (if bool_decide (1 < size log₁) then
      ∃ ver' : nat, ver' ≤ ver₁ ∧ map_Forall (λ _ ver'', ver'' ≤ ver') vers₁
    else vers₁ = ∅) →
    dom vers₁ ⊂ dom log₁ →
    dbc71 order₁ →
    order₁ !! backup = Some idx₁ →
    StronglySorted (a73 order₁) index₁ →
    map_Forall (λ _ idx', idx' ≤ idx₁) order₁ →
    Forall val_is_unboxed desired →

    inv e23 (caf72_inv γ γᵥ γₕ γᵢ γ_val l (length expected)) -∗
    inv a21 (c78_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ l) -∗
    inv x22 (ad61_inv Φ γ γₑ γₗ γₜ lexp ldes dq dq' expected desired) -∗
    ba57 γᵣ i γₗ γₑ backup -∗
    ec29_own γₕ backup γₚ expected -∗
    backup ↦∗□ expected -∗

    token γₜ -∗
    ldes' ↦∗ desired -∗
    l ↦ #ver₁ -∗
    ac62 log₁ -∗
    mono_nat_auth_own γᵥ (1/4) ver₁ -∗
    (l +ₗ 2) ↦∗{#1/2} cache -∗
    (if Nat.even ver₁ then
      ab24_own γᵢ (1/4) index₁ ∗
      mono_nat_auth_own γᵥ (1/4) ver₁ ∗
      (l +ₗ 2) ↦∗{#1/2} cache
    else True) -∗
    (▷ caf72_inv γ γᵥ γₕ γᵢ γ_val l (length expected) ={⊤ ∖ ↑e23, ⊤}=∗ emp) -∗
    mono_nat_auth_own γᵥ (1/2) ver₁ -∗
    bad56 γᵣ requests₁ -∗
    x66_inv γ backup expected requests₁ (dom log₁) -∗
    a27_own γ_vers 1 vers₁ -∗
    ab24_own γᵢ (1/2) index₁ -∗
    a27_own γₒ 1 order₁ -∗
    (▷ c78_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ l ={⊤ ∖ ↑e23 ∖ ↑a21, ⊤ ∖ ↑e23}=∗ emp) -∗
    own γᵢ (●{#1/4} map_seq 0 (to_agree <$> index₁)) -∗
    ca32_own γ_val 1 validated -∗
    ghost_var γ (1/2) (backup, expected) -∗
    (l +ₗ 1) ↦ InjLV #ldes' -∗
    own γₕ (● (fmap (M:=gmap loc) to_agree log₁))
    ={⊤ ∖ ↑e23 ∖ ↑a21, ⊤}=∗
      ⌜log₁ !! ldes' = None⌝ ∗
      (lexp ↦∗{dq} expected ∗ ldes ↦∗{dq'} desired -∗ Φ #true) ∗
      eee30_own γ_vers ldes' ver₁ ∗
      (∃ γₚ', ec29_own γₕ ldes' γₚ' desired) ∗
      ldes' ↦∗□ desired ∗
      eee30_own γₒ ldes' (S idx₁).
  Proof.
    iIntros (Hpos Hleneq Hlencache Hne Hindex₁ Hcache₁ Hloglen₁ Hlenᵢ₁ Hnodup₁ Hrange₁
            Hvallogged Hdomord Hvers₁ Hdomvers₁ Hinj₁ Hidx₁ Hmono₁ Hubord₁ Hunboxed).
    iIntros "#Hreadinv #Hinv #Hcasinv #◯Hγᵣ #◯Hγₕ #□Hbackup".
    iIntros "Hγₜ Hldes' Hver Hlogtokens ●Hγᵥ Hcache".
    iIntros "Hlock Hcl ●Hγᵥ' ●Hγᵣ Hreginv ●Hγ_vers ●Hγᵢ' ●Hγₒ Hcl' ●Hγᵢ ●Hγ_val Hγ Hbackup₁ ●Hγₕ".
    simplify_eq.

    iPoseProof (bfd59_agree with "●Hγᵣ ◯Hγᵣ") as "%Hagree".
    iPoseProof (d48_agree with "●Hγₕ ◯Hγₕ") as "%Hlogged₁'".

    assert (snd <$> log₁ !! backup = Some expected) as Hlogged₁.
    { rewrite Hlogged₁' //. }

    iAssert (⌜log₁ !! ldes' = None⌝)%I as "%Hldes'fresh".
    { destruct (log₁ !! ldes') eqn:Hbound; last done.
      iExFalso.
      iPoseProof (big_sepM_lookup with "Hlogtokens") as "Hlogged".
      { done. }
      destruct p.
      iDestruct "Hlogged" as "[_ Hldes'₁]".
      iApply (ec70 with "Hldes' Hldes'₁").
      { rewrite map_Forall_lookup in Hloglen₁.
        apply Hloglen₁ in Hbound. lia. }
      lia. }

    rewrite -(take_drop_middle _ _ _ Hagree).
    rewrite /x66_inv big_sepL_app big_sepL_cons /ad65_inv.
    iDestruct "Hreginv" as "(Hlft & (%Hbackupin & Hγₗ & %Φ' & %γₜ' & %lexp' & %ldes'' & %dq₁ & %dq₂ & %expected' & %desired' & Hγₑ & ?) & Hrht)".
    iInv x22 as "[(HΦ & [%b >Hγₑ'] & >Hγₗ') | [(>Hcredit & AU & >Hγₑ' & >Hγₗ') | (>Htok & [%b >Hγₑ'] & [%b' >Hγₗ'])]]" "Hclose".

    3: iCombine "Hγₜ Htok" gives %[].
    {
    by iCombine "Hγₗ Hγₗ'" gives %[_ ?%bool_decide_eq_false]. }
    iCombine "Hγₑ Hγₑ'" gives %[_ <-%bool_decide_eq_true].
    iMod (ghost_var_update_halves false with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']".
    rewrite bool_decide_eq_true_2; last done.

    iMod (ghost_var_update_halves false with "Hγₗ Hγₗ'") as "[Hlin Hlin']".

    iMod (lc_fupd_elim_later with "Hcredit AU") as "AU".
    iMod "AU" as (vs' backup''') "[Hγ' [_ Hconsume]]".
    rewrite /b28.
    iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
    iMod (ghost_var_update_halves (ldes', desired) with "Hγ Hγ'") as "[Hγ Hγ']".
    simplify_eq.
    rewrite bool_decide_eq_true_2; last done.
    iMod ("Hconsume" with "[$Hγ']") as "HΦ".
    iMod ("Hclose" with "[Hγₜ Hlin' Hγₑ']") as "_".
    { do 2 iRight. iFrame. }

    iMod (d112 with "Hlogtokens Hγ Hlft") as "(Hlogtokens & Hγ & Hlft)".
    { done. }
    { done. }
    { done. }
    { done. }
    { by destruct (log₁ !! ldes'). }
    iMod (d112 with "Hlogtokens Hγ Hrht") as "(Hlogtokens & [Hγ Hγ'] & Hrht)".
    { done. }
    { done. }
    { done. }
    { done. }
    { by destruct (log₁ !! ldes'). }
    replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done.

    iMod token_alloc as "[%γₚ' Hγₚ']".

    iMod (x44_update ldes' desired γₚ' with "●Hγₕ") as "[[●Hγₕ ●Hγₕ'] #◯Hγₕ₁]".
    { done. }
    iDestruct "Hbackup₁" as "[Hbackup₁ Hbackup₁']".
    assert (O < size log₁) as Hlogsome₁.
    { assert (size log₁ ≠ 0); last lia.
      rewrite map_size_ne_0_lookup.
      naive_solver. }
    assert (ldes' ∉ dom log₁) as Hldes'freshdom.
    { rewrite not_elem_of_dom //. }
    iMod (ea45_update ldes' ver₁ with "●Hγ_vers") as "[●Hγ_vers ◯Hγ_vers]".
    { rewrite -not_elem_of_dom. set_solver. }

    assert (size (<[ldes':=(γₚ', desired)]> log₁) > 1) as Hvers₁multiple.
    { rewrite map_size_insert_None //. lia. }
    iMod (a114 with "●Hγₕ") as "[●Hγₕ ◯Hγₕcopy]".
    assert (map_Forall (λ _ ver'', ver'' ≤ ver₁) (<[ldes':=ver₁]> vers₁)) as Hub₁.
    { destruct (decide (size log₁ = 1)) as [Hsing | Hsing].
      - rewrite bool_decide_eq_false_2 in Hvers₁; last lia.
        subst. rewrite insert_empty map_Forall_singleton //.
      - rewrite bool_decide_eq_true_2 in Hvers₁; last lia.
        rewrite map_Forall_insert.
        destruct Hvers₁ as (ver_invalid₁ & Hver_invalid_le₁ & Hub).
        split; first done.
        eapply map_Forall_impl; first done.
        intros l' ver''.
        simpl. lia.
        rewrite -not_elem_of_dom. set_solver. }
    iMod (ea45_update ldes' (S idx₁) with "●Hγₒ") as "[●Hγₒ ◯Hγₒ]".
    { rewrite -not_elem_of_dom. set_solver. }
    iMod ("Hcl'" with "[$●Hγ_vers $●Hγᵥ' $●Hγᵣ $●Hγₕ $Hbackup₁ $Hγ Hlft Hrht Hlin Hγₑ $●Hγₒ $●Hγᵢ']") as "_".
    { rewrite lookup_insert_eq. iExists (S idx₁).
      rewrite (take_drop_middle _ _ _ Hagree).
      rewrite bool_decide_eq_true_2; last lia.
      iSplit.
      { done. }
      iNext. iSplit.
      { iApply (d67 _ _ _ _ (dom log₁)).
        { set_solver. }
        rewrite -{3}(take_drop_middle _ _ _ Hagree) /x66_inv.
        iFrame.
        rewrite /ad65_inv.
        iFrame "% #".
        rewrite bool_decide_eq_false_2; last first.
        { intros <-. congruence. }
        rewrite bool_decide_eq_false_2; last done.
        iFrame. }
        iSplit.
        { iPureIntro. do 2 rewrite dom_insert. set_solver. }
        iPureIntro.
        split.
        - exists ver₁.
          rewrite lookup_insert_eq.
          repeat split; auto.
          rewrite bool_decide_eq_true_2 //.
        - repeat split.
          { set_solver. }
          { apply acbd98_insert; last done.
            intros [loc Hcontra]%elem_of_map_img.
            eapply map_Forall_lookup_1 in Hcontra; last done.
            simpl in Hcontra. lia. }
          { rewrite lookup_insert_eq //. }
          { apply f74_alloc; last done.
            rewrite Forall_forall in Hrange₁. auto. }
          { rewrite map_Forall_insert. split; first done.
            eapply map_Forall_impl; eauto.
            rewrite -not_elem_of_dom. set_solver. } }
    iAssert (⌜backup ≠ ldes'⌝)%I as "%Hnoaba".
    { iIntros (->).
      iApply (ec70 with "Hldes' □Hbackup"); first done.
      lia. }
    assert (backup' ≠ ldes') as Hnoaba'.
    { intros ->.
      apply last_Some_elem_of in Hindex₁.
      rewrite Forall_forall in Hrange₁.
      apply Hrange₁ in Hindex₁.
      rewrite elem_of_dom in Hindex₁.
      destruct Hindex₁.
      congruence. }
    iMod (x96 with "Hldes'") as "#Hldes'".
    iPoseProof (e113_update with "Hlogtokens Hγₚ' Hldes'") as "Hlogtokens".
    { done. }
    iMod ("Hcl" with "[$Hγ' $Hlogtokens $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hbackup₁' $Hver $●Hγₕ' $●Hγ_val]") as "_".
    { iFrame "% # ∗". repeat iSplit; auto.

      { rewrite map_Forall_insert //. }
      { rewrite lookup_insert_eq //=. }
      { iPureIntro. eapply Forall_impl; first done.
        simpl. set_solver. }
      { iPureIntro. destruct (Nat.even ver₁) eqn:Heven₁; last done.
        rewrite lookup_insert_ne; auto. }
      { rewrite bool_decide_eq_false_2 //. set_solver. }
      { rewrite dom_insert. iPureIntro. set_solver. } }
    iModIntro.
    iFrame "% # ∗".
  Qed.

  Lemma ee127 {A} (R : relation A) :
    Symmetric R → Symmetric (Forall2 R).
  Proof.
    intros Hsym xs ys Hxy.
    induction Hxy; by constructor.
  Qed.

  Lemma ecac128 vs vs' :
    Forall val_is_unboxed vs →
      length vs = length vs' →
        Forall2 vals_compare_safe vs vs'.
  Proof.
    revert vs'. induction vs as [| v vs IH].
    - intros vs' Hunboxed Hlen.
      symmetry in Hlen.
      rewrite length_zero_iff_nil in Hlen. simplify_eq. constructor.
    - intros vs' Hunboxed Hlen.
      destruct vs' as [|v' vs'].
      { done. }
      simplify_eq. inv Hunboxed. constructor.
      + by left.
      + auto.
  Qed.

  Lemma c129_spec (γ γᵥ γₕ γᵣ γᵢ γ_val γ_vers γₒ : gname) (l lexp ldes : loc) (dq dq' : dfrac) (expected desired : list val) :
    length expected > 0 → length expected = length desired → Forall val_is_unboxed expected → Forall val_is_unboxed desired →
      inv e23 (caf72_inv γ γᵥ γₕ γᵢ γ_val l (length expected)) -∗
        inv a21 (c78_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ l) -∗
          lexp ↦∗{dq} expected -∗
            ldes ↦∗{dq'} desired -∗
              <<{ ∀∀ backup actual, b28 γ backup actual  }>>
                x9 (length expected) #l #lexp #ldes @ ↑N
              <<{ if bool_decide (actual = expected) then ∃ backup', b28 γ backup' desired else b28 γ backup actual |
                  RET #(bool_decide (actual = expected)); lexp ↦∗{dq} expected ∗ ldes ↦∗{dq'} desired }>>.
    Proof.
Admitted.
End ecb141_wf.
