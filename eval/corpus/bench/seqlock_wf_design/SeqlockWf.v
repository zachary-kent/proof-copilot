From iris.program_logic Require Import atomic.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import lang proofmode notation lib.array.
Require Import Stdlib.ZArith.Zquot.
Require Import Arith ZArith ZifyClasses ZifyInst Lia.
Import derived_laws.bi.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Global Program Instance da0 : BinOp Nat.modulo :=
  {| TBOp := Z.modulo ; TBOpInj := Nat2Z.inj_mod |}.
Add Zify BinOp da0.

Global Program Instance cb1 : BinOp Nat.div :=
  {| TBOp := Z.div ; TBOpInj := Nat2Z.inj_div |}.
Add Zify BinOp cb1.

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

Class fbe10 (Σ : gFunctors) := {
  x52 :: heapGS Σ;
}.

Section a59.
  Context `{!fbe10 Σ, !heapGS Σ}.

  Context (N : namespace).

  Definition fb11 := N .@ "a59".

  Definition x12 := N .@ "c4".

  Definition b14 (γᵥ : gname) (vs : list val) : iProp Σ := True%I.

  Definition efd41 (v : val) (γ : gname) (n : nat) : iProp Σ := True%I.

  Lemma efd41_persistent (v : val) (γ : gname) (n : nat) : Persistent (efd41 v γ n).
  Proof. apply _. Qed.

  Lemma bd42_spec (n : nat) (src : loc) dq vs :
    length vs = n → n > 0 →
      {{{ src ↦∗{dq} vs }}}
        bcaf2 n #src
      {{{ v γ, RET v; src ↦∗{dq} vs ∗ efd41 v γ n ∗ b14 γ vs  }}}.
  Proof.
Admitted.

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
