From iris.program_logic Require Import atomic.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import lang proofmode notation lib.array.
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

Class fbe7 (Σ : gFunctors) := {
  x35 :: heapGS Σ;
}.

Section a38.
  Context `{!fbe7 Σ, !heapGS Σ}.

  Context (N : namespace).

  Definition fb8 := N .@ "a38".

  Definition b10 (γ : gname) (vs : list val) : iProp Σ := True%I.

  Definition efd30 (v : val) (γₕ : gname) (n : nat) : iProp Σ := True%I.

  Lemma efd30_persistent (v : val) (γₕ : gname) (n : nat) : Persistent (efd30 v γₕ n).
  Proof. apply _. Qed.

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

  Lemma x34_spec (γₕ : gname) (v : val) (n : nat) :
    n > 0 →
      efd30 v γₕ n -∗
        <<{ ∀∀ vs, b10 γₕ vs  }>>
          f4 n v @ ↑N
        <<{ ∃∃ copy : loc, b10 γₕ vs | RET #copy; copy ↦∗ vs }>>.
  Proof.
Admitted.

End a38.
