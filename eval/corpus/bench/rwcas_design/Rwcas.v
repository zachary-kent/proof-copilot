From iris.program_logic Require Import atomic.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import lang proofmode notation.

Definition new_rwcas : val := λ: "x", ref "x".

Definition read : val := λ: "x", !"x".

Definition write : val :=
  λ: "l" "v",
    let: "p" := NewProph in
    Resolve (CmpXchg "l" !"l" "v") "p" #();;
    #().

Class rwcasG Σ := {
  rwcas_heapGS :: heapGS Σ;
}.

Section rwcas.

  Context `{!rwcasG Σ}.

  Context (N : namespace).

  Definition rwcasN : namespace := N .@ "rwcas".

  Definition value (γ : gname) (n : Z) : iProp Σ := True%I.

  Definition is_rwcas (γ : gname) (v : val) : iProp Σ := True%I.

  Lemma is_rwcas_persistent (γ : gname) (v : val) : Persistent (is_rwcas γ v).
  Proof. apply _. Qed.

  Lemma new_rwcas_spec (n : Z) :
    {{{ True }}}
      new_rwcas #n
    {{{ γ l, RET l; is_rwcas γ l ∗ value γ n }}}.
  Proof.
Admitted.

  Lemma read_spec (γ : gname) (v : val) :
    is_rwcas γ v -∗
      <<{ ∀∀ (n : Z), value γ n }>> read v @ ↑N <<{ value γ n | RET #n }>>.
  Proof.
Admitted.

  Lemma write_spec γ v (q : Z) :
    is_rwcas γ v -∗
      <<{ ∀∀ (n : Z), value γ n }>> write v #q @ ↑N <<{ value γ q | RET #() }>>.
  Proof.
Admitted.

End rwcas.
