(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Utf8. (* → λ ∀ ∃ ↔ *)

Require Import dfs_graph_def.

Set Implicit Arguments.

Reserved Notation "x '<sc' y" (at level 70).

Inductive dfs_sub_calls : (list 𝓔 * list 𝓔) → (list 𝓔 * list 𝓔) -> Prop :=
  | in_dsc_0 : ∀ v x l, x ∈ v → (v,l) <sc (v,x::l)
  | in_dsc_1 : ∀ v x l, x ∉ v → (x::v,succs x++l) <sc (v,x::l)
where "x '<sc' y" := (dfs_sub_calls x y).

Definition 𝔻dfs v l := Acc dfs_sub_calls (v,l).

Fact g_dfs_d_dfs v l : (∃o, v ⊔ l ⟼d o) -> 𝔻dfs v l.
Proof.
  intros (o & H); revert H.
  induction 1; constructor; inversion 1; tauto.
Qed.

Section dfs.

  (* The explicit dependent pattern matching

     match l ** return 𝔻dfs _ l → _ ** with

     ** ... ** added below, is not needed any more for Coq 8.11+ *)

  Let Fixpoint dfs_pwc v l (D : 𝔻dfs v l) {struct D} : {o | v⊔l ⟼d o}.
  Proof. refine(
    match l return 𝔻dfs _ l → _ with
      | nil  => λ _,       exist _ v _
      | x::l => λ D, 
      match x ∈? v as b return x ∈? v = b → _ with
        | true  => λ E, 
             let (o,Go) := dfs_pwc v l _
             in            exist _ o _
        | false => λ E, 
             let (o,Go) := dfs_pwc (x::v) (succs x ++ l) _
             in            exist _ o _
      end eq_refl
    end D).
    1,2,4: cycle 1. (* reordering of proof obligations *)
    1-2: apply Acc_inv with (1 := D); constructor; apply mem_iff; auto.
    * now constructor 1.
    * constructor 2; auto; apply mem_iff; auto.
    * constructor 3; auto; apply mem_iff; auto.
  Qed.
  
  Definition dfs v l D := proj1_sig (@dfs_pwc v l D).

  Definition dfs_spec v l D : v ⊔ l ⟼d @dfs v l D.
  Proof. apply (proj2_sig _). Qed.

End dfs.

(** The domain is exactly the projection of the graph *)

Theorem d_dfs_eq_g_dfs v l : 𝔻dfs v l ↔ exists o, v ⊔ l ⟼d o.
Proof.
  split.
  + intros D; exists (dfs D); apply dfs_spec.
  + apply g_dfs_d_dfs.
Qed.

(* → λ ∀ ∃ ↔ *)

Fact 𝔻dfs_1 v : 𝔻dfs v nil.
Proof. constructor; inversion 1. Qed.

Fact 𝔻dfs_2 v x l : x ∈ v → 𝔻dfs v l → 𝔻dfs v (x::l).
Proof. constructor; inversion 1; tauto. Qed.

Fact 𝔻dfs_3 v x l : x ∉ v → 𝔻dfs (x::v) (succs x++l) → 𝔻dfs v (x::l).
Proof. constructor; inversion 1; tauto. Qed.

Section 𝔻dfs_rect.

  (* This is Type-bounded induction principle
       
     Notice HP0 which restricts the induction principle to
     proof irrelevant predicates ... no big deal because
     dfs is proof irrelevant anyway *)

  Variables (P   : ∀ v l, 𝔻dfs v l → Type)
            (HPi : ∀ v l D1 D2, @P v l D1 → @P v l D2)
            (HP1 : ∀ v, P (𝔻dfs_1 v))
            (HP2 : ∀ v x l H D (_ : P D), P (@𝔻dfs_2 v x l H D))
            (HP3 : ∀ v x l H D (_ : P D), P (@𝔻dfs_3 v x l H D)).

  Fixpoint 𝔻dfs_rect v l D { struct D } : @P v l D.
  Proof.
    destruct l as [ | x l ].
    * apply HPi with (1 := HP1 _).
    * case_eq (mem x v); intros H.
      + refine (HPi _ (HP2 _ _ (𝔻dfs_rect _ _ _))).
        - now apply mem_iff.
        - apply Acc_inv with (1 := D); constructor; apply mem_iff; auto.
      + refine (HPi _ (HP3 _ _ (𝔻dfs_rect _ _ _))).
        - now apply mem_iff.
        - apply Acc_inv with (1 := D); constructor; apply mem_iff; auto.
  Qed.

End 𝔻dfs_rect.

Definition 𝔻dfs_rec (P : ∀ v l, 𝔻dfs v l → Set) := 𝔻dfs_rect P.
Definition 𝔻dfs_ind (P : ∀ v l, 𝔻dfs v l → Prop) := 𝔻dfs_rect P.

