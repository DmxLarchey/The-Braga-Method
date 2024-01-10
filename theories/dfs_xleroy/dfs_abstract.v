(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             JF Monin                   [**]                *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                            [**] Affiliation Verimag -- UGA *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2.1 FREE SOFTWARE LICENSE AGREEMENT        *)
(**************************************************************)

Require Import List Relations Utf8.

Import ListNotations.

Arguments clos_refl_trans {_}.
#[global] Hint Constructors clos_refl_trans : core.

#[global] Infix "∈" := In (at level 70, no associativity).
#[global] Infix "∉" := (λ x a, ¬ x ∈ a) (at level 70, no associativity).
#[global] Notation "P ⊆ Q" := (∀x, P x → Q x) (at level 70, no associativity, format "P  ⊆  Q").
#[global] Notation "P ≡ Q" := (∀x, P x ↔ Q x) (at level 70, no associativity, format "P  ≡  Q").
#[global] Notation "⦃ l ⦄" := (λ x, x ∈ l) (at level 1, format "⦃ l ⦄").
#[global] Notation "P ∪ Q" := (λ x, P x ∨ Q x) (at level 20, left associativity, format "P  ∪  Q").

#[global] Hint Resolve in_eq in_cons
                       incl_nil_l incl_refl incl_tran
                       incl_cons incl_tl : core.

Section crt_exclude.

  Variables (X : Type) (R : X → X → Prop).

  Implicit Types (P Q : X → Prop).

  (** crt_exclude R P x y means :
      - there is a R-sequence x = x1 R x2 R ... R xn = y
        where x1,...,x{n-1} do not belong to P
      - orelse (equivalently) y can be reached from x
        following the relation R while also not crossing 
        the predicate P, except possibly at y *)
  Inductive crt_exclude (P : X → Prop) : X → X → Prop :=
    | crt_excl_refl x : crt_exclude P x x
    | crt_excl_step x y z : ¬ P x → R x y → crt_exclude P y z → crt_exclude P x z.

  Hint Constructors crt_exclude : core.

  Definition crt_exclude_refl := crt_excl_refl.

  Fact crt_exclude_trans P x y z : crt_exclude P x y → crt_exclude P y z → crt_exclude P x z.
  Proof. induction 1; eauto. Qed.

  Hint Resolve crt_exclude_trans : core.

  Fact crt_exclude_mono P Q : P ⊆ Q → ∀ x y, crt_exclude Q x y → crt_exclude P x y.
  Proof. induction 2; eauto. Qed.

  Hint Resolve crt_exclude_mono : core.

  Fact crt_exclude_empty x y :
         crt_exclude (λ _, False) x y 
       ↔ clos_refl_trans R x y.
  Proof.
    split.
    + induction 1; eauto.
    + revert x; apply clos_refl_trans_ind_right; eauto. 
  Qed.

  Fact crt_exclude_yes P x y : crt_exclude P x y → P x → x = y.
  Proof. induction 1; tauto. Qed.

  Notation weak_dec Q := (∀z, Q z ∨ ~ Q z).

  Fact crt_exclude_choice P Q x y :
         weak_dec Q
       → crt_exclude P x y
       → crt_exclude Q x y ∨ ∃z, Q z ∧ crt_exclude P z y.
  Proof. 
    intros D.
    induction 1 as [ | x y z H1 H2 H3 IH3 ]; eauto.
    destruct (D x) as [ H0 | H0 ].
    + right; exists x; eauto.
    + destruct IH3; eauto.
  Qed.

  Lemma crt_exclude_union P Q x y :
           weak_dec Q
         → crt_exclude P x y
         → crt_exclude (Q ∪ P) x y 
         ∨ ∃q z, Q q ∧ R q z ∧ crt_exclude (Q ∪ P) z y.
  Proof.
    intros D.
    induction 1 as [ x | x y z H1 H2 H3 IH3 ]; auto.
    destruct IH3 as [ IH3 | IH3 ]; destruct (D x) as [ H4 | H4 ]; eauto.
    + right; exists x, y; auto.
    + left; constructor 2 with y; auto; tauto.
  Qed.

  (* If there is a path from x to y excluding P, then
     the last occurence of x in this path gives a sub-path 
     from x to y which excludes {x} ∪ P *)
  Corollary crt_exclude_last P x y :
           weak_dec (eq x)
         → crt_exclude P x y
         → x = y ∨ ∃z, R x z ∧ crt_exclude (eq x ∪ P) z y.
  Proof.
    intros H1 H2.
    destruct crt_exclude_union
      with (1 := H1) (2 := H2)
      as [ H | (? & z & <- & ? & ?) ]; eauto.
    rewrite (crt_exclude_yes _ _ _ H); auto.
  Qed.

  Let CRT a l x := ∃i, i ∈ l ∧ crt_exclude ⦃a⦄ i x.

  Fact crt_exclude_fold_nil a : ⦃a⦄ ∪ CRT a [] ≡ ⦃a⦄.
  Proof.
    intros x; split; eauto.
    now intros [ | (? & [] & _) ].
  Qed.

(*
  Fact crt_exclude_fold_cons a l x :
         weak_dec (⦃a⦄ ∪ CRT a l)
       → ⦃a⦄ ∪ CRT a l ∪ crt_exclude (⦃a⦄ ∪ CRT a l) x
       ≡ ⦃a⦄ ∪ CRT a (x::l).
  Proof.
    intros D z; split.
    + intros [ [ H | (i & [] ) ] | H ]; eauto.
      * right; exists i; eauto.
      * right; exists x; split; auto.
        revert H; apply crt_exclude_mono; auto.
    + intros [ H | (i & [ <- | Hi ] & ?) ]; eauto.
      destruct crt_exclude_choice 
        with (2 := H)
             (Q := ⦃a⦄ ∪ CRT a l)
        as [ H1 | (u & H1 & H3) ]; auto.
      * destruct H1 as [ H1 | (i & H1 & H2) ]; eauto.
        - destruct (crt_exclude_yes _ _ _ H3 H1); auto.
        - left; right; exists i; eauto.
      * left; right; exists i; eauto.
  Qed.
*)

  Fact crt_exclude_special a x y :
      weak_dec (⦃a⦄ ∪ crt_exclude ⦃a⦄ x)
    → crt_exclude ⦃a⦄ y 
    ⊆ ⦃a⦄ ∪ crt_exclude ⦃a⦄ x ∪ crt_exclude (⦃a⦄ ∪ crt_exclude ⦃a⦄ x) y.
  Proof.
    intros D z H.
    destruct crt_exclude_choice
        with (2 := H)
             (Q := ⦃a⦄ ∪ crt_exclude ⦃a⦄ x)
        as [ H1 | (u & H1 & H2) ]; auto.
    destruct H1 as [ H1 | H1 ]; eauto.
    destruct (crt_exclude_yes _ _ _ H2 H1); auto.
  Qed.

  Fact crt_exclude_special' a x y :
      weak_dec (⦃a⦄ ∪ crt_exclude ⦃a⦄ x)
    → ⦃a⦄ ∪ crt_exclude ⦃a⦄ x ∪ crt_exclude (⦃a⦄ ∪ crt_exclude ⦃a⦄ x) y
    ≡ ⦃a⦄ ∪ crt_exclude ⦃a⦄ x ∪ crt_exclude ⦃a⦄ y.
  Proof.
    intros D z; split.
    + intros [ | H ]; auto; right.
      revert H; apply crt_exclude_mono; auto.
    + intros [ | H ]; auto.
      now apply crt_exclude_special.
  Qed.

  Inductive crt_nocycle : (X → Prop) → X → X → Prop :=
    | crt_nc_refl P x : crt_nocycle P x x
    | crt_nc_step P x y z : ¬ P x → R x y → crt_nocycle (eq x ∪ P) y z → crt_nocycle P x z.

  Hint Constructors crt_nocycle : core.

  Fact crt_nocycle_mono P Q : P ⊆ Q → ∀ x y, crt_nocycle Q x y → crt_nocycle P x y.
  Proof. 
    intros H1 x y H2; revert H2 P H1. 
    induction 1 as [ | P x y z H1 H2 H3 IH3 ]; eauto.
    intros Q HQ. 
    constructor 2 with y; eauto. 
    apply IH3; intros ? []; eauto.
  Qed.

  Fact crt_nocycle_member P x y : crt_nocycle P x y → P x → x = y.
  Proof. induction 1; tauto. Qed. 

End crt_exclude.

Arguments crt_exclude {_}.
#[global] Hint Constructors crt_exclude : core.

Arguments crt_nocycle {_}.
#[global] Hint Constructors crt_nocycle : core.

Section dfs_post_condition.

  Variable (X : Type).

  Implicit Types (α : X → Prop) (l : list X).
  
  Variables (in_dec : ∀ x l, {x ∈ l} + {x ∉ l})
            (succ : X → list X).

  (* For Ω : (X → Prop) → Prop, the set P is a smallest 
     satisfying Ω for inclusion. *)
  Definition smallest Ω α := Ω α ∧ ∀β, Ω β → α ⊆ β.

  Fact smallest_equiv Ω Ψ	: Ω ≡ Ψ → smallest Ω ≡ smallest Ψ.
  Proof.
    intros H a; split; intros (H1%H & H2); split; auto;
      intros ? ?%H; now apply H2.
  Qed.

  (* The invariant for dfs_acc wrt to accumulator "a" is an
     upper bound of a stable under "succ" of its member
     which are not members of "a" already, formulated in
     a positive way. *)
  Definition dfs_acc_invar a α := ∀x, α x → x ∈ a ∨ ⦃succ x⦄ ⊆ α.

  Fact dfs_acc_invar_equiv a α β :
        β ≡ α → dfs_acc_invar a α → dfs_acc_invar a β.
  Proof.
    intros E H x []%E%H; eauto; right.
    intros; apply E; eauto.
  Qed.

  Notation next := (λ v u, u ∈ succ v).

  Local Fact dfs_acc_invar_crt_exclude a α x y :
          dfs_acc_invar a α
        → crt_exclude next ⦃a⦄ x y
        → α x
        → α y.
  Proof.
    intros H; induction 1; auto.
    intros []%H; eauto; tauto.
  Qed.

  Local Fact crt_exclude_dfs_acc_invar a x :
         dfs_acc_invar a (⦃a⦄ ∪ crt_exclude next ⦃a⦄ x).
  Proof.
    intros y [ H | H ]; auto.
    induction H as [ x | x y z Hx Hy H1 [ IH1 | IH1 ] ]; eauto.
    + destruct (in_dec x a); eauto.
    + right; intros ? []%IH1; eauto.
  Qed.
 
  (* A high-level characterization of the output of
     dfs_acc, provided it exist: it is equivalent
     to the union of ⦃a⦄ and crt_exclude next ⦃a⦄ x *)
  Lemma dfs_acc_post_condition a x α :
         smallest (λ α, α x ∧ ⦃a⦄ ⊆ α ∧ dfs_acc_invar a α) α
       ↔ α ≡ ⦃a⦄ ∪ crt_exclude next ⦃a⦄ x.
  Proof.
    split.
    + intros ((H1 & H2 & H3) & H4).
      intros y; split; revert y.
      * apply H4; repeat split; eauto.
        apply crt_exclude_dfs_acc_invar.
      * intros ? []; auto.
        eapply dfs_acc_invar_crt_exclude; eauto.
    + intros H; repeat split.
      * apply H; eauto.
      * intros ? ?; apply H; auto.
      * generalize (crt_exclude_dfs_acc_invar a x).
        apply dfs_acc_invar_equiv, H.
      * intros β (H1 & H2 & H3) y [Hy%H2 | Hy]%H; auto.
        eapply dfs_acc_invar_crt_exclude; eauto. 
  Qed.

  (* The invariant for dfs is a set stable under succ *)
  Definition dfs_invar α := ∀ x y, α x → y ∈ succ x → α y.

  Fact dfs_invar_iff : dfs_invar ≡ dfs_acc_invar [].
  Proof.
    split.
    + right; eauto.
    + intros H ? ? []%H ?; now auto.
  Qed.

  Fact smallest_invar_equiv x :
        smallest (λ α, α x ∧ dfs_invar α)
      ≡ smallest (λ α, α x ∧ ⦃[]⦄ ⊆ α ∧ dfs_acc_invar [] α).
  Proof.
    apply smallest_equiv.
    intros ?; rewrite dfs_invar_iff; simpl; tauto.
  Qed.

  Lemma dfs_post_condition x α :
         smallest (λ α, α x ∧ dfs_invar α) α
       ↔ α ≡ clos_refl_trans next x.
  Proof.
    rewrite smallest_invar_equiv,
            dfs_acc_post_condition.
    simpl; split; intros E y; rewrite E, crt_exclude_empty; tauto.
  Qed.

End dfs_post_condition.

Arguments smallest {X}.
Arguments dfs_acc_invar {X}.
Arguments dfs_invar {X}.




