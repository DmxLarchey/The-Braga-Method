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

  Lemma crt_exclude_further P Q x y :
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
    destruct crt_exclude_further
      with (1 := H1) (2 := H2)
      as [ H | (? & z & <- & ? & ?) ]; eauto.
    rewrite (crt_exclude_yes _ _ _ H); auto.
  Qed.

  Notation crt_exclude_union P l := (λ x, ∃i, i ∈ l ∧ crt_exclude P i x).

  Fact crt_exclude_union_nil a : ⦃a⦄ ∪ crt_exclude_union ⦃a⦄ [] ≡ ⦃a⦄.
  Proof.
    intros x; split; eauto.
    now intros [ | (? & [] & _) ].
  Qed.

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

  Implicit Types (A B α : X → Prop).
  
  Variables (succ : X → list X).

  Implicit Type Ω : (X → Prop) → Prop.

  (* For Ω : (X → Prop) → Prop, the set P is a smallest 
     satisfying Ω for inclusion. *)
  Definition smallest Ω α := Ω α ∧ ∀β, Ω β → α ⊆ β.

  Notation ext Ω := (∀ α β, α ≡ β → Ω α → Ω β).

  Fact smallest_ext Ω : ext Ω → ext (smallest Ω).
  Proof.
    intros E a b H (H1 & H2); split.
    + eapply E; eauto.
    + intros c Hc z Hz%H; revert z Hz.
      now apply H2.
  Qed. 

  Fact smallest_equiv Ω Ψ	: Ω ≡ Ψ → smallest Ω ≡ smallest Ψ.
  Proof.
    intros H a; split; intros (H1%H & H2); split; auto;
      intros ? ?%H; now apply H2.
  Qed.

  Fact smallest_uniq Ω α β : smallest Ω α → smallest Ω β → α ≡ β.
  Proof.
    intros H1 H2 x; split; revert x.
    + apply H1, H2.
    + apply H2, H1.
  Qed.

  (* The invariant for dfs_acc wrt to accumulator "A" is an
     upper bound of a stable under "succ" of its member
     which are not members of "A" already, formulated in
     a positive way. *)
  Definition dfs_acc_invar A α := ∀x, α x → A x ∨ ⦃succ x⦄ ⊆ α.

  Fact dfs_acc_invar_mono A B α : A ⊆ B → dfs_acc_invar A α → dfs_acc_invar B α.
  Proof. intros H1 H2 x []%H2; auto. Qed.

  Fact dfs_acc_invar_ext A : ext (dfs_acc_invar A).
  Proof.
    intros ? ? E H ? []%E%H; eauto; right.
    intros; apply E; auto.
  Qed.

  Notation next := (λ v u, u ∈ succ v).

  Local Fact dfs_acc_invar_crt_exclude A α x y :
          dfs_acc_invar A α
        → crt_exclude next A x y
        → α x
        → α y.
  Proof.
    intros H; induction 1; auto.
    intros []%H; eauto; tauto.
  Qed.

  Fact crt_exclude_dfs_acc_invar A x :
         (∀ x, A x ∨ ¬ A x)
       → dfs_acc_invar A (A ∪ crt_exclude next A x).
  Proof.
    intros D y [ H | H ]; auto.
    induction H as [ x | x y z Hx Hy H1 [ IH1 | IH1 ] ]; eauto.
    + destruct (D x); eauto.
    + right; intros ? []%IH1; eauto.
  Qed.

  Let INV A x α := α x ∧ A ⊆ α ∧ dfs_acc_invar A α.

  Hint Resolve dfs_acc_invar_ext : core.

  Local Fact INV_ext A x : ext (INV A x).
  Proof.
    intros alpha beta E (H1%E & H2 & H3); repeat split; eauto.
    intros; apply E; auto.
  Qed.

  Lemma smallest_crt_exclude A x :
         (∀ x, A x ∨ ¬ A x)
       → smallest (INV A x) (A ∪ crt_exclude next A x).
  Proof.
    repeat split; eauto.
    + apply crt_exclude_dfs_acc_invar; auto.
    + intros β (H1 & H2 & H3) y [Hy%H2 | Hy]; auto.
      eapply dfs_acc_invar_crt_exclude; eauto.
  Qed. 

  (* A high-level characterization of the output of
     dfs_acc, provided it exist: it is equivalent
     to the union of ⦃a⦄ and crt_exclude next ⦃a⦄ x *)
  Lemma dfs_acc_post_condition A x α :
         (∀ x, A x ∨ ¬ A x)
       → smallest (λ α, α x ∧ A ⊆ α ∧ dfs_acc_invar A α) α
       ↔ α ≡ A ∪ crt_exclude next A x.
  Proof.
    intros D; split.
    + intro.
      eapply smallest_uniq.
      * eassumption.
      * now apply smallest_crt_exclude.
    + intros H. 
      generalize (smallest_crt_exclude A x D).
      apply smallest_ext.
      * apply INV_ext.
      * intro; rewrite <- H; tauto.
  Qed.

  (* The invariant for dfs is a set stable under succ *)
  Definition dfs_invar α := ∀ x y, α x → y ∈ succ x → α y.

  Fact dfs_invar_iff : dfs_invar ≡ dfs_acc_invar (λ _, False).
  Proof.
    split.
    + right; eauto.
    + intros H ? ? []%H ?; now auto.
  Qed.

  Fact smallest_invar_equiv x :
        smallest (λ α, α x ∧ dfs_invar α)
      ≡ smallest (λ α, α x ∧ (λ _, False) ⊆ α ∧ dfs_acc_invar (λ _, False) α).
  Proof.
    apply smallest_equiv.
    intros ?; rewrite dfs_invar_iff; simpl; tauto.
  Qed.

  Lemma dfs_post_condition x α :
         smallest (λ α, α x ∧ dfs_invar α) α
       ↔ α ≡ clos_refl_trans next x.
  Proof.
    rewrite smallest_invar_equiv,
            dfs_acc_post_condition; [ | tauto ].
    simpl; split; intros E y; rewrite E, crt_exclude_empty; tauto.
  Qed.

End dfs_post_condition.

Arguments smallest {X}.
Arguments dfs_acc_invar {X}.
Arguments dfs_invar {X}.




