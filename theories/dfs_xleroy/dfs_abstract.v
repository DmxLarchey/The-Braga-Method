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

  (** crt_exclude R P x y :
      y can be reached from x by a R-sequence, 
      not crossing P, except possibly at y *)
  Inductive crt_exclude (P : X → Prop) : X → X → Prop :=
    | crt_excl_refl x : crt_exclude P x x
    | crt_excl_step x y z : ¬ P x → R x y → crt_exclude P y z → crt_exclude P x z.

  Hint Constructors crt_exclude : core.

  Fact crt_exclude_empty x y :
         crt_exclude (fun _ => False) x y 
       ↔ clos_refl_trans R x y.
  Proof.
    split.
    + induction 1; eauto.
    + revert x; apply clos_refl_trans_ind_right; eauto. 
  Qed.

  Fact crt_exclude_mono P Q : P ⊆ Q → ∀ x y, crt_exclude Q x y → crt_exclude P x y.
  Proof. induction 2; eauto. Qed.

  Hint Resolve crt_exclude_mono : core.

  Let f P x y := P y ∨ crt_exclude P x y.

  Fact fl_f P l y : fold_left f l P y ↔ P y ∨ ∃ x, x ∈ l ∧ crt_exclude P x y.
  Proof.
    induction l as [ | x l IHl ] in y, P |- *; simpl.
    + split; auto; now intros [ | (? & ? & _) ].
    + rewrite IHl; unfold f; split.
      * intros [ [] | (u & ? & ?) ]; eauto.
        right; exists u; split; eauto.
        eapply crt_exclude_mono; [ | eassumption ]; simpl; auto.
      * intros [ | (u & [ <- | Hu ] & ?) ]; eauto.
        assert (P y ∨ crt_exclude P x y ∨ crt_exclude (λ u, P u ∨ crt_exclude P x u) u y) as [ | [] ]; eauto.
        clear IHl Hu l.
        induction H as [ | ? ? ? ? ? ? [ | [] ] ]; eauto.
        do 2 right; constructor 2 with y; auto.
  Admitted.

End crt_exclude.

Arguments crt_exclude {_}.
#[global] Hint Constructors crt_exclude : core.

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




