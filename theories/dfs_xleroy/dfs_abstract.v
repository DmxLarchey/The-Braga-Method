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

#[global] Notation "P ⊆ Q" := (∀x, P x → Q x) (at level 70, no associativity, format "P  ⊆  Q").
#[global] Notation "P ≡ Q" := (∀x, P x ↔ Q x) (at level 70, no associativity, format "P  ≡  Q").
#[global] Notation "P ∪ Q" := (λ x, P x ∨ Q x) (at level 20, left associativity, format "P  ∪  Q").

#[global] Infix "∈" := In (at level 70, no associativity).
#[global] Infix "∉" := (λ x a, ¬ x ∈ a) (at level 70, no associativity).
#[global] Notation "⦃ l ⦄" := (λ x, x ∈ l) (at level 1, format "⦃ l ⦄").

#[global] Hint Resolve in_eq in_cons
                       incl_nil_l incl_refl incl_tran
                       incl_cons incl_tl : core.

Section crt_exclude.

  Variables (X : Type) (R : X → X → Prop).

  Implicit Types (A B : X → Prop).

  Section crt_exclude_def.

    Variables A : X → Prop.

    (* Instead of an inductive definition like

       Inductive crt_exclude : X → X → Prop :=
         | crt_excl_refl x : crt_exclude P x x
         | crt_excl_step x y z : ¬ A x → R x y → crt_exclude y z → crt_exclude x z.

       we use an equivalent definition using the
       existing clos_refl_trans, and establish
       simulated constructors and recursors. *)

    Definition crt_exclude := clos_refl_trans (λ x y, ¬ A x ∧ R x y).

    Fact crt_exclude_refl x : crt_exclude x x.
    Proof. constructor 2. Qed.

    Fact crt_exclude_step x y z : ¬ A x → R x y → crt_exclude y z → crt_exclude x z.
    Proof. constructor 3 with y; eauto. Qed.

    Fact crt_exclude_trans x y z : crt_exclude x y → crt_exclude y z → crt_exclude x z.
    Proof. econstructor 3; eauto. Qed.

    Variables (P : X → X → Prop)
              (HP0 : ∀x, P x x)
              (HP1 : ∀ x y z, ¬ A x → R x y → crt_exclude y z → P y z → P x z).

    Theorem crt_exclude_ind x y : crt_exclude x y → P x y.
    Proof.
      intros H%clos_rt_rt1n_iff.
      induction H as [ | ? ? ? [] ?%clos_rt_rt1n_iff ]; eauto.
    Qed.

  End crt_exclude_def.

  Hint Resolve crt_exclude_refl crt_exclude_step crt_exclude_trans : core.

  Fact crt_exclude_mono A B : A ⊆ B → ∀ x y, crt_exclude B x y → crt_exclude A x y.
  Proof. induction 2 using crt_exclude_ind; eauto. Qed.

  Hint Resolve crt_exclude_mono : core.

  Fact crt_exclude_empty x y :
         crt_exclude (λ _, False) x y 
       ↔ clos_refl_trans R x y.
  Proof.
    split.
    + induction 1 using crt_exclude_ind; eauto.
    + revert x; apply clos_refl_trans_ind_right; eauto. 
  Qed.

  Fact crt_exclude_yes A x y : crt_exclude A x y → A x → x = y.
  Proof. induction 1 using crt_exclude_ind; tauto. Qed.

  Fact crt_exclude_inv A x y : crt_exclude A x y → x = y ∨ ¬ A x ∧ ∃z, R x z ∧ crt_exclude A z y.
  Proof. induction 1 using crt_exclude_ind; eauto. Qed.

  Notation weak_dec A := (∀z, A z ∨ ~ A z).

  Fact crt_exclude_choice A B x y :
         weak_dec B
       → crt_exclude A x y
       → crt_exclude B x y ∨ ∃z, B z ∧ crt_exclude A z y.
  Proof. 
    intros wdec.
    induction 1 as [ | ? ? ? ? ? ? IH ] using crt_exclude_ind; eauto.
    destruct (wdec x).
    + right; exists x; eauto.
    + destruct IH; eauto.
  Qed.

  Lemma crt_exclude_further A B x y :
           weak_dec B
         → crt_exclude A x y
         → crt_exclude (B ∪ A) x y 
         ∨ ∃q z, B q ∧ R q z ∧ crt_exclude (B ∪ A) z y.
  Proof.
    intros wdec.
    induction 1 as [ | x y ? ? ? ? IH ] using crt_exclude_ind; auto.
    destruct IH; destruct (wdec x); eauto.
    + right; exists x, y; auto.
    + left; apply crt_exclude_step with y; auto; tauto.
  Qed.

  (* If there is a path from x to y excluding A, then
     the last occurence of x in this path gives a sub-path 
     from x to y which excludes {x} ∪ A *)
  Corollary crt_exclude_last A x y :
           weak_dec (eq x)
         → crt_exclude A x y
         → x = y ∨ ∃z, R x z ∧ crt_exclude (eq x ∪ A) z y.
  Proof.
    intros H1 H2.
    destruct crt_exclude_further
      with (1 := H1) (2 := H2)
      as [ H | (? & z & <- & ? & ?) ]; eauto.
    rewrite (crt_exclude_yes _ _ _ H); auto.
  Qed.

  Notation crt_exclude_union A L := (λ x, ∃i, L i ∧ crt_exclude A i x).

  Fact crt_exclude_union_nil A : A ∪ crt_exclude_union A (λ _, False)  ≡ A.
  Proof.
    intros x; split; eauto.
    now intros [ | (? & [] & _) ].
  Qed.

  Fact crt_exclude_special A x y :
      let B := A ∪ crt_exclude A x
      in  weak_dec B → crt_exclude A y ⊆ B ∪ crt_exclude B y.
  Proof.
    intros B D z H.
    destruct crt_exclude_choice
        with (2 := H)
             (B := B)
        as [ H1 | (u & H1 & H2) ]; unfold B; auto.
    destruct H1 as [ H1 | H1 ]; eauto.
    destruct (crt_exclude_yes _ _ _ H2 H1); auto.
  Qed.

End crt_exclude.

Arguments crt_exclude {_}.
#[global] Hint Resolve crt_exclude_refl crt_exclude_step crt_exclude_trans : core.

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
    intros H; induction 1 using crt_exclude_ind; auto.
    intros []%H; eauto; tauto.
  Qed.

  Fact crt_exclude_dfs_acc_invar A x :
         (∀ x, A x ∨ ¬ A x)
       → dfs_acc_invar A (A ∪ crt_exclude next A x).
  Proof.
    intros D y [ H | H ]; auto.
    induction H as [ x | x y z Hx Hy H1 [ IH1 | IH1 ] ] using crt_exclude_ind; eauto.
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




