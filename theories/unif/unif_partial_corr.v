(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Bool Arith Lia Utf8. (* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ ≠ *)

Require Import unif_graph_def unif_fun unif_fix.

Set Implicit Arguments.

(** We can show partial correction and termination, but first
    we need so preliminary notions and results *)

(** Substitution equivalence *)

Definition subst_eq σ υ := forall x, (µ x)⦃σ⦄ = (µ x)⦃υ⦄.

Infix "≈" := subst_eq (at level 70, no associativity).

(* ≈ preserves substituted terms *)

Fact subst_eq_trm σ υ : σ ≈ υ → ∀t, t⦃σ⦄  = t⦃υ⦄.
Proof. intros H; induction t; simpl; f_equal; auto; apply H. Qed.

(* ≈ is an equivalence relation *)

Fact subst_eq_refl σ : σ ≈ σ.
Proof. red; auto. Qed.

Fact subst_eq_sym σ υ : σ ≈ υ → υ ≈ σ.
Proof. intros H ?; symmetry; apply H. Qed.

Fact subst_eq_trans σ υ τ : σ ≈ υ → υ ≈ τ → σ ≈ τ.
Proof. intros H1 H2 ?; rewrite H1, H2; auto. Qed.

(* composition is associative and a congruence under ≈ *)

Fact subst_eq_assoc σ υ τ  : (σ o υ) o τ ≈ σ o (υ o τ).
Proof. intro; repeat rewrite subst_comp_spec; auto. Qed.

Fact subst_eq_congrl σ υ τ : υ ≈ τ → σ o υ ≈ σ o τ.
Proof. intros H x; do 2 rewrite subst_comp_spec; apply subst_eq_trm; trivial. Qed.

(** The notion of most general unifier (mgu). Due to the list representation
    of subsitution, mgus are not unique and they can do whatever permutations 
    on variables outside of m and n *)

(* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ ≠ *)

Definition mgu m n σ := 
    m⦃σ⦄ = n⦃σ⦄ ∧ ∀υ, m⦃υ⦄ = n⦃υ⦄ → ∃τ, υ ≈ σ o τ.

Fact mgu_refl u : mgu u u ∅.
Proof. split; auto; intros r ?; exists r; unfold subst_comp; simpl; auto; apply subst_eq_refl. Qed.

Fact mgu_sym u v σ : mgu u v σ → mgu v u σ.
Proof. intros []; split; auto. Qed.

(** mgus compose *)

Lemma mgu_comp m m' σ n n' υ : 
         mgu m m' σ 
       → mgu n⦃σ⦄ n'⦃σ⦄ υ 
       → mgu (m⋄n) (m'⋄n') (σ o υ).
Proof.
  intros (H1 & H2) (H3 & H4); split.
  + do 2 rewrite subst_comp_spec; simpl.
    rewrite H1, H3; trivial.
  + intros p Hp.
    simpl in Hp.
    trm eq inv Hp as E1 E2.
    destruct (H2 _ E1) as (k1 & Hk1).
    do 2 rewrite (subst_eq_trm Hk1), subst_comp_spec in E2.
    destruct (H4 _ E2) as (k2 & Hk2).
    exists k2.
    apply subst_eq_trans with (1 := Hk1),
          subst_eq_sym,
          subst_eq_trans with (1 := subst_eq_assoc _ _ _),
          subst_eq_sym,
          subst_eq_congrl, Hk2.
Qed.

Section mgu_Var.

  (* a more intricate proof here, with two generalizations *)

  Let nocc_check_subst_rec t x m : x ⊀ m → m=µ x ∨ m⦃(x,t)::∅⦄ = m.
  Proof.
    revert t; induction m as [ y | c | m IHm n IHn ]; intros t; simpl occ_check.
    + simpl; destruct (eqV_dec y x); subst; auto.
    + simpl; auto.
    + intros H; simpl; right.
      destruct (IHm t).
      * tauto.
      * destruct H; subst; auto.
      * destruct (IHn t).
        - tauto.
        - destruct H; subst; auto.
        - simpl; f_equal; auto.
  Qed.

  Let nocc_check_subst x m : x ⊀ m → m⦃(x,m)::∅⦄ = m.
  Proof.
    intros H.
    destruct (nocc_check_subst_rec m x m); auto.
    subst; simpl; auto.
    destruct (eqV_dec x x) as [ | [] ]; auto.
  Qed.

  (** If x does not occur (check) in m then [(x,m)] is an mgu of µ x and m *)

  Lemma mgu_Var x m : x ⊀ m → mgu (µ x) m ((x,m)::∅).
  Proof.
    intros Hx; split.
    + simpl.
      destruct (eqV_dec x x) as [ | [] ]; auto.
      symmetry; apply nocc_check_subst; auto.
    + intros r Hr; exists r.
      intros y; simpl.
      destruct (eqV_dec y x) as [ H | ]; auto.
      subst; apply Hr.
  Qed.

End mgu_Var.

(** When there is no unifier *)

(* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ ≠ *)

Definition no_unif u v := forall σ, u⦃σ⦄ ≠ v⦃σ⦄ .

Infix "≬" := no_unif (at level 70).

Fact no_unif_sym u v : u ≬ v → v ≬ u.
Proof. intros H s E; apply (H s); auto. Qed.

Section occ_check_no_unif.

  (* also a non-obvious lemma here *)

  Let occ_check_size σ x t : x ≺ t → ⟦(µ x)⦃σ⦄⟧ < ⟦t⦃σ⦄⟧.
  Proof.
    induction t as [ y | c | m IHm n IHn ]; simpl in *; try tauto.
    revert IHm IHn.
    case_eq (σ↑x).
    + intros v Hv IHm IHn.
      intros [ H | [ H | [ H | H ] ] ]; subst; simpl.
      1,2: rewrite Hv; lia.
      * apply IHm in H; lia.
      * apply IHn in H; lia.
    + intros v Hv IHm IHn.
      simpl; lia.
  Qed.

  (** if x occur checks in m the µ x and m cannot by unified *)

  Lemma occ_check_no_unif x m : x ≺ m → µ x ≬  m.
  Proof.
    intros H s E.
    apply f_equal with (f := trm_size) in E.
    generalize (occ_check_size s _ _ H); lia.
  Qed.

End occ_check_no_unif.

Section unif_partial_correctness_1.
 
  (** We can now show partial correctness of unif on its domain
      We use the dependent induction principle *)

  (* Called on its domain unif produces an mgu or a proof of
     non-unifiability *)

  Theorem unif_partial_correct m n (D : 𝔻unif m n) : 
             match unif D with  
               | Some s => mgu m n s
               | None   => m ≬ n
             end.
  Proof.
    induction D as 
      [ u v H1 H2 IH 
      | c m n
      | c m n
      | c x
      | m n x
      | x m
      | c d
      | m n m' n' D1 ID1 H1
      | m n m' n' D1 ID1 s H1 D2 ID2
      ] using 𝔻unif_rect.
    + rewrite (unif_pirr _ H1); auto.
    + rewrite unif_fix_1; discriminate.
    + rewrite unif_fix_2; discriminate.
    + rewrite unif_fix_3.
      apply mgu_sym, mgu_Var; simpl; tauto.
    + destruct (occ_check_dec x (m⋄n)) as [ H | H ].
      * rewrite unif_fix_4; auto.
        apply no_unif_sym, occ_check_no_unif; auto.
      * rewrite unif_fix_4'; auto.
        apply mgu_sym, mgu_Var; auto.
    + destruct (occ_check_dec x m) as [ H | H ].
      * rewrite unif_fix_5; auto.
        apply occ_check_no_unif; auto.
      * rewrite unif_fix_5'; auto.
        apply mgu_Var; auto.
    + destruct (eqC_dec c d) as [ -> | H ].
      * rewrite unif_fix_6; apply mgu_refl.
      * rewrite unif_fix_6'; auto.
        now inversion 1.
    + rewrite unif_fix_7.
      rewrite H1 in ID1.
      intros s E; apply (ID1 s).
      trm eq inv E as E1 E2; auto.
    + rewrite H1 in ID1.
      case_eq (unif D2).
      * intros r Hr.
        rewrite Hr in ID2.
        rewrite unif_fix_8' with (1 := Hr).
        apply mgu_comp; auto.
      * intros H2.
        rewrite H2 in ID2.
        rewrite unif_fix_8; auto.
        intros s' E; simpl in E.
        trm eq inv E as E1 E2.
        apply ID1 in E1.
        destruct E1 as (k & Hk).
        apply (ID2 k).
        now rewrite <- !subst_comp_spec,
                    <- !subst_eq_trm with (1 := Hk).
  Qed.

End unif_partial_correctness_1.

(** Now we finish with totality/termination but we need 
    more tools obtained as partial correctness results *)

(* A convenient tactic used several times below 
   for inclusions between lists with ++ :: *)

Tactic Notation "finish" "by" hyp(H) := 
  revert H; simpl; rewrite !in_app_iff; simpl; tauto.

(** variable lists and substitutions *)

(* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ ≠ *)

Fact trm_vars_subst σ t : ⟪t⦃σ⦄⟫ ⊆ ⟪t⟫ ++ flat_map (λ c, ⟪snd c⟫) σ.
Proof.
  induction t as [ x | c | m Hm n Hn ].
  + simpl.
    destruct (subst_var_spec σ x) as [ (m & -> & H2) | (-> & H2) ].
    * intros y Hy.
      right; apply in_flat_map.
      exists (x,m); simpl; auto.
    * intros ? [ | [] ]; left; auto.
  + intros _ [].
  + intros x Hx; simpl in Hx.
    destruct ∈ at Hx;
    [ apply Hm in Hx 
    | apply Hn in Hx ]; finish by Hx.
Qed.

Fact trm_vars_subst_In x m t : x ∈ ⟪t⦃(x,m)::∅⦄⟫ → x ∈ ⟪m⟫.
Proof.
  induction t as [ y | d | m' Hm' n' Hn' ]; simpl.
  + destruct (eqV_dec y x); auto.
    intros [| []]; subst; tauto.
  + tauto.
  + rewrite in_app_iff; tauto.
Qed.

Section unif_partial_correctness_2.

  (** Another partial correctness result:

      the variables in the output of unif m n = Some σ
      already occur in m or n *)

  Lemma mgu_trm_vars_incl m n (D : 𝔻unif m n) : 
          match unif D with
            | Some σ => ∀t, ⟪t⦃σ⦄⟫ ⊆ ⟪m⟫++⟪n⟫++⟪t⟫
            | None   => True
          end.
  Proof.
    induction D as 
      [ u v H1 H2 IH 
      | c m n
      | c m n
      | c x
      | m n x
      | x m
      | c d
      | m n m' n' D1 ID1 H1
      | m n m' n' D1 ID1 s H1 D2 ID2
      ] using 𝔻unif_rect.
    + rewrite (unif_pirr _ H1); auto.
    + rewrite unif_fix_1; auto.
    + rewrite unif_fix_2; auto.
    + rewrite unif_fix_3.
      intros t y Hy.
      apply trm_vars_subst in Hy; finish by Hy.
    + destruct (occ_check_dec x (m⋄n)) as [ H | H ].
      * rewrite unif_fix_4; auto.
      * rewrite unif_fix_4'; auto.
        intros t y Hy.
        apply trm_vars_subst in Hy; finish by Hy.
    + destruct (occ_check_dec x m) as [ H | H ].
      * rewrite unif_fix_5; auto.
      * rewrite unif_fix_5'; auto.
        intros t y Hy.
        apply trm_vars_subst in Hy; finish by Hy.
    + destruct (eqC_dec c d) as [ -> | H ].
      * rewrite unif_fix_6.
        intros t y Hy.
        apply trm_vars_subst in Hy; finish by Hy.
      * rewrite unif_fix_6'; auto.
    + rewrite unif_fix_7; auto.
    + rewrite H1 in ID1.
      case_eq (unif D2).
      * intros r Hr.
        rewrite Hr in ID2.
        rewrite unif_fix_8' with (1 := Hr).
        intros t x Hx.
        rewrite subst_comp_spec in Hx; apply ID2 in Hx.
        destruct ∈ at Hx; apply ID1 in Hx; finish by Hx.
      * intros E; rewrite E in ID2.
        rewrite unif_fix_8; auto.
  Qed.

End unif_partial_correctness_2.

(* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ ≠ *)

Section unif_partial_correctness_3.

  (** Another partial correctness result:

      the output of unif m n = Some σ is either
      - the identity substitution 
      - σ erases some variable x of m or n, ie 
        x always disappears after substitution by σ *)

  Lemma mgu_trm_vars_dec m n (D : 𝔻unif m n) : 
         match unif D with
           | Some σ => σ ≈ ∅ ∨ ∃x, x ∈ ⟪m⟫++⟪n⟫ ∧ ∀t, x ∉ ⟪t⦃σ⦄⟫
           | None   => True
         end.
  Proof.
    induction D as 
      [ u v H1 H2 IH 
      | c m n
      | c m n
      | c x
      | m n x
      | x m
      | c d
      | m n m' n' D1 ID1 H1
      | m n m' n' D1 ID1 s H1 D2 ID2
      ] using 𝔻unif_rect.
    + now rewrite (unif_pirr _ H1).
    + now rewrite unif_fix_1.
    + now rewrite unif_fix_2.
    + rewrite unif_fix_3; right.
      exists x; split.
      * simpl; auto.
      * intros t; induction t as [ y | d | m Hm n Hn ]; simpl.
        - simpl; destruct (eqV_dec y x); intros []; subst; tauto.
        - intros [].
        - rewrite in_app_iff; tauto.
    + destruct (occ_check_dec x (m⋄n)) as [ H | H ].
      * now rewrite unif_fix_4.
      * rewrite unif_fix_4'; auto; right.
        exists x; split.
        - simpl; rewrite !in_app_iff; simpl; auto.
        - intros t Ht.
          apply H, trm_vars_occ_check.
          split; try discriminate.
          revert Ht; apply trm_vars_subst_In.
    + destruct (occ_check_dec x m) as [ H | H ].
      * now rewrite unif_fix_5.
      * rewrite unif_fix_5'; auto.
        rewrite trm_vars_nocc_check in H.
        destruct H as [ H | H ].
        - left; subst.
          intros y; simpl; destruct (eqV_dec y x); subst; auto.
        - right; exists x; split.
          ++ simpl; auto.
          ++ intros t Ht; apply H; revert Ht; apply trm_vars_subst_In.
    + destruct (eqC_dec c d) as [ [] | H ].
      * rewrite unif_fix_6; left; apply subst_eq_refl.
      * now rewrite unif_fix_6'.
    + now rewrite unif_fix_7.
    + rewrite H1 in ID1.
      case_eq (unif D2).
      * intros r Hr.
        rewrite Hr in ID2.
        rewrite unif_fix_8' with (1 := Hr).
        destruct ID1 as [ ID1 | ID1 ];
        destruct ID2 as [ ID2 | ID2 ].
        - left; intros x. 
          rewrite subst_comp_spec, 
                  subst_eq_trm with (1 := ID1),
                  subst_eq_trm with (1 := ID2); auto.
        - destruct ID2 as (x & G1 & G2).
          right; exists x; split.
          ++ do 2 rewrite subst_eq_trm with (1 := ID1), subst_nil in G1; finish by G1.
          ++ intro; rewrite subst_comp_spec, subst_eq_trm with (1 := ID1), subst_nil; apply G2.
        - destruct ID1 as (x & G1 & G2).
          right; exists x; split.
          ++ finish by G1.
          ++ intro; rewrite subst_comp_spec, subst_eq_trm with (1 := ID2), subst_nil; apply G2.
        - destruct ID2 as (x & G1 & G2).
          right; exists x; split.
          ++ generalize (mgu_trm_vars_incl D1); rewrite H1.
             intros G3; destruct ∈ at G1; apply G3 in G1; finish by G1.
          ++ intro; rewrite subst_comp_spec; apply G2. 
      * intros E; rewrite E in ID2.
        now rewrite unif_fix_8.
  Qed.

End unif_partial_correctness_3.