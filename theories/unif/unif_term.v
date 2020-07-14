(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Bool Lia List Extraction Utf8. (* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ ≠ *)

Require Import induction.

Require Import unif_graph_def unif_fun unif_fix unif_partial_corr.

Infix "⊊" := sincl (at level 70, no associativity).

(** We can now show that unif m n is total, using a tailored
    induction principle *)

Section induction_principle_for_termination.

  (** We build the induction principle specialized for the
      termination proof of unif with the following well-founded
      relation (m',n') << (m,n) if [1] /\ ([2a] \/ [2b ]) where

        [1]  ⟪m'⟫++⟪n'⟫ ⊆ ⟪m⟫++⟪n⟫
        [2a] either ⟦m'⟧ < ⟦m⟧ 
        [2b] inclusion [1] is strict *)

  Variable (P : Λ → Λ → Prop)
           (HP : ∀ m n, 
                   (∀ m' n', ⟪m'⟫++⟪n'⟫ ⊆ ⟪m⟫++⟪n⟫ 
                           → (⟦m'⟧ < ⟦m⟧ ∨ ∃x, x ∉ ⟪m'⟫++⟪n'⟫ ∧ x ∈ ⟪m⟫++⟪n⟫)
                           → P m' n') 
                → P m n).

  Let unif_total_rec c : P (fst c) (snd c).
  Proof.
    induction c as [ (?,?) IH ] 
        using (well_founded_induction 
                 (wf_lex_sincl_measure (fun c => ⟪fst c⟫++⟪snd c⟫)
                                       (fun c => ⟦fst c⟧))); simpl.
    apply HP; intros ? ? H1 H2. 
    apply (IH (_,_)); red; simpl.
    unfold sincl; tauto.
  Qed.

  Theorem unif_total_ind m n : P m n.
  Proof. apply (unif_total_rec (_,_)). Qed.

End induction_principle_for_termination.

(* We use the unif_total_ind induction principle.
   Starting from unif (m⋄m') (n⋄n'), the first recursive sub-call 
   is unif m n of which the termination is captured with [1+2a]
   and then, 
     a) either m/n do not unify and there is no more recursive sub-call;
     b) or the produced substitution σ for m/n is the identity and we can justify 
        termination of the sub-call on m'/n' by [1+2a] again; 
     c) or at least one variable of m or n is erased by σ and 
        we justify termination for m'⦃σ⦄/n'⦃σ⦄ with [1+2b]. *) 

Theorem unif_total m n : 𝔻unif m n.
Proof.
  revert m n; apply unif_total_ind; intros u v IH.
  destruct u as [ x1 | c1 | m m' ].
  + apply 𝔻unif_5.
  + destruct v as [ | | ].
    * apply 𝔻unif_3.
    * apply 𝔻unif_6.
    * apply 𝔻unif_1.
  + destruct v as [ x2 | c2 | n n' ].
    * apply 𝔻unif_4.
    * apply 𝔻unif_2.
    * (* The case where recursive sub-calls occur *)
      assert (𝔻unif m n) as D1.
      { apply IH; simpl; [ | lia ].
        intros ? H; finish by H. }
      case_eq (unif D1).
      2: intros E; apply 𝔻unif_7 with D1; auto. (* unif m n = None *)
      intros σ Hσ.                              (* unif m n = Some σ *)
      apply 𝔻unif_8 with (1 := Hσ).
      generalize (mgu_trm_vars_dec D1); rewrite Hσ.
      intros [ H2 | (x & H2 & H3) ].
      - rewrite !(subst_eq_trm H2), !subst_nil.
        apply IH; simpl; [ | lia ].
        intros ? H; finish by H.
      - generalize (mgu_trm_vars_incl D1); rewrite Hσ; intros H4.
        apply IH; simpl.
        ++ intros t Ht; destruct ∈ at Ht; apply H4 in Ht; finish by Ht.
        ++ right; exists x; split.
           ** intros H; destruct ∈ at H; revert H; apply H3.
           ** finish by H2.
Qed.

(** We finish with the definition of a total unify function 
    return either an mgu or a proof of non-unifiability *)

Definition unify u v : { r | match r with Some s => mgu u v s | None => u ≬ v end }.
Proof. exists (unif (unif_total u v)); apply unif_partial_correct. Defined.

(** unify is axiom-free *)

Check unify.
Print Assumptions unify.

(** And extracts properly, removing termination certificates *)

Extraction Inline eqV_dec eqC_dec occ_check_dec unif.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Recursive Extraction unify.

