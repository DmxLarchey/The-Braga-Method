(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import NArith Lia Wellfounded Extraction.

Set Implicit Arguments.

Section factb.

  (** Factorial over binary natural numbers by well founded 
      induction over a measure, easy with well_founded_induction_type *)

  Open Scope N.

  Reserved Notation "x '⟼' y" (at level 70, no associativity).

  Inductive 𝔾factb : N -> N -> Prop :=
    | in_g_fact_0 : 0 ⟼ 1
    | in_g_fact_1 n f : 0 < n -> n-1 ⟼ f -> n ⟼ n*f
  where "x ⟼ y" := (𝔾factb x y).

  Hint Constructors 𝔾factb : core.

  Fact 𝔾factb_fun n f1 f2 : n ⟼ f1 -> n ⟼ f2 -> f1 = f2.
  Proof.
     intros H; revert H f2.
     induction 1; inversion 1; auto; try lia.
     f_equal; auto.
  Qed.

  Section factb_pwc.

    Let factb_pwc n : { f | n ⟼ f }.
    Proof. 
      induction n as [ n fact ] using (well_founded_induction_type N.lt_wf_0).
      refine (match N.eqb n 0 as b return N.eqb n 0 = b -> _ with
        | true  => fun Hn => exist _ 1 _ 
        | false => fun Hn => let (f,Gf) := fact (n-1) _ in exist _ (n*f) _
      end eq_refl).
      + apply N.eqb_eq in Hn as ->; constructor.
      + apply N.eqb_neq in Hn; lia.
      + apply N.eqb_neq in Hn; constructor; auto; lia.
    Qed.

    Definition factb n := proj1_sig (factb_pwc n).
    Fact factb_spec n : n ⟼ factb n.
    Proof. apply (proj2_sig _). Qed.

  End factb_pwc.

  Hint Resolve factb_spec : core.

  Fact factb_0 : factb 0 = 1.
  Proof. apply 𝔾factb_fun with 0; auto. Qed.

  Fact factb_1 n : 0 < n -> factb n = n*factb (n-1).
  Proof. intros; apply 𝔾factb_fun with n; auto. Qed.

End factb.

Extract Inductive bool => "bool" [ "true" "false" ].

(** There is a parasitic let in that I cannot remove here ... 
    It is coming from the inlining of well_founded_induction_type *)
Extraction factb.

  