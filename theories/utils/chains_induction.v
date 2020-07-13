(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia.

Set Implicit Arguments.

Section wf_chains.

  Variables (X : Type) (R : X -> X -> Prop).
  
  Inductive chain : nat -> X -> X -> Prop :=
    | in_chain_0 : forall x, chain 0 x x
    | in_chain_1 : forall n x y z, R x y -> chain n y z -> chain (S n) x z.
    
  Fact chain_plus a b x y z : chain a x y -> chain b y z -> chain (a+b) x z.
  Proof.
    induction 1 as [ | ? ? y ]; simpl; auto.
    constructor 2 with y; auto.
  Qed.

  Fact chain_rev n x y z : chain n x y -> R y z -> chain (S n) x z.
  Proof.
    intros H1 H2.
    replace (S n) with (n+1) by lia.
    apply chain_plus with y; auto.
    constructor 2 with z; auto.
    constructor 1.
  Qed.

  (* If chains to x have bounded length then x is R-accessible *)
  
  Lemma Acc_chains k x : (forall n y, chain n y x -> n <= k) -> Acc R x.
  Proof.
    revert x; induction k as [ | k IHk ]; intros x Hx.
    + constructor 1; intros y Hy.
      generalize (Hx _ _ (in_chain_1 Hy (in_chain_0 x))); lia.
    + constructor 1; intros y Hy.
      apply IHk; intros n z Hn.
      apply le_S_n, (Hx _ z), chain_rev with y; auto.
  Qed.

  (* If every x has bounded chains to itself then R is WF *)
  
  Hypothesis (HR : forall x, exists k, forall n y, chain n y x -> n <= k). 

  Theorem wf_chains : well_founded R.
  Proof.
    intros x.
    destruct (HR x) as (k & Hk).
    revert Hk; apply Acc_chains.
  Qed.
  
End wf_chains.
