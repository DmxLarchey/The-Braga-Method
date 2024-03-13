(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List Wellfounded.

Require Import php chains_induction.

Set Implicit Arguments.

Local Fact incl_nil X (l : list X) : incl nil l.
Proof. firstorder. Qed.

Local Fact list_has_dup_nil_inv X : ~ list_has_dup (@nil X).
Proof. inversion 1. Qed.

Local Hint Resolve incl_refl incl_cons incl_nil list_has_dup_nil_inv : core.

Section sincl.

  (** Strict inclusion between lists is a well founded relation *)

  Variable (X : Type).

  Implicit Type (l m : list X).
    
  (* sincl l m if incl l m and there is a witness in m \ l *)

  Definition sincl l m := incl l m /\ exists x, ~ In x l /\ In x m.

  (* Any n-chain m ~~> l contains a duplication-free subset of l of size n *)

  Lemma sincl_chain n m l :   
       chain sincl n m l -> incl m l 
                         /\ exists ll, ~ list_has_dup ll 
                                      /\ length ll = n 
                                      /\ incl ll l
                                      /\ forall x, In x m -> In x ll -> False.
  Proof.
    induction 1 as [ m | n m l k H1 H2 (H7 & ll & H3 & H4 & H5 & H6) ].
    + split; auto; exists nil; simpl; repeat split; auto.
    + split.
      * intros ? ?; apply H7, H1; auto.
      * destruct H1 as (G1 & x & G2 & G3).
        exists (x::ll); simpl; repeat split; auto.
        - contradict H3.
          apply list_has_dup_cons_inv in H3 as [ H3 | ]; auto.
          destruct (H6 x); auto.
        - intros y F1 [ <- | F2 ]; try tauto.
          apply (H6 y); auto.
  Qed.

  (* Hence, by the PHP, if there is a n-chain to l then n must be less than length l *)
   
  Theorem wf_sincl : well_founded sincl.
  Proof.
    apply wf_chains.
    intros l; exists (length l).
    intros n m H.
    apply sincl_chain in H.
    destruct H as (_ & ll & H1 & H2 & H3 & _).
    destruct (le_lt_dec n (length l)) as [ | C ]; auto.
    subst; destruct H1.
    apply finite_pigeon_hole with l; auto.
  Qed.

End sincl.

Arguments wf_sincl {X}.

Section sincl_maj.

  (** Strict reverse inclusion between lists is well founded over a finite domain 
      Removed the use of decidable equality from the proof using wf_chains *)

  Variable (X : Type) (M : list X). (* This is the upper-bound/finiteness of the domain *)

  (* l cap M strictly contains in m cap M *)

  Definition sincl_maj l m := (forall x, In x m -> In x M -> In x l) 
                            /\ exists x, ~ In x m /\ In x l /\ In x M.

  (* Any n-chain m ~~> l contains a duplication-free subset of M of size n *)
                            
  Lemma sincl_maj_chains n m l :   chain sincl_maj n m l 
                   -> exists ll, ~ list_has_dup ll 
                                /\ incl ll M 
                                /\ length ll = n 
                                /\ incl ll m.
  Proof.
    induction 1 as [ x | n m k l H1 H2 (ll & H3 & H4 & H5 & H6) ].
    + exists nil; repeat split; auto.
    + destruct H1 as (H1 & a & G1 & G2 & G3).
      exists (a::ll); repeat split; auto.
      * contradict H3.
        apply list_has_dup_cons_inv in H3.
        destruct H3 as [ H3 | ]; auto.
        destruct G1; apply H6; auto.
      * simpl; f_equal; auto.
      * apply incl_cons; auto.
        intros ? ?; auto.
  Qed.

  (* Hence, by the PHP, if there is a n-chain to l then n is less than length M *)

  Theorem wf_sincl_maj : well_founded sincl_maj.
  Proof.
    apply wf_chains.
    intros l; exists (length M).
    intros n m H.
    apply sincl_maj_chains in H.
    destruct H as (ll & H1 & H2 & H3 & _).
    destruct (le_lt_dec n (length M)) as [ | C ]; auto.
    subst n; destruct H1.
    apply finite_pigeon_hole with M; auto.
  Qed.

End sincl_maj.

Arguments wf_sincl_maj {X}.

Section lex_sincl.

  Variable (X Y : Type) (f : X -> list Y) (R : X -> X -> Prop) (HR : well_founded R).

  Definition lex_sincl (x1 x2 : X) := sincl (f x1) (f x2) \/ incl (f x1) (f x2) /\ R x1 x2.

  Let lex_prop l : forall x, incl (f x) l -> Acc lex_sincl x.
  Proof.
    induction l as [ l IHl ] using (well_founded_induction wf_sincl).
    induction x as [ x IHx ] using (well_founded_induction HR).
    intros Hx.
    constructor.
    intros y [ (H1 & z & H2 & H3) | (H1 & H2) ].
    apply IHl with (f y).
    split. 
    intros ? ?; apply Hx, H1; trivial.
    exists z; split; auto.
    apply incl_refl.
    apply IHx; auto.
    revert Hx; apply incl_tran; auto.
  Qed.

  Theorem wf_lex_sincl : well_founded lex_sincl.
  Proof.
    intros x; apply lex_prop with (f x), incl_refl.
  Qed.

End lex_sincl.

Section lex_sincl_measure.

  Variable (X Y : Type) (f : X -> list Y) (m : X -> nat). 

  Definition lex_sincl_measure (x1 x2 : X) := sincl (f x1) (f x2) \/ incl (f x1) (f x2) /\ m x1 < m x2.
  
  Corollary wf_lex_sincl_measure : well_founded lex_sincl_measure.
  Proof.
    apply wf_lex_sincl with (R := fun x y => m x < m y), wf_inverse_image, lt_wf.
  Qed.

End lex_sincl_measure.

    
