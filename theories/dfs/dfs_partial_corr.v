(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Utf8. (* → λ ∀ ∃ ↔ ∧ ∨ *)

Require Import php.

Require Import dfs_graph_def dfs_fun dfs_fix.

Set Implicit Arguments.

Section dfs_partial_correctness.

 (****************************************************
       Specification of g_dfs/dfs by IR is finished
   ****************************************************)
  
  (** Let us establish the partial correctness of dfs *)
 
  (* dfs computes a finite invariant *)

  Definition dfs_invariant_t v l i := 
         v ⊆ i
       ∧ l ⊆ i
       ∧ ∀x, x ∈ i → x ∈ v ∨ succs x ⊆ i.

  (* when defined, dfs v l produces an invariant lP as a finite list :
       a) which contains v 
       b) which contains l
       c) and any succs-image of x ∈ lP\v belongs to lP 

     and this invariant is the least for that property *) 

  (* → λ ∀ ∃ ↔ ∧ ∨ *)

  Theorem dfs_invariant v l D : dfs_invariant_t v l (@dfs v l D)
                          ∧ ∀i, dfs_invariant_t v l i → dfs D ⊆ i.
  Proof.
    unfold dfs_invariant_t, incl in *.
    induction D as [ v l D1 D2 
                   | v 
                   | v x l H1 D ID1 
                   | v x l H1 D ID1 ] using 𝔻dfs_rect. (* We could also use dfs_ind *)
    
    (* the property we show is proof irrelevant *)
    
    - rewrite (dfs_pirr _ D1); auto.
    
    (* first constructor for dfs _ nil *)

    - rewrite dfs_fix_1; unfold dfs_invariant_t.
      unfold incl; repeat split; simpl; tauto.
    
    (* second constructor for dfs v (x::_) where x ∈ v *) 

    - rewrite dfs_fix_2; unfold dfs_invariant_t in * |- *.
      destruct ID1 as ((H2 & H3 & H4) & H5).
      repeat split; simpl; try tauto.
      * intros y [ [] | ? ]; auto.
      * intros P (? & ? & ?); apply H5.
        repeat split; auto.
 
    (* third constructor for dfs v (x::_) where x ∉ v *) 

    - rewrite dfs_fix_3; unfold dfs_invariant_t in * |- *.
      destruct ID1 as ((H2 & H3 & H4) & H5).
      repeat split; auto.
      * intros y Hy; apply H2; right; auto.
      * intros y [ ? | ? ]; subst.
        apply H2; simpl; auto.
        apply H3, in_or_app; simpl; auto.
      * intros y Hy.
        apply H4 in Hy.
        destruct Hy as [ [ | ] | ]; auto; subst; right.
        intros ? ?; apply H3, in_or_app; simpl; auto.
      * intros P (G1 & G2 & G3).
        apply H5.
        repeat split; auto.  
        + intros ? [ ? | ? ]; subst; auto; apply G2; simpl; auto.
        + intros y Hy.
          apply in_app_or in Hy; destruct Hy; 
            [ destruct (G3 x); auto | ]; [ | destruct H1; auto | ];
            apply G2; simpl; auto.
        + intros ? Hy; destruct (G3 _ Hy); simpl; auto.
  Qed.

  (* dfs contains no duplicated value, unless there is one in v 
     hence dfs is also minimal w.r.t. cardinality *)

  Fact dfs_no_dups v l D : list_has_dup (@dfs v l D) → list_has_dup v.
  Proof.
    induction D as [ v l D1 D2 
                   | v 
                   | v x l H1 D ID1 
                   | v x l H1 D ID1 ] using 𝔻dfs_ind.

    * rewrite (dfs_pirr _ D1); auto.
    * rewrite dfs_fix_1; auto.
    * rewrite dfs_fix_2; auto.
    * rewrite dfs_fix_3.
      intros H; specialize (ID1 H).
      apply list_has_dup_cons_inv in ID1; tauto.
  Qed.

End dfs_partial_correctness.
