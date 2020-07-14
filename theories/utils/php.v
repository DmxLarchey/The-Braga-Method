(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia List Permutation.

Set Implicit Arguments.

Section php.

  (* A short proof of the finite PHP *)

  Variable (X : Type).

  Implicit Type (l : list X).

  Inductive list_has_dup : list X -> Prop :=
    | in_list_hd0 : forall l x, In x l -> list_has_dup (x::l)
    | in_list_hd1 : forall l x, list_has_dup l -> list_has_dup (x::l).
  
  Fact list_has_dup_cons_inv x l : list_has_dup (x::l) -> In x l \/ list_has_dup l.
  Proof. inversion 1; subst; auto. Qed.
  
  Fact list_has_dup_app_left l m : list_has_dup m -> list_has_dup (l++m).
  Proof. induction l; simpl; auto; constructor 2; auto. Qed.
  
  Fact list_has_dup_app_right l m : list_has_dup l -> list_has_dup (l++m).
  Proof. 
    induction 1; simpl.
    constructor 1; apply in_or_app; left; auto.
    constructor 2; auto.
  Qed.

  Fact incl_cons_inv_l x l m : incl (x::l) m <-> In x m /\ incl l m.
  Proof.
    split.
    + intros H; split; [ | intros ? ? ]; apply H; simpl; auto.
    + intros (? & ?) z [ -> | ? ]; auto.
  Qed.

  Definition has_dup l := exists x a b c, l = a++x::b++x::c.

  Fact has_dup_cons x l : has_dup (x::l) <-> In x l \/ has_dup l.
  Proof.
    split.
    * intros (y & [ | z a ] & b & c & H).
      + inversion H; rewrite in_app_iff; simpl; auto.
      + inversion H; right; exists y, a, b, c; auto.
    * intros [ H | (y & a & b & c & ->) ].
      + apply in_split in H; destruct H as (a & b & ->).
        exists x, nil, a, b; auto.
      + exists y, (x::a), b, c; auto. 
  Qed.

  Fact list_has_dup_equiv l : list_has_dup l <-> has_dup l.
  Proof.
    split.
    + induction 1 as [ l x Hx | l x Hl (y & aa & bb & cc & IHl) ].
      * apply in_split in Hx as (bb & cc & ->).
        exists x, nil, bb, cc; auto.
      * exists y, (x::aa), bb, cc; subst; auto.
    + intros (x & aa & bb & cc & ->).
      apply list_has_dup_app_left.
      constructor 1.
      apply in_or_app; simpl; auto.
  Qed.

  Fact has_dup_perm l m : Permutation l m -> has_dup l -> has_dup m.
  Proof.
    induction 1; auto.
    + rewrite !has_dup_cons.
      intros [ H1 | ]; auto; left; revert H1.
      apply Permutation_in; auto.
    + rewrite !has_dup_cons; simpl.
      intros [ [] | ? ]; auto; tauto.
  Qed.

  Fact has_dup_insert l x r : has_dup (l++r) -> has_dup (l++x::r).
  Proof.
    intros H; apply has_dup_perm with (l := x::l++r).
    + apply Permutation_cons_app; auto.
    + apply has_dup_cons; auto.
  Qed.

  Fact incl_cons_inv_r l x m : incl l (x::m) -> incl l m \/ In x l.
  Proof.
    induction l as [ | y l IHl ].
    + left; intros ? [].
    + rewrite incl_cons_inv_l.
      intros ([ -> | H1] & H2).
      * right; simpl; auto.
      * destruct (IHl H2).
        - rewrite incl_cons_inv_l; tauto.
        - right; simpl; auto.
  Qed.

  Fact incl_cons_inv_dup l x m : 
         incl l (x::m) 
      -> incl l m 
      \/ (exists a b, l = a++x::b /\ incl (a++b) m) 
      \/ has_dup l.
  Proof.
    intros H.
    destruct incl_cons_inv_r with (1 := H) as [ H1 | H1 ]; auto.
    apply in_split in H1; destruct H1 as (a & b & ->).
    destruct (@incl_cons_inv_r a x m) as [ H2 | H2 ].
    + intros ? ?; apply H, in_app_iff; auto.
    + destruct (@incl_cons_inv_r b x m) as [ H3 | H3 ].
      * intros ? ?; apply H, in_app_iff; simpl; auto.
      * right; left; exists a, b; split; auto.
        intros ?; rewrite in_app_iff; intros []; auto.
      * apply in_split in H3; destruct H3 as (c & d & ->).
        do 2 right; exists x, a, c, d; auto.
    + apply in_split in H2; destruct H2 as (c & d & ->).
      do 2 right; exists x, c, d, b; rewrite app_ass; auto.
  Qed.

  Theorem php l m : incl l m -> length m < length l -> has_dup l.
  Proof.
    revert l; induction m as [ | y m IHm ]; simpl; try lia; intros l;
      try (simpl; lia).
    + destruct l as [ | x l ]; simpl; try lia. 
      intros H; destruct (H x); simpl; auto.
    + intros H1 H2.
      apply incl_cons_inv_dup in H1.
      destruct H1 as [ H1 | [ (a & b & -> & H3) | H1 ] ]; auto.
      * apply IHm; auto; lia.
      * rewrite app_length in H2; simpl in H2.
        apply has_dup_insert, IHm; auto.
        rewrite app_length; lia.
  Qed.

  Corollary finite_pigeon_hole l m : length l < length m -> incl m l -> list_has_dup m.
  Proof. intros; apply list_has_dup_equiv, php with l; auto. Qed.

End php.
