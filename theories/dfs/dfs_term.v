(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Extraction Utf8. (* → λ ∀ ∃ ↔ ∧ ∨ *)

Require Import induction.

Require Import dfs_graph_def dfs_fun dfs_fix dfs_partial_corr.

Set Implicit Arguments.

Section dfs_domain_characterization.

  (* Hence dfs v l cannot terminate unless such a finite invariant exists
     (because that is what it computes ...) 
     Let us show that this condition is also sufficient *)

  Theorem 𝔻dfs_domain v l : 𝔻dfs v l ↔ ∃i, dfs_invariant_t v l i.
  Proof.
    split.
    + (* The direct implication is trivially derived from partial correctness *)

      intros D; exists (dfs D); apply dfs_invariant.
    + (* The reverse implication is more complicated, much more ...
         We proceed by lexicographic product 
           a) strict reverse inclusion bounded by i for v
           b) structural induction for l *)

      unfold dfs_invariant_t, incl.
      intros (i & H1 & H2 & H3).
      revert v H1 l H2 H3.
    
      (** Induction on v using upper-bounded strict reverse inclusion as well-founded relation *)
    
      induction v as [ v IHv ] using (well_founded_induction (wf_sincl_maj i)); intros Hv.
    
      (** Structural induction on l *)
    
      induction l as [ | x l IHl ]; intros Hl H.
      1: apply 𝔻dfs_1.
      case_eq (mem x v); 
        [ rewrite mem_true_iff 
        | rewrite mem_false_iff ]; intros Hx.
      * (* dfs v (x::_) where x ∈ v *) 
        clear IHv.
        apply 𝔻dfs_2; auto.
        apply IHl; auto.                (* Induction on l *)
        intros; apply Hl; right; auto.
      * (* dfs v (x::_) where x ∉ v *) 
        clear IHl.
        apply 𝔻dfs_3; auto.
        assert (Hx' : In x i) 
          by (apply Hl; left; auto).
        apply IHv.                     (* Induction on v *)
        - split;
          [ right; auto
          | exists x; repeat split; auto; left; auto ].
        - intros y [ ? | ? ]; subst; auto.
        - intros y Hy.
          apply in_app_or in Hy.
          destruct Hy as [ Hy | Hy ].
          ++ apply H in Hx'.
             destruct Hx' as [ Hx' | Hx' ].
             ** tauto.
             ** apply Hx'; auto.
          ++ apply Hl; right; auto.
        - intros y Hy; apply H in Hy; simpl; tauto.
  Qed.

  (* Using the domain characterized by invariants, 
     monotonicity properties are easy to establish ... 
     it is much harder with d_dfs based induction. *)

  Fact 𝔻dfs_mono v v' l l' : v ⊆ v' → l' ⊆ v'++l → 𝔻dfs v l → 𝔻dfs v' l'.
  Proof.
    intros H1 H2.
    do 2 rewrite 𝔻dfs_domain.
    intros (lP & H3 & H4 & H5).
    exists (v'++lP); repeat split; auto.
    + intros ? ?; apply in_or_app; left; auto.
    + intros x Hx; apply in_or_app.
      apply H2, in_app_or in Hx.
      destruct Hx; auto.
    + intros x Hx.
      apply in_app_or in Hx.
      destruct Hx as [ Hx | Hx ]; auto.
      apply H5 in Hx.
      destruct Hx as [ Hx | Hx ].
      * left; apply H1; auto.
      * right; intros ? ?; apply in_or_app; right; auto.
  Qed.
  
  (* dfs is usually called as dfs nil l. 
     In that case, the invariant is simpler 

     It is list containing l and closed under succs
   *)

  (* → λ ∀ ∃ ↔ ∧ ∨ *)

  Definition dfs_nil_invariant_t l i := l ⊆ i ∧ ∀x, x ∈ i → succs x ⊆ i.

  (* Partial correctness of dfs nil: it computes the minimal invariant *)

  Corollary dfs_nil_invariant l D : dfs_nil_invariant_t l (@dfs nil l D)
                              ∧ ∀i, dfs_nil_invariant_t l i → dfs D ⊆ i.
  Proof.
    generalize (dfs_invariant D); intros ((_ & H2 & H3) & H4).
    repeat split; auto.
    + intros x Hx.
      destruct (H3 _ Hx) as [ [] | ]; auto.
    + intros i (G1 & G2); apply H4.
      repeat split; auto.
      intros _ []. 
  Qed.

  (* "Total" correctedness: dfs terminates provided an invariant exists *)

  Corollary 𝔻dfs_nil_domain l : 𝔻dfs nil l ↔ ex (dfs_nil_invariant_t l). 
  Proof.
    split.
    + intros D; exists (dfs D); apply dfs_nil_invariant.
    + rewrite 𝔻dfs_domain.
      intros (inv & H1 & H2).
      exists inv; split; auto.
      intros _ [].
  Qed.

End dfs_domain_characterization.

Section finite_domain.

  (* In particular, if 𝓔 is finite then dfs terminate *)
 
  Hypothesis (H𝓔 : ∃l𝓔, ∀x:𝓔, x ∈ l𝓔).

  Fact 𝔻dfs_total v l : 𝔻dfs v l.
  Proof. 
    apply 𝔻dfs_domain.
    destruct H𝓔 as (l𝓔 & ?).
    unfold dfs_invariant_t, incl.
    exists l𝓔; auto.
  Qed.

End finite_domain.

Section non_termination.

  (* We assume as an example that 𝓔 is isomorphic to nat
     and succs x = [S x] *)

  Hypothesis (f : nat -> 𝓔) (g : 𝓔 -> nat) 
             (Hfg : forall x, f (g x) = x)
             (Hgf : forall n, g (f n) = n)
             (Hsuccs : forall x, succs x = f (S (g x)) :: nil).

  Fact max_list l : { m | m ∈ l ∧ ∀k, k ∈ l → k <= m } + { l = nil }.
  Proof.
    induction l as [ | n l IHl ].
    + right; auto.
    + left; destruct IHl as [ (m & H1 & H2) | H ].
      * destruct (le_lt_dec m n) as [ H | H ].
        - exists n; simpl; split; auto.
          intros k [ <- | H3 ]; auto.
          apply H2 in H3; lia.
        - exists m; simpl; split; auto.
          intros k [ <- | H3 ]; auto; lia.
      * exists n; subst; split; simpl; auto.
        intros ? [ <- | [] ]; auto.
  Qed. 

  Fact unbounded_list_absurd l : (∀n, n ∈ l → S n ∈ l) → l = nil.
  Proof.
    intros H.
    destruct (max_list l) as [ (m & H1 & H2) | -> ]; auto.
    apply H, H2 in H1; lia.
  Qed.

  Fact dfs_non_termination l : 𝔻dfs nil l ↔ l = nil. 
  Proof.
    split.
    * rewrite 𝔻dfs_nil_domain.
      intros (i & H1 & H2).
      assert (map g l ⊆ map g i) as H3.
      { intro n; rewrite !in_map_iff.
        intros (x & <- & ?); exists x; auto. } 
      rewrite (unbounded_list_absurd (map g i)) in H3.
      + destruct l as [ | x ]; auto; exfalso; apply (H3 (g x)); simpl; auto.
      + intros n; rewrite !in_map_iff.
        intros (x & <- & Hx). 
        exists (f (S (g x))).
        rewrite Hgf; split; auto.
        apply (H2 x); auto.
        rewrite Hsuccs; left; auto. 
    * intros ->; apply 𝔻dfs_nil_domain.
      exists nil; repeat split; unfold incl; firstorder.
  Qed.

End non_termination.

Check 𝔻dfs.
Print Assumptions 𝔻dfs.

Check dfs.
Print Assumptions dfs.

Check 𝔻dfs_total.
Print Assumptions 𝔻dfs_total.

Check dfs_non_termination.
Print Assumptions dfs_non_termination.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
(* Extract Inlined Constant app => "(@)". *)

Recursive Extraction dfs.



