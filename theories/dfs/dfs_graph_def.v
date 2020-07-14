(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Utf8.

Set Implicit Arguments.

(* This is Depth First Search as in Krauss (2009)

   http://www21.in.tum.de/%7Ekrauss/function/function.pdf

   let rec dfs v l =
     match l with
       | []   -> v
       | x::l -> if x ∈ v then dfs v l else dfs (x::v) (succs x @ l)
     
  where succs : 𝓔 -> 𝓔 list
  and       ∈ : 𝓔 -> 𝓔 list -> bool

  Termination over a infinite domain is ensured by the
  existence of a finite invariant, ie closed under
  succs (see below).
  
  Defining dfs by well-founded induction is going to be
  particularily difficult ...
  
  It works like a charm via Bar inductive predicates to get 
  a simulated Inductive/Recursive definition of a partial 
  function: forall v l, d_dfs v l -> list 𝓔.
  
  Termination (represented by d_dfs v l) is delayed afterwards 
  where it is much easier to establish.

  Inductive d_dfs : list 𝓔 -> list 𝓔 -> Prop :=
    | d_dfs_0 : forall v,                                              d_dfs v nil
    | d_dfs_1 : forall v x l,   In x v -> d_dfs     v            l  -> d_dfs v (x::l)
    | d_dfs_2 : forall v x l, ~ In x v -> d_dfs (x::v) (succs x++l) -> d_dfs v (x::l)
  with Fixpoint dfs v l (D : d_dfs v l) : list X := match D with
    | d_dfs_0 v         => v
    | d_dfs_1 v x l _ D => dfs D
    | d_dfs_2 v x l _ D => dfs D
  end.

*)

Tactic Notation "bool" "discr" := 
  try match goal with 
      | H: ?a = true , G: ?b = false |- _ => exfalso; now rewrite H in G 
      end.

Fact true_false x : x = true -> x = false -> False.
Proof. intros; bool discr. Qed.

Infix "∈" := In (at level 70, no associativity).
Notation "x ∉ l" := (~ In x l) (at level 70, no associativity).
Infix "⊆" := incl (at level 70, no associativity).

Parameters  (𝓔 : Type)
            (mem : 𝓔 -> list 𝓔 -> bool)
            (succs : 𝓔 -> list 𝓔).

Infix "∈?" := mem (at level 70, no associativity).

Parameter mem_true_iff : forall x l, x ∈? l = true <-> x ∈ l.

Corollary mem_false_iff x l : x ∈? l = false <-> x ∉ l.
Proof.
  rewrite <- mem_true_iff.
  now destruct (x ∈? l).
Qed.

Hint Resolve mem_true_iff mem_false_iff : core.

Corollary mem_iff x l :   (x ∈? l = true  <-> x ∈ l)
                       /\ (x ∈? l = false <-> x ∉ l).
Proof. split; auto. Qed.

Lemma not_mem_true x l (N : x ∉ l) (E : x ∈? l = true) : False.
Proof. apply N, mem_iff, E. Qed.

Lemma not_mem_false x l (N : x ∈ l) (E : x ∈? l = false) : False.
Proof. revert N; apply mem_iff, E. Qed.
  
(* We define the graph g_dfs of dfs corresponding to the 
   above recursive scheme which has 3 branches 

   Hence the functional specification of dfs is 

         g_dfs v l (dfs v l)

*)

(* → λ ∀ *)

Reserved Notation "v '⊔' l '⟼d' o" (at level 70, format "v  ⊔  l  ⟼d o").

Inductive 𝔾dfs : list 𝓔 -> list 𝓔 -> list 𝓔 -> Prop := 
  | in_gdfs_0 : ∀ v, v ⊔ nil ⟼d v
  | in_gdfs_1 : ∀ v x l o, x ∈ v → v ⊔ l ⟼d o → v ⊔ x::l ⟼d o
  | in_gdfs_2 : ∀ v x l o, x ∉ v → x::v ⊔ succs x++l ⟼d o → v ⊔ x::l ⟼d o
where "v ⊔ l ⟼d o" := (𝔾dfs v l o).

(* We show that the graph is functional/deterministic *)

Fact 𝔾dfs_fun v l o1 o2 : v ⊔ l ⟼d o1 → v ⊔ l ⟼d o2 → o1 = o2.
Proof.
  intros H; revert H o2.
  induction 1 as [ v | v x l o1 H1 H2 IH2 | v x l o1 H1 H2 IH2 ].
  + inversion 1; auto.
  + inversion 1; subst.
    * apply IH2; auto.
    * tauto.
  + inversion 1; subst.
    * tauto.
    * apply IH2; auto.
Qed.

