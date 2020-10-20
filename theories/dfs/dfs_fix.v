(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Utf8. (* → λ ∀ ∃ ↔ *)

Require Import dfs_graph_def dfs_fun. 

Set Implicit Arguments.

(* dfs is proof irrelevant *)

Fact dfs_pirr v l D1 D2 : @dfs v l D1 = @dfs v l D2.
Proof. apply 𝔾dfs_fun with v l; apply dfs_spec. Qed.

(* Fixpoint equations corresponding to the above I/R definition *)

Fact dfs_fix_1 v : dfs (𝔻dfs_1 v) = v.
Proof. apply 𝔾dfs_fun with v nil; [ | constructor 1 ]; apply dfs_spec. Qed.

Fact dfs_fix_2 v x l H D : dfs (@𝔻dfs_2 v x l H D) = dfs D.
Proof. apply 𝔾dfs_fun with v (x::l); [ | constructor 2; auto ]; apply dfs_spec. Qed.

Fact dfs_fix_3 v x l H D : dfs (@𝔻dfs_3 v x l H D) = dfs D.
Proof. apply 𝔾dfs_fun with v (x::l); [ | constructor 3; auto ]; apply dfs_spec. Qed.

Section dfs_ind.

  (* We can retrieve an non-dependent induction principle for dfs 
     which is very similar to the induction principle of g_dfs *)

  Variables (P : list 𝓥 → list 𝓥 → list 𝓥 → Prop)
            (HP1 : ∀ v, P v nil v)
            (HP2 : ∀ v x l r, x ∈ v → P v l r → P v (x::l) r)
            (HP3 : ∀ v x l r, x ∉ v → P (x::v) (succs x ++ l) r → P v (x::l) r).

  Theorem dfs_ind v l D : P v l (@dfs v l D).
  Proof.
    induction D as [ v l D1 D2 | | | ] using 𝔻dfs_ind.
    + rewrite (dfs_pirr _ D1); auto.
    + rewrite dfs_fix_1; auto.
    + rewrite dfs_fix_2; auto.
    + rewrite dfs_fix_3; auto.
  Qed.

End dfs_ind.
