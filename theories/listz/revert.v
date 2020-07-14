(**************************************************************)
(*   Copyright                                                *)
(*             Jean-François Monin           [+]              *)
(*                                                            *)
(*            [+] Affiliation VERIMAG - Univ. Grenoble-Alpes  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* List traversal from right to left *)  
Require Import List Utf8 Extraction.
Import ListNotations.

Require Import compo.
Require Import lr.
Require Import lr_rec.

(* ========================================================================== *)
(* Special case: reverting a list *)

(* -------------------------------------------------------------------------- *)
(* Graph *)
(* 
We use a symmetric definition of revert.
The natural definition, 𝔾_rev corresponds to a left to right traversal.
The definition corresponding to fold_left is its mirror, 𝔾_zrev.
They are equivalent and equivalent to a version whci non-deterministically
goes towards the left or towards the right (𝔾_rev_nd).
 *)

(*
Remarks : 
- NO append
- :: and +: are used in a fully symmetrical way
*)

Section sec_context.

Context {A : Type}.
Implicit Type l u v : list A.
Implicit Type r : lr A.
Implicit Type x y z : A.


Inductive 𝔾_rev : list A → list A → Prop :=
| Rnil : 𝔾_rev [] []
| Rcons : ∀ {x v u}, 𝔾_rev v u → 𝔾_rev (x :: v) (u +: x)
.

Definition 𝔾_zrev : list A → list A → Prop :=
  fun u v => 𝔾_rev v u.

(* Non-deterministic version *)  
Inductive 𝔾_rev_nd : list A → list A → Prop :=
| Rnd_nil : 𝔾_rev_nd [] []
| Rnd_cons : ∀ x v u, 𝔾_rev_nd v u → 𝔾_rev_nd (x :: v) (u +: x)
| Rnd_consr : ∀ z v u, 𝔾_rev_nd v u → 𝔾_rev_nd (v +: z) (z :: u)
.

(* The latter is of course symmetrical *)
Lemma 𝔾_rev_nd_sym :
  ∀ v u, 𝔾_rev_nd v u → 𝔾_rev_nd u v.
Proof.
  intros v u ir. induction ir as [| x v u ir Hir | z v u ir Hir].
  - apply Rnd_nil.
  - apply Rnd_consr, Hir.
  - apply Rnd_cons, Hir.
Qed.

(* Easy direction *)
Lemma 𝔾_rev_special_case :
  ∀ v u, 𝔾_rev v u → 𝔾_rev_nd v u.
Proof.
  intros v u ir. induction ir as [| x v u ir Hir].
  - apply Rnd_nil.
  - apply Rnd_cons, Hir.
Qed.

(* Unidirectionnal version compatible with +: *)
Lemma 𝔾_rev_consr :
  ∀ v u, 𝔾_rev v u → ∀ z, 𝔾_rev (v +: z) (z :: u).
Proof.
  intros v u ir z. induction ir as [| x v u ir Hir]; simpl.
  - apply (Rcons Rnil). (* [z] = [] +: z *)
  - apply (Rcons Hir). (* z :: (u +: x)  =  (z :: u) +: x *)
Qed.

(* Symmetry (consequence of compatibility with +: *)
Lemma 𝔾_rev_sym : ∀ v u, 𝔾_rev v u → 𝔾_rev u v.
Proof.
  intros v u ir. induction ir as [| x v u ir Hir].
  - apply Rnil.
  - apply 𝔾_rev_consr, Hir.
Qed.

(* Then 𝔾_rev suffices *)
Lemma 𝔾_rev_general_case :
  ∀ v u, 𝔾_rev_nd v u → 𝔾_rev v u.
Proof.
  intros v u ir. induction ir as [| x v u ir Hir | z v u ir Hir].
  - apply Rnil.
  - apply Rcons, Hir.
  - apply 𝔾_rev_sym, Rcons, 𝔾_rev_sym, Hir.
Qed.

Notation "v '⟼rv' u" := (𝔾_rev v u) (at level 70, format "v  ⟼rv  u").

(* -------------------------------------------------------------------------- *)
(* Program 1 *)

(* Standard inefficient revert *)
Fixpoint rev_slow_std l : list A :=
  match l with
  | [] => [] 
  | x :: v => rev_slow_std v  +: x
  end.

Theorem rev_slow_std_corr l : l ⟼rv (rev_slow_std l).
Proof.
  induction l as [| x l Hl]; simpl.
  - apply Rnil.
  - apply Rcons, Hl.
Qed.

(* The same, conform by construction *)
Fixpoint rev_slow_std_pwc l : {u | l ⟼rv u} :=
  match l with
  | [] => exist _ [] Rnil
  | x :: v => let (u, G) := rev_slow_std_pwc v in
              exist _ (u +: x) (Rcons G)
  end.

(* -------------------------------------------------------------------------- *)
(* Program 2 *)

(* Inefficient revert in the opposite direction, conform by construction,
    using the Braga method *)

(* The explicit dependent pattern matching

   match l2r u as x return ** 𝔻lz (r2l x) ... → _ ** with

   ** ... ** added below, is not needed any more for Coq 8.11+ *) 

(*  ⟼rv is used in the opposite direction *)
Let
Fixpoint zrev_slow_pwc u (D : 𝔻lz u) : {v | v ⟼rv u}.
  gen_help u (λ l v, v ⟼rv l); apply up_llP in D; revert D.
  refine (match l2r u as x return 𝔻lz (r2l x) 
                                → (∀ y : list A, y ⟼rv r2l x → y ⟼rv u) 
                                → _ with
          | Nilr       => λ D T,  exist _ [] _
          | Consr u' x => λ D T,
                 let (v, G) := zrev_slow_pwc u' (π_𝔻lz D) in
                 exist _ (x :: v) _
          end); simpl in D,T.
  - apply T; constructor.
  - apply T; constructor; exact G.
Defined.

Definition zrev_slow u : 𝔻lz u → list A :=
  fun D => let (v, _) := zrev_slow_pwc u D in v.

Lemma zrev_slow_conform u (D: 𝔻lz u) :
  u ⟼rv zrev_slow u D.
Proof.
  apply 𝔾_rev_sym.
  unfold zrev_slow; destruct (zrev_slow_pwc u) as [v G].
    exact G.
Qed.

(* -------------------------------------------------------------------------- *)
(* Program 3 *)

(* Efficient revert, standard version *)
Fixpoint rev_fast l u : list A :=
  match l with
  | [] => u
  | x :: l' => rev_fast l' (x :: u)
  end.

Lemma rev_fast_consr l z : rev_fast (l +: z) = cons z << rev_fast l.
Proof.
  induction l as [ | x u Hu].
  - reflexivity.
  - change (rev_fast ((x :: u) +: z)) with (rev_fast (u+:z) << cons x).
    rewrite Hu. reflexivity.
Qed.

Lemma rev_fast_conform u : rev_fast u [] ⟼rv u.
Proof.
  induction (𝔻lz_all u) as [ | u Gu z].
  - simpl. constructor 1.
  - rewrite rev_fast_consr. constructor 2. exact Gu.
Qed.

Lemma rev_fast_compl u v : v ⟼rv u  ->  v = rev_fast u [].
Proof.
  induction 1 as [ | x v u G HG].
  - reflexivity.
  - rewrite rev_fast_consr, HG. reflexivity.
Qed.

(* rev_fast computes the same result as the reference version zrev_slow *)
(* Partial correctness *)
Theorem rev_fast_correct_partial :
  ∀u (D : 𝔻lz u), rev_fast u [] = zrev_slow u D.
Proof.
  intros; symmetry.
  apply rev_fast_compl, 𝔾_rev_sym, zrev_slow_conform.
Qed.

(* Total correctness *)
Theorem rev_fast_correct_total : ∀u, rev_fast u [] = zrev_slow u (𝔻lz_all u).
Proof. intro u; apply rev_fast_correct_partial. Qed.

End sec_context.
(* -------------------------------------------------------------------------- *)

(* Extraction Inline rev_slow_std_pwc. *)

Extract Inductive list => "list" [ "[]" "(::)" ].
Recursive Extraction
           rev_slow_std 
           rev_slow_std_pwc
           zrev_slow 
           rev_fast.
