(**************************************************************)
(*   Copyright                                                *)
(*             Jean-François Monin           [+]              *)
(*             Dominique Larchey-Wendling    [*]              *)
(*                                                            *)
(*            [+] Affiliation VERIMAG - Univ. Grenoble-Alpes  *)
(*            [*] Affiliation LORIA -- CNRS                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* List traversal from right to left *)
Require Import List Utf8.
Import ListNotations.

Require Import lr.
(* The domain of 𝔾_foldl happens to be exactly 𝔻lz as defined in lr_rec *)
Require Import lr_rec.


(* Here is a reference definition of List.fold_left, which follows the
same structural pattern as List.fold_right, but where lists are
traversed from right to left.

let rec foldl_ref f b l = fakematch l with
  | [] → b
  | u +: z → f (foldl_ref f b u) z

This can be actually programmed by reflecting this
decomposition of lists from the right using l2r.

let rec foldl_ref f b l = match l2r l with
  | Nilr → b
  | Consr (u, z) → f (foldl_ref f b u) z

This definition corresponds to the usual informal drawings explaining
the expected result. It is of course quite inefficient, however and it
can be seen as a specification of fold_left.

let rec foldl f b l = match l with
   | [] → b
   | x :: l → foldl f (f b x) l

This Coq scripts shows that foldl is actually equivalent to
foldl_ref.

The point is to get a Coq definition of foldl_ref, whereas
the recursion is not the usual structural recursion on lists.
Following the method exposed at Braga, we start with an
inductive graph corresponding to foldl_ref.
*)

(* -------------------------------------------------------------------------- *)
(* Relational Graph *)

Section sec_context.

Context {A B: Type}.
Implicit Type l u v : list A.
Implicit Type r : lr A.
Implicit Type x y z : A.
Implicit Type b : B.

Section sec_params_foldl.
Variable f: B → A → B.
Variable b0 : B.


Reserved Notation "l '⟼fl' b" (at level 70, format "l  ⟼fl  b").

Inductive 𝔾_foldl : list A → B → Prop :=
| FLnil : [] ⟼fl b0
| FLcons : ∀ {u z b},    u ⟼fl b   →  u +: z ⟼fl f b z
where "l ⟼fl b" := (𝔾_foldl l b).

(* A technical variant of FLcons, for later convenience *)
Definition FLcons_lrl {u z b} : lrl u ⟼fl b  →  u +: z ⟼fl f b z.
  refine (fun G => FLcons _). pattern u. exact (down_llP _ u G).
Defined.

(* -------------------------------------------------------------------------- *)
(* Using the Braga method *)

(* foldl conform by construction (or "packed with conformness") *)

(* The explicit dependent pattern matching

   match l2r l as x return ** 𝔻lz (r2l x) ... → _ ** with

   ** ... ** added below, is not needed any more for Coq 8.11+ *) 

(* Shape of the goal before refine:
   𝔻lz (r2l (l2r l)) →
   (∀y, r2l (l2r l) ⟼fl y → l ⟼fl y) →
   {b | l ⟼fl b} *)
Let Fixpoint foldl_pwc l (D: 𝔻lz l): {b | l ⟼fl b}.
Proof.
  gen_help l 𝔾_foldl. apply up_llP in D; revert D.
  refine (match l2r l as x return 𝔻lz (r2l x) 
                                → (∀ y : B, r2l x ⟼fl y → l ⟼fl y) 
                                → _ with
          | Nilr      => λ D T,  exist _ b0 _
          | Consr u z => λ D T,
                 let (b, Gb) := foldl_pwc u (π_𝔻lz D) in
                 exist _ (f b z) _
          end).
  - apply T; constructor 1.
  - apply T; constructor 2; exact Gb.
Defined.

(* Alternative definition, with just an equality in the Trojan horse
   -->
   + simpler goal before refine
   - structural inversion of D obtained after a rewriting step,
     cannot directly be put in the match
   - no explicit view of the rewriting steps
     (rewrite makes no difference between eq_ind and eq_recT)
*)
Let Fixpoint foldl_pwc_eq l (D: 𝔻lz l): {b | l ⟼fl b}.
Proof.
  generalize (lrl_id l).
  (* r2l (l2r l) = l → {b | l ⟼fl b} *)
  refine (match l2r l with
          | Nilr      => λ E,  exist _ b0 _
          | Consr u z => λ E,
                  let (b, Gb) := foldl_pwc_eq u _ in
                  exist _ (f b z) _
          end); simpl in E.
  - rewrite <- E in *. constructor 1.
  - rewrite <- E in D. apply (π_𝔻lz D).
  - rewrite <- E in *. constructor 2. exact Gb.
Defined.

(* The reference function for foldl *)
Definition foldl_ref l (D : 𝔻lz l) : B :=
  proj1_sig (foldl_pwc l D).

Lemma foldl_ref_corr_partial l (D: 𝔻lz l) :
  l ⟼fl foldl_ref l D.
Proof.
  exact (proj2_sig (foldl_pwc l D)).
Qed.

(* -------------------------------------------------------------------------- *)
(* Version corresponding to OCaml fold_left *)
Fixpoint foldl b l : B :=
    match l with
    | [] => b
    | x :: l => foldl (f b x) l
    end.

(* foldl is compatible with +: in the following sense *)
Lemma foldl_consr b (u: list A) (z: A) :
  foldl b (u +: z) = f (foldl b u) z.
Proof.
  revert b. induction u as [|x u Hu]; intro b; simpl.
  - reflexivity.
  - rewrite Hu. reflexivity.
Qed.

(* Completeness of foldl wrt 𝔾_foldl follows *)
Theorem foldl_compl b l :  l ⟼fl b  →  b = foldl b0 l.
Proof.
  intro g. induction g as [ | u z b g Hg]; simpl.
  - reflexivity.
  - rewrite foldl_consr. rewrite Hg. reflexivity.
Qed.
(* Corollary for free: 𝔾_foldl is functional; but useless *)

(* Partial conformity wrt 𝔾_foldl: whenever l is in the domain,
   fold computes a good result *)
(* Induction on  𝔻lz l *)
Theorem foldl_corr_partial l : 𝔻lz l  →  l ⟼fl foldl b0 l.
Proof.
  intro D. induction D as [ | u Gu z].
  - apply FLnil.
  - rewrite foldl_consr. apply (FLcons Gu).
Qed.

(* Total conformity wrt 𝔾_foldl follows independently *)
Corollary foldl_corr l :  l  ⟼fl  foldl b0 l.
Proof.
  apply foldl_corr_partial. apply 𝔻lz_all.
Qed.

End sec_params_foldl.

(* -------------------------------------------------------------------------- *)
(* Partial conformity wrt foldl_ref: whenever foldl_ref terminates,
   fold computes the same result *)
Theorem foldl_equiv_partial :
     ∀ f b l (D: 𝔻lz l), foldl f b l = foldl_ref f b l D.
Proof.
  intros. symmetry. apply foldl_compl. apply foldl_ref_corr_partial.
Qed.

(* Total conformity wrt foldl_ref follows independently *)
Corollary foldl_equiv_total :
    ∀ f b l, foldl f b l = foldl_ref f b l (𝔻lz_all l).
Proof.
  intros; apply foldl_equiv_partial.
Qed.

(* Additional remarks
- conformity of foldl wrt foldl_ref needs its completeness wrt 𝔾_foldl,
  not its conformity
- conformity of foldl wrt 𝔾_foldl is technically easier:
  an induction on the domain;
  in contrast, the definition foldl_ref requires a stronger recursion,
  including projective inversions (see lr_rec)
- as expected, termination is considered separately (with 𝔻lz_all),
  whatever the approach (using a relational or a functional specification)
*)

End sec_context.

(* -------------------------------------------------------------------------- *)
(* Extraction *)

Require Import Extraction.
Extract Inductive list => "list" [ "[]" "(::)" ].
Recursive Extraction foldl_ref foldl.
(*

type 'a lr =
| Nilr
| Consr of 'a list * 'a

(** val l2r : 'a1 list -> 'a1 lr **)

let rec l2r = function
| [] -> Nilr
| x::lr0 ->
  (match l2r lr0 with
   | Nilr -> Consr ([], x)
   | Consr (lg, z) -> Consr ((x::lg), z))

(** val foldl_ref : ('a2 -> 'a1 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec foldl_ref f b0 l =
  match l2r l with
  | Nilr -> b0
  | Consr (u, z) -> f (foldl_ref f b0 u) z

(** val foldl : ('a2 -> 'a1 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec foldl f b = function
| [] -> b
| x::l0 -> foldl f (f b x) l0


*)


(* -------------------------------------------------------------------------- *)
