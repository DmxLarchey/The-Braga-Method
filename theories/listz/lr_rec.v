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

(* ========================================================================== *)
(* Tools for recursive programming on lists traversed from right to left *)

Section sec_context.

Context {A : Type}.
Implicit Type l u : list A.
Implicit Type r : lr A.
Implicit Type z : A.

(* High-level version *)
(* 
                      𝔻listz u
  ----------      ----------------
  𝔻listz []       𝔻listz (u +: z)

 *)

Inductive 𝔻listz : list A → Prop :=
| 𝔻nil : 𝔻listz []
| 𝔻consr : ∀ u z, 𝔻listz u → 𝔻listz (u +: z)
.

Definition 𝔻listz_all l : 𝔻listz l.
Proof.
  induction l as [| x u D].
  - constructor.
  - induction D as [| u z D HD].
    + change [x] with ([] +: x); do 2 constructor.
    + apply (𝔻consr _ _ HD). (* (x :: (u +: z))  =  ((x :: u) +: z) *)
Defined.

Unset Elimination Schemes.

(* We will use the following variant of the previous definition,
   which sticks to the implementation of the fake pattern matching

   |  fakematch l with  |    by     |   match l2r l with    |
   |  | [] => ...       |           |   | Nilr => ...       |
   |  | u +: z => ...   |           |   | Consr u z => ...  |
   |  end               |           |   end                 |

  and turns out to have an easier-to-explain inversion.

  The introduction rules are:

                       𝔻lz u         𝔻lr (l2r l)
   ---------      ---------------     -----------
   𝔻lr Nilr       𝔻lr (Consr u z)       𝔻lz l

 *)

Inductive 𝔻lz : list A -> Prop :=
| 𝔻lz_1 l : 𝔻lr (l2r l) → 𝔻lz l
with 𝔻lr  : lr A -> Prop :=
| 𝔻lr_Nilr : 𝔻lr Nilr
| 𝔻lr_Consr : ∀ u z, 𝔻lz u → 𝔻lr (Consr u z)
.

Set Elimination Schemes.

(* The induction scheme for 𝔻lz is easy to prove, by fixpoint,
   basic pattern matchings, and a trivial rewriting step *)
Theorem 𝔻lz_ind (P: list A → Prop) :
  P []  →  (∀ u, P u → ∀ z, P (u +: z)) →
  ∀ l, 𝔻lz l → P l.
Proof.
  intros Pnil Pconsr.
  refine (fix fxp l D {struct D} : _ := _).
  destruct D as [l D]. rewrite <- lrl_id.
  destruct D as [| u z Pu]; simpl.
  - apply Pnil.
  - apply Pconsr. apply (fxp u Pu).
Qed.

(* Defining 𝔻lz_rect is more difficult.
   Done below using the Braga approach *)

(* The two definition of 𝔻lz are actually equivalent *)
Lemma lz_listz l : 𝔻lz l → 𝔻listz l.
Proof.
  induction 1; constructor; assumption.
Qed.

Lemma listz_lz l : 𝔻listz l → 𝔻lz l.
Proof.
  intros D.
  induction D as [| u z D HD]; constructor.
  - constructor.
  - rewrite l2r_consr. constructor. apply HD.
Qed.

Corollary 𝔻lz_all l : 𝔻lz l.
Proof. apply listz_lz, 𝔻listz_all. Qed.

(* -------------------------------------------------------------------------- *)
(* Structural projection of 𝔻consr *)

Let shape r : Prop :=
  match r with Consr u z => True | _ => False end.

(* Simplest version without "harmless" (or "singleton") Prop to Type elim *)
(* Recovering the u component of r when r is Consr u z with an available default value:
   the u given as input.
   This makes no assumption on the type of u, and
   z could be recovered in the same way if needed, using
        let z := match r with Consr u z => z | _ => z end in
*)

(* Designed in 2 steps *)
Let π_𝔻lr {u z} (D: 𝔻lr (Consr u z)) : 𝔻lz u :=
  match D in 𝔻lr r return
        let u := match r with Consr u z => u | _ => u end 
        in shape r → 𝔻lz u with
  | 𝔻lr_Consr u z D => λ G, D
  |  _              => λ G, match G with end
  end I.

(* Versions using an auxiliary function defined first, for recovering u from r *)
(* Version using a "harmless" (or "singleton") Prop to Type elim *)

Let lrleft_he r : shape r → list A :=
  match r with Consr u z => λ _, u | _ => λ G, (match G with end) end.

Let π_𝔻lr_he {u z} (D: 𝔻lr (Consr u z)) : 𝔻lz u :=
  match D in 𝔻lr r return ∀ G, 𝔻lz (lrleft_he r G) with
  | 𝔻lr_Consr u0 z0 D0 => λ G, D0
  |  _                  => λ G, match G with end
  end I.

(** Another version w/o harmless elim Prop -> Type using False_elim *)

Definition False_elim X : False -> X :=
  fix loop f := loop (match f : False with end).

Let lrleft_no_he r : shape r → list A :=
  match r with Consr u z => λ _, u | _ => λ G, False_elim _ G end.

Let π_𝔻lr_no_he {u z} (D: 𝔻lr (Consr u z)) : 𝔻lz u :=
  match D in 𝔻lr r return ∀ G, 𝔻lz (lrleft_no_he r G) with
  | 𝔻lr_Consr u0 z0 D0 => λ G, D0
  |  _                  => λ G, match G with end
  end I.

(* Finally, the simple version given first can be written in a similar way *)
Let lrleft r : list A → list A :=
  match r with Consr u z => λ _, u | _ => λ u0, u0 end.

Let π_𝔻lr' {u z} (D: 𝔻lr (Consr u z)) : 𝔻lz u :=
  match D in 𝔻lr r return ∀(G: shape r), 𝔻lz (lrleft r u) with
  | 𝔻lr_Consr u0 z0 D0 => λ G, D0
  |  _                  => λ G, match G with end
  end I.

(* In contrast, lrleft_he and lrleft_no_he cannot be inlined
   because they require a G argument, whose type depends on r.
*)


(* Definitions of π_𝔻lz *)
Definition π_𝔻lz {u z} (D : 𝔻lz (u +: z)) : 𝔻lz u :=
  match D in 𝔻lz l return l = u+:z → _ with
    𝔻lz_1 l Dr => λ G, π_𝔻lr (same_by_l2r_consr G Dr)
  end eq_refl.

(* Compact Version in 1 step *)
Definition π_𝔻lz_compact {u z} (D : 𝔻lz (u +: z)) : 𝔻lz u :=
 match D in 𝔻lz l return l = u+:z → _ with
 | 𝔻lz_1 _ Dr => λ G, 
   match same_by_l2r_consr G Dr in 𝔻lr r return
         let u := match r with Consr u z => u | _ => u end in
         shape r → 𝔻lz u with
   | 𝔻lr_Consr u _ Du => λ G, Du
   |  _               => λ G, match G with end
   end (I : shape (Consr u z))
 end eq_refl.

(* -------------------------------------------------------------------------- *)

(* A recursor for Type which does NOT pattern match over 𝔻lz l
   in Type context but there is eq_rect in it !! *)

(* Using up_llP and down_llT in order to constrain the use of eq_ind
   and eq_rect, hence a clearer view of the underlying reasoning *)
Definition 𝔻lz_rect (P: list A → Type) :
  P []  →  (∀ u, P u → ∀ z, P (u +: z)) →  ∀ l, 𝔻lz l → P l :=
  fun Pnil Pconsr =>
    fix fxp l (D : 𝔻lz l) {struct D} : P l :=
    (match l2r l as r return (𝔻lz (r2l r) → (P (r2l r) → P l) → P l)
     with
     | Nilr      => fun D L => L Pnil
     | Consr u z => fun D L => L (Pconsr u (fxp u (π_𝔻lz D)) z)
     end (up_llP 𝔻lz l D)) (down_llT P l).


(* Interactive version, on all lists *)
Definition list_zrect (P: list A → Type) :
  P []  →  (∀ u, P u → ∀ z, P (u +: z))  →  ∀ l, P l.
Proof.
  intros Pnil Pconsr.
  intro l. generalize (𝔻lz_all l). revert l.
  refine (fix fxp l D {struct D} : _ := _).
  generalize (down_llT P l).
  apply up_llP in D.
  revert D.
  destruct (l2r l) as [| u z]; simpl; intros D L; apply L.
  - apply Pnil.
  - apply Pconsr, fxp, (π_𝔻lz D).
Defined.

End sec_context.
