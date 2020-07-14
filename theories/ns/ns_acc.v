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

Require Import Arith Lia Utf8 Extraction.

Require Import ns.

Section Acc_rect'.

  Variables
      (K : Type) (R : K -> K -> Prop) 
      (P  : forall x, Acc R x -> Type)
      (HP : forall x Ax, (forall y Hyx, P y (Acc_inv Ax y Hyx)) -> P x Ax).

  Fixpoint Acc_rect' x (Ax : Acc R x) {struct Ax} : P x Ax :=
    HP x Ax (λ y Hyx, Acc_rect' y (Acc_inv Ax y Hyx)).

End Acc_rect'.

Extraction Inline Acc_rect'.

Section ns_acc.

Variable (X : Type) (g : X -> X) (b : X -> bool).

Notation "x '⟼ns' y" := (@𝔾ns _ g b x y) (at level 70, no associativity).
Notation "x ';' n '⟼nsa' y" := (@𝔾nsa _ g b x n y) (at level 70, no associativity).

Reserved Notation "x '<sc' y" (at level 70).

Inductive subcall : X → X → Prop :=
  | in_sc_1 x : b x = false → g x <sc x
where "x <sc y" := (subcall x y).

Definition 𝔻ns' := Acc subcall.

(* Variant zero, weakly specified *)

Definition ns_Acc : ∀x, 𝔻ns' x → nat.
Proof.
  induction 1 as [ x _ IHD ] using Acc_rect'.
  case_eq (b x); intros G.
  + exact 0.
  + apply S, (IHD (g x)).
    now constructor.
Defined.

Definition nsa_Acc : ∀x, nat → 𝔻ns' x → nat.
Proof.
  intros x n D; revert x D n; induction 1 as [ x _ IHD ] using Acc_rect'; intros n.
  case_eq (b x); intros G.
  + exact 0.
  + apply S, (IHD (g x)) with (2 := S n).
    now constructor.
Defined.

(* First variant, via Acc_rect' directly *)

Definition ns1 : ∀x, 𝔻ns' x → {o | x ⟼ns o}.
Proof.
  induction 1 as [ x _ IHD ] using Acc_rect'.
  case_eq (b x); intros G.
  + exists 0; now constructor.
  + refine (let (o,Co) := IHD (g x) _ in exist _ (S o) _).
    * now constructor.
    * now constructor.
Defined.

Definition nsa1 : ∀x n, 𝔻ns' x → {o | x;n ⟼nsa o}.
Proof.
  intros x n D; revert x D n.
  induction 1 as [ x _ IHD ] using Acc_rect'; intros n.
  case_eq (b x); intros G.
  + exists n; now constructor.
  + refine (let (o,Co) := IHD (g x) _ (S n) in exist _ o _). (* destruct generates a let in *)
    * now constructor.
    * now constructor.
Defined.

(* Second variant, inlining Acc_rect' *)

Fixpoint ns_pwc_Acc x (D : 𝔻ns' x) : {o | x ⟼ns o}.
Proof. refine(
  match b x as bx return b x = bx → _ with
    | true  => λ G, exist _ 0 _
    | false => λ G, let (o,Co) := ns_pwc_Acc (g x) _ in
                    exist _ (S o) _ 
  end eq_refl).
  1-2: cycle 1.
  + apply Acc_inv with (1 := D); now constructor.
  + now constructor 1.
  + now constructor 2.
Defined.

Fixpoint nsa_pwc_Acc x n (D : 𝔻ns' x) : {o | x;n ⟼nsa o}.
Proof. refine(
  match b x as bx return b x = bx → _ with
    | true  => λ G, exist _ n _
    | false => λ G, let (o,Co) := nsa_pwc_Acc (g x) (S n) _ in
                    exist _ o _ 
  end eq_refl).
  1-2: cycle 1.
  + apply Acc_inv with (1 := D); now constructor.
  + now constructor 1.
  + now constructor 2.
Defined.

(* Third variant, we simulate constructors and a dependent eliminator *)

Fact 𝔻ns'_tt x : b x = true → 𝔻ns' x.
Proof. constructor; inversion 1; bool discr. Qed.

Fact 𝔻ns'_ff x : b x = false → 𝔻ns' (g x )→ 𝔻ns' x.
Proof. constructor; inversion 1; auto; bool discr. Qed.

Section 𝔻ns'_rect.

  Variable P : forall x, 𝔻ns' x -> Type.

  Hypothesis (HPi : forall x D1 D2, P x D1 -> P x D2)
             (HP0 : forall x E, P _ (𝔻ns'_tt x E))
             (HP1 : forall x E D, P _ D -> P _ (𝔻ns'_ff x E D)).

  Theorem 𝔻acc_rect : ∀x D, P x D.
  Proof.
    induction D as [ x D IHD ] using Acc_rect'.
    case_eq (b x); intros G.
    + apply HPi with (1 := HP0 _ G).
    + refine (HPi _ _ _ (HP1 _ G _ (IHD (g x) _))).
      constructor; auto.
  Defined.

End 𝔻ns'_rect.

(* Third variant, via the dependent eliminator *)

Definition ns3 x (D : 𝔻ns' x) : {o | x ⟼ns o}.
Proof.
  induction D as [ | x E | x E D IHD ] using 𝔻acc_rect; trivial.
  + exists 0; now constructor.
  + refine (let (o,Co) := IHD in exist _ (S o) _).
    now constructor.
Defined.

Definition nsa3 x n (D : 𝔻ns' x) : {o | x;n ⟼nsa o}.
Proof.
  revert n;
  induction D as [ | x E | x E D IHD ] using 𝔻acc_rect; intros n; trivial.
  + exists n; now constructor.
  + refine (let (o,Co) := IHD (S n) in exist _ o _); now constructor.
Defined.

End ns_acc.

Extract Inductive bool => "bool" [ "true" "false" ].
Extraction Inline 𝔻acc_rect.

Recursive Extraction ns_Acc ns1 ns_pwc_Acc ns3.
Recursive Extraction nsa_Acc nsa1 nsa_pwc_Acc nsa3.

