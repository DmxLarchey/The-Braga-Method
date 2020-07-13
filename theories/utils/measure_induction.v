(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Wellfounded Extraction.

Set Implicit Arguments.

Section measure_rect.

  Variable (X : Type) (m : X -> nat) (P : X -> Type).

  Hypothesis F : forall x, (forall x', m x' < m x -> P x') -> P x.

  Arguments F : clear implicits.

  Notation R := (fun x y => m x < m y).
  Let Rwf : forall x : X, Acc R x.
  Proof. apply wf_inverse_image with (f := m), lt_wf. Qed.

  Definition measure_rect x : P x :=
    (fix loop x (A : Acc R x) { struct A } := 
      F x (fun x' H' => loop x' (Acc_inv A H'))) _ (Rwf _).

End measure_rect.

Extraction Inline measure_rect.

Tactic Notation "induction" "on" hyp(x) "as" ident(IH) "with" "measure" uconstr(f) :=
   pattern x; revert x; apply measure_rect with (m := fun x => f); intros x IH.

Section measure2_rect.

  Variable (X Y : Type) (m : X -> Y -> nat) (P : X -> Y -> Type).

  Hypothesis F : (forall x y, (forall x' y', m x' y' < m x y -> P x' y') -> P x y).

  Arguments F : clear implicits.

  Let m' (c : X * Y) := match c with (x,y) => m x y end.

  Notation R := (fun c d => m' c < m' d).
  Let Rwf : well_founded R.
  Proof. apply wf_inverse_image with (f := m'), lt_wf. Qed.

  Definition measure2_rect x y : P x y :=
    (fix loop x y (A : Acc R (x,y)) { struct A } := 
      F x y (fun x' y' H' => loop x' y' (@Acc_inv _ _ _ A (_,_) H'))) _ _ (Rwf (_,_)).

End measure2_rect.

Extraction Inline measure2_rect.

Tactic Notation "induction" "on" hyp(x) hyp(y) "as" ident(IH) "with" "measure" uconstr(f) :=
   pattern x, y; revert x y; apply measure2_rect with (m := fun x y => f); intros x y IH.
