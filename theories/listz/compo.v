(**************************************************************)
(*   Copyright                                                *)
(*             Jean-François Monin           [+]              *)
(*                                                            *)
(*            [+] Affiliation VERIMAG - Univ. Grenoble-Alpes  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* Fucntion composition usually denoted by g o f in maths *)

Definition compo {A B C} (g : B -> C) (f : A -> B) : A -> C :=
  fun x => g (f x).

Notation "g << f" := (compo g f) (at level 45, right associativity).
