(**************************************************************)
(*   Copyright                                                *)
(*             Jean-François Monin           [+]              *)
(*                                                            *)
(*            [+] Affiliation VERIMAG - Univ. Grenoble-Alpes  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* A lightweight tactic for marking terms at given places *)

Definition MARQ {A: Type} (x:A) := x.

Tactic Notation "mark" constr(i) "at" integer_list(l) :=
  pattern i at l;
  match goal with |- ?f ?x => change (f (MARQ x)) end;
  cbv beta.

Tactic Notation "mark" constr(i) "at" ne_integer_list(l) "in" hyp(H) :=
  pattern i at l in H;
  match type of H with ?f ?x => change (f (MARQ x)) in H end;
  cbv beta in H.

