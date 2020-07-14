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

Require Import List Extraction.

Print False_rect.

Definition False_elim (X : Type) : unit -> False -> X :=
  fix loop x f := loop tt (match f : False with end).

Section head_partial.

  Variable X : Type.

  Definition is_cons (l : list X) := match l with _::_ => True | _ => False end.
  
  Definition head_match_end l : is_cons l -> X :=
    match l  with
      | nil  => fun G => match G with end
      | x::_ => fun _ => x
    end.

  Definition head_False_rect l : is_cons l -> X :=
    match l  with
      | nil  => fun G => False_rect _ G
      | x::_ => fun _ => x
    end.

  Definition head_False_elim l : is_cons l -> X :=
    match l  with
      | nil  => fun G => False_elim _ tt G
      | x::_ => fun _ => x
    end.

End head_partial.

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

(* Extraction with an infinite loop *)
Recursive Extraction head_False_elim.
(* Extractions with an exception *)
Recursive Extraction head_match_end.
Recursive Extraction head_False_rect.

