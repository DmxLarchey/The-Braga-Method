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

(* This one performs harmless elimination of False : Prop into Type 
   and extracts to an exception "assert false" *)

Print False_rect.

(* This one avoids harmless elimination Prop -> Type by replacing
   it with an infinite loop. 
   It thus extracts to "let rec loop _ = loop () in loop ()" *)

Definition False_loop (X : Type) : False -> X :=
  (fix loop _ f := loop tt (match f : False with end)) tt.

Extraction Inline False_loop.

(* This one avoids harmless elimination False : Prop into Type
   by first eliminating False : Prop into Empty_set : Type
   using a loop and then eliminating Empty_set : Type into Type
   using a "match _ : Empty_set with end". And since that elimination
   is from Type to Type, it is not a harmless elim.
   Finally it extracts to an exception "assert false" *)

Definition False_exc (X : Type) (f : False) : X := 
  match False_loop Empty_set f return X with end.

Extraction Inline False_exc.

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

  Definition head_False_loop l : is_cons l -> X :=
    match l  with
      | nil  => fun G => False_loop _ G
      | x::_ => fun _ => x
    end.

  Definition head_False_exc l : is_cons l -> X :=
    match l  with
      | nil  => False_exc _
      | x::_ => fun _ => x
    end.

End head_partial.

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive Extraction False_exc.

(* Extraction with an infinite loop *)
Recursive Extraction head_False_loop.
(* Extraction with an exception BUT w/o harmless elimination *)
Recursive Extraction head_False_exc.
(* Extractions with an exception and harmless elimination *)
Recursive Extraction head_match_end.
Recursive Extraction head_False_rect.

Recursive Extraction False_loop.

