(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             JF Monin                   [**]                *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                            [**] Affiliation Verimag -- UGA *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2.1 FREE SOFTWARE LICENSE AGREEMENT        *)
(**************************************************************)

(* Implementation of the comment in ackermann_simple.v
"Exaggerating a lot more, take a domain such as:"
*)

Require Import Utf8 Extraction.

Inductive Gack : nat → nat → nat → Prop :=
  | Gack_0_n n       : Gack 0 n (S n)
  | Gack_S_0 m o     : Gack m 1 o
                     → Gack (S m) 0 o
  | Gack_S_S m n v o : Gack (S m) n v
                     → Gack m v o
                     → Gack (S m) (S n) o.

#[local] Hint Constructors Gack : core.

Inductive Dack (n m : nat) : Prop := Dexagg : (∀ x y, Dack x y) → Dack n m.

Definition Dack_pi {m n} (d : Dack m n) : ∀ {x y}, Dack x y :=
  match d with
  | Dexagg _ _ f => f
  end.

(* The fully specified Ackermann function *)
Fixpoint ack_pwc m n (d : Dack m n) : sig (Gack m n).
Proof.
  refine(match m, n return Dack m n → sig (Gack m n) with
  |   0 ,   _ => λ _, exist _ (S n) _
  | S m ,   0 => λ d, let (o,ho) := ack_pwc m 1 (Dack_pi d)     in
                      exist _ o _
  | S m , S n => λ d, let (v,hv) := ack_pwc (S m) n (Dack_pi d) in
                      let (o,ho) := ack_pwc m v (Dack_pi d)  in
                      exist _ o _
  end d); eauto.
Defined.

(* Of course no termination certificate can be prodided! *)
Lemma no_ack_termination m n : Dack m n → False.
Proof.
  induction 1 as [m n d Hd]. exact (Hd 0 0).
Qed.

(* Now the definition of Ackermann, stripped of its low-level spec *)
Definition ack m n (d : Dack m n) := proj1_sig (ack_pwc m n d).

(* We recover the spec for ack *)
Lemma ack_spec m n (d : Dack m n) : Gack m n (ack m n d).
Proof. apply (proj2_sig _). Qed.

(* Extraction as usual *)
Extraction Inline ack_pwc.
Extraction ack.
