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

(** Extraction of the following version of Ackermann
    where the two branches depending on the match on
    n are factored in before the outer call of ack

    let rec ack m n =
      match m with
     |   0 -> S n
     | S m -> ack m 
      (match n with
       |   0 -> S 0
      | S n -> ack (S m) n)

    Several versions, including one inspired by D. Monniaux
    using an inductive subspec Prop instead of a match subspec.
*)

Require Import Utf8 Extraction.

Inductive Gack : nat → nat → nat → Prop :=
  | Gack_0_n n       : Gack 0 n (S n)
  | Gack_S_0 m o     : Gack m 1 o
                     → Gack (S m) 0 o
  | Gack_S_S m n v o : Gack (S m) n v
                     → Gack m v o
                     → Gack (S m) (S n) o.

Inductive Dack : nat → nat → Prop :=
  | Dack_0_n n     : Dack 0 n
  | Dack_S_0 {m}   : Dack m 1
                   → Dack (S m) 0
  | Dack_S_S {m n} : Dack (S m) n
                   → (∀v, Gack (S m) n v → Dack m v)
                   → Dack (S m) (S n).

#[local] Hint Constructors Gack Dack : core.

(** Small inversions for domain projections *)

Definition is_S_0 m n := match m, n with | S _, 0   => True | _, _ => False end.
Definition is_S_S m n := match m, n with | S _, S _ => True | _, _ => False end.

Definition Dack_pi1 {m} (d : Dack (S m) 0) : Dack m 1 :=
  match d in Dack m n return is_S_0 m n → Dack (pred m) _ with
  | Dack_0_n _   => λ C, match C with end
  | Dack_S_0 h   => λ _, h
  | Dack_S_S _ _ => λ C, match C with end
  end I.

Definition Dack_pi2 {m n} (d : Dack (S m) (S n)) : Dack (S m) n :=
  match d in Dack m n return is_S_S m n → Dack _ (pred n) with
  | Dack_0_n _   => λ C, match C with end
  | Dack_S_0 h   => λ C, match C with end
  | Dack_S_S h _ => λ _, h
  end I.

Definition Dack_pi3 {m n} (d : Dack (S m) (S n)) : ∀{v}, Gack (S m) n v → Dack m v :=
  match d in Dack m n return is_S_S m n → ∀v, Gack _ (pred n) v → Dack (pred m) v with
  | Dack_0_n _   => λ C, match C with end
  | Dack_S_0 h   => λ C, match C with end
  | Dack_S_S _ h => λ _, h
  end I.

(* The fully specified Ackermann function *)
Fixpoint ack_pwc m n (d : Dack m n) : sig (Gack m n).
Proof.
  refine (match m return Dack m _ → sig (Gack m _) with
  | 0   => λ _, exist _ (S n) _
  | S m => λ d, let (v,hv) :=
                  match n return Dack _ n → sig (match n with 0 => eq 1 | S n => Gack (S m) n end) with
                  | 0   => λ _, exist _ 1 eq_refl
                  | S n => λ d, ack_pwc (S m) n (Dack_pi2 d)
                  end d in
                let (o,ho) := ack_pwc m v
                    (match n return Dack _ n → match n with 0 => eq 1 | S _ => _ end v → _ with
                     | 0   => λ d hv, match hv with eq_refl => Dack_pi1 d end
                     | S n => λ d hv, Dack_pi3 d hv
                     end d hv) in
                exist _ o _
  end d); eauto.
  destruct n; subst; eauto.
Defined.

Inductive Gack' m : nat → nat → Prop :=
  | Gack'_0 : Gack' m 0 1
  | Gack'_S n o : Gack (S m) n o → Gack' m (S n) o.

#[local] Hint Constructors Gack' : core.

Arguments Gack'_0 {_}.
Arguments Gack'_S {_ _ _}.

(* The same with an inductive spec *)
Fixpoint ack_pwc' m n (d : Dack m n) : sig (Gack m n).
Proof.
  refine (match m return Dack m _ → sig (Gack m _) with
  | 0   => λ _, exist _ (S n) _
  | S m => λ d, let (v,hv) := match n return Dack _ n → sig (Gack' _ n) with
                  | 0   => λ d, exist _ 1 _
                  | S n => λ d, let (v,hv) := ack_pwc' (S m) n (Dack_pi2 d) in
                                exist _ v _
                end d in
                let (o,ho) := ack_pwc' m v
                  (match hv in Gack' _ n v return Dack _ n → Dack _ v with
                  | Gack'_0   => λ d, Dack_pi1 d
                  | Gack'_S h => λ d, Dack_pi3 d h
                  end d) in
                exist _ o _
  end d); eauto.
  destruct hv; eauto.
Defined.

Definition ack_pwc'' : ∀ m n, Dack m n → sig (Gack m n).
Proof.
  fix loop 3; intros m n Hn.
  destruct m as [ | m ].
  + exists (S n); eauto.
  + assert {v | Gack' m n v} as (v & hv).
    * destruct n as [ | n ].
      - exists 1; eauto.
      - destruct (loop (S m) n) as (v & hv).
        ++ now apply Dack_pi2.
        ++ exists v; eauto.
    * destruct (loop m v) as (o & ho).
      - destruct hv.
        ++ now apply Dack_pi1.
        ++ eapply Dack_pi3; eauto.
      - exists o.
        destruct hv; eauto.
Defined.

(* Termination of ack. Lexicographic product is by nested induction *)
Lemma ack_termination m n : Dack m n.
Proof.
  induction m in n |- *; eauto.
  induction n; eauto.
Qed.

(* Now the definition of Ackermann, combined with termination
   and stripped of its low-level spec *)
Definition ack m n := proj1_sig (ack_pwc m n (ack_termination m n)).

(* We recover the spec for ack *)
Lemma ack_spec m n : Gack m n (ack m n).
Proof. apply (proj2_sig _). Qed.

(* Inversion lemma for Gack *)
Fact Gack_inv m n o :
        Gack m n o
      → match m, n with
        |   0 ,   _ => S n = o
        | S m ,   0 => Gack m 1 o
        | S m , S n => ∃v, Gack (S m) n v ∧ Gack m v o
        end.
Proof. destruct 1; eauto. Qed.

(* Gack is a functional relation, via Gack_inv *)
Lemma Gack_fun m n o₁ o₂ : Gack m n o₁ → Gack m n o₂ → o₁ = o₂.
Proof.
  induction 1 as [ | | ? ? ? ? _ IH1 _ ? ] in o₂ |- *; intros G%Gack_inv; auto.
  destruct G as (? & []%IH1 & ?); eauto.
Qed.

(* Fixpoint equations come from Gack constructors
   and Gack_[spec_fun] *)

#[local] Hint Resolve ack_spec Gack_fun : core.

Fact ack_fix_0n n : ack 0 n = S n.
Proof. eauto. Qed.

Fact ack_fix_S0 m : ack (S m) 0 = ack m 1.
Proof. eauto. Qed.

Fact ack_fix_SS m n : ack (S m) (S n) = ack m (ack (S m) n).
Proof. eauto. Qed.

(* Extraction is right on spot *)
Extraction Inline ack_pwc.
Recursive Extraction ack ack_pwc' ack_pwc''.
