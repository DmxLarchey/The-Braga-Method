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
  refine(match m, n return Dack m n → sig (Gack m n) with
  |   0 ,   _ => λ _, exist _ (S n) _
  | S m ,   0 => λ d, let (o,ho) := ack_pwc m 1 (Dack_pi1 d)     in
                      exist _ o _
  | S m , S n => λ d, let (v,hv) := ack_pwc (S m) n (Dack_pi2 d) in
                      let (o,ho) := ack_pwc m v (Dack_pi3 d hv)  in
                      exist _ o _
  end d); eauto.
Defined.

(* Termination of ack. Lexicographic product is by nested induction *)
Lemma ack_termination m n : Dack m n.
Proof.
  induction m in n |- *; eauto.
  induction n; eauto.
Defined.

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
Extraction ack.

(* This alternate avoids tailored small inversions and
   replaces them with the generic Acc_inv, so we get
   a shorter proof.*)

(* We define the sub-call/call relation inductivelly *)
Inductive ack_sub_calls : nat*nat → nat*nat → Prop :=
  | ack_sc_1 m     : ack_sub_calls (m,1) (S m,0)
  | ack_sc_2 m n   : ack_sub_calls (S m,n) (S m, S n)
  | ack_sc_3 m n v : Gack (S m) n v → ack_sub_calls (m,v) (S m,S n).

#[local] Hint Constructors ack_sub_calls : core.

Arguments Acc_inv {_ _ _} _ {_}.

(* We use Acc_inv that recover the sub-term for a proof of d : Acc ... *)
Fixpoint ack_pwc_Acc m n (d : Acc ack_sub_calls (m,n)) : sig (Gack m n).
Proof.
  refine(match m, n return Acc ack_sub_calls (m,n) → sig (Gack m n) with
  |   0 ,   _ => λ _, exist _ (S n) _
  | S m ,   0 => λ d, let (o,ho) := ack_pwc_Acc m 1 (Acc_inv d _)     in
                      exist _ o _
  | S m , S n => λ d, let (v,hv) := ack_pwc_Acc (S m) n (Acc_inv d _) in
                      let (o,ho) := ack_pwc_Acc m v (Acc_inv d _)     in
                      exist _ o _
  end d); eauto.
Defined.

Lemma ack_sub_calls_inv p q :
       ack_sub_calls p q 
     → match q with
       | (  0 ,   n) => False
       | (S m ,   0) => (m,1) = p
       | (S m , S n) => (S m,n) = p
                      ∨ ∃v, Gack (S m) n v ∧ (m,v) = p
       end.
Proof. destruct 1; eauto. Qed.

Lemma ack_termination_Acc m n : Acc ack_sub_calls (m,n).
Proof.
  induction m in n |- *; [ | induction n ];
    constructor. 
  1,2: intros ? []%ack_sub_calls_inv; auto.
  intros ? [ | (? & _ & ?)]%ack_sub_calls_inv; subst; auto.
Qed.

(** Then we can finish as in the case of Dack with the def of ack
    and the fixpoint equations, and extraction *)

(* ---------------------------------------------------------------------- *)
(* Computation times *)

(* Explicit program for termination certificates *)
Definition ack_termination_expl : ∀ m n, Dack m n :=
  fix loop_m m : ∀ n, Dack m n :=
    match m with
    | O   => Dack_0_n
    | S m =>
        let loopm := loop_m m in
        fix loop_n n : Dack (S m) n :=
          match n with
          | O   => Dack_S_0 (loopm 1)
          | S n => Dack_S_S (loop_n n) (λ v _, loopm v)
          end
    end.

Definition ack_expl m n := proj1_sig (ack_pwc m n (ack_termination_expl m n)).

(* Very small values as input provide much maller computation times *)
Time Compute ack_termination_expl 3 2. (* 0.004 s *)
Time Compute ack_expl 3 4. (* 0.002 s *)

(* Larger values can be computed *)
Time Compute ack_termination 9 9. (* 2.36 s *)
Time Compute ack_termination_expl 9 9. (* 0.98 s *)
Time Compute ack_expl 3 10. (* 8.7 s *)
Time Compute ack 3 10. (* 8.1 s *)
