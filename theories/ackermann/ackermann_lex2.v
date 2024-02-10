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

Require Import Wellfounded Utf8 Extraction.

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

(** Detailed explanation of the termination of ack using
    the lexicographic product of the successor relation *)

(* lex2 (m,n) (m',n') encodes that the pair
   (m,n) is smaller than the pair (m',n')
   in the lexicographic product of the 
   successor relation. *)
Inductive lex2 : nat*nat → nat*nat → Prop :=
  | lex2_lft m u v : lex2 (m,u) (S m,v)        (* (m,_) < (S m,_) *)
  | lex2_rt m n :    lex2 (m,n) (m,S n).       (* (m,n) < (m,S n) *)

Inductive lex2_inv_0S n : nat*nat → Prop :=
  | lex2_inv_0S_intro : lex2_inv_0S n (0,n).

Inductive lex2_inv_S0 m : nat*nat → Prop :=
  | lex2_inv_S0_intro n : lex2_inv_S0 m (m,n).

Inductive lex2_inv_SS m n : nat*nat → Prop :=
  | lex2_inv_SS_intro1 n' : lex2_inv_SS m n (m,n')
  | lex2_inv_SS_intro2 :    lex2_inv_SS m n (S m,n).

Fact lex2_inv {p q} : 
       lex2 p q
     → match q with
       | (0   , 0  ) => False
       | (0   , S n) => lex2_inv_0S n p
       | (S m , 0  ) => lex2_inv_S0 m p
       | (S m , S n) => lex2_inv_SS m n p
       end.
Proof. destruct 1 as [ ? ? [] | [] ]; constructor. Defined.

Theorem lex2_wf : well_founded lex2.
Proof.
  intros (m,n).
  induction m in n |- *; induction n; constructor.
  all: now intros _ []%lex2_inv.
Defined.

(* Termination of ack. *)
Lemma ack_termination m n : Dack m n.
Proof.
  generalize (lex2_wf (m,n)).
  revert m n.
  refine (fix loop m n a { struct a } := _).
  destruct m as [ | m ].
  + constructor.
  + destruct n as [ | n ].
    * constructor.
      apply loop, Acc_inv with (1 := a).
      constructor.
    * constructor.
      - apply loop, Acc_inv with (1 := a).
        constructor.
      - intros v _.
        apply loop, Acc_inv with (1 := a).
        constructor.
Defined.

(* ---------------------------------------------------------------------- *)
(* Computation times *)

(* Explicit program for termination certificates *)
Definition ack_termination_expl : ∀ m n, Dack m n :=
  fix loop_m m : ∀ n, Dack m n :=
    match m with
    | O   => Dack_0_n
    | S m =>
        fix loop_n n : Dack (S m) n :=
          match n with
          | O   => Dack_S_0 (loop_m m 1)
          | S n => Dack_S_S (loop_n n) (λ v _, loop_m m v)
          end
    end.

(* Now the definition of Ackermann, combined with termination
   and stripped of its low-level spec 
   
   The two versions of ack and ack_expl are there to compare
   the computation time of the Ltac based termination proof
   and of the program based version of the proof. *)
Definition ack m n := proj1_sig (ack_pwc m n (ack_termination m n)).
Definition ack_expl m n := proj1_sig (ack_pwc m n (ack_termination_expl m n)).

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

Fact acc_sub_calls_lex2 p q : ack_sub_calls p q → lex2 p q.
Proof. induction 1; simpl; constructor. Qed.

Lemma ack_termination_Acc : well_founded ack_sub_calls.
Proof. apply wf_incl with (1 := acc_sub_calls_lex2), lex2_wf. Qed.

(** Then we can finish as in the case of Dack with the def of ack
    and the fixpoint equations, and extraction *)

Print ack_termination.
Print ack_termination_expl.

(* Very small values as input provide much maller computation times *)
Time Compute ack_termination_expl 3 2. (* 0.004 s *)
Time Compute ack_expl 3 4. (* 0.002 s *)

(** DLW: for some strange reason, the hand coded computation
    of the value is slower than the one using the Ltac script.
    I suspect the hand coded version does not have any opaque
    part while the other one may have some non-critical bits
    Opaque. I do not see any another reason because both
    proofs perform the same computation ... 

    Btw I do not get stable enough times to compare. 
    In the last try, the _expl version is 0.5% faster ... *)

(** JFM: got similarly unstable results. *)

Time Compute ack 3 10. (* takes a very long time *)
Time Compute ack_expl 3 10. (* 8.7 s *)


(* Larger values can be computed *)
(* Time Compute ack_termination 9 9. (* 2.36 s *)
Time Compute ack_termination_expl 9 9. (* 0.98 s *) *)




