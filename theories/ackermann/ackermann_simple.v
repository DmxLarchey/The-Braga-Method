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

(* A simpler inductive domain that works for
   special cases such as the Ackermann function *)

Require Import Utf8 Extraction.

Inductive Gack : nat → nat → nat → Prop :=
  | Gack_0_n n       : Gack 0 n (S n)
  | Gack_S_0 m o     : Gack m 1 o
                     → Gack (S m) 0 o
  | Gack_S_S m n v o : Gack (S m) n v
                     → Gack m v o
                     → Gack (S m) (S n) o.

(* Inductive domain, without any reference to Gack, which NOT the
   standard Braga method.*)

(*
There is a pitfall here: it is always possible to remove G in the
definition of the domain, as far as the DEFINITION of the function is
concerned; but the big danger is that the domain will become much 
smaller than expected or even empty.
(Exagerating a lot more, take a domain such as 
Inductive Dack n m : Prop := Dack x y : Dack x y → Dack n m).

This is why it is important to look at actual termination, i.e. 
Lemma ack_termination here.

Usually G is crucial for termination in the presence of nested 
recursion because it constrains the recursive calls actually performed.  
In the case of the Ackermann function this constraint happens to be 
unneeded.

However to see that, it is necessary to be aware of what happens in
the construction of proof certificates performed by ack_termination.
Here, writing the program turns out to be not that hard, though it 
requires more effort than writing the script and results in 11 lines 
instead of 2 to 4.
More importantly, we immediately see that many variants of the function
(where recursive calls are replaced by other expressions) are
definable and total. Thinking a little bit more, if you ignored
lexicographix ordering (which is certainly not the case of the
readers; but it is not the point here), you have an opportunity
to discover it.

I (JFM) see this as an intereresting take hom lesson against the
temptation of letting whatever kind of "Artificial Intelligence" 
performing too many tasks: those tasks will be quickly performed 
and you have the result, yes, but WITHOUT providing any understanding 
(the real meaning of intelligence) of what happens; even worse, 
like here, HIDING what happens.

(DLW) Modifying Dack to correspond to the induction principle
actually used to show termination is very *NOT* Braga IHMO.
Precisely because you do not want to know a priori why it
terminates.

The script "ack_termination" gives enough info on the proof.
Induction on m (with n universally quantified), then on n.
The rest is solved by eauto because it is so easy. I could
have detailed it, or used info_auto or info_eauto to get the
details. *)

Inductive Dack : nat → nat → Prop :=
  | Dack_0_n n     : Dack 0 n
  | Dack_S_0 {m}   : Dack m 1
                   → Dack (S m) 0
  | Dack_S_S {m n} : Dack (S m) n
                   → (∀v, Dack m v)
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

Definition Dack_pi3 {m n} (d : Dack (S m) (S n)) : ∀{v}, Dack m v :=
  match d in Dack m n return is_S_S m n → ∀v, Dack (pred m) v with
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
                      let (o,ho) := ack_pwc m v (Dack_pi3 d)  in
                      exist _ o _
  end d); eauto.
Defined.

(* Termination of ack. Lexicographic product is by nested induction *)
Lemma ack_termination m n : Dack m n.
Proof.
  induction m in n |- *.
  + info_trivial.
  + induction n.
    * info_auto.
    * info_auto.
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
Extraction ack.

(* ---------------------------------------------------------------------- *)
(* Computation times *)

(* Explicit program for termination certificates *)
(* "expl" stands both for "explicit" and "explanation" *)
Definition ack_termination_expl : ∀ m n, Dack m n :=
  fix loop_m m : ∀ n, Dack m n := 
    match m with
    | O   => Dack_0_n
    | S m =>
        let loopm := loop_m m in
        fix loop_n n : Dack (S m) n :=
          match n with
          | O   => Dack_S_0 (loopm 1)
          | S n => Dack_S_S (loop_n n) loopm
          end
    end.

(*
Here is the program developed in file ackermann.v:
Definition ack_termination_expl : ∀ m n, Dack m n :=
  fix loop_m m : ∀ n, Dack m n :=
    match m with
    | O   => Dack_0_n
    | S m =>
        let loopm := loop_m m in
        fix loop_n n : Dack (S m) n :=
          match n with
          | O   => Dack_S_0 (loopm 1)
          | S n => Dack_S_S (loop_n n) (λ v hv, loopm v)
          end
    end.
There we discovered that hv, a proof of Gack (S m) n v, is unused.
This suggests that Dack could be simplified as proposed in the current
file. And without loss in Lemma ack_termination as just checked.
*)

Definition ack_expl m n := proj1_sig (ack_pwc m n (ack_termination_expl m n)).

(* Very small values as input provide much maller computation times *)
Time Compute ack_termination_expl 3 2. (* 0.004 s *)
Time Compute ack_expl 3 4. (* 0.002 s *)

(* Larger values can be computed *)
Time Compute ack_termination 9 9. (* 0.61 s *)
Time Compute ack_termination_expl 9 9. (* 2.3 s *)
Time Compute ack_expl 3 10. (* 9.6 s *)
Time Compute ack 3 10. (* 8.2 s *)
