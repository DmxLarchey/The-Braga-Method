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

(* This is the variant following the approach of D. Moniaux.

   In this variant of the domain predicate, the output value
   of the nested call is recovered using an existential
   quantifier ∃v, favoured over a universal quantifier ∀v.

   This change has some (limited) consequences, mainly
 
   - we now need functionality of Gack to perform rewrite
     (this is a match on a proof of identity). This occurs
     in the third projection of the domain predicate;

   - and also, that the domain is included in the projection
     of the graph: Dack m n → ex (Gack m n), while proving
     termination. This can of course be proved using ack_pwc
     itself.

   DLW: I recall using a similar ∃-characterisation for
   another example (possibly f91? or maybe unification?) 
   in the early days of the discovery of the Braga method,
   but later decided it was more cumbersome to work with 
   that the ∀-characterisation.
   Not sure it works so well when the function is indeed
   partial and not total like Ackermann.
*)

Require Import Utf8 Extraction.

Inductive Gack : nat → nat → nat → Prop :=
  | Gack_0_n n       : Gack 0 n (1+n)
  | Gack_S_0 m o     : Gack m 1 o
                     → Gack (S m) 0 o
  | Gack_S_S m n v o : Gack (S m) n v
                     → Gack m v o
                     → Gack (S m) (S n) o.

Fact Gack_inv m n o :
        Gack m n o
      → match m, n with
        |   0 ,   _ => o = 1+n
        | S m ,   0 => Gack m 1 o
        | S m , S n => ∃v, Gack (S m) n v ∧ Gack m v o
        end.
Proof. destruct 1; eauto. Qed.

Lemma Gack_fun {m n o₁ o₂} : Gack m n o₁ → Gack m n o₂ → o₁ = o₂.
Proof.
  induction 1 as [ | | ? ? ? ? _ IH1 _ ? ] in o₂ |- *; intros G%Gack_inv; auto.
  destruct G as (? & <-%IH1 & ?); eauto.
Qed.

(* The modification is on the second rule 
   which is now ∃v, Gack (S m) n v ∧ Dack m v 
   instead of   ∀v, Gack (S m) n v → Dack m v 
   hence we get the rule

    Dack_S_S {m n} : Dack (S m) n
                   → (∃v, Gack (S m) n v ∧ Dack m v)
                   → Dack (S m) (S n)

   Notice that the ∃ can be stripped into

    Dack_S_S {m n} : Dack (S m) n
                   → ∀v, (Gack (S m) n v ∧ Dack m v)
                        → Dack (S m) (S n)
  
   or equivalently, permuting ∀v with → ahead
   and stripping away ∧ using Curry-Howard

    Dack_S_S {m n v} : Dack (S m) n
                     → Gack (S m) n v
                     → Dack m v
                     → Dack (S m) (S n)

   which is the version favoured by DM.

  Notice that all the variants can be worked out,
  not just the last one.
*)

(* We modify the domain Dack here, as explained above *)
Inductive Dack : nat → nat → Prop :=
  | Dack_0_n n       : Dack 0 n
  | Dack_S_0 {m}     : Dack m 1
                     → Dack (S m) 0
  | Dack_S_S {m n v} : Dack (S m) n
                     → Gack (S m) n v
                     → Dack m v
                     → Dack (S m) (S n).

Definition is_S_0 m n := match m, n with | S _, 0   => True | _, _ => False end.
Definition is_S_S m n := match m, n with | S _, S _ => True | _, _ => False end.

Definition Dack_pi1 {m} (d : Dack (S m) 0) : Dack m 1 :=
  match d in Dack m n return is_S_0 m n → Dack (pred m) _ with
  | Dack_0_n _   => λ C, match C with end
  | Dack_S_0 h   => λ _, h
  | Dack_S_S _ _ _ => λ C, match C with end
  end I.

Definition Dack_pi2 {m n} (d : Dack (S m) (S n)) : Dack (S m) n :=
  match d in Dack m n return is_S_S m n → Dack _ (pred n) with
  | Dack_0_n _   => λ C, match C with end
  | Dack_S_0 h   => λ C, match C with end
  | Dack_S_S h _ _ => λ _, h
  end I.

(* We modify the proof here. Notice that we need Gack_fun *)
Definition Dack_pi3 {m n} (d : Dack (S m) (S n)) : ∀{v}, Gack (S m) n v → Dack m v :=
  match d in Dack m n return is_S_S m n → ∀v, Gack _ (pred n) v → Dack (pred m) v with
  | Dack_0_n _   => λ C, match C with end
  | Dack_S_0 h   => λ C, match C with end
  | Dack_S_S _ hv d' => λ _ _ hw,
    match Gack_fun hv hw with
    | eq_refl => d' 
    end
  end I.

#[local] Hint Constructors Gack Dack : core.

(* Unchanged *)
Fixpoint ack_pwc m n (d : Dack m n) : sig (Gack m n).
Proof.
  refine(match m, n return Dack m n → sig (Gack m n) with
  |   0 ,   _ => λ _, exist _ (1+n) _
  | S m ,   0 => λ d, let (o,ho) := ack_pwc m 1 (Dack_pi1 d)     in
                      exist _ o _
  | S m , S n => λ d, let (v,hv) := ack_pwc (S m) n (Dack_pi2 d) in
                      let (o,ho) := ack_pwc m v (Dack_pi3 d hv)  in
                      exist _ o _
  end d); eauto.
Defined.

(* In this approach, we need the map Dack m n → ex (Gack m n), 
   hence we use ack_pwc *)
Lemma ack_termination m n : Dack m n.
Proof.
  induction m in n |- *; eauto.
  induction n; auto.
  destruct ack_pwc with (1 := IHn); eauto.
Qed.

(* Unchanged bellow *)

Definition ack m n := proj1_sig (ack_pwc m n (ack_termination m n)).

Lemma ack_spec m n : Gack m n (ack m n).
Proof. apply (proj2_sig _). Qed.

#[local] Hint Resolve ack_spec Gack_fun : core.

Fact ack_fix_0n n : ack 0 n = 1+n.
Proof. eauto. Qed.

Fact ack_fix_S0 m : ack (S m) 0 = ack m 1.
Proof. eauto. Qed.

Fact ack_fix_SS m n : ack (S m) (S n) = ack m (ack (S m) n).
Proof. eauto. Qed.

Extraction Inline ack_pwc.
Extraction ack.
