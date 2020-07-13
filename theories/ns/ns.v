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

Require Import Arith Lia Utf8 Extraction.

(** Target : nb of g steps to get some condition b

      let rec ns x = match b x with true => 0 | false => S (ns (g x))

   Algorithm using an accumulator

      let rec nsa x n = match b x with true => n | false => nsa (g x) (S n)

   We prove that ns computes the same result as nsa

   We characterize their domains with the below iterator 
         g↑n = g o g o ... o g   n times 
*)

(* The iterator, tail-recursive *)

Reserved Notation "g ↑ n" (at level 1, format "g ↑ n").
Fixpoint iter {X} g n (x : X) :=
  match n with 
    | 0   => x
    | S n => g↑n (g x)
  end
where "g ↑ n" := (iter g n).

(* A small tactic to eliminate goal where b = true and b = false appear as hypotheses *)

Tactic Notation "bool" "discr" := 
  try match goal with 
    | H: ?a = true , G: ?b = false |- _ => exfalso; now rewrite H in G 
  end.

Section ns_nsa.

Variable (X : Type) (g : X -> X) (b : X -> bool).

Unset Elimination Schemes.

Fact true_false {x} : x = true -> x = false -> False.
Proof. intros; bool discr. Qed.

(** The custom inductive domain of ns and nsa *)

(*
(* Coq knowledgeable users know that it is a better policy
   to put x as a parameter rather than an indice.
   This would allow a short-cut in projections
   as shown below in this comment, 
   but this would not suit more general situations.
*)
Inductive 𝔻ns (x: X) : Prop :=
  | 𝔻ns_tt : b x = true  → 𝔻ns x
  | 𝔻ns_ff : b x = false → 𝔻ns (g x) → 𝔻ns x
  .

Definition 𝜋_𝔻ns {x} (G : b x = false) (D : 𝔻ns x) :  𝔻ns (g x) :=
  match D with
  | 𝔻ns_tt _ E     => match true_false E G with end
  | 𝔻ns_ff _ _ Dgx => Dgx
  end.
*)

(* *This definition with x as an indice corresponds to the rules of the paper *)
Inductive 𝔻ns : X -> Prop :=
  | 𝔻ns_tt : ∀x, b x = true  → 𝔻ns x
  | 𝔻ns_ff : ∀x, b x = false → 𝔻ns (g x) → 𝔻ns x
  .

(** The inversion of constructor 𝔻ns_ff *)

Definition 𝜋_𝔻ns {x} (D : 𝔻ns x) : b x = false → 𝔻ns (g x) :=
  match D with
  | 𝔻ns_tt x E     => λ G, match true_false E G with end
  | 𝔻ns_ff x E Dgx => λ G, Dgx
  end.

Set Elimination Schemes.

Section sec_direct_ns.

(** First we define ns/nsa as structural fixpoint on 
    the domain predicate with a weak spec *)
  
(* "Let" in order to forget ns and nsa after this section *)  

Let
Fixpoint ns x (D : 𝔻ns x) : nat :=
  match b x as bx return b x = bx → _ with
  | true  => λ _, 0
  | false => λ G, S (ns (g x) (𝜋_𝔻ns D G))
  end eq_refl.

(* We get fixpoints equation by simpl!! *)
Let ns_fix_tt x E : ns x (𝔻ns_tt x E) = 0.
Proof. simpl; now rewrite E. Qed.

Let ns_fix_ff x E D : ns x (𝔻ns_ff x E D) = S (ns (g x) D).
Proof. simpl; now rewrite E. Qed.

Let
Fixpoint nsa x (n : nat) (D : 𝔻ns x) : nat :=
  match b x as bx return b x = bx → _ with
  | true  => λ _, n
  | false => λ G, nsa (g x) (S n) (𝜋_𝔻ns D G)
  end eq_refl.

Let nsa_fix_tt x n E : nsa x n (𝔻ns_tt x E) = n.
Proof. simpl; now rewrite E. Qed.

Let nsa_fix_ff x n E D : nsa x n (𝔻ns_ff x E D) = nsa (g x) (S n) D.
Proof. simpl; now rewrite E. Qed.

(* We can show this identity by structural recursion on D *)

Lemma ns_nsa_n_direct : ∀x n D, nsa x n D = ns x D + n.
Proof.
  refine (fix loop x n D { struct D } := _).
  destruct D as [ x E | x E D ]; simpl.
  - now rewrite E.
  - now rewrite loop, E, <- plus_n_Sm.
Qed.

Corollary ns_nsa_direct : ∀x (D: 𝔻ns x), nsa x 0 D = ns x D.
Proof. intros; now rewrite ns_nsa_n_direct, plus_n_O. Qed.

End sec_direct_ns.

(** We build a proof-irrelevant Type bounded eliminator for 𝔻ns *)

Section eliminator_for_𝔻ns.

  Variable P : ∀x, 𝔻ns x -> Type.

  Hypothesis (HPi : ∀x D1 D2, P x D1 → P x D2)
             (HP0 : ∀x E, P _ (𝔻ns_tt x E))
             (HP1 : ∀x E D, P _ D → P _ (𝔻ns_ff x E D)).

  Fixpoint 𝔻ns_rect x D { struct D } : P x D.
  Proof.
    case_eq (b x); intros G.
    + apply HPi with (1 := HP0 _ G).
    + apply HPi with (1 := HP1 _ G _ (𝔻ns_rect _ (𝜋_𝔻ns D G))).
  Qed.

End eliminator_for_𝔻ns.

(* The computational graph of ns *)

Reserved Notation "x '⟼ns' y" (at level 70, no associativity).
Inductive 𝔾ns : X → nat → Prop :=
  | in_grns_0 x   : b x = true               → x ⟼ns 0
  | in_grns_1 x o : b x = false → g x ⟼ns o → x ⟼ns S o
where "x ⟼ns o" := (𝔾ns x o).

(* The computational graph of nsa *)

Reserved Notation "x ';' n '⟼nsa' y" (at level 70, no associativity).
Inductive 𝔾nsa : X → nat → nat → Prop :=
  | in_grnsa_0 x n   : b x = true                       →  x;n ⟼nsa n
  | in_grnsa_1 x n o : b x = false  →  g x;S n ⟼nsa o  →  x;n ⟼nsa o
where "x ; n ⟼nsa o" := (𝔾nsa x n o).

(* Both graphs are deterministic/functional *)

Fact 𝔾ns_fun x u v : x ⟼ns u  →  x ⟼ns v  →  u = v.
Proof.
  intros H; revert H v.
  induction 1; inversion 1; auto; bool discr.
Qed.

Fact 𝔾nsa_fun x n u v : x;n ⟼nsa u  →  x;n ⟼nsa v  →  u = v.
Proof.
  intros H; revert H v.
  induction 1; inversion 1; auto; bool discr.
Qed.

Section pwc.

(** First we define ns/nsa as structural fixpoint over the
    custom domain predicate but here strongly specified wrt 
    their respective coputational graphs *)

Let
Fixpoint ns_pwc x (D : 𝔻ns x) : {o | x ⟼ns o}.
Proof. refine(
   match b x as bx return b x = bx → _ with
   | true  => λ G, exist _ 0 _
   | false => λ G, let (o,Co) := ns_pwc (g x) (𝜋_𝔻ns D G)
                   in exist _ (S o) _
   end eq_refl).
  + now constructor.
  + now constructor.
Qed.

Definition ns (x: X) D : nat := proj1_sig (ns_pwc x D).

Fact ns_spec x D : x ⟼ns ns x D.
Proof. apply (proj2_sig _). Qed.

Let Fixpoint nsa_pwc x n (D: 𝔻ns x) : {o | x;n ⟼nsa o}.
Proof. refine(
   match b x as bx return b x = bx → _ with
   | true =>  λ G, exist _ n _
   | false => λ G, let (o,Co) := nsa_pwc (g x) (S n) (𝜋_𝔻ns D G)
                   in exist _ o _
   end eq_refl).
  + now constructor.
  + now constructor.
Qed.

Definition nsa (x: X) (n: nat) D : nat := proj1_sig (nsa_pwc x n D).

Fact nsa_spec x n D : x;n ⟼nsa nsa x n D.
Proof. apply (proj2_sig _). Qed.

End pwc.

(* 𝔻ns cover all values where there is a possible output for ns *)

Fact ns_complete x : 𝔻ns x ↔ exists o, x ⟼ns o.
Proof.
  split.
  + intros D; exists (ns _ D); apply ns_spec.
  + intros (o & Co); revert Co.
    induction 1. 
    * now constructor 1.
    * now constructor 2.
Qed.

Fact ns_pirr {x} D1 D2 : ns x D1 = ns x D2.
Proof. apply (𝔾ns_fun x); apply ns_spec. Qed.

Fact ns_fix_tt x E : ns x (𝔻ns_tt x E) = 0.
Proof. apply 𝔾ns_fun with (1 := ns_spec _ _); now constructor. Qed.

Fact ns_fix_ff x E D : ns x (𝔻ns_ff x E D) = S (ns (g x) D).
Proof. apply 𝔾ns_fun with (1 := ns_spec _ _); constructor; auto; apply ns_spec. Qed.

(* (λ x _, 𝔻ns x) cover all values where there is a possible output for nsa *)

Fact nsa_complete x n : 𝔻ns x ↔ exists o, x;n ⟼nsa o.
Proof.
  split.
  + intros D; exists (nsa _ n D); apply nsa_spec.
  + intros (o & Co); revert Co.
    induction 1. 
    * now constructor 1.
    * now constructor 2.
Qed.

Fact nsa_pirr {x n} D1 D2 : nsa x n D1 = nsa x n D2.
Proof. apply (𝔾nsa_fun x n); apply nsa_spec. Qed.

Fact nsa_fix_tt x n E : nsa x n (𝔻ns_tt x E) = n.
Proof. apply 𝔾nsa_fun with (1 := nsa_spec _ _ _); now constructor. Qed.

Fact nsa_fix_ff x n E D : nsa x n (𝔻ns_ff x E D) = nsa (g x) (S n) D.
Proof. apply 𝔾nsa_fun with (1 := nsa_spec _ _ _); constructor; auto; apply nsa_spec. Qed.

(* Identity by proof-irrelevant dependent induction on D *)

Lemma nsa_ns_n x D : ∀n, nsa x n D = ns x D + n.
Proof.
  induction D as [ x D1 D2 | x E | x E D IH] using 𝔻ns_rect; intro n; simpl.
  + now rewrite (nsa_pirr _ D1), (ns_pirr _ D1).
  + now rewrite nsa_fix_tt, ns_fix_tt.
  + now rewrite nsa_fix_ff, ns_fix_ff, IH, <- plus_n_Sm.
Qed.

Corollary ns_nsa : ∀x (D: 𝔻ns x), nsa x 0 D = ns x D.
Proof. intros; now rewrite nsa_ns_n, plus_n_O. Qed.

(* Variant 1, by induction on the graph 𝔾ns *)

Lemma nsa_ns_n_𝔾ns : ∀x (D : 𝔻ns x) n, nsa x n D = ns x D + n.
Proof.
  intros x D n.
  generalize (ns x D) (ns_spec x D).
  intros o H; revert H n D.
  induction 1; intros n D; destruct D; bool discr.
  + now rewrite nsa_fix_tt.
  + now rewrite nsa_fix_ff, plus_Snm_nSm.
Qed.

(* Variant 2, by induction on the graph 𝔾nsa *)

Lemma nsa_ns_n_𝔾nsa : ∀x (D : 𝔻ns x) n, nsa x n D = ns x D + n.
Proof.
  intros x D n.
  generalize (nsa x n D) (nsa_spec x n D).
  intros o H; revert H D.
  induction 1; intros D; destruct D; bool discr.
  + now rewrite ns_fix_tt.
  + now rewrite ns_fix_ff, plus_Snm_nSm.
Qed.

Section termination.

(** m is the first nat such that b (g↑m x) = true *)

Definition is_first x m := 
       b (g↑m x) = true 
     ∧ forall k, k < m → b (g↑k x) = false.

Theorem ns_partially_correct x D : is_first x (ns x D).
Proof.
  generalize x (ns _ D) (ns_spec _ D); clear x D.
  induction 1 as [ x Ex | x u Ex _ [ H1 H2 ] ].
  + split; auto; intros; lia.
  + split; auto.
    intros [] ?; auto; apply H2; lia.
Qed.

(** m is the first nat above b such that b (g↑(m-n) x) = true *)

Definition is_first_above x n m := 
      n ≤ m 
    ∧ b (g↑(m-n) x) = true 
    ∧ ∀k, k+n < m → b (g↑k x) = false.

Theorem nsa_partially_correct x n D : is_first_above x n (nsa x n D).
Proof.
  revert n; induction D as [ x D1 D2 | x E | x E D IH ] using 𝔻ns_rect; intros n.
  + now rewrite (nsa_pirr _ D1).
  + rewrite nsa_fix_tt; split; [ | split ]; auto.
    * replace (n-n) with 0 by lia; auto.
    * intros; lia.
  + destruct (IH (S n)) as (H1 & H2 & H3).
    rewrite nsa_fix_ff; split; [ | split ]; try lia.
    * now replace (nsa _ (S n) D-n) with (S (nsa _ (S n) D - S n)) by lia.
    * intros [] ?; auto; apply H3; lia.
Qed.

(* find first under a given informative bounded *)

Theorem first_under_bound x n : b (g↑n x) = true → ∃m, is_first x m.
Proof.
  revert x; induction n as [ | n IHn ]; intros x Hx.
  + exists 0; split; auto; intros; lia.
  + case_eq (b x); intros H.
    * exists 0; split; auto; intros; lia.
    * destruct IHn with (1 := Hx) as (m & H1 & H2).
      exists (S m); split; auto.
      intros [] ?; auto; apply H2; lia.
Qed.

(* Domain of both ns and nsa:

          ns x and ns x n terminate 
      iff there is k s.t. b (g↑k x) = true 
*)

Theorem 𝔻ns_high_level x : 𝔻ns x ↔ ∃k, b (g↑k x) = true.
Proof.
  split.
  + intros D; exists (ns _ D); apply ns_partially_correct.
  + intros (n & Hn).
    destruct first_under_bound with (1 := Hn) as (m & Hm).
    clear n Hn; revert m x Hm.
    induction m as [ | n IHn ]; intros x (H1 & H2).
    * constructor 1; apply H1.
    * constructor 2.
      - apply (H2 0); lia.
      - apply IHn; split; auto.
        intros; apply (H2 (S _)); lia.
Qed.

End termination.

End ns_nsa.

Extract Inductive bool => "bool" [ "true" "false" ].

Recursive Extraction ns nsa.

