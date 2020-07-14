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

(* List traversal from right to left *)

Require Import List Utf8.
Import ListNotations.

Require Import mark.

Reserved Notation "x '+:' y" (at level 59, left associativity, format "x +: y").

Fixpoint consr {A} (l : list A) (y : A) { struct l } : list A :=
  match l with
  | [] => [y]
  | x :: l => x :: l +: y
  end
where "x +: y" := (consr x y) : list_scope.

Inductive lr (A: Type) : Type :=
| Nilr : lr A
| Consr : list A → A → lr A
.

Arguments Nilr {A}.
Arguments Consr {A}.

Definition r2l {A} (r: lr A) : list A :=
  match r with
  | Nilr => []
  | Consr u z => u +: z
  end.

(* Simulating destruct from right to left *)
Fixpoint l2r {A} (l : list A) : lr A :=
  match l with
  | [] => Nilr
  | x :: lr =>
     match l2r lr with
     | Nilr => Consr [] x
     | Consr lg z => Consr (x :: lg) z
     end
  end.

(* Reflecting lists "constructed" with +:, using lr *)
Tactic Notation "reflect_lr_term" constr(t) :=
    let changed :=
    match t with
    | context C [@nil ?t] =>  context C [@r2l t Nilr]
    | context C [(?x +: ?y)]  =>  context C [r2l (Consr x y)]
    end in exact changed.
Tactic Notation "reflect_lr" :=
  match goal with |- ?concl => change ltac:(reflect_lr_term concl) end.
Tactic Notation "reflect_lr" "in" hyp(H) :=
  let t := type of H in change ltac:(reflect_lr_term t) in H.

(* The same at marked places *)
Tactic Notation "Mreflect_lr_term" constr(t) :=
    let changed :=
    match t with
    | context C [MARQ (@nil) ?t] =>  context C [@r2l t Nilr]
    | context C [MARQ (@consr) ?t ?x ?y]  =>  context C [@r2l t (Consr x y)]
    end in exact changed.
Tactic Notation "mreflect_lr" :=
  match goal with |- ?concl => change ltac:(Mreflect_lr_term concl) end.
Tactic Notation "mreflect_lr" "in" hyp(H) :=
  let t := type of H in change ltac:(Mreflect_lr_term t) in H.


Section sec_context.

Context {A: Type}.
Implicit Type l u v : list A.
Implicit Type x y z : A.
Implicit Type r : lr A.

(* -------------------------------------------------------------------------- *)
(* Easy key lemmas: r2l et l2r are inverse bijections *)

Lemma l2r_consr : ∀ u z, l2r (u +: z) = Consr u z.
Proof .
  intros u z; induction u as [ | x u Hu]; simpl; [ | rewrite Hu ]; reflexivity.
Qed.


Definition same_by_l2r_consr {P: lr A → Prop} {l u z} (E : l = u+:z) :
  P (l2r l) -> P (Consr u z).
Proof. intros p; rewrite <-l2r_consr, <-E; exact p. Defined.

Lemma rlr_id : ∀ r, l2r (r2l r) = r.
Proof. intros []; simpl; [reflexivity | apply l2r_consr]. Qed.

Corollary r2l_consr : ∀ r u z, r2l r = u +: z → r = Consr u z.
Proof.
  intros r u z e.
  rewrite <- (rlr_id r), e; apply l2r_consr.
Qed.


(*Definition lrl l := r2l (l2r l).*)
Notation lrl := (λ l, r2l (l2r l)).

Lemma lrl_id : ∀ l, lrl l = l.
Proof.
  induction l as [| x v Hv]; simpl.
  - reflexivity.
  - destruct (l2r v) as [| u z]; rewrite <- Hv; reflexivity.
Defined.

Ltac rewrite_lrl := cbv beta; rewrite lrl_id.

Corollary l2r_Nilr : ∀ l, l2r l = Nilr → l = [].
Proof.
  intros l e. reflect_lr. rewrite <- e. symmetry. apply lrl_id.
Qed.

Corollary l2r_Consr : ∀ l u z, l2r l = Consr u z → l = u +: z.
Proof.
  intros l u z e. reflect_lr. rewrite <- e. symmetry. apply lrl_id.
Qed.

(* Cast functions, in Prop and in Type *)
(* Using them constrain the use of eq_ind and eq_rect,
   hence a clearer view of the underlying reasoning *)
Definition up_llP (P: list A → Prop) u : P u → P (lrl u).
Proof. rewrite_lrl; exact (fun p => p). Defined.

Definition up_llT (P: list A → Type) u : P u → P (lrl u).
Proof. rewrite_lrl; exact (fun p => p). Defined.

Definition down_llP (P: list A → Prop) u : P (lrl u) → P u.
Proof. rewrite_lrl; exact (fun p => p). Defined.

Definition down_llT (P: list A → Type) u : P (lrl u) → P u.
Proof. rewrite_lrl; exact (fun p => p). Defined.


End sec_context.

Notation lrl := (λ l, r2l (l2r l)).

(* Adds in the goal a helper ∀ r, R (r2l (l2r l)) r  →  R l r *)
Ltac gen_help l R := generalize (λ y, down_llP (λ x, R x y) l).

