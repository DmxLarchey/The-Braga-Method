(**************************************************************)
(*   Copyright Dominique Larchey-Wendling    [*]              *)
(*             Jean-François Monin           [+]              *)
(*                                                            *)
(*            [*] Affiliation LORIA -- CNRS                   *)
(*            [+] Affiliation VERIMAG - Univ. Grenoble-Alpes  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Utf8. (* → λ ∀ ∃ ↔ ∧ ∨ *)

Set Implicit Arguments.

(** The type of If-then-else expressions *)

Inductive cexpr : Set := At : cexpr | If : cexpr → cexpr → cexpr → cexpr.

Notation α := At.
Notation ω := If.
Notation Ω := cexpr.

(** The graph 𝔾 : Ω -> Ω -> Prop of nm 
    with notation x ⟼ y for (𝔾 x y)
 *)

Reserved Notation "x '⟼n' y" (at level 70, no associativity).

Inductive 𝔾nm : Ω → Ω → Prop :=
  | in_gnm_0 :     α ⟼n α
  | in_gnm_1 y ny z nz : 
                   y ⟼n ny 
                 → z ⟼n nz 
                 → ω α y z ⟼n ω α ny nz
  | in_gnm_2 u v w y z na nb nc : 
                   ω v y z ⟼n na 
                 → ω w y z ⟼n nb 
                 → ω u na nb ⟼n nc
                 → ω (ω u v w) y z ⟼n nc
where "x ⟼n y" := (𝔾nm x y).

(** 𝔾nm is a functional/deterministic graph *)

Fact 𝔾nm_fun e n1 n2 : e ⟼n n1  →  e ⟼n n2  →  n1 = n2.
Proof.
  intros H; revert H n2.
  induction 1 as [ 
                 | y ny z nz H1 IH1 H2 IH2
                 | u v w y z na nb nc H1 IH1 H2 IH2 H3 IH3 ]; inversion 1; subst; auto.
  - f_equal; auto.
  - apply IH1 in H9; subst.
    apply IH2 in H10; subst.
    apply IH3 in H11; subst.
    auto.
Qed.