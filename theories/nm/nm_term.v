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

Require Import Arith Lia Extraction Utf8. (* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ *)

Require Import induction.
Require Import nm_graph_def nm_fun nm_props_def nm_props.

Set Implicit Arguments.

(** Termination/totality by induction on ⟪e⟫ *)

Hint Resolve nm_dec : core.

Theorem 𝔻nm_total e : 𝔻nm e.
Proof.
  induction on e as IHe with measure ⟪e⟫.
  destruct e as [ | [ | u v w ] y z ].
  + apply 𝔻nm_1.
  + apply 𝔻nm_2; apply IHe; simpl; lia.
  + assert (D1 : 𝔻nm (ω v y z)) by auto.
    assert (D2 : 𝔻nm (ω w y z)) by auto.
    apply 𝔻nm_3 with D1 D2.
    apply IHe. 
    apply le_lt_trans with (2 := ce_size_special _ _ _ _ _).
    auto.
Qed.

Hint Resolve nm_normal nm_equiv : core.

Definition pnm e : { ne | normal ne ∧ e ~Ω ne }. 
Proof. exists (nm _ (𝔻nm_total e)); split; auto. Defined.

Extraction Inline nm.
Recursive Extraction pnm.

