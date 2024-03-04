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

Require Import Arith Lia Utf8. (* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ *)

Require Import nm_graph_def nm_fun nm_props_def.

Set Implicit Arguments.

Theorem nm_equiv e D : e ~Ω nm e D.
Proof.
  generalize (nm _ D) (nm_spec D); clear D.
  induction 1 as [ 
                 |
                 | a b c y z nb nc na H1 IH1 H2 IH2 H3 IH3 ]; auto.
  apply equiv_trans with (1 := in_eq_0 _ _ _ _ _),
        equiv_trans with (2 := IH3),
        in_eq_1; auto.
Qed.

Theorem nm_normal e D : normal (nm e D).
Proof. 
 generalize (nm _ D) (nm_spec D); clear D.
 induction 1; auto.
Qed.

#[export] Hint Resolve ce_size_sub_2 ce_size_sub_3 ce_size_mono ce_size_smono_1 : core.
  
(** nm preserves the measure *)

Theorem nm_dec e D : ⟪nm e D⟫ ≤ ⟪e⟫.
Proof.
  generalize (nm _ D) (nm_spec D); clear D.
  induction 1 as [ 
                 | y ny z nz H1 IH1 H2 IH2
                 | a b c y z nb nc na H1 IH1 H2 IH2 H3 IH3 ]; auto.
  apply le_trans with (1 := IH3),
        le_trans with (2 := ce_size_special _ _ _ _ _); auto.
Qed.
