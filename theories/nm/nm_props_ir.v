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

Require Import nm_graph_def nm_fun nm_fix nm_props_def.

Set Implicit Arguments.

Theorem nm_equiv e D : e ~Ω @nm e D.
Proof.
  induction D as 
    [ e D1 D2 
    |
    | y z D1 ID1 D2 ID2 
    | a b c y z D1 ID1 D2 ID2 D3 ID3 
    ] using 𝔻nm_rect.
  + rewrite (nm_pirr _ _ D1); auto.
  + rewrite nm_fix_1; auto.
  + rewrite nm_fix_2; auto.
  + rewrite nm_fix_3.
    apply equiv_trans with (2 := ID3),
          equiv_trans with (1 := in_eq_0 _ _ _ _ _); auto.
Qed.

Theorem nm_normal e D : normal (nm e D).
Proof.
  induction D as 
    [ e D1 D2 
    |
    | y z D1 ID1 D2 ID2 
    | a b c y z D1 ID1 D2 ID2 D3 ID3 
    ] using 𝔻nm_rect.
  + rewrite (nm_pirr _ _ D1); auto.
  + rewrite nm_fix_1; constructor.
  + rewrite nm_fix_2; constructor; auto.
  + now rewrite nm_fix_3.
Qed.

Hint Resolve ce_size_sub_2 ce_size_sub_3 ce_size_mono ce_size_smono_1 : core.
  
(** nm preserves the measure *)

Theorem nm_dec e D : ⟪nm e D⟫ ≤ ⟪e⟫.
Proof.
  induction D as 
    [ e D1 D2 
    |
    | y z D1 ID1 D2 ID2 
    | a b c y z D1 ID1 D2 ID2 D3 ID3 
    ] using 𝔻nm_rect.
  + rewrite (nm_pirr _ _ D1); auto.
  + rewrite nm_fix_1; auto.
  + rewrite nm_fix_2; simpl; lia.
  + rewrite nm_fix_3.
    apply le_trans with (1 := ID3),
          le_trans with (2 := ce_size_special _ _ _ _ _); auto.
Qed.
