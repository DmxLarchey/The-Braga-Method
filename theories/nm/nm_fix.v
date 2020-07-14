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

Require Import Utf8. (* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ *)

Require Import nm_graph_def nm_fun.

(* Irrelevance and fixpoint properties of nm *)
  
Fact nm_pirr e D1 D2 : nm e D1 = nm e D2.
Proof. apply 𝔾nm_fun with e; apply nm_spec. Qed.

Fact nm_fix_1 : nm α 𝔻nm_1 = α.
Proof. apply 𝔾nm_fun with α; [ | constructor ]; apply nm_spec. Qed.

Fact nm_fix_2 y z D1 D2 : nm (ω α y z) (𝔻nm_2 D1 D2) = ω α (nm y D1) (nm z D2).
Proof. apply 𝔾nm_fun with (ω α y z); [ | constructor ]; apply nm_spec. Qed.

Fact nm_fix_3 u v w y z D1 D2 D3 : 
            nm (ω (ω u v w) y z) (𝔻nm_3 D1 D2 D3) 
          = nm (ω u (nm (ω v y z) D1) (nm (ω w y z) D2)) D3.
Proof. 
  apply 𝔾nm_fun with (ω (ω u v w) y z).
  + apply nm_spec.
  + constructor 3 with (nm _ D1) (nm _ D2); apply nm_spec.
Qed.
