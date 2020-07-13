(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Bool Utf8. (* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ ≠ *)

Require Import unif_graph_def.

Set Implicit Arguments.

Unset Elimination Schemes.

Inductive 𝔻unif : Λ → Λ → Prop :=
  | in_du_0 c m n :      𝔻unif (φ c) (m⋄n)
  | in_du_1 c m n :      𝔻unif (m⋄n) (φ c)
  | in_du_2 c v :        𝔻unif (φ c) (µ v)
  | in_du_3 v m n :      𝔻unif (m⋄n) (µ v)
  | in_du_4 v m :        𝔻unif (µ v) m
  | in_du_5 c d :        𝔻unif (φ c) (φ d)
  | in_du_6 m n m' n' :  m ⋉ m' ⟼u None
                       → 𝔻unif m m'  
                       → 𝔻unif (m⋄n) (m'⋄n')
  | in_du_7 m n m' n' :  (∃σ, m ⋉ m' ⟼u Some σ)
                       → 𝔻unif m m' 
                       → (∀σ, m ⋉ m' ⟼u Some σ → 𝔻unif n⦃σ⦄ n'⦃σ⦄)
                       → 𝔻unif (m⋄n) (m'⋄n').

Set Elimination Schemes.

(** The domain containes the projection of the graph 
    This check is not needed anywhere, could be removed *)

Local Fact 𝔾unif_𝔻unif u v : (∃r, 𝔾unif u v r) → 𝔻unif u v.
Proof.
  intros (r & Hr); revert Hr.
  induction 1 as [ c m n 
                 | c m n 
                 | c x 
                 | m n x H1 
                 | m n x H1 
                 | x m H1
                 | x m H1
                 | c d H1
                 | c d H1
                 | m m' n n' H1 IH1
                 | m m' n n' σ H1 IH1 H2 IH2
                 | m m' n n' σ υ H1 IH1 H2 IH2
                 ].
  + constructor 1; exists c, m, n; auto.
  + constructor 2; exists c, m, n; auto.
  + constructor 3; exists c, x; auto.
  + constructor 4; exists m, n, x; auto.
  + constructor 4; exists m, n, x; auto.
  + constructor 5; exists x; auto.
  + constructor 5; exists x; auto.
  + constructor 6; exists c, d; auto.
  + constructor 6; exists c, d; auto.
  + constructor 7; auto.
  + constructor 8; auto.
    * exists σ; auto. 
    * intros s Hs.
      generalize (𝔾unif_fun Hs H1); inversion 1; subst; auto.
  + constructor 8; auto.
    * exists σ; auto.
    * intros s Hs.
      generalize (𝔾unif_fun Hs H1); inversion 1; subst; auto.
Qed.

Section unif.

  (** The actual recursive definition of unif, fully dependent, 
      with computational contents separated from logical contents *)

  (* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ ≠ *)
  
  Let Fixpoint unif_pwc u v (D : 𝔻unif u v) { struct D } : { r | u ⋉ v ⟼u r }.
  Proof. refine (
    match u as u' return u = u' → _ with
      | µ x   => λ E D, match occ_check_dec x v with
        | left H  => exist _ None _
        | right H => exist _ (Some ((x,v)::∅)) _
      end
      | φ c => λ E D, match v with
        | µ y => λ D, exist _ (Some ((y,u)::∅)) _
        | φ d => λ D, match eqC_dec c d with
          | left H  => exist _ (Some ∅) _
          | right H => exist _ None _
        end
        | m'⋄n' => λ D, exist _ None _
      end D
      | m⋄n  => λ E D, match v with
        | µ y => λ D, match occ_check_dec y u with
          | left H  => exist _ None _
          | right H => exist _ (Some ((y,u)::∅)) _
        end
        | φ d => λ D, exist _ None _
        | m'⋄n' => λ D, 
        let (r,Cr) := @unif_pwc m m' _
        in match r with
          | Some r => λ Cr,
          let (s,Cs) := @unif_pwc n⦃r⦄ n'⦃r⦄ _
          in match s with
            | Some s => λ Cs, exist _ (Some (r o s)) _
            | None   => λ Cs, exist _ None _
          end Cs
          | None   => λ Cr, exist _ None _ 
        end Cr
      end D
    end eq_refl D).
    1-11: cycle 9.
    1: inversion D; trivial.
    1: inversion D; auto; generalize (𝔾unif_fun Cr H2); discriminate.
    11: constructor 11 with r; trivial.
    all: subst u; constructor; trivial.
  Qed.

  (** Now we project to get two projections *)

  Definition unif u v (D : 𝔻unif u v) := proj1_sig (@unif_pwc _ _ D).

  Fact unif_spec u v D : u⋉v ⟼u @unif u v D.
  Proof. apply (proj2_sig _). Qed.

End unif.

Hint Resolve unif_spec : core.

(** The virtual constructions of the domain *)

Fact 𝔻unif_1 c m n : 𝔻unif (φ c) (m⋄n).     Proof. constructor. Qed.
Fact 𝔻unif_2 c m n : 𝔻unif (m⋄n) (φ c).     Proof. constructor. Qed.
Fact 𝔻unif_3 c x :   𝔻unif (φ c) (µ x).     Proof. constructor. Qed.
Fact 𝔻unif_4 m n x : 𝔻unif (m⋄n) (µ x).     Proof. constructor. Qed.
Fact 𝔻unif_5 x t :   𝔻unif (µ x) t.         Proof. constructor. Qed.
Fact 𝔻unif_6 c d :   𝔻unif (φ c) (φ d).     Proof. constructor. Qed.

(* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ ≠ *)

Fact 𝔻unif_7 m n m' n' (D : 𝔻unif m m') : 
       unif D = None → 𝔻unif (m⋄n) (m'⋄n').
Proof. intros H; constructor 7; auto; rewrite <- H; auto. Qed.

Fact 𝔻unif_8 m n m' n' (D : 𝔻unif  m m') σ : 
       unif D = Some σ → 𝔻unif n⦃σ⦄ n'⦃σ⦄ → 𝔻unif (m⋄n) (m'⋄n').
Proof.
  intros H1 D2; constructor 8; auto.
  + exists σ; rewrite <- H1; auto. 
  + intros s' Hs'.
    generalize (𝔾unif_fun Hs' (unif_spec D)).
    rewrite H1; inversion 1; subst; auto.
Qed.

Section 𝔻unif_rect.

  (* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ ≠ *)

  Variable   P   : ∀ u v, 𝔻unif u v → Type.

  Hypothesis HPi : ∀ u v (D1 D2 : 𝔻unif u v), P D1 → P D2.

  Hypothesis HP1 : ∀ c m n, P (𝔻unif_1 c m n).
  Hypothesis HP2 : ∀ c m n, P (𝔻unif_2 c m n).
  Hypothesis HP3 : ∀ c x,   P (𝔻unif_3 c x).
  Hypothesis HP4 : ∀ m n x, P (𝔻unif_4 m n x).
  Hypothesis HP5 : ∀ x m,   P (𝔻unif_5 x m).
  Hypothesis HP6 : ∀ c d,   P (𝔻unif_6 c d).
  Hypothesis HP7 : ∀ m n m' n' (D1 : 𝔻unif m m') (ID1 : P D1) (H1 : unif D1 = None), P (𝔻unif_7 n n' D1 H1).
  Hypothesis HP8 : ∀ m n m' n' (D1 : 𝔻unif m m') (ID1 : P D1) σ (H1 : unif D1 = Some σ) 
                               (D2 : 𝔻unif n⦃σ⦄ n'⦃σ⦄) (ID2 : P D2), P (𝔻unif_8 _ _ D1 H1 D2).

  Fixpoint 𝔻unif_rect u v (D : 𝔻unif u v) { struct D } : P D.
  Proof.
    destruct u as [ x | c | m n ].
    + apply HPi with (1 := HP5 _ _).
    + destruct v as [ y | d | m' n' ].
      * apply HPi with (1 := HP3 _ _).
      * apply HPi with (1 := HP6 _ _).
      * apply HPi with (1 := HP1 _ _ _).
    + destruct v as [ y | d | m' n' ].
      * apply HPi with (1 := HP4 _ _ _).
      * apply HPi with (1 := HP2 _ _ _).
      * assert (𝔻unif m m') as D'. 
        { inversion D; trivial. }
        case_eq (unif D').
        - intros σ Hσ.
          refine (HPi _ (HP8 _ _ (𝔻unif_rect m m' D') Hσ (𝔻unif_rect _ _ _))).
          inversion D; trivial.
          ++ exfalso.
             rewrite (𝔾unif_fun (unif_spec D') H2) in Hσ.
             discriminate.
          ++ apply H5; rewrite <- Hσ; apply unif_spec.
        - intros H.
          apply HPi with (1 := HP7 _ _ (𝔻unif_rect m m' D') H).
  Qed.

End 𝔻unif_rect.

