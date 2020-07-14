(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Bool Utf8. (* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ ≠ *)

Require Import unif_graph_def unif_fun.

Set Implicit Arguments.

(** Now proof-irrelevance and fixpoint equations *)

Fact unif_pirr u v (D1 D2 : 𝔻unif u v) : unif D1 = unif D2.
Proof. apply 𝔾unif_fun with u v; apply unif_spec. Qed.

Fact unif_fix_1 c m n : unif (𝔻unif_1 c m n) = None.
Proof. apply 𝔾unif_fun with (2 := in_gu_0 c m n), unif_spec. Qed.

Fact unif_fix_2 c m n : unif (𝔻unif_2 c m n) = None.
Proof. apply 𝔾unif_fun with (2 := in_gu_1 c m n), unif_spec. Qed.

Fact unif_fix_3 c x : unif (𝔻unif_3 c x) = Some ((x,φ c)::∅).
Proof. apply 𝔾unif_fun with (2 := in_gu_2 c x), unif_spec. Qed.

Fact unif_fix_4 m n x : x ≺ m⋄n → unif (𝔻unif_4 m n x) = None.
Proof. intros H; apply 𝔾unif_fun with (2 := in_gu_3 H), unif_spec. Qed.

Fact unif_fix_4' m n x : x ⊀ m⋄n → unif (𝔻unif_4 m n x) = Some ((x,m⋄n)::∅).
Proof. intros H; apply 𝔾unif_fun with (2 := in_gu_4 H), unif_spec. Qed.

Fact unif_fix_5 x m : x ≺ m → unif (𝔻unif_5 x m) = None.
Proof. intros H; apply 𝔾unif_fun with (2 := in_gu_5 _ _ H), unif_spec. Qed.

Fact unif_fix_5' x m : x ⊀ m → unif (𝔻unif_5 x m) = Some ((x,m)::∅).
Proof. intros H; apply 𝔾unif_fun with (2 := in_gu_6 _ _ H), unif_spec. Qed.

Fact unif_fix_6 c : unif (𝔻unif_6 c c) = Some ∅.
Proof. apply 𝔾unif_fun with (2 := in_gu_7 (eq_refl c)), unif_spec. Qed.

Fact unif_fix_6' c d : c ≠ d → unif (𝔻unif_6 c d) = None.
Proof. intros H; apply 𝔾unif_fun with (2 := in_gu_8 H), unif_spec. Qed.

Fact unif_fix_7 m n m' n' (D1 : 𝔻unif m m') (H1 : unif D1 = None) : 
            unif (𝔻unif_7 n n' D1 H1) = None.
Proof.
  assert (m⋉m' ⟼u None) as H2.
  { rewrite <- H1; apply unif_spec. }
  apply 𝔾unif_fun with (2 := in_gu_9 n n' H2), unif_spec. 
Qed.

Fact unif_fix_8 m n m' n' (D1 : 𝔻unif m m') σ (H1 : unif D1 = Some σ) (D2 : 𝔻unif  n⦃σ⦄ n'⦃σ⦄) : 
            unif D2 = None → unif (𝔻unif_8 _ _ D1 H1 D2) = None.
Proof.
  intros H2.
  assert (m⋉m' ⟼u Some σ) as H3.
  { rewrite <- H1; apply unif_spec. }
  assert (n⦃σ⦄ ⋉ n'⦃σ⦄ ⟼u None) as H4.
  { rewrite <- H2; apply unif_spec. }
  apply 𝔾unif_fun with (2 := in_gu_a _ _ H3 H4), unif_spec. 
Qed.

Fact unif_fix_8' m n m' n' (D1 : 𝔻unif m m') σ (H1 : unif D1 = Some σ) 
                           (D2 : 𝔻unif n⦃σ⦄ n'⦃σ⦄) υ : 
            unif D2 = Some υ → unif (𝔻unif_8 _ _ D1 H1 D2) = Some (σ o υ).
Proof.
  intros H2.
  assert (m⋉m' ⟼u Some σ) as H3.
  { rewrite <- H1; apply unif_spec. }
  assert (n⦃σ⦄ ⋉ n'⦃σ⦄ ⟼u Some υ) as H4.
  { rewrite <- H2; apply unif_spec. }
  apply 𝔾unif_fun with (2 := in_gu_b _ _ H3 H4), unif_spec. 
Qed.

(** Now we have unif, d_unif and their constructors, 
    the induction principle, fixpoint eqs and proof-irrelevance *)


