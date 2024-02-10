(** DLW: ceci est un retravail d'un code initial de David Monniaux
         en factorisant le recurseur mutuel. On peut utiliser soit
         le récurseur de David, soit le récurseur standard. *) 

Require Import Utf8.

Unset Elimination Schemes.

Inductive ack2_spec : nat → nat → nat → Prop :=
| ack2_m0 {n} : ack2_spec 0 n (S n)
| ack2_mS {m n x y} : ack2i_spec m n x → ack2_spec m x y → ack2_spec (S m) n y

with ack2i_spec : nat → nat → nat → Prop :=
| ack2i_n0 {m} : ack2i_spec m 0 1
| ack2i_nS {m n x} : ack2_spec (S m) n x → ack2i_spec m (S n) x.

(** Deux inversion non-structurelles *)

Lemma ack2_spec_inv {m n y} :
      ack2_spec m n y
    → match m with
      | O   => S n = y
      | S m => ∃x, ack2i_spec m n x ∧ ack2_spec m x y
      end.
Proof. intros []; eauto. Qed.

Lemma ack2i_spec_inv {m n x} :
      ack2i_spec m n x 
    → match n with
      | O => 1 = x
      | S n => ack2_spec (S m) n x
      end.
Proof. now intros []. Qed.

(** Une inversion structurelle *)

Definition not0 n := match n with 0 => False | _ => True end.

(** ack2_spec_inv_S ne peut pas être écrite indépendement/factorisée
    car elle retourne un triplet dépendent, cf ack123.v *)

Definition ack2i_spec_inv_S {m n x} (a : ack2i_spec m (S n) x) : ack2_spec (S m) n x :=
  match a in ack2i_spec _ n _ return not0 n → ack2_spec _ (pred n) _ with
  | ack2i_n0   => λ C, match C with end
  | ack2i_nS h => λ _, h
  end I.

Section ack2_spec_ind.

  Variables (P Q : nat → nat → nat → Prop)
            (HP0 : ∀ {n}, P 0 n (S n))
            (HPS : ∀ {m n x y}, ack2i_spec m n x → Q m n x → ack2_spec m x y → P m x y → P (S m) n y)
            (HQ0 : ∀ {m}, Q m 0 1)
            (HQS : ∀ {m n x}, ack2_spec (S m) n x → P (S m) n x → Q m (S n) x).


  (* Ceci est le récurseur utilisé dans le code de David, que l'on factorise
     pour plus de lisibilité. Dans ce récurseur: 
     - ack2_spec_inv_S est inlinée (elle renvoit un triplet dépendant)
     - par contre ack2i_spec_inv peut elle être factorisée, cf ci-dessus *)

  Fixpoint ack2_spec_ind {m n x} (a : ack2_spec m n x) {struct a}  : P m n x :=
    match m return ack2_spec m _ _ → _ with
    |   0 => λ a, match ack2_spec_inv a in _ = x return P _ _ x with eq_refl => HP0 end
    | S m => λ a, match a in ack2_spec m _ _ return not0 m → P m _ _ with
                  | ack2_m0       => λ C, match C with end
                  | ack2_mS h1 h2 => λ _, HPS h1 (ack2i_spec_ind h1) h2 (ack2_spec_ind h2)
                  end I
    end a
  with ack2i_spec_ind {m n x} (a : ack2i_spec m n x) {struct a} : Q m n x :=
    match n return ack2i_spec _ n _ → _ with
    |   0 => λ a, match ack2i_spec_inv a in _ = n return Q _ _ n with eq_refl => HQ0 end
    | S n => λ a, let a' := ack2i_spec_inv_S a in HQS a' (ack2_spec_ind a')
    end a.

  (* Pour info, ceci est le récurseur mutuel standard *)
  Fixpoint ack2_spec_ind_std {m n x} (a : ack2_spec m n x) {struct a} : P m n x :=
    match a with
    | ack2_m0       => HP0
    | ack2_mS h1 h2 => HPS h1 (ack2i_spec_ind_std h1) h2 (ack2_spec_ind_std h2)
    end
  with ack2i_spec_ind_std {m n x} (a : ack2i_spec m n x) {struct a} : Q m n x :=
    match a with
    | ack2i_n0   => HQ0
    | ack2i_nS h => HQS h (ack2_spec_ind_std h)
    end.

End ack2_spec_ind.

(* La preuve de déterministe, par induction (mutuelle) structurelle le premier ack2_spec 
   puis inversion dépendante sur le deuxième *) 
Theorem ack2_spec_det_with_recursor m n r₁ r₂ : ack2_spec m n r₁ → ack2_spec m n r₂ → r₁ = r₂.
Proof.
  intros a; revert r₂; pattern m, n, r₁; revert m n r₁ a.
  apply ack2_spec_ind with (Q := λ m n r₁, ∀ r₂, ack2i_spec m n r₂ → r₁ = r₂).
  + now intros ? ? ->%ack2_spec_inv.
  + now intros ? ? ? ? _ IH1 _ IH2 ? (? & <-%IH1 & ?%IH2)%ack2_spec_inv.
  + now intros ? ? ->%ack2i_spec_inv.
  + now intros ? ? ? _ IH ? ?%ack2i_spec_inv%IH.
Qed.

