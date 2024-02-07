(** DLW: ceci est un retravail d'un code initial de David Monniaux *)
(** Le schéma suivi pour regrouper les composantes de certains constructeurs
    dans un inductif auxiliaire (ack2_spec) est apparenté au schéma suivi
    pour les petites inversions à base d'inductifs partiels exposées en 2021
    https://www-verimag.imag.fr/~monin/Talks/sir.pdf
    et évoquées à TYPES'22
    https://www-verimag.imag.fr/~monin/Publis/Docs/types22-smallinv.pdf

    L'objectif ici est de permettre d'accéder dans le même match
    aux deux sous-termes de la spec de ack (S m) (S n) y
    pour alléger l'écriture du récurseur.
 *)

(* JFM -> DLW : le résumé ci-dessus correspond à ma perception, tu vérifies
   quand même que cela te va, ou tu rectifies ? *)

Require Import Utf8.

Unset Elimination Schemes.

(* On garde la forme existentielle ici, avec un prédicat spécialisé 
   en lieu et place de (∃x, ack2i_spec m n x ∧ ack2_spec m x y),
   ck ack2_ack2i.v *)
(* JFM -> DLW : typo ligne juste avant ? *)
Inductive ack1_spec : nat → nat → nat → Prop :=
| ack1_m0 {n} : ack1_spec 0 n (S n)
| ack1_mS {m n y} : ack2_spec m n y → ack1_spec (S m) n y
with      ack2_spec : nat → nat → nat → Prop :=
| ack2_in {m n y x} : ack3_spec m n x → ack1_spec m x y → ack2_spec m n y
with      ack3_spec : nat → nat → nat → Prop :=
| ack3_n0 {m} : ack3_spec m 0 1
| ack3_nS {m n x} : ack1_spec (S m) n x → ack3_spec m (S n) x.

(* Le constructeur alternatif, montrant que cette spec est équivalente
   à celle d'origine *)
Fact ack1_mS' {m n x y} : ack3_spec m n x → ack1_spec m x y → ack1_spec (S m) n y.
Proof. constructor 2; auto; econstructor; eauto. Qed.

Lemma ack1_spec_inv {m n y} :
      ack1_spec m n y
    → match m with
      | O   => S n = y
      | S m => ack2_spec m n y
      end.
Proof. now intros []. Qed.

Definition not0 n := match n with 0 => False | _ => True end.

Definition ack1_spec_inv_S {m n y} (a : ack1_spec (S m) n y) : ack2_spec m n y :=
  match a in ack1_spec m _ _ return not0 m → ack2_spec (pred m) _ _ with
  | ack1_m0   => λ C, match C with end
  | ack1_mS h => λ _, h
  end I.

(* Pas besoin d'inverser ack2, un simple match/destruct suffit *)

Lemma ack3_spec_inv {m n x} :
      ack3_spec m n x
    → match n with
      | O => 1 = x
      | S n => ack1_spec (S m) n x
      end.
Proof. now intros []. Qed.

Definition ack3_spec_inv_S {m n x} (a : ack3_spec m (S n) x) : ack1_spec (S m) n x :=
  match a in ack3_spec _ n _ return not0 n → ack1_spec _ (pred n) _ with
  | ack3_n0   => λ C, match C with end
  | ack3_nS h => λ _, h
  end I.

Section ack123_spec_ind.

  (** Ici le recurseur non standard, qui commence par un match sur m/n. *)

  Variables (P Q : nat → nat → nat → Prop)
            (HP0 : ∀ {n}, P 0 n (S n))
            (HPS : ∀ {m n x y}, ack3_spec m n x → Q m n x → ack1_spec m x y → P m x y → P (S m) n y)
            (HQ0 : ∀ {m}, Q m 0 1)
            (HQS : ∀ {m n x}, ack1_spec (S m) n x → P (S m) n x → Q m (S n) x).

  Fixpoint ack1_spec_ind_alt {m n x} (a : ack1_spec m n x) { struct a } : P m n x :=
    match m return ack1_spec m _ _ → _ with
    | 0   => λ a, match ack1_spec_inv a in _ = n return P _ _ n with eq_refl => HP0 end
    | S m => λ a, match ack1_spec_inv_S a with
                  | ack2_in h1 h2 => HPS h1 (ack3_spec_ind_alt h1) h2 (ack1_spec_ind_alt h2)
                  end
    end a
  with ack3_spec_ind_alt {m n x} (a : ack3_spec m n x) { struct a } : Q m n x :=
    match n return ack3_spec _ n _ → _ with
    | 0   => λ a, match ack3_spec_inv a in _ = n return Q _ _ n with eq_refl => HQ0 end
    | S n => λ a, HQS (ack3_spec_inv_S a) (ack1_spec_ind_alt (ack3_spec_inv_S a))
    end a.

  (* Le même avec 3 fixpoints mutuels *) 
  Fixpoint ack1_spec_ind_alt3 {m n x} (a : ack1_spec m n x) { struct a } : P m n x :=
    match m return ack1_spec m _ _ → _ with
    | 0   => λ a, match ack1_spec_inv a in _ = n return P _ _ n with eq_refl => HP0 end
    | S m => λ a, ack2_spec_ind_alt3 (ack1_spec_inv_S a)
    end a
  with ack2_spec_ind_alt3 {m n x} (a : ack2_spec m n x) { struct a } : P (S m) n x :=
    match a with
    | ack2_in h1 h2 => HPS h1 (ack3_spec_ind_alt3 h1) h2 (ack1_spec_ind_alt3 h2)
    end
  with ack3_spec_ind_alt3 {m n x} (a : ack3_spec m n x) { struct a } : Q m n x :=
    match n return ack3_spec _ n _ → _ with
    | 0   => λ a, match ack3_spec_inv a in _ = n return Q _ _ n with eq_refl => HQ0 end
    | S n => λ a, HQS (ack3_spec_inv_S a) (ack1_spec_ind_alt3 (ack3_spec_inv_S a))
    end a.

  (** Voici le récurseur standard, qui a le même type, mais pas le même algo. *)

  Fixpoint ack1_spec_ind_std {m n x} (a : ack1_spec m n x) { struct a } : P m n x :=
    match a with
    | ack1_m0   => HP0
    | ack1_mS h => match h with
                   | ack2_in h1 h2 => HPS h1 (ack3_spec_ind_std h1) h2 (ack1_spec_ind_std h2)
                   end
    end
  with ack3_spec_ind_std {m n x} (a : ack3_spec m n x) { struct a } : Q m n x :=
    match a with
    | ack3_n0   => HQ0
    | ack3_nS h => HQS h (ack1_spec_ind_std  h)
    end.

  (* Le même avec 3 fixpoints mutuels *) 
  Fixpoint ack1_spec_ind_std3 {m n x} (a : ack1_spec m n x) { struct a } : P m n x :=
    match a with
    | ack1_m0   => HP0
    | ack1_mS h => ack2_spec_ind_std3 h
    end
  with ack2_spec_ind_std3 {m n x} (a : ack2_spec m n x) { struct a } : P (S m) n x :=
    match a with
    | ack2_in h1 h2 => HPS h1 (ack3_spec_ind_std3 h1) h2 (ack1_spec_ind_std3 h2)
    end
  with ack3_spec_ind_std3 {m n x} (a : ack3_spec m n x) { struct a } : Q m n x :=
    match a with
    | ack3_n0   => HQ0
    | ack3_nS h => HQS h (ack1_spec_ind_std3  h)
    end.

End ack123_spec_ind.

(* La même preuve que ack1_spec_det mais avec le recurseur factorisé: on
   peut utiliser n'importe lequel entre ack1_spec_ind_{alt,std} *)
Theorem ack2_spec_det_with_recursor m n r₁ r₂ : ack1_spec m n r₁ → ack1_spec m n r₂ → r₁ = r₂.
Proof.
  intros a; revert r₂; pattern m, n, r₁; revert m n r₁ a.
  apply ack1_spec_ind_alt with (Q := λ m n r₁, ∀ r₂, ack3_spec m n r₂ → r₁ = r₂).
  + now intros ? ? ->%ack1_spec_inv.
  + intros ? ? ? ? _ IH1 _ IH2 ? H%ack1_spec_inv.
    destruct H as [ m n r₂ r H1 H2 ].
    apply IH1 in H1 as ->.
    now apply IH2 in H2 as ->.
  + now intros ? ? ->%ack3_spec_inv.
  + now intros ? ? ? _ IH ? ?%ack3_spec_inv%IH.
Qed.

