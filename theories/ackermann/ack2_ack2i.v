(** DLW: ceci est un retravail d'un code initial de David Monniaux *) 

Require Import Utf8.

Unset Elimination Schemes.

(* On garde la forme existencielle ici, au lieu de déplier et on 
   a donc un type mutuellement inductif imbriqué avec ex(ists) et
   and ("et" logique) *)
Inductive ack2_spec : nat → nat → nat → Prop :=
| ack2_m0 {n} : ack2_spec 0 n (S n)
| ack2_mS {m n y} : (∃x, ack2i_spec m n x ∧ ack2_spec m x y) → ack2_spec (S m) n y

with ack2i_spec : nat → nat → nat → Prop :=
| ack2i_n0 {m} : ack2i_spec m 0 1
| ack2i_nS {m n x} : ack2_spec (S m) n x → ack2i_spec m (S n) x.

(* Le constructeur alternatif *)
Fact ack2_mS' {m n x y} : ack2i_spec m n x → ack2_spec m x y → ack2_spec (S m) n y.
Proof. constructor 2; eauto. Qed.

Lemma ack2_spec_inv {m n y} :
      ack2_spec m n y
    → match m with
      | O   => y = S n
      | S m => ∃x, ack2i_spec m n x ∧ ack2_spec m x y
      end.
Proof. now intros []. Qed.

Definition not0 n := match n with 0 => False | _ => True end.

Definition ack2_spec_inv_S {m n y} (a : ack2_spec (S m) n y) : ∃x, ack2i_spec m n x ∧ ack2_spec m x y :=
  match a in ack2_spec m _ _ return not0 m → ∃_, ack2i_spec (pred m) _ _ ∧ ack2_spec (pred m) _ _ with
  | ack2_m0   => λ C, match C with end
  | ack2_mS h => λ _, h
  end I.

Lemma ack2i_spec_inv {m n x} :
      ack2i_spec m n x 
    → match n with
      | O => x = 1
      | S n => ack2_spec (S m) n x
      end.
Proof. now intros []. Qed.

Definition ack2i_spec_inv_S {m n x} (a : ack2i_spec m (S n) x) : ack2_spec (S m) n x :=
  match a in ack2i_spec _ n _ return not0 n → ack2_spec _ (pred n) _ with
  | ack2i_n0   => λ C, match C with end
  | ack2i_nS h => λ _, h
  end I.

(* La même idée de départ que DM:

     induction mutuelle structurelle sur SPEC1 (resp. SPECi1)

   mais on commence par un match sur m (resp. n) aussi lieu 
   d'un match sur SPEC1.

   On pourrait d'ailleurs faire ça aussi dans ce cas parce qu'on
   est dans Prop, càd utiliser le récurseur standard sur les
   inductif mutuel. C'est plus simple en fait, mais là ce n'est 
   plus les petites inversions *)
Fixpoint ack2_spec_det {m n r₁ r₂} (SPEC1 : ack2_spec m n r₁) (SPEC2 : ack2_spec m n r₂) {struct SPEC1 } : r₁ = r₂
   with  ack2i_spec_det {m n r₁ r₂} (SPECi1 : ack2i_spec m n r₁) (SPECi2 : ack2i_spec m n r₂) {struct SPECi1} : r₁ = r₂.
Proof.
  + destruct m as [ | m ].
    * apply ack2_spec_inv in SPEC1, SPEC2; simpl in *; now subst.
    * revert SPEC1 SPEC2.
      intros (x & SPECi1s & SPEC1s)%ack2_spec_inv_S          (* on a besoin de CE sous-terme strict *)
             (x' & SPECi2s & SPEC2s)%ack2_spec_inv.          (* mais pas de celui là *)
      apply ack2_spec_det with (1 := SPEC1s).                (* on utilise le sous-terme SPEC1s the SPEC1 *)
      now destruct (ack2i_spec_det _ _ _ _ SPECi1s SPECi2s). (* et aussi le sous-terme SPECi1s to SPEC1 *)
  + destruct n as [ | n ].
    * apply ack2i_spec_inv in SPECi1, SPECi2; simpl in *; now subst.
    * exact (ack2_spec_det _ _ _ _ (ack2i_spec_inv_S SPECi1) (ack2i_spec_inv SPECi2)).
Qed.

Section ack2_spec_ind.

  (** Ici on factorise le recurseur de la preuve précédente. Attention ce n'est pas
      le recurseur usuel qui procède par un match sur a en premier. *)

  Variables (P Q : nat → nat → nat → Prop)
            (HP0 : ∀ n, P 0 n (S n))
            (HPS : ∀ m n x y, ack2i_spec m n x → Q m n x → ack2_spec m x y → P m x y → P (S m) n y)
            (HQ0 : ∀ m, Q m 0 1)
            (HQS : ∀ m n x, ack2_spec (S m) n x → P (S m) n x → Q m (S n) x).

  Fixpoint ack2_spec_ind_alt m n x (a : ack2_spec m n x) { struct a } : P m n x
      with ack2i_spec_ind_alt m n x (a : ack2i_spec m n x) { struct a } : Q m n x.
  Proof.
    + destruct m as [ | m ].
      * now apply ack2_spec_inv in a as ->.
      * apply ack2_spec_inv_S in a as (y & H1 & H2).
        apply HPS with y; trivial.
        - now apply ack2i_spec_ind_alt.
        - now apply ack2_spec_ind_alt.
    + destruct n as [ | n ].
      * now apply ack2i_spec_inv in a as ->.
      * apply HQS; [ | apply ack2_spec_ind_alt ]; now apply ack2i_spec_inv_S.
  Qed.

  (** Voici le récurseur standard, qui a le même type, mais pas le même algo. *)

  Fixpoint ack2_spec_ind_std m n x (a : ack2_spec m n x) { struct a } : P m n x
      with ack2i_spec_ind_std m n x (a : ack2i_spec m n x) { struct a } : Q m n x.
  Proof.
    + destruct a as [ | m n y (x & []) ]; eauto.
    + destruct a; eauto.
  Qed.

End ack2_spec_ind.

(* La même preuve que ack2*_spec_det mais avec le recurseur factorisé: on
   peut utiliser n'importe lequel entre ack2_spec_ind_{alt,std} *)
Theorem ack2_spec_det_with_recursor m n r₁ r₂ : ack2_spec m n r₁ → ack2_spec m n r₂ → r₁ = r₂.
Proof.
  intros a; revert r₂; pattern m, n, r₁; revert m n r₁ a.
  apply ack2_spec_ind_alt with (Q := λ m n r₁, ∀ r₂, ack2i_spec m n r₂ → r₁ = r₂).
  + now intros ? ? ->%ack2_spec_inv.
  + now intros ? ? ? ? _ IH1 _ IH2 ? (? & <-%IH1 & ?%IH2)%ack2_spec_inv.
  + now intros ? ? ->%ack2i_spec_inv.
  + now intros ? ? ? _ IH ? ?%ack2i_spec_inv%IH.
Qed.

(*** On garde ça pour la petite histoire *)

(* L'inversion a une forme "étrange" ici car la valeur de
   retour doit être un triplet dépendant de la forme
           exists x, P x /\ Q x 
   Donc on lui donne la forme d'un principe d'induction *)
Definition ack_spec_inv_S' (P : nat → nat → Prop) m n y : 
       (∀x, ack2i_spec m n x → ack2_spec m x y → P n y)
      → ack2_spec (S m) n y → P n y := λ f a,
  match a in ack2_spec m' _ _ return not0 m' → (∀x, ack2i_spec (pred m') _ x → ack2_spec (pred m') x _ → P _ _) → P _ _ with
  | ack2_m0                             => λ C _, match C with end
  | ack2_mS (ex_intro _ _ (conj h1 h2)) => λ _ f, f _ h1 h2
  end I f.

