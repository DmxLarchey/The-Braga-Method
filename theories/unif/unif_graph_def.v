(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* A "real" algorithm with nested recursion, unification

   µ v : is a variable (term)
   φ c : is a constant (term)
   m⋄n : is a compound term

   occ-check x (µ _)   = false
   occ-check x (φ _)   = false
   occ-check x (M  N)  = (µ x =? m) 
                      or (µ x =? n) 
                      or occ-check x m 
                      or occ-check x n

   unify (µ v) m       = if occ-check v m 
                         then None 
                         else Some [(v,m)]

   unify (φ c) (µ v)   = Some [(v,φ c)]

   unify (φ c) (φ d)   = if c =? d 
                         then Some [] 
                         else None

   unify (φ c) (_⋄_)   = None

   unify (_⋄_) (φ c)   = None

   unify (m⋄n) (µ v)   = if occ-check v (m⋄n) 
                         then None
                         else Some [(v,m⋄n)]

   unify (m⋄n) (m'⋄n') = match unify m m' with
                           | None   ⇒ None
                           | Some σ ⇒ match unify (σ n) (σ n') with
                                   | None   ⇒ None
                                   | Some υ ⇒ Some (σ o υ)


  From http://www21.in.tum.de/~krauss/function/function.pdf
  
  orig algo from Z. Manna, R. Waldinger, 
  
  "Deductive synthesis of the unification algorithm"
  
  https://www.sri.com/sites/default/files/uploads/publications/pdf/689.pdf

  We synthesize something close to ...

  Inductive d_unif : trm -> trm -> Prop := 
    | d_unif_1 : forall c m n,          d_unif (φ c) (m⋄n)
    | d_unif_2 : forall c m n,          d_unif (m⋄n) (φ c)
    | d_unif_3 : forall c x,            d_unif (φ c) (µ x)
    | d_unif_4 : forall m n x,          d_unif (m⋄n) (µ x)
    | d_unif_5 : forall x t,            d_unif (µ x) t
    | d_unif_6 : forall c d,            d_unif (φ c) (φ d)
    | d_unif_7 : forall m n m' n' D1,   unif m m' D1 = None     
                                     -> d_unif (m⋄n) (m'⋄n')
    | d_unif_8 : forall m n m' n' D1 σ, unif m m' D1 = Some σ 
                                     -> d_unif (subst σ n) (subst σ n') 
                                     -> d_unif (m°n) (m'⋄n')
  with Fixpoint unif m n (D : d_unif m n) := 
  match D with
    | d_unif_1 c m n => None
    | d_unif_2 c m n => None
    | d_unif_3 c x   => Some ((x,φ c)::∅)
    | d_unif_4 m n x => if occ_check x (m ⋄ n) then None else Some ((x,m⋄n)::∅)
    | d_unif_5 x m   => if occ_check x m       then None else Some ((x,m)::∅)
    | d_unif_6 c d   => if c =? d then Some ∅ else None 
    | d_unif_7 _ _ _ _ _ _ => None
    | d_unif_8 m n m' n' D1 σ H1 D2 => match unif (subst σ n) (subst σ n') D2 with
                                         | None    => None
                                         | Some υ => Some (σ o υ)
                                       end
  end.

*)

Require Import List Bool Utf8. (* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ *)

Set Implicit Arguments.

(** Small list goodies *)

Infix "∈" := In (at level 70, no associativity).
Notation "x ∉ l" := (¬ x ∈ l) (at level 70, no associativity).
Infix "⊆" := incl (at level 70, no associativity).

Tactic Notation "destruct" "∈" "at" hyp(H) :=
  repeat match type of H with 
    | In _ (_ ++ _)  => apply in_app_or in H; destruct H as [ H | H ]
    | In _ (_ :: _)  => destruct H as [ H | H ]
  end.

Parameter (𝓥  : Type) (eqV : 𝓥  → 𝓥  → bool) (eqV_spec : ∀ x y, eqV x y = true ↔ x = y).
Parameter (𝓒  : Type) (eqC : 𝓒  → 𝓒  → bool) (eqC_spec : ∀ x y, eqC x y = true ↔ x = y).

(** A type of constants and a type of variables, both discrete *)

Lemma eq_bool_dec {X} (eqb : X → X → bool) :
         (∀ x y, eqb x y = true ↔ x = y)
      -> (∀ x y : X, { x=y } + { x≠y }).
Proof.
  intros H x y; generalize (H x y).
  refine (match eqb x y with true => _ | false => _ end); intros [ H1 H2 ].
  + left; auto.
  + right; intros ->; now specialize (H2 eq_refl).
Qed.

Fact eqV_dec (x y : 𝓥 ) : { x=y } + { x≠y }.
Proof. apply eq_bool_dec with (1 := eqV_spec). Qed.

Fact eqC_dec : forall x y : 𝓒 , { x=y } + { x≠y }.
Proof. apply eq_bool_dec with (1 := eqC_spec). Qed.

(** The type of terms, ie binary trees built from C or V as leaves *)

Inductive trm : Type := 
  | Var : 𝓥  → trm
  | Cst : 𝓒  → trm
  | App : trm → trm → trm.

(** Compact notations *)

Notation Λ := trm.
Notation µ := Var.
Notation φ := Cst.
Notation "a ⋄ b" := (App a b) (at level 61, left associativity, format "a ⋄ b").

(** The inversion lemma (injectivity) for _⋄_ = _⋄_ and a tactic for it *)

(* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ ≠ *)

Fact term_eq_app_inv m n m' n' : m⋄n = m'⋄n' → m = m' ∧ n = n'.
Proof. now inversion 1. Qed.

Tactic Notation "trm" "eq" "inv" hyp(H) "as" ident(E1) ident(E2) :=
  apply term_eq_app_inv in H; destruct H as [ E1 E2 ].

(** Various equality deciders *)

Hint Resolve eqC_dec eqV_dec : core.

Definition trm_eq_dec (u v : Λ) : { u=v } + { u≠v }.
Proof. decide equality. Qed.

(* Implemented with tight control of computational behavior because 
   it is extracted *)

Definition eq_Var_b x m : bool :=
  match m with 
    | µ y => if eqV_dec x y then true else false
    | _   => false
  end.
 
Fact eq_Var_b_spec x m : eq_Var_b x m = true ↔ µ x = m.
Proof.
  destruct m as [ y | | ]; simpl; try (split; discriminate).
  destruct (eqV_dec x y); subst; split; try tauto; try discriminate.
  now inversion 1.
Qed.

(* We use the Boolean decider for better extraction *)

Definition eq_Var_dec (x : 𝓥 ) (t : Λ) : { µ x=t } + { µ x≠t }.
Proof.
  generalize (eq_Var_b_spec x t).
  destruct (eq_Var_b x t); intros [ H1 H2 ]; try tauto.
  right; intros <-.
  now specialize (H2 eq_refl).
Qed.

(** Term size and variable list *)

Reserved Notation "⟦ x ⟧" (at level 1, format "⟦ x ⟧").

Fixpoint trm_size t :=
  match t with
    | m⋄n => 1+⟦m⟧+⟦n⟧
    | _   => 0
  end
where "⟦ t ⟧" := (trm_size t).

Reserved Notation "⟪ x ⟫" (at level 1, format "⟪ x ⟫").

Fixpoint trm_vars t := 
  match t with
    | µ x => x::nil
    | φ _ => nil 
    | m⋄n => ⟪m⟫ ++ ⟪n⟫
  end
where "⟪ t ⟫" := (trm_vars t).

(** Occur check, see below for charact. vs var list *)

(* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ ≠ *)

Reserved Notation "x ≺ t" (at level 70, no associativity).

Fixpoint occ_check (x : 𝓥 ) (t : Λ) :=
  match t with
    | m⋄n => µ x=m ∨ µ x=n ∨ x ≺ m ∨ x ≺ n
    | _   => False
  end
where "x ≺ t" := (occ_check x t).

Notation "x ⊀ t" := (~ x ≺ t) (at level 70).

(* x occur checks in m is m is not µx and x belongs to the variables of m *)
 
Fact trm_vars_occ_check x m : x ≺ m ↔ m≠µ x ∧ x ∈ ⟪m⟫.
Proof.
  induction m as [ y | c | m Hm n Hn ].
  + simpl.
    split; try tauto.
    intros (H1 & [ H2 | [] ]); subst; tauto.
  + simpl; tauto.
  + simpl; rewrite Hm, Hn.
    split.
    * intros [|[|[|]]]; split; try discriminate;
        subst; rewrite in_app_iff; simpl; tauto.
    * intros (_ & H).
      destruct ∈ at H.
      - destruct (trm_eq_dec m (µ x)); subst; tauto.
      - destruct (trm_eq_dec n (µ x)); subst; tauto.
Qed.

Fact trm_vars_nocc_check x m : x ⊀ m ↔ m=µ x ∨ x ∉ ⟪m⟫.
Proof.
  rewrite trm_vars_occ_check.
  destruct (trm_eq_dec m (Var x)); tauto.
Qed.

(* Careful Boolean implementation for better extraction *)

Reserved Notation "x '≺?' t" (at level 1, no associativity).

Fixpoint occ_check_b (x : 𝓥 ) (t : Λ) :=
  match t with
    | µ _ => false
    | φ _ => false 
    | m⋄n => eq_Var_b x m || eq_Var_b x n || x ≺? m || x ≺? n
  end
where "x ≺? t" := (occ_check_b x t).

Fact occ_check_b_spec x t : x ≺? t = true ↔ x ≺ t.
Proof.
  induction t as [ y | c | m IHm n IHn ]; simpl; try easy.
  rewrite !orb_true_iff, !eq_Var_b_spec, IHm, IHn; tauto.
Qed.
 
(* We implement occ_check decision using the Boolean function 
   for better extraction, because this one is used in the
   code of unif below *)
 
Definition occ_check_dec x t : { x ≺ t } + { x ⊀ t }.
Proof.
  generalize (occ_check_b_spec x t).
  refine (match x ≺? t with 
    | true => _
    | false => _
  end); intros [ H1 H2 ]; try tauto.
  right; intro H; apply H2 in H; discriminate.
Qed.

(** // Substitutions of variables and then inside terms *)

Notation Σ := (list (𝓥 *Λ)).  (* the type of substitutions *)
Notation "∅" := (@nil _).     (* Notation for the empty/identity substitution *)

Reserved Notation "σ ↑ x" (at level 61, format "σ ↑ x").

(* We avoid unicode in extracted terms because 
   it does not mix well with OCaml. So here
   the letter s is used instead of σ *)

Fixpoint subst_var s (x : 𝓥 ) : option Λ :=
  match s with 
    | ∅      => None
    | (y,t)::s => if eqV_dec x y then Some t else s↑x
  end
where "σ ↑ x" := (subst_var σ x).

(* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ ≠ *)

Fact subst_var_spec σ x : { m | σ↑x = Some m ∧ (x,m) ∈ σ } 
                        + { σ↑x = None ∧ ∀m, (x,m) ∉ σ }.
Proof.
  induction σ as [ | (y,m) σ IHσ ].
  + right; simpl; tauto.
  + simpl.
    destruct (eqV_dec x y) as [ H | H ].
    * left; exists m; subst; tauto.
    * destruct IHσ as [ (n & H1 & H2) | (H1 & H2) ].
      - left; exists n; tauto.
      - right; split; auto.
        intros n [ H3 | H3 ].
        ++ destruct H; inversion H3; auto.
        ++ revert H3; apply H2.
Qed.

Reserved Notation "t ⦃ s ⦄" (at level 1, left associativity, format "t ⦃ s ⦄").

Fixpoint subst s t :=
  match t with
    | µ x => 
    match s↑x with 
      | Some v => v
      | None   => µ x 
    end
    | φ x      => φ x
    | m⋄n      => m⦃s⦄⋄n⦃s⦄
  end
where "t ⦃ σ ⦄" := (subst σ t).

(** The composition of substitutions *)

  Definition subst_comp s r := map (fun c => (fst c, (snd c)⦃r⦄)) s ++ r.

Notation "x 'o' y" := (subst_comp x y) (at level 60, format "x  o  y").

Fact subst_nil t : t⦃∅⦄  = t.
Proof. induction t; simpl; f_equal; auto. Qed.

Fact subst_comp_spec σ υ t : t⦃σ o υ⦄ = t⦃σ⦄⦃υ⦄.
Proof.
  induction t as [ x | c | m IHm n IHn ]; simpl; auto.
  + induction σ as [ | (y,t) s IHs ]; simpl.
    * unfold subst_comp; simpl; auto.
    * destruct (eqV_dec x y) as [ H | H ]; auto.
  + f_equal; auto.
Qed.

(** The graph of unif, ie a ⋉ b ⟼ r encodes 
    the ternary relation r = unif a b *)

(* → λ ∀ ∃ ↔ ∧ ∨ ≤ ¬ ≠ *)

Reserved Notation "a ⋉ b ⟼u r" (at level 70).

Inductive 𝔾unif : Λ → Λ → option Σ → Prop :=
    | in_gu_0 c m n :             φ c ⋉ m⋄n   ⟼u None
    | in_gu_1 c m n :             m⋄n ⋉ φ c   ⟼u None
    | in_gu_2 c x :               φ c ⋉ µ x   ⟼u Some ((x,φ c)::∅)
    | in_gu_3 m n x :             x ≺ m⋄n
                               →  m⋄n ⋉ µ x   ⟼u None
    | in_gu_4 m n x :             x ⊀ m⋄n
                               →  m⋄n ⋉ µ x   ⟼u Some ((x,m⋄n)::∅)
    | in_gu_5 x m :               x ≺ m
                               →  µ x ⋉ m     ⟼u None
    | in_gu_6 x m :               x ⊀ m
                               →  µ x ⋉ m     ⟼u Some ((x,m)::∅)
    | in_gu_7 c d :               c = d
                               →  φ c ⋉ φ d   ⟼u Some ∅
    | in_gu_8 c d :               c ≠ d
                               →  φ c ⋉ φ d   ⟼u None
    | in_gu_9 m m' n n' :         m   ⋉ m'    ⟼u None
                               →  m⋄n ⋉ m'⋄n' ⟼u None
    | in_gu_a m m' n n' σ :       m   ⋉ m'    ⟼u Some σ
                               → n⦃σ⦄ ⋉ n'⦃σ⦄ ⟼u None
                               →  m⋄n ⋉ m'⋄n' ⟼u None
    | in_gu_b m m' n n' σ υ :     m   ⋉ m'    ⟼u Some σ
                               → n⦃σ⦄ ⋉ n'⦃σ⦄ ⟼u Some υ
                               →  m⋄n ⋉ m'⋄n' ⟼u Some (σ o υ)
where "a ⋉ b ⟼u r" := (𝔾unif a b r). 

(** The graph is functional *)

Fact 𝔾unif_fun m n o1 o2 : m ⋉ n ⟼u o1  →  m ⋉ n ⟼u o2  →  o1 = o2.
Proof.
  intros H; revert H o2.
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
                 ]; intros r2; inversion 1; subst; auto; try discriminate; try tauto.
  + apply IH1 in H6; discriminate.
  + apply IH1 in H7; inversion H7; subst.
    apply IH2 in H8; discriminate.
  + apply IH1 in H7; discriminate.
  + apply IH1 in H7; inversion H7; subst.
    apply IH2 in H8; discriminate.
  + apply IH1 in H7; inversion H7; subst.
    apply IH2 in H8; inversion H8; subst.
    trivial.
Qed.
