(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2.1 FREE SOFTWARE LICENSE AGREEMENT        *)
(**************************************************************)

(** Extraction of dfs nested with foldleft

    let rec foldleft f l x =
      match l with
      | []   -> x
      | y::l -> foldleft f l (f x y);;

    (* in_dec tests whether x belongs to a or not *)
    let rec dfs in_dec succ a x =
      match in_dec x a with
      | true  -> a
      | false -> foldleft (dfs succ) (succ x) (x::a).

*)

Require Import List Utf8 Extraction.

Import ListNotations.

Require Import induction.

#[local] Infix "∈" := (@In _) (at level 70, no associativity).
#[local] Infix "⊆" := incl (at level 70, no associativity).

#[local] Hint Resolve in_eq in_cons : core.

Section foldleft.

  (** A partial version of foldleft *)

  Variables (X Y : Type) 
            (F : X → Y → X → Prop)
            (Ffun : ∀ {a y b1 b2}, F a y b1 → F a y b2 → b1 = b2)
            (D : X → Y → Prop)
            (HD : ∀ a y b, F a y b → D a y)
            (f : ∀ x y, D x y → {o | F x y o}).

  Implicit Type (l : list Y).

  Inductive Gfoldleft : list Y → X → X → Prop :=
    | Gfl_nil a            : Gfoldleft [] a a
    | Gfl_cons {a y l b o} : F a y b 
                           → Gfoldleft l b o 
                           → Gfoldleft (y::l) a o.

  Fact Gfoldleft_inv {m a o} :
       Gfoldleft m a o 
     → match m with
       | []   => a = o
       | y::l => ∃b, F a y b ∧ Gfoldleft l b o
       end.
  Proof. destruct 1; eauto. Qed.

  Inductive Dfoldleft : list Y → X → Prop :=
    | Dfl_nil a            : Dfoldleft [] a
    | Dfl_cons {a y l}     : D a y 
                           → (∀b, F a y b → Dfoldleft l b) 
                           → Dfoldleft (y::l) a.

  Let is_nnil l := match l with [] => False | _ => True end.

  Let dhead {l} : is_nnil l → Y :=
    match l with
    | []   => λ C, match C with end
    | y::_ => λ _, y
    end.
  
  Let dtail {l} : is_nnil l → list Y :=
    match l with
    | []   => λ C, match C with end
    | _::l => λ _, l
    end.

  Definition Dfoldleft_pi1 {m a} (d : Dfoldleft m a) :
      ∀ (hm : is_nnil m), D a (dhead hm) :=
    match d with
    | Dfl_nil _    => λ C, match C with end
    | Dfl_cons f _ => λ _, f
    end.

  Definition Dfoldleft_pi2 {m a} (d : Dfoldleft m a) :
      ∀ (hm : is_nnil m) b, F a (dhead hm) b → Dfoldleft (dtail hm) b :=
    match d with
    | Dfl_nil _    => λ C, match C with end
    | Dfl_cons _ d => λ _, d
    end.

  (* Beware that foldleft_pwc is by structural induction on the domain
     predicate, not on l !! Possibly we could do by induction on l *)
  Fixpoint foldleft_pwc l a (d : Dfoldleft l a) {struct d} : {o | Gfoldleft l a o}.
  Proof.
    refine (match l return Dfoldleft l _ → _ with
    | []   => λ _, exist _ a _
    | y::m => λ d, let (b,hb) := f a y (Dfoldleft_pi1 d I)                 in
                   let (o,ho) := foldleft_pwc m b (Dfoldleft_pi2 d I _ hb) in
                   exist _ o _
    end d); econstructor; eauto.
  Defined.

  (*

  Fact Dfoldleft_iff_Gfoldleft l a : Dfoldleft l a ↔ ∃o, Gfoldleft l a o.
  Proof.
    split.
    + intros (o & ?)%foldleft_pwc; now exists o.
    + intros (o & H); revert H.
      induction 1 as [ | a y l b o1 H1 H2 IH2 ]; econstructor; eauto.
      intros o2 H3; now rewrite (Ffun H3 H1).
  Qed.

  Variables (g : X → Y → X) (Hg : ∀x y, F x y (g x y)).

  Fact Gfoldleft_fold_left l a : Gfoldleft l a (fold_left g l a).
  Proof. induction l in a |- *; simpl; econstructor; eauto. Qed.

  *)

End foldleft.

Arguments Gfoldleft {X Y}.
Arguments Dfoldleft {X Y}.

Check Dfoldleft.

Check foldleft_pwc.
Arguments foldleft_pwc {X Y} F {D}.

Section dfs.

  Variables (X : Type).

  Implicit Type l : list X.

  Variables (in_dec : ∀ x l, {x ∈ l} + {~ x ∈ l})
            (succ : X → list X).

  Unset Elimination Schemes.

  Inductive Gdfs : list X → X → list X → Prop :=
    | Gdfs_stop {a x} :     x ∈ a
                          → Gdfs a x a
    | Gdfs_next {a x o} : ~ x ∈ a
                          → Gfoldleft Gdfs (succ x) (x::a) o
                          → Gdfs a x o.

  Inductive Ddfs : list X → X → Prop :=
    | Ddfs_stop {a x} :   x ∈ a 
                        → Ddfs a x 
    | Ddfs_next {a x} : ~ x ∈ a
                        → Dfoldleft Gdfs Ddfs (succ x) (x::a)
                        → Ddfs a x.

  Set Elimination Schemes.

  Fact Gdfs_inv0 a x o : Gdfs a x o → x ∈ a → a = o.
  Proof. now destruct 1. Qed.

  Fact Gdfs_inv1 a x o : Gdfs a x o → ~ x ∈ a → Gfoldleft Gdfs (succ x) (x::a) o.
  Proof. now destruct 1. Qed.

  Definition Ddfs_inv {a x} (d : Ddfs a x) : 
    ~ x ∈ a → Dfoldleft Gdfs Ddfs (succ x) (x::a) :=
    match d with
    | Ddfs_stop h   => λ C, match C h with end 
    | Ddfs_next _ h => λ _, h 
    end.

  Hint Constructors Gfoldleft Gdfs : core.

  Fixpoint dfs_pwc a x (d : Ddfs a x) { struct d } : sig (Gdfs a x).
  Proof.
    refine (
      match in_dec x a with
      | left h  => exist _ a _ 
      | right h =>
        let (o,ho) := foldleft_pwc Gdfs dfs_pwc (succ x) (x::a) (Ddfs_inv d h)
        in exist _ o _
      end
    ); eauto. 
  Defined.

  Section Gdfs_ind.

    (* A nested induction principle for (Gfoldleft Gdfs) / Gdfs *)

    Variables (P : list X → list X → list X → Prop)
              (Q : list X → X → list X → Prop)

              (HP0 : ∀a, P [] a a) 

              (HP1 : ∀ a y l b o,
                         Gdfs a y b 
                       → Q a y b 
                       → Gfoldleft Gdfs l b o
                       → P l b o  
                       → P (y::l) a o)

              (HQ0 : ∀ a x,
                         x ∈ a
                       → Q a x a)

              (HQ1 : ∀ a x o,
                       ~ x ∈ a
                       → Gfoldleft Gdfs (succ x) (x::a) o
                       → P (succ x) (x::a) o
                       → Q a x o).

    (* This requires a nested fixpoint *)
    Fixpoint Gdfs_ind a x o (d : Gdfs a x o) { struct d } : Q a x o.
    Proof.
      destruct d.
      + apply HQ0; trivial.
      + apply HQ1; trivial.
        induction H0; eauto.
    Qed. 

  End Gdfs_ind.

  (* We can deduce functionality *)
  Lemma Gdfs_fun {a x o1 o2} : Gdfs a x o1 → Gdfs a x o2 → o1 = o2.
  Proof.
    intros H; revert o2; pattern a, x ,o1; revert a x o1 H.
    apply Gdfs_ind with (P := fun l a o => ∀o2, Gfoldleft Gdfs l a o2 → o = o2).
    + now intros ? ? ?%Gfoldleft_inv.
    + intros a x l b1 o1 _ IH1 _ IH2 o2 (b2 & H3 & H4)%Gfoldleft_inv.
      rewrite (IH1 _ H3) in IH2; auto.
    + intros a x h o H%Gdfs_inv0; auto.  
    + intros ? ? ? ? ? ? ? ?%Gdfs_inv1; eauto.
  Qed.

  (* And the link between Gdfs and Ddfs *)
  Lemma Gdfs_Ddfs a x o : Gdfs a x o → Ddfs a x.
  Proof.
    revert a x o.
    apply Gdfs_ind with (P := λ l a o, Dfoldleft Gdfs Ddfs l a)
                        (Q := λ a x o, Ddfs a x). 
    1,3 : econstructor; eauto.
    + intros a x l b o1 H1 IH1 H2 IH2.
      constructor; auto.
      intros o2 H3.
      now rewrite (Gdfs_fun H3 H1).
    + constructor 2; auto.
  Qed.

  Theorem Dfs_iff_Gdfs a x : Ddfs a x ↔ ∃o, Gdfs a x o.
  Proof.
    split.
    + intros (o & ?)%dfs_pwc; now exists o.
    + now intros (? & ?%Gdfs_Ddfs).
  Qed.

  Let dfs_linvariant a l i := 
    a ⊆ i ∧ l ⊆ i ∧ ∀y, y ∈ i → y ∈ a ∨ succ y ⊆ i.

  Definition dfs_invariant a x i := 
    a ⊆ i ∧ x ∈ i ∧ ∀y, y ∈ i → y ∈ a ∨ succ y ⊆ i.

  Hint Resolve incl_nil_l incl_refl incl_tran incl_cons : core.

  (* This is partial correctness: the output of dfs, if it exists,
     is a smallest invariant *)
  Theorem Gdfs_invariant a x o :
       Gdfs a x o
     → dfs_invariant a x o
     ∧ ∀i, dfs_invariant a x i → o ⊆ i.
  Proof.
    revert a x o.
    apply Gdfs_ind with
      (P := λ l a o, dfs_linvariant a l o ∧ ∀i, dfs_linvariant a l i → o ⊆ i).
    + intros a; repeat split; auto.
      now intros i (H1 & _).
    + intros a x l b o _ ((H1 & H2 & H3) & H4) _ ((G1 & G2 & G3) & G4); repeat split; eauto.
      * intros y [ []%H3 | ]%G3; eauto.
      * intros i (F1 & (F2 & F3)%incl_cons_inv & F4).
        apply G4; repeat split; eauto.
        - apply H4; repeat split; eauto.
        - intros y []%F4; eauto.
    + intros a x Hx; repeat split; auto.
      now intros i (H1 & _).
    + intros a x o Hx _ (((H1 & H2)%incl_cons_inv & H3 & H4) & H5); repeat split; eauto.
      * intros ? [ [ <- | ] | ]%H4; eauto.
      * intros i (G1 & G2 & G3).
        apply H5; repeat split; eauto.
        - destruct (G3 _ G2); auto; tauto.
        - intros ? []%G3; eauto.
  Qed.

  Section termination_easy.

    (** Now we can instanciate for _ ∈ succ _ is well founded
        and show that dfs terminates in that case w/o using 
        partial correctness *)

    Hypothesis hsucc : well_founded (λ u v, u ∈ succ v).

    (** Termination is very easy under well-foundedness of succ *)
    Theorem dfs_wf_termination a x : Ddfs a x.
    Proof.
      induction x as [ x IHx ] using (well_founded_induction hsucc) in a |- *.
      destruct (in_dec x a) as [ H | H ].
      + now constructor 1.
      + constructor 2; trivial.
        clear H.
        revert IHx; generalize (succ x) (x::a); clear x a.
        intro l; induction l; econstructor; eauto.
    Qed.

  End termination_easy.

  Section termination_hard.

    (** We study a more general termination criteria, THE MOST
        GENERAL, using partial correctness *)
 
    Theorem Ddfs_domain a x i : dfs_invariant a x i → Ddfs a x.
    Proof.
      intros H0; generalize H0; intros (H1 & H2 & H3); clear H0.
      revert a H1 x H2 H3.
  
      induction a as [ a IHa ] using (well_founded_induction (wf_sincl_maj i)); intros Ha. 
      intros x Hx Hax.
      destruct (in_dec x a) as [ H | H ].
      + now constructor 1.
      + constructor 2; trivial.
        assert (IH : forall l, x::a ⊆ l -> l ⊆ i -> 
              ∀y, y ∈ i → Ddfs l y).
        1:{ intros l H1 H2 y H3.
            apply IHa; trivial.
            + split; eauto.
            + intros z []%Hax; eauto. }
        clear IHa.
        destruct (Hax _ Hx) as [ | Hsucc ]; [ tauto | ].
        cut (x::a ⊆ i); auto.
        clear H Ha Hx.
        revert IH; generalize (x::a); intros m IHm Hm.
        revert Hsucc; generalize (succ x); clear x a.
        intros l Hl; revert Hl m Hm IHm.
        induction l as [ | x l IHl ]; intros Hl m Hm IHm.
        * constructor 1.
        * constructor 2.
          - apply IHm; auto.
          - apply incl_cons_inv in Hl as [].
            intros o ((? & ? & ?) & ?)%dfs_invariant; apply IHl; eauto.
            apply H4; repeat split; auto.
    Admitted. 


  End termination_hard.

End dfs.

Recursive Extraction dfs_pwc.

Check dfs_pwc.
