(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2.1 FREE SOFTWARE LICENSE AGREEMENT        *)
(**************************************************************)

(** Following the "Braga method", we proceed with 
    the extraction of dfs using dfs_acc (externally) 
    nested with foldleft (see below), ie the example 
    partialy discussed by X. Leroy in its CoqPL 2024
    paper:

       https://inria.hal.science/hal-04356563/document

    The dfs algo. originaly presented in the "Braga" book
    chapter, and in the files theories/dfs/*.v herein, is
    different but computes a similar output (possibly exactly
    the same?). It avoids nesting foldleft by working on two
    lists directly.

    Notice that X. Leroy presents his dfs example with an
    internal nesting of a (specialized version) of foldleft.
    We could also do that one but instead favor the
    external nesting of a "parametric" foldleft, which
    adds so extra complexity to this example, however 
    possibly instructive for other cases.

    Below we also discuss the restrictive (too strong) 
    termination argument X. Leroy uses, ie that the successor
    graph is well-founded, and later, after the proof of
    partial correctness, we give the "weakest pre-condition"
    for termination of dfs and dfs_acc.

    (* f : 'a -> 'b -> 'a
       l : 'b list
       x : 'a
       foldleft f l x : 'a *)

    let rec foldleft f l x =
      match l with
      | []   -> x
      | y::l -> foldleft f l (f x y);;

    (* Below, we have 

       in_dec : 'a -> 'a list -> bool  
       succ : 'a -> 'a list 

       where (in_dec x a) tests whether x belongs to a or not 
       and (succ x) computes the (list of) successors of x *)

    (* (dfs_acc in_dec succ a x) computes the list of nodes
       encountered in a depth first search traversal of
       a graph (described by "succ") starting at "x", avoiding
       repeating nodes or crossing "a" twice. 

       a : 'a list
       x : 'a
       dfs_acc in_dec succ a x : 'a list *)

    let rec dfs_acc in_dec succ a x =
      match in_dec x a with
      | true  -> a
      | false -> x::foldleft (dfs_acc in_dec succ) (succ x) a.

    (* (dfs in_dec succ a x) computes the list of nodes
       encountered in a depth first search traversal of
       a graph (ie succ) starting at "x" and avoiding
       repetitions

       x : 'a
       dfs in_dec succ x : 'a list *)

    let dfs in_dec succ x = dfs_acc in_dec succ [] x

    (* Well-foundness of the relation (λ u v, u ∈ succ v) 
       is sufficient for termination but NOT mandatory.

       For instance, when succ x = [x], then dfs_acc/dfs 
       both terminate. The weakest precondition is described 
       below.

       Since dfs in_dec succ x computes a list of nodes 
       containing x and stable under succ, such an invariant
       must exist for dfs to terminate, and this is indeed a
       (the weakest) sufficient condition for termination.
       See the code below for justifications. *)

*)

Require Import List Utf8 Extraction.

Import ListNotations.

(* We use the wf_sincl_maj induction principle, ie that
   strict reverse inclusion between lists is a well-founded
   relation when restricted by a fixed upper-bound. *)
Require Import dfs_abstract.

Section foldleft.

  (** A partial and polymorphic version of foldleft *)

  Variables (X Y : Type)
            (F : X → Y → X → Prop)
            (D : X → Y → Prop)
            (f : ∀ x y, D x y → {o | F x y o}).

  Implicit Type (l : list Y).

  (* The computational graph of foldleft f, parameterized
     by the computational graph of f. *)
  Inductive Gfoldleft : list Y → X → X → Prop :=
    | Gfl_nil a            : Gfoldleft [] a a
    | Gfl_cons {a y l b o} : F a y b 
                           → Gfoldleft l b o 
                           → Gfoldleft (y::l) a o.

  (* The inductive domain of foldleft f, parameterized
     by the domain of f. *)
  Inductive Dfoldleft : list Y → X → Prop :=
    | Dfl_nil a            : Dfoldleft [] a
    | Dfl_cons {a y l}     : D a y 
                           → (∀b, F a y b → Dfoldleft l b) 
                           → Dfoldleft (y::l) a.

  Hint Constructors Gfoldleft Dfoldleft : core.

  Local Fact Gfoldleft_inv {m a o} :
       Gfoldleft m a o
     → match m with
       | []   => a = o
       | y::l => ∃b, F a y b ∧ Gfoldleft l b o
       end.
  Proof. destruct 1; eauto. Qed.

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

  (* First projection of the domain, inverting
     the second constructor 
             
             d : D a y        f : ...
           ------------------------------
                 dfl : Dfl_cons d f 

     while providing precisely the strict sub-term d
     out of dfl. *)
  Let Dfoldleft_pi1 {m a} (dfl : Dfoldleft m a) :
      ∀ (hm : is_nnil m), D a (dhead hm) :=
    match dfl with
    | Dfl_nil _    => λ C, match C with end
    | Dfl_cons d _ => λ _, d
    end.

  Let Dfl_pi1 {y l a} : Dfoldleft (y::l) a → D a y :=
    λ dfl, Dfoldleft_pi1 dfl I.

  (* Second projection of the domain, inverting
     the second constructor

             d : ...   f : ∀b, F a y b → Dfoldleft l b
           ---------------------------------------------
                     dfl : Dfl_cons d f 

     while providing precisely the strict sub-term f
     out of dfl. *)
  Let Dfoldleft_pi2 {m a} (dfl : Dfoldleft m a) :
      ∀ (hm : is_nnil m) b, F a (dhead hm) b → Dfoldleft (dtail hm) b :=
    match dfl with
    | Dfl_nil _    => λ C, match C with end
    | Dfl_cons _ f => λ _, f
    end.

  Let Dfl_pi2 {y l a b} : Dfoldleft (y::l) a → F a y b → Dfoldleft l b :=
    λ dfl, Dfoldleft_pi2 dfl I b.

  (* Beware that foldleft is by structural induction on the domain
     predicate, not on l!! Induction on l works for foldleft alone
     but not when nested with dfs_acc below. It seems the guardedness
     checker cannot analyse situations where an argument is indeed 
     decreasing but the path is not completely covered by structural
     arguments. *)
  Fixpoint foldleft l a (d : Dfoldleft l a) {struct d} : {o | Gfoldleft l a o}.
  Proof.
    (* We separate the code from the logic. Notice dependent
       pattern matching below with d reverted into the scope
       of the match. *)
    refine (match l return Dfoldleft l _ → _ with
    | []   => λ _, exist _ a _
    | y::m => λ d, let (b,hb) := f a y (Dfl_pi1 d)           in
                   let (o,ho) := foldleft m b (Dfl_pi2 d hb) in
                   exist _ o _
    end d); eauto.
  Defined.

End foldleft.

Arguments Gfoldleft {X Y}.
Arguments Gfl_nil {X Y F}.
Arguments Gfl_cons {X Y F _ _ _ _ _}.
Arguments Dfoldleft {X Y}.
Arguments foldleft {X Y} F {D}.

Section dfs.

  Variable (X : Type).

  Implicit Type l : list X.

  Variables (in_dec : ∀ x l, {x ∈ l} + {x ∉ l})
            (succ : X → list X).

  Unset Elimination Schemes.

  (** Because of nesting, the below inductive predicates Gdfs
      and Ddfs do not generate powerful enough recursors. We
      implement our own by hand, ie nested fixpoints.*)

  (* This is the computational graph of dfs_acc (below),
     ie the computaional steps described as an inductive
     relation, here nested with that for (foldleft dfs_acc). *)
  Inductive Gdfs : list X → X → list X → Prop :=
    | Gdfs_stop {a x} :     x ∈ a
                          → Gdfs a x a
    | Gdfs_next {a x o} :   x ∉ a
                          → Gfoldleft Gdfs (succ x) a o
                          → Gdfs a x (x::o).

  (* The inductive domain of dfs_acc. *)
  Inductive Ddfs : list X → X → Prop :=
    | Ddfs_stop {a x} :     x ∈ a
                          → Ddfs a x
    | Ddfs_next {a x} :     x ∉ a
                          → Dfoldleft Gdfs Ddfs (succ x) a
                          → Ddfs a x.

  Set Elimination Schemes.

  Local Fact Gdfs_inv0 a x o : Gdfs a x o → x ∈ a → a = o.
  Proof. now destruct 1. Qed.

  Local Fact Gdfs_inv1 a x o :
          Gdfs a x o
        → x ∉ a
        → match o with 
          | []   => False 
          | y::o => y = x ∧ Gfoldleft Gdfs (succ x) a o
          end.
  Proof. now destruct 1. Qed.

  (* Second projection of the domain Ddfs when x ∉ a,
     inverting the second constructor

             h : x ∉ a   dfl : Dfoldleft Gdfs Ddfs (succ x) a
           ---------------------------------------------------------
                          d : Ddfs_next h dfl

     while providing precisely the strict sub-term dfl out
     of d : Ddfs_next h dfl . *)
  Let Ddfs_pi {a x} (d : Ddfs a x) :
      x ∉ a → Dfoldleft Gdfs Ddfs (succ x) a :=
    match d with
    | Ddfs_stop h     => λ C, match C h with end
    | Ddfs_next _ dfl => λ _, dfl
    end.

  Hint Constructors Dfoldleft Gfoldleft Gdfs : core.

  (* We define dfs_acc (with an accumulator of already visited nodes)
     by structural induction on the (inductive) domain argument, nested
     with a call to foldleft. *)
  Fixpoint dfs_acc a x (d : Ddfs a x) {struct d} : {o | Gdfs a x o}.
  Proof.
    (* We separate the code from the logic *)
    refine (match in_dec x a with
    | left h  => exist _ a _
    | right h =>
              let (o,ho) := foldleft Gdfs dfs_acc (succ x) a (Ddfs_pi d h)
              in exist _ (x::o) _
    end); eauto.
  Defined.

  Section termination_easy.

    (** Termination is somewhat easy under well-foundedness of x
        in the succ relation. *)

    Theorem dfs_Acc_termination a x : x ∈ a ∨ Acc (λ u v, u ∈ succ v) x → Ddfs a x.
    Proof.
      intros [ Hx | Hx ].
      1: now constructor 1.
      induction Hx as [ x _ IHx ] in a |- *.
      destruct (in_dec x a) as [ | H ].
      + now constructor 1.
      + constructor 2; trivial.
        clear H.
        revert IHx; generalize (succ x) a; clear x a.
        intro l; induction l; econstructor; eauto.
    Qed.

  End termination_easy.

  (** Below we do not assume the above strong termination criterium
      and show the properties of dfs_acc by reasonning exclusively
      on the low-level specification of dfs_acc via the computational
      graph Gdfs, ie w/o establishing fixpoint equations for dfs_acc,
      which could be done as an alternative approach (using Gdfs_fun).

      We prove partial correctness and then termination under
      the weakest pre-condition of the existence of a specific
      invariant. dfs_acc actually outputs a least of such
      invariant. *)

  Section Gdfs_ind.

    (** First, a useful mutual induction principle 
        for (Gfoldleft Gdfs) / Gdfs which allows to show:
        - functionality of Gdfs
        - inclusion of Gdfs into Ddfs
        - partial correctness of dfs_acc 

        Notice that we have to use a nested fixpoint here. *)

    Variables (P : list X → list X → list X → Prop)
              (Q : list X → X → list X → Prop)

              (HP0 : ∀a, P [] a a)

              (HP1 : ∀ {a y l b o},
                         Gdfs a y b 
                       → Q a y b 
                       → Gfoldleft Gdfs l b o
                       → P l b o  
                       → P (y::l) a o)

              (HQ0 : ∀ {a x},
                         x ∈ a
                       → Q a x a)

              (HQ1 : ∀ {a x o},
                         x ∉ a
                       → Gfoldleft Gdfs (succ x) a o
                       → P (succ x) a o
                       → Q a x (x::o)).

    Let Gfoldleft_ind (Gdfs_ind : ∀ {a x o}, Gdfs a x o → Q a x o) :=
      fix loop {l a o} (gfl : Gfoldleft Gdfs l a o) {struct gfl} :=
        match gfl with
        | Gfl_nil a    => HP0 a
        | Gfl_cons f g => HP1 f (Gdfs_ind f) g (loop g)
        end.

    (* This requires a nesting with Gfoldleft_ind above. It could be
       done inline (see below) but we separate here for readability.
       This nesting is comparable to that of foldleft/dfs_acc except
       that the structural arguments are the computational graphs,
       not the inductive domains. Pattern matching on these is ok
       since the recursor is over Prop, not Set/Type. *)
    Local Fixpoint Gdfs_ind a x o (d : Gdfs a x o) {struct d} : Q a x o :=
      match d with
      | Gdfs_stop h     => HQ0 h
      | Gdfs_next h gfl => HQ1 h gfl (Gfoldleft_ind Gdfs_ind gfl)
      end.

    (* The same proof term, but using an Ltac script with nesting inlined. *)
    Let Fixpoint Gdfs_ind_script a x o (d : Gdfs a x o) {struct d} : Q a x o.
    Proof.
      destruct d as [ | ? ? ? ? gfl ].
      + now apply HQ0.
      + apply HQ1; trivial.
        induction gfl; eauto.
    Qed.

  End Gdfs_ind.

  (* We can deduce functionality of Gdfs. *)
  Local Lemma Gdfs_fun {a x o₁ o₂} : Gdfs a x o₁ → Gdfs a x o₂ → o₁ = o₂.
  Proof.
    intros H; revert o₂; pattern a, x, o₁; revert a x o₁ H.
    apply Gdfs_ind with (P := λ l a o, ∀o2, Gfoldleft Gdfs l a o2 → o = o2).
    + now intros ? ? ?%Gfoldleft_inv.
    + intros ? ? ? ? ? _ IH1 _ IH2 ? (? & [])%Gfoldleft_inv.
      apply IH2; erewrite IH1; eauto.
    + intros ? ? ? ? ?%Gdfs_inv0; auto.
    + intros ? ? ? ? ? ? [] []%Gdfs_inv1; easy || f_equal; eauto.
  Qed.

  (* And then the inclusion of Gdfs in Ddfs. *)
  Local Lemma Gdfs_incl_Ddfs : ∀ a x o, Gdfs a x o → Ddfs a x.
  Proof.
    apply Gdfs_ind with (P := λ l a o, Dfoldleft Gdfs Ddfs l a)
                        (Q := λ a x o, Ddfs a x);
      [ constructor 1 | | constructor 1 | constructor 2 ]; eauto.
    intros a x l b o1 H1 IH1 H2 IH2.
    constructor; auto.
    intros ? H3.
    now rewrite (Gdfs_fun H3 H1).
  Qed.

  (* Hence the domain Ddfs, characterized inductivelly
     for the purpose of defining dfs_acc by structural
     induction on it, is indeed (equivalent to) the 
     projection of the computational graph Gdfs. *)
  Theorem Dfs_iff_Gdfs a x : Ddfs a x ↔ ∃o, Gdfs a x o.
  Proof.
    split.
    + intros (o & ?)%dfs_acc; now exists o.
    + now intros (? & ?%Gdfs_incl_Ddfs).
  Qed.

  (* This is the partial correctness of dfs_acc via its low-level 
     characterization (ie Gdfs): the output of dfs_acc (when it exists)
     is a smallest invariant containing x. *)
  Theorem dfs_acc_partially_correct a x o :
       Gdfs a x o → smallest (λ α, α x ∧ ⦃a⦄ ⊆ α ∧ dfs_acc_invar succ a α) ⦃o⦄.
  Proof.
    revert a x o.
    (** The property to be established for Gfoldleft Gdfs l a o has to be provided,
        here the smallest invariant containing l. *)
    apply Gdfs_ind with (P := λ l a o, smallest (λ α, ⦃l⦄ ⊆ α ∧ ⦃a⦄ ⊆ α ∧ dfs_acc_invar succ a α) ⦃o⦄);
      unfold dfs_acc_invar.
    + repeat split; easy || auto; red; auto.
    + intros a x l b o _ ((H1 & H2 & H3) & H4) _ ((G1 & G2 & G3) & G4); repeat split; eauto.
      * intros ? [ [] | ?%G1 ]; eauto.
      * intros ? [ []%H3| ]%G3; eauto.
      * intros ? (F1 & F2 & F3).
        apply G4; repeat split; eauto.
        - apply H4; repeat split; auto.
        - intros ? []%F3; eauto.
    + repeat split; auto.
      now intros ? (? & []).
    + intros a x o Hx _ ((H1 & H2 & H3) & H4); repeat split; auto.
      * intros z [ <- | []%H3 ]; eauto.
      * intros m (H5 & H6 & H7).
        intros z [ <- | Hz ]; auto; revert z Hz.
        apply H4; repeat split; eauto.
        destruct (H7 _ H5); auto; tauto.
  Qed.

  Notation next := (λ v u, u ∈ succ v).

  Corollary dfs_acc_crt_excluded a x o :
        Gdfs a x o → ⦃o⦄ ≡ ⦃a⦄ ∪ crt_exclude next ⦃a⦄ x.
  Proof.
    intros ?%dfs_acc_partially_correct.
    apply dfs_acc_post_condition; auto.
  Qed.

  (* We need to study the cumulativity of Gdfs *)
  Fact Gdfs_mono a b x y o o' : Gdfs a y b → Gdfs a x o -> Gdfs b x o'.
  Admitted.

  Fact Ddfs_mono a b y : Gdfs a y b → Ddfs a ⊆ Ddfs b.
  Proof.
    intros H1 x (o & H2)%Dfs_iff_Gdfs.
    revert y b H1.
    pattern a, x, o; revert a x o H2.
    apply Gdfs_ind
      with (P := λ l a o, forall y b, Gdfs a y b -> Dfoldleft Gdfs Ddfs l b).
    + constructor 1.
    + intros a x l b o H1 IH1 H2 IH2 y c Hc.
      constructor 2; eauto.
      intros; eapply IH2. 
  Admitted.

  Fact Ddfs_mono' a b x : ⦃a⦄ ⊆ ⦃b⦄ -> dfs_acc_invar succ a ⦃b⦄ → Ddfs a x → Ddfs b x.
  Proof.
    intros H1 H2 (o & Ho)%Dfs_iff_Gdfs; revert b H1 H2; pattern a, x, o; revert a x o Ho.
    apply Gdfs_ind with (P := λ l a o, forall b, ⦃a⦄ ⊆ ⦃b⦄ -> dfs_acc_invar succ a ⦃b⦄ -> Dfoldleft Gdfs Ddfs l b).
    + constructor 1.
    + intros a x l b o H1 IH1 H2 IH2 c Hc1 Hc2.
      constructor 2; auto.
      intros d Hd.
      (* Here we use partial correctness *)
      generalize (dfs_acc_crt_excluded _ _ _ H1)
                 (dfs_acc_crt_excluded _ _ _ Hd).
      intros H3 H4.
      apply IH2.
      intros z [ | ]%H3.
      * apply H4; eauto.
      * admit.
      * admit.
    + constructor 1; auto.
    + intros a x o Hx H1 IH1 b Hb.
      destruct (in_dec x b) as [ H | H ].
      * now constructor 1.
      * constructor 2; auto.
  Admitted.

(*
  (* This property does not holds.
     If b=[x] and a=[] then 
       - Gdfs b x [x]
       - while o st that Gdfs a x o
         can contain many more points that just x *) 
  Fact Gdfs_mono a b x o : a ⊆ b → Gdfs a x o → ∃o', (o ⊆ b++o' ∧ Gdfs b x o').
  Proof.
    intros H1 H2; revert b H1; pattern a, x, o; revert a x o H2.
    apply Gdfs_ind with (P := λ l a o, ∀b, a ⊆ b → ∃o', o ⊆ o' ∧ Gfoldleft Gdfs l b o').
    + intros a b Hab; exists b; split; auto.
    + intros a x l b o _ IH1 _ IH2 c Hac.
      apply IH1 in Hac as (o1 & (o2 & [])%IH2 & G2).
      exists o2; split; auto.
      econstructor; eauto.
    + intros a x Hxa b Hb; exists b; split; auto.
    + intros a x o Hx H IH b Hab.
      destruct IH with (1 := Hab) as (o' & G1 & G2).
      destruct (in_dec x b).
      exists (x::o'); split; eauto.
      constructor 2; auto.
  Admitted.

*)

  Inductive bar (P : X → Prop) x : Prop :=
    | bar_stop : P x → bar P x
    | bar_step : (forall y, y ∈ succ x → bar P y) → bar P x.

  Hint Resolve Ddfs_mono : core.

  Lemma bar_Ddfs a x : bar ⦃a⦄ x → Ddfs a x.
  Proof.
    induction 1 as [ x Hx | x Hx IHx ].
    + now constructor 1.
    + destruct (in_dec x a) as [ H | H ].
      * now constructor 1.
      * constructor 2; auto.
        generalize (succ x) a IHx; clear a x Hx IHx H.
        induction l; intros; eauto.
        constructor 2; eauto.
  Qed.

  (* Now we want to study termination via a theorem like this one ... *)

  Theorem Gdfs_wf : ∀ a x o, Gdfs a x o → bar ⦃a⦄ x.
  Proof.
    apply Gdfs_ind with (P := λ l a o, forall x, x ∈ l → bar ⦃a⦄ x).
    + now simpl.
    + intros a y l b o H1 [IH1 | IH1] H2 IH2.
      * intros [ | k u ] z v E; simpl in E.
        - inversion E; subst z v; simpl; auto.
        - inversion E; subst l k.
          destruct (IH2 _ _ _ eq_refl).
  Admitted.

End dfs.
