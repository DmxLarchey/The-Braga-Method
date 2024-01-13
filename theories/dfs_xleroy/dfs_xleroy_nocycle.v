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

    Assuming in_dec and succ, the algorithm we study here 
    in this file, the one proposed by X. Leroy in the above
    reference is

      let rec dfs_xl a x :=
        match in_dec x a with
        | true  -> a
        | false -> x::foldleft dfs_xl (succ x) a

    whereas in dfs_braga_direct.v we study 

      let rec dfs_braga a x =
        match in_dec x a with
        | true  -> a
        | false -> foldleft dfs_braga (succ x) (x::a)

    Notice the difference in the position in the programs
    where x is appended to the output (or accumulator a).
    This has a major impact on the weakest pre-condition,
    ie when does dfs_xl or dfs_braga actually terminate:
    - the call (dfs_xl [] x) terminates if and only if
      x is in the well-founded part of the succ relation,
      hence when there are finitely many points succ-reachable
      from x and also no cycle in that part of the succ-graph;
    - the call (dfs_braga [] x) terminates if and only if
      there are finitely many points succ-reachable from x. 
      The existence of cycles do not impact termination.

    Additionally, dfs_xl does output neither the left-right
    nor the right-left prefix traversal of the graph.
    dfs_braga seems to output the reverse of the left-right
    prefix traversal of the graph. Here left (resp. right) 
    is the head (resp. tail) of the list (succ x).

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
       at x is sufficient for termination of dfs in_dec [] x 
       but also MANDATORY as established below. *)

*)

Require Import List Relations Utf8 Extraction.

Import ListNotations.

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

  Local Definition Dfl_pi1 {y l a} : Dfoldleft (y::l) a → D a y :=
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

  Local Definition Dfl_pi2 {y l a b} : Dfoldleft (y::l) a → F a y b → Dfoldleft l b :=
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
Arguments Gfoldleft_ind {_ _ _ _} _ _ {_ _ _}.
Arguments Gfl_nil {X Y F}.
Arguments Gfl_cons {X Y F _ _ _ _ _}.
Arguments Dfoldleft {X Y}.
Arguments foldleft {X Y} F {D}.

Check Dfl_pi2.
Arguments Dfl_pi2 {X Y F D _ _ _ _}.
Arguments Dfl_pi1 {X Y F D _ _ _}.


Section dfs.

  Variable (X : Type).

  Implicit Types (l : list X) (x : X).

  Variables (in_dec : ∀ x l, {x ∈ l} + {x ∉ l})
            (succ : X → list X).

  Local Fact in_wdec l x : x ∈ l ∨ x ∉ l.
  Proof. destruct (in_dec x l); auto. Qed.

  Local Fact eq_wdec x y : x = y ∨ x ≠  y.
  Proof.
    destruct (in_dec x [y]) as [ [ <- | [] ] | C ]; auto.
    right; contradict C; subst; auto.
  Qed.

  Hint Resolve in_wdec eq_wdec : core.

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
  Local Definition Ddfs_pi {a x} (d : Ddfs a x) :
      x ∉ a → Dfoldleft Gdfs Ddfs (succ x) a :=
    match d with
    | Ddfs_stop h     => λ C, match C h with end
    | Ddfs_next _ dfl => λ _, dfl
    end.

  Hint Constructors Dfoldleft Gfoldleft Gdfs : core.

  (* We define dfs_acc (with an accumulator of already visited nodes)
     by structural induction on the (inductive) domain argument, nested
     with a call to foldleft. Another (simpler) solution is to inline
     the nested instance of foldleft Gdfs dfs_acc. *)
  Fixpoint dfs_acc a x (d : Ddfs a x) {struct d} : {o | Gdfs a x o}.
  Proof.
    (* We separate the code from the logic *)
    refine (match in_dec x a with
    | left h  =>    exist _ a _
    | right h => let (o,ho) := foldleft Gdfs dfs_acc (succ x) a (Ddfs_pi d h)
                 in exist _ (x::o) _
    end); eauto.
  Defined.

  Hint Constructors Gfoldleft : core.

  Fixpoint dfs_acc_inlined a x (d : Ddfs a x) {struct d} : {o | Gdfs a x o}.
  Proof.
    (* We separate the code from the logic *)
    refine (match in_dec x a with
    | left h  =>    exist _ a _
    | right h => 
         let (o,ho) :=
          (fix dfs_list l a (dl : Dfoldleft Gdfs Ddfs l a) {struct dl} : sig (Gfoldleft Gdfs l a) :=
            match l return Dfoldleft _ _ l _ → _ with
            | []   => λ _, exist _ a _
            | y::m => λ d, let (b,hb) := dfs_acc_inlined a y (Dfl_pi1 d) in
                           let (o,ho) := dfs_list m b (Dfl_pi2 d hb)         in
                           exist _ o _
            end dl) (succ x) a (Ddfs_pi d h) 
         in exist _ (x::o) _
    end); eauto.
  Defined.

  (** Termination (sufficiency), ie the predicate Ddfs [] x holds, 
      is somewhat easy under well-foundedness of x in the succ relation. *)

  Theorem dfs_acc_termination a x : x ∈ a ∨ Acc (λ u v, u ∈ succ v) x → Ddfs a x.
  Proof.
    intros [ | Hx ]; [ now constructor 1 | ].
    induction Hx as [ x _ IHx ] in a |- *.
    destruct (in_dec x a) as [ | H ].
    + now constructor 1.
    + constructor 2; trivial.
      clear H.
      revert IHx; generalize (succ x) a; clear x a.
      intro l; induction l; econstructor; eauto.
  Qed.

  Corollary dfs_termination x : Acc (λ u v, u ∈ succ v) x → Ddfs [] x.
  Proof. intros; apply dfs_acc_termination; auto. Qed.

  (** The study of necessary conditions for termination is more 
      complicated and requires a proof of partial correctness.

      Below we show that the above (strong) termination condition
      Acc (λ u v, u ∈ succ v) x is actually *necessary* for termination.
 
      For this, we show that when the computational graph of dfs_acc
      outputs something from input a x, then it must be that
      any infinite succ sequence from x eventually meets a.

      This is one aspect of partial correctness, the other aspect
      being that the output of dfs_acc a x is a list containing
      the y that are either in a or reachable from x using a 
      (succ) path no crossing a. *)
 
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

              (HP1 : ∀ {a x l b o},
                         Gdfs a x b 
                       → Q a x b 
                       → Gfoldleft Gdfs l b o
                       → P l b o  
                       → P (x::l) a o)

              (HQ0 : ∀ {a x},
                         x ∈ a
                       → Q a x a)

              (HQ1 : ∀ {a x o},
                         x ∉ a
                       → Gfoldleft Gdfs (succ x) a o
                       → P (succ x) a o
                       → Q a x (x::o)).

    (* This requires a nesting with the generic Gfoldleft_ind above.
       It could be done with an inlined nested fixpoint but we separate
       here for readability.
       This nesting is comparable to that of foldleft/dfs_acc except
       that the structural arguments are the computational graphs,
       not the inductive domains. Pattern matching on these is ok
       since the recursor is over Prop, not Set/Type. *)
    Fixpoint Gdfs_ind {a x o} (d : Gdfs a x o) {struct d} : Q a x o :=
      match d with
      | Gdfs_stop h     => HQ0 h
      | Gdfs_next h gfl => HQ1 h
                               gfl
                               (Gfoldleft_ind
                                  HP0
                                  (λ _ _ _ _ _ h1 h2 h3, HP1 h1 (Gdfs_ind h1) h2 h3) 
                                  gfl)
      end.

    (* This is for completeness as well, showing that we can proceed
       with Ltac but this does not display the structural decrease as
       well as in the proof term above.
       The same proof term as Gdfs_ind, but using an Ltac script 
       with implemented via a call to "induction". *)
    Local Fixpoint Gdfs_ind_script a x o (d : Gdfs a x o) {struct d} : Q a x o.
    Proof.
      destruct d as [ | ? ? ? H gfl ].
      + now apply HQ0.
      + apply HQ1; trivial.
        clear H.
        induction gfl; eauto.
    Qed.

    (* This is for completeness but not really needed below *)
    Theorem Gdfs_mutual_ind : (∀ l a o, Gfoldleft Gdfs l a o → P l a o)
                            ∧ (∀ a x o, Gdfs a x o → Q a x o).
    Proof.
      split; eauto.
      + apply Gfoldleft_ind; eauto.
        intros; eapply HP1; eauto.
        apply Gdfs_ind; auto.
      + apply @Gdfs_ind.
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

  Notation next := (λ v u, u ∈ succ v).

  (* (finitary branching) bar inductive classically meaning
     that no infinite succ path can avoid P. *) 
  Inductive bar (P : X → Prop) x : Prop :=
    | bar_stop : P x → bar P x
    | bar_step : (∀ y, y ∈ succ x → bar P y) → bar P x.

  Fact bar_empty x : bar (λ _, False) x ↔ Acc (λ u v, u ∈ succ v) x.
  Proof.
    split.
    + induction 1; eauto; [ tauto | now constructor ].
    + induction 1; now constructor 2.
  Qed.

  Fact bar_inv P x : bar P x → P x ∨ ∀ y, y ∈ succ x → bar P y.
  Proof. destruct 1; auto. Qed.

  Fact crt_exclude_bar P x y : crt_exclude next P x y → bar P x → bar P y.
  Proof.
    induction 1 as [ | x y z H1 H2 H3 IH3 ] using crt_exclude_ind; auto.
    intros [ []%H1 | ]%bar_inv; eauto.
  Qed.

  Notation crt_exclude_union R P L := (λ x, ∃i, L i ∧ crt_exclude R P i x).

  (** We get a stronger partial correctness post-condition that when considering
      the Braga variant of the dfs algorithm that . Indeed, in this case,
      when dfs a x outputs a result (ie terminates), it must further be that
      bar ⦃a⦄ x holds, ie any infinite path from x must cross ⦃a⦄. *)

  Theorem dfs_acc_partially_correct a x o :
            Gdfs a x o
          → bar ⦃a⦄ x
          ∧ ⦃o⦄ ≡ ⦃a⦄ ∪ crt_exclude next ⦃a⦄ x.
  Proof.
    revert a x o.
    apply Gdfs_ind with (P := λ l a o, Forall (bar ⦃a⦄) l ∧ ⦃o⦄ ≡ ⦃a⦄ ∪ crt_exclude_union next ⦃a⦄ ⦃l⦄).
    + intros a; split; auto.
      intros; now rewrite crt_exclude_union_nil with (A := ⦃_⦄).
    + intros a x l b o _ (B1 & E1) _ (B2 & E2); split.
      * constructor; auto.
        revert B2; apply Forall_impl.
        clear E2 l o.
        induction 1 as [ y [ Hy | Hy ]%E1 | y Hy IHy ].
        - now constructor 1.
        - now apply crt_exclude_bar with (1 := Hy).
        - now constructor 2. 
      * intros y; rewrite E2, E1; split.
        - intros [ [] | (i & H1 & H2) ]; eauto.
          right; exists i; split; auto.
          revert H2; apply crt_exclude_mono.
          intros; apply E1; auto.
        - intros [ | (i & [ <- | Hi ] & H1) ]; auto.
          apply crt_exclude_special with (x := x) in H1
            as [ [ H1 | H1 ] | H1 ]; eauto.
          ++ right; exists i; split; auto.
             revert H1; apply crt_exclude_mono.
             intro; apply E1.
          ++ intro z; rewrite <- E1; destruct (in_dec z b); auto.
    + intros a x Hax; split.
      * now constructor 1.
      * intros y; split; auto.
        intros [ | H ]; auto.
        now destruct (crt_exclude_yes _ _ _ _ _ H Hax).
    + intros a x o Hax _ (B1 & E1); split.
      * constructor 2; now apply Forall_forall.
      * intros z; simpl.
        rewrite E1; split.
        - intros [ <- | [ | (? & []) ] ]; eauto.
        - intros [ | [ | [] ]%crt_exclude_inv ]; auto.
  Qed.

  Corollary dfs_acc_pre_condition a x o : Gdfs a x o → bar ⦃a⦄ x.
  Proof. apply dfs_acc_partially_correct. Qed.

  Corollary dfs_acc_post_condition a x o : Gdfs a x o → ⦃o⦄ ≡ ⦃a⦄ ∪ crt_exclude next ⦃a⦄ x.
  Proof. apply dfs_acc_partially_correct. Qed.

  Lemma dfs_pre_condition x o : Gdfs [] x o → Acc (λ u v, u ∈ succ v) x.
  Proof. now intros ?%dfs_acc_pre_condition%bar_empty. Qed.

  Lemma dfs_post_condition x o : Gdfs [] x o → ⦃o⦄ ≡ clos_refl_trans next x.
  Proof.
    intros H y.
    rewrite <- crt_exclude_empty, dfs_acc_post_condition; eauto.
    simpl; tauto.
  Qed.

  Hint Resolve dfs_pre_condition : core.

  Theorem dfs_weakest_pre_condition x :
            (∃o, Gdfs [] x o)
          ↔ Acc (λ u v, u ∈ succ v) x.
  Proof.
    split.
    + intros []; eauto.
    + now intros ?%dfs_termination%Dfs_iff_Gdfs.
  Qed.

  (* This is the dfs algorithm associated to Gdfs with the most
     general specification since the pre-condition is the weakest-possible. 
     The post-condition does not include the absence of succ-cycles in
     the output but this is implied by the pre-condition already. *) 
  Definition dfs x (dx : Acc (λ u v, u ∈ succ v) x) : {l | ⦃l⦄ ≡ clos_refl_trans next x}.
  Proof.
    (* We separate the code from the logic *)
    refine (let (m,hm) := dfs_acc [] x _ in exist _ m _).
    + now apply Dfs_iff_Gdfs, dfs_weakest_pre_condition.
    + now apply dfs_post_condition.
  Defined.

  Definition dfs_inlined x (dx : Acc (λ u v, u ∈ succ v) x) : {l | ⦃l⦄ ≡ clos_refl_trans next x}.
  Proof.
    (* We separate the code from the logic *)
    refine (let (m,hm) := dfs_acc_inlined [] x _ in exist _ m _).
    + now apply Dfs_iff_Gdfs, dfs_weakest_pre_condition.
    + now apply dfs_post_condition.
  Defined.

End dfs.

Check dfs_weakest_pre_condition.
Check dfs_inlined.

Extraction Inline dfs_acc_inlined.

Recursive Extraction dfs dfs_inlined. 
