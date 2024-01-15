(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             JF Monin                   [**]                *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                            [**] Affiliation Verimag -- UGA *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2.1 FREE SOFTWARE LICENSE AGREEMENT        *)
(**************************************************************)

(** Following the "Braga method", we proceed with 
    the extraction of dfs_xl using dfs (with an accumulator)
    nested with foldleft (either externally or internal, 
    see below), ie one of the examples discussed by X. Leroy
    in its CoqPL 2024 paper:

       https://inria.hal.science/hal-04356563/document

    The DFS algo. as originaly presented in the "Braga" book
    chapter, and in the files theories/dfs/*.v herein, is
    different but computes a similar output. It avoids 
    nesting foldleft by working on two lists directly.
    It is more comparable to dfs_braga below.

    Assuming in_dec and succ, the algorithm we study here 
    in this file, the one proposed by X. Leroy in the above
    reference is

      let dfs_xl x :=
        let rec dfs x a =
          match in_dec x a with
          | true  -> a
          | false -> x::foldleft dfs (succ x) a
        in dfs x []
 
    whereas in dfs_braga.v we study 

      let rec dfs_braga x =
        let rec dfs x a =
          match in_dec x a with
          | true  -> a
          | false -> foldleft dfs (succ x) (x::a)
        in dfs x []

    Notice the difference in the position in the programs
    where "x" is appended to the output (or accumulator "a").
    This has a *major* impact on the weakest pre-condition,
    ie when does dfs_xl or dfs_braga actually terminate:
    - the call (dfs_xl x) terminates if and *only if*
      "x" is in the well-founded part of the succ relation,
      hence when there are finitely many points succ-reachable
      from "x" and also no cycle exists in that part of the
      succ-graph;
    - the call (dfs_braga x) terminates if and only if
      there are finitely many points succ-reachable from
      "x". The existence of cycles does not impact termination.

    Additionally, dfs_xl does output neither the left-right
    nor the right-left prefix traversal of the graph. Here left 
    (resp. right) means the head (resp. tail) of the list "succ x". 
    See the file dfs_xleroy/dfs_tests.ml for counter-examples.

    On the other hand, dfs_braga seems to output the reverse 
    of the left-right prefix traversal of the graph. To be
    confirmed with a proof though.

    Notice that X. Leroy presents his dfs_xl example with an
    internal nesting of a (specialized version) of foldleft,
    denoted as dfs_int and dfs_xl_int below.

    We implement that internal nesting but we also implement 
    an external nesting of a "parametric" foldleft,
    which adds some extra complexity to this example, ie
    managing a partial high-order functional program of 
    which the parameters are partial functions, however 
    possibly instructive for other cases.

    Below we also discuss the restrictive (a bit too strong
    in the case of dfs_[int/ext]) termination argument X. Leroy 
    uses, ie that the successor graph is well-founded, and later,
    after the proof of partial correctness, we give the 
    "weakest pre-condition" for termination of both dfs
    and dfs_xl.

    (* f : 'b -> 'a -> 'a
       l : 'b list
       x : 'a
       foldleft f l x : 'a *)

    let rec foldleft f l a =
      match l with
      | []   -> a
      | y::l -> foldleft f l (f y a);;

    (* Below, we have 

       in_dec : 'a -> 'a list -> bool  
       succ : 'a -> 'a list 

       where (in_dec x a) tests whether x belongs to a or not 
       and (succ x) computes the (list of) successors of x *)

    (* (dfs x a) computes the list of nodes
       encountered in a depth first search traversal of
       a graph (described by "succ") starting at "x", avoiding
       repeating nodes or crossing "a" twice. 

       x : 'a
       a : 'a list
       dfs x a : 'a list *)

    let rec dfs x a =
      match in_dec x a with
      | true  -> a
      | false -> x::foldleft dfs (succ x) a

    (* (dfs_xl x) computes the list of nodes
       encountered in a depth first search traversal of
       a graph (ie succ) starting at "x" and avoiding
       repetitions

       x : 'a
       dfs_xl x : 'a list *)

    let dfs_xl x = dfs x []

    (* Well-foundness of the relation (λ u v, u ∈ succ v) 
       at x is sufficient for termination of dfs_xl x 
       but also MANDATORY as established below. *)

*)

Require Import List Relations Utf8 Extraction.

Import ListNotations.

Require Import dfs_abstract.

Section dfs_xleroy.

  Variable (X : Type).

  Implicit Types (l : list X) (x : X).

  Variables (in_dec : ∀ x l, {x ∈ l} + {x ∉ l})
            (succ : X → list X).

  Local Fact in_wdec l x : x ∈ l ∨ x ∉ l.
  Proof. destruct (in_dec x l); auto. Qed.

  Local Fact eq_wdec x y : x = y ∨ x ≠ y.
  Proof.
    destruct (in_dec x [y]) as [ [ <- | [] ] | C ]; auto.
    right; contradict C; subst; auto.
  Qed.

  Hint Resolve in_wdec eq_wdec : core.

  Unset Elimination Schemes.

  (** Because of nesting, the below inductive predicates Gdfs
      and Ddfs do not generate powerful enough recursors. We
      implement our own by hand, ie nested fixpoints, see
      Gdfs_ind below.*)

  (* This is the computational graph of dfs (below),
     ie the computational steps described as an inductive
     relation, here nested with that for (foldleft dfs). *)
  Inductive Gdfs : X → list X → list X → Prop :=
    | Gdfs_stop {x a} :     x ∈ a
                          → Gdfs x a a
    | Gdfs_next {x a o} :   x ∉ a
                          → Gfoldleft Gdfs (succ x) a o
                          → Gdfs x a (x::o).

  (* The inductive domain of dfs used as a structural 
     termination argument for the computation of dfs.
     The correspondance with Gdfs is established below. *)
  Inductive Ddfs : X → list X → Prop :=
    | Ddfs_stop {x a} :     x ∈ a
                          → Ddfs x a
    | Ddfs_next {x a} :     x ∉ a
                          → Dfoldleft Gdfs Ddfs (succ x) a
                          → Ddfs x a.

  Set Elimination Schemes.

  Local Fact Gdfs_inv0 x a o : Gdfs x a o → x ∈ a → a = o.
  Proof. now destruct 1. Qed.

  Local Fact Gdfs_inv1 x a o :
          Gdfs x a o
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
  Local Definition Ddfs_pi {x a} (d : Ddfs x a) :
      x ∉ a → Dfoldleft Gdfs Ddfs (succ x) a :=
    match d with
    | Ddfs_stop yes   => λ no, match no yes with end
    | Ddfs_next _ dfl => λ _, dfl
    end.

  Hint Constructors Dfoldleft Gfoldleft Gdfs : core.

  (** We can already define dfs with an accumulator nested
      with foldleft both with an external (dfs_ext) and an internal
      nesting (dfs_int). Here the pre/post conditions
      are of low-level (computational) nature. *)

  (* We define dfs (with an accumulator of already visited nodes)
     by structural induction on the (inductive) domain argument, nested
     with an external call to foldleft.

     Using refine(... _ ...) in the presentation, we separate the code 
     from the post-condition logic (here just eauto thanks to hints). 
     The pre-condition logic is just "Ddfs_pi d h" and could also be 
     postponed with a hole _ but we use a manually defined term Ddfs_pi 
     above that is intentionnaly and carefully hand-written to witness 
     structural decrease. *)
  Fixpoint dfs_ext x a (d : Ddfs x a) {struct d} : {o | Gdfs x a o}.
  Proof.
    refine (match in_dec x a with
    | left h  =>    exist _ a _
    | right h => let (o,ho) := foldleft Gdfs dfs_ext (succ x) a (Ddfs_pi d h)
                 in exist _ (x::o) _
    end); eauto.
  Defined.

  (* We define dfs (with an accumulator of already visited nodes)
     by structural induction on the (inductive) domain argument, nested
     with an internal call to (a specialize version of) foldleft. 

     Since we inline foldleft, we also need to use the structural projections
     Dfl_pi[1,2] of its domain to justify structural decrease. *)
  Fixpoint dfs_int x a (d : Ddfs x a) {struct d} : {o | Gdfs x a o}.
  Proof.
    refine (match in_dec x a with
    | left h  => 
            exist _ a _
    | right h => 
         let (o,ho) :=
          (fix dfs_list l a dl {struct dl} : sig (Gfoldleft Gdfs l a) :=
            match l return Dfoldleft _ _ l _ → _ with
            | []   => λ _, exist _ a _
            | y::m => λ d, let (b,hb) := dfs_int y a (Dfl_pi1 d)     in
                           let (o,ho) := dfs_list m b (Dfl_pi2 d hb) in
                           exist _ o _
            end dl) (succ x) a (Ddfs_pi d h) 
         in exist _ (x::o) _
    end); eauto.
  Defined.

  (** Now we study the high-level semantics, ie both termination
      and partial correctness. We start with the (a bit strong for
      dfs_[int,ext]) termination argument proposed by X. Leroy that does
      not need partial correctness information to establish termination,
      a situation which is a bit unusual for nested algorithms. *) 

  (** Termination (sufficiency), ie the predicate Ddfs x a holds, 
      is somewhat easy under well-foundedness of x in the succ relation. *)

  Theorem dfs_termination_Acc x a : Acc (λ u v, u ∈ succ v) x → Ddfs x a.
  Proof.
    induction 1 as [ x _ IHx ] in a |- *.
    destruct (in_dec x a) as [ | H ].
    + now constructor 1.
    + constructor 2; trivial.
      clear H.
      revert IHx; generalize (succ x) a; clear x a.
      intro l; induction l; econstructor; eauto.
  Qed.

  (** The study of (necessary conditions for) termination is more 
      complicated and requires a proof of partial correctness.

      Below we show that the above (strong) termination condition
      Acc (λ u v, u ∈ succ v) x is actually *necessary* for termination,
      but only in the case of dfs_xl x := dfs x [].
 
      For this, we show that when the computational graph of dfs
      outputs something from inputs "x" and "a", then it must be that
      any infinite succ sequence from "x" eventually meets "a", expressed
      as the bar inductive predicate (bar ⦃a⦄ x).

      This is one aspect of partial correctness, the other aspect
      being that the output of (dfs x a) is a list containing
      the "y" that are either in "a" or reachable from "x" using a 
      (succ) path no crossing "a". *)

  (** We start by factoring out a general mutual recursor for Gdfs
      that will be used to show many properties of Gdfs. *)

  Section Gdfs_ind.

    (** First, a useful mutual induction principle 
        for (Gfoldleft Gdfs) / Gdfs which allows to show:
        - functionality of Gdfs
        - inclusion of Gdfs into Ddfs
        - partial correctness of dfs_[int,ext]

        Notice that we have to use a nested fixpoint here. *)

    Variables (P : list X → list X → list X → Prop)
              (Q : X → list X → list X → Prop)

              (HP0 : ∀a, P [] a a)

              (HP1 : ∀ {x a l b o},
                         Gdfs x a b 
                       → Q x a b 
                       → Gfoldleft Gdfs l b o
                       → P l b o  
                       → P (x::l) a o)

              (HQ0 : ∀ {x a},
                         x ∈ a
                       → Q x a a)

              (HQ1 : ∀ {x a o},
                         x ∉ a
                       → Gfoldleft Gdfs (succ x) a o
                       → P (succ x) a o
                       → Q x a (x::o)).

    (* This requires a nesting with the generic Gfoldleft_ind above.
       It could be done with an inlined nested fixpoint but we separate
       here for readability.
       This nesting is comparable to that of foldleft/dfs except
       that the structural arguments are the computational graphs,
       not the inductive domains. Pattern matching on these is ok
       since the recursor is over Prop, ie neither Set nor Type. *)
    Fixpoint Gdfs_ind {x a o} (d : Gdfs x a o) {struct d} : Q x a o :=
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
    Local Fixpoint Gdfs_ind_script x a o (d : Gdfs x a o) {struct d} : Q x a o.
    Proof.
      destruct d as [ | ? ? ? H gfl ].
      + now apply HQ0.
      + apply HQ1; trivial.
        clear H.
        induction gfl; eauto.
    Qed.

    (* This is for completeness but not really needed below *)
    Theorem Gdfs_mutual_ind : (∀ l a o, Gfoldleft Gdfs l a o → P l a o)
                            ∧ (∀ x a o, Gdfs x a o → Q x a o).
    Proof.
      split; eauto.
      + apply Gfoldleft_ind; eauto.
        intros; eapply HP1; eauto.
        apply Gdfs_ind; auto.
      + apply @Gdfs_ind.
    Qed.

  End Gdfs_ind.

  (* We can deduce functionality of Gdfs. *)
  Local Lemma Gdfs_fun {x a o₁ o₂} : Gdfs x a o₁ → Gdfs x a o₂ → o₁ = o₂.
  Proof.
    intros H; revert o₂; pattern x, a, o₁; revert x a o₁ H.
    apply Gdfs_ind with (P := λ l a o, ∀o2, Gfoldleft Gdfs l a o2 → o = o2).
    + now intros ? ? ?%Gfoldleft_inv.
    + intros ? ? ? ? ? _ IH1 _ IH2 ? (? & [])%Gfoldleft_inv.
      apply IH2; erewrite IH1; eauto.
    + intros ? ? ? ? ?%Gdfs_inv0; auto.
    + intros ? ? ? ? ? ? [] []%Gdfs_inv1; easy || f_equal; eauto.
  Qed.

  (* And then the inclusion of Gdfs in Ddfs. *)
  Local Lemma Gdfs_incl_Ddfs : ∀ x a o, Gdfs x a o → Ddfs x a.
  Proof.
    apply Gdfs_ind with (P := λ l a o, Dfoldleft Gdfs Ddfs l a)
                        (Q := λ x a o, Ddfs x a);
      [ constructor 1 | | constructor 1 | constructor 2 ]; eauto.
    intros x a l b o1 H1 IH1 H2 IH2.
    constructor; auto.
    intros ? H3.
    now rewrite (Gdfs_fun H3 H1).
  Qed.

  (* Hence the domain Ddfs, characterized inductivelly
     for the purpose of defining dfs_[int,ext] by structural
     induction on it, is indeed (equivalent to) the 
     projection of the computational graph Gdfs, ie
     Ddfs indeed characterizes termination of dfs
     according to its description as Gdfs. *)
  Theorem Dfs_iff_Gdfs x a : Ddfs x a ↔ ∃o, Gdfs x a o.
  Proof.
    split.
    + intros (o & ?)%dfs_int; now exists o.
    + now intros (? & ?%Gdfs_incl_Ddfs).
  Qed.

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

  Notation next := (λ v u, u ∈ succ v).

  (** See dfs_abstract for crt_exclude R P x y which means there
      is a R-path from x to y avoiding P, except possibly at y *)
  Fact crt_exclude_bar P x y : crt_exclude next P x y → bar P x → bar P y.
  Proof.
    induction 1 as [ | x y z H1 H2 H3 IH3 ] using crt_exclude_ind; auto.
    intros [ []%H1 | ]%bar_inv; eauto.
  Qed.

  (** There is a P-avoiding R-path from a point of L to y *)
  Notation crt_exclude_union R P L := (λ y, ∃i, L i ∧ crt_exclude R P i y).

  (** We get a stronger partial correctness post-condition that when
      considering the dfs_braga variant of the DFS algorithm. Indeed,
      in this case when dfs x a outputs a result (ie terminates), it 
      must be that bar ⦃a⦄ x further holds, ie any infinite path from
      x must cross ⦃a⦄. *)
  Theorem dfs_partially_correct x a o :
            Gdfs x a o
          → bar ⦃a⦄ x
          ∧ ⦃o⦄ ≡ ⦃a⦄ ∪ crt_exclude next ⦃a⦄ x.
  Proof.
    revert x a o.
    apply Gdfs_ind with (P := λ l a o, Forall (bar ⦃a⦄) l ∧ ⦃o⦄ ≡ ⦃a⦄ ∪ crt_exclude_union next ⦃a⦄ ⦃l⦄).
    + intros a; split; auto.
      intros; now rewrite crt_exclude_union_nil with (A := ⦃_⦄).
    + intros x a l b o _ (B1 & E1) _ (B2 & E2); split.
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
    + intros x a Hax; split.
      * now constructor 1.
      * intros y; split; auto.
        intros [ | H ]; auto.
        now destruct (crt_exclude_yes _ _ _ _ _ H Hax).
    + intros x a o Hax _ (B1 & E1); split.
      * constructor 2; now apply Forall_forall.
      * intros z; simpl.
        rewrite E1; split.
        - intros [ <- | [ | (? & []) ] ]; eauto.
        - intros [ | [ | [] ]%crt_exclude_inv ]; auto.
  Qed.

  Corollary dfs_pre_condition x a o : Gdfs x a o → bar ⦃a⦄ x.
  Proof. apply dfs_partially_correct. Qed.

  Corollary dfs_post_condition x a o : Gdfs x a o → ⦃o⦄ ≡ ⦃a⦄ ∪ crt_exclude next ⦃a⦄ x.
  Proof. apply dfs_partially_correct. Qed.

  (* Termination of dfs_[int,ext] with non empty a(ccumulator) is
     more complicated than that of dfs_xl x := dfs x [].
     In particular, we use partial correctness for this. *)
  Lemma dfs_termination_bar P x : bar P x → ∀a, P ⊆ ⦃a⦄ → Ddfs x a.
  Proof.
    induction 1 as [ x Hx | x Hx IHx ].
    + constructor 1; eauto.
    + intros a Ha.
      destruct (in_dec x a) as [ | H ].
      * constructor 1; auto.
      * constructor 2; trivial.
        clear H.
        revert IHx a Ha.
        rewrite <- Forall_forall.
        generalize (succ x).
        clear x Hx.
        induction 1 as [ | x l H Hl IHl ]; intros a Ha.
        - constructor 1.
        - constructor 2; eauto.
          intros o Ho.
          apply IHl.
          intros b Hb%Ha.
          apply dfs_post_condition with (1 := Ho); auto.
  Qed.

  Hint Resolve dfs_pre_condition : core.

  (* We get a precise (necessary and sufficient) condition for
     the termination of dfs with an arbitrary a(ccumulator). *)
  Theorem dfs_weakest_pre_condition x a :
            (∃o, Gdfs x a o) ↔ bar ⦃a⦄ x.
  Proof.
    split.
    + intros []; eauto.
    + intros H; apply Dfs_iff_Gdfs, dfs_termination_bar with (1 := H); auto.
  Qed.

  Lemma dfs_xl_pre_condition x o : Gdfs x [] o → Acc (λ u v, u ∈ succ v) x.
  Proof. now intros ?%dfs_pre_condition%bar_empty. Qed.

  Lemma dfs_xl_post_condition x o : Gdfs x [] o → ⦃o⦄ ≡ clos_refl_trans next x.
  Proof.
    intros H y.
    rewrite <- crt_exclude_empty, dfs_post_condition; eauto.
    simpl; tauto.
  Qed.

  Hint Resolve dfs_xl_pre_condition : core.

  Theorem dfs_xl_weakest_pre_condition x :
            (∃o, Gdfs x [] o) ↔ Acc (λ u v, u ∈ succ v) x.
  Proof.
    split.
    + intros []; eauto.
    + now intros ?%(dfs_termination_Acc _ [])%Dfs_iff_Gdfs.
  Qed.

  (* This is the dfs_xl algorithm associated to Gdfs with the most
     general specification since the pre-condition is the weakest-possible. 
     The post-condition does not include the absence of succ-cycles in
     the output but this is implied by the pre-condition already. *) 
  Definition dfs_xl_ext x (dx : Acc (λ u v, u ∈ succ v) x) : {l | ⦃l⦄ ≡ clos_refl_trans next x}.
  Proof.
    (* We separate the code from the logic *)
    refine (let (m,hm) := dfs_ext x [] _ in exist _ m _).
    + now apply Dfs_iff_Gdfs, dfs_xl_weakest_pre_condition.
    + now apply dfs_xl_post_condition.
  Defined.

  (* The same with internal nesting of foldleft *) 
  Definition dfs_xl_int x (dx : Acc (λ u v, u ∈ succ v) x) : {l | ⦃l⦄ ≡ clos_refl_trans next x}.
  Proof.
    (* We separate the code from the logic *)
    refine (let (m,hm) := dfs_int x [] _ in exist _ m _).
    + now apply Dfs_iff_Gdfs, dfs_xl_weakest_pre_condition.
    + now apply dfs_xl_post_condition.
  Defined.

End dfs_xleroy.

Check dfs_xl_weakest_pre_condition.
Check dfs_xl_ext.
Check dfs_xl_int.

(* We can extract dfs_xl_ext with external nesting of foldleft *)
Extraction Inline dfs_ext.
Recursive Extraction dfs_xl_ext.

(* We can extract dfs_xl_int with internal nesting of foldleft, ie
   the reference algorithm of X. Leroy. *)
Extraction Inline dfs_int.
Extraction dfs_xl_int.

(* If we further instruct the extraction mechanism to inline
   foldleft, then when extracting dfs_xl_ext as above, we get the
   SAME extraction as for dfs_xl_int, except for irrelevant 
   internal names. *)
Extraction Inline foldleft.
Extraction dfs_xl_ext. 
