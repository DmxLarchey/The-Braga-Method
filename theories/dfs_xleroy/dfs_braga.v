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

(** The file is complementary to 

             theories/dfs_xleroy/dfs_xleroy.v

    and implements the following DFS algorithm

      let dfs_braga x =
        let rec dfs x a =
          match in_dec x a with
          | true  -> a
          | false -> foldleft dfs (succ x) (x::a)
         in dfs x []

    with external nesting of foldleft following 
    the "Braga method" steps. Internal nesting of foldleft
    can be obtained by a further Extraction Inline directive.

    For its semantics, this algorithm compares mostly to the 
    original DFS algorithm as discussed in the "Braga" book 
    chapter and in the files theories/dfs/*.v herein.

      let dfs_book x =
        let rec dfs v l =
          match l with 
          | []   -> v
          | x::l ->
            match in_dec x v
            | true  -> dfs v l
            | false -> dfs (x::v) (succ x)@l
        in dfs [] [x]

    These two algoritms (dfs_braga & dfs_book) are different 
    but compute the SAME outputs. This equivalence is established
    below as theorem Gdfs_book_braga showing that their respective 
    computational graphs are equivalent. Hence, they also have the 
    same weakest pre-condition: the existence of a finite set 
    containing "x" and stable under "succ". In particular, loops 
    in the succ graph have no impact on termination.

    Their (common) output is the list of points succ-reachable 
    from x. Repetitions are avoided (this is not proved in here
    but the result is available as dfs_no_dups in the file
    theories/dfs/dfs_partial_corr.v).

    The order of the output seems to be the reverse of prefix 
    left-right traversal of the graph (remains TO BE ESTABLISHED).

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

       a : 'a list
       x : 'a
       dfs x a : 'a list *)

    let rec dfs x a =
      match in_dec x a with
      | true  -> a
      | false -> foldleft dfs (succ x) (x::a).

    (* (dfs_braga x) computes the list of nodes
       encountered in a depth first search traversal of
       a graph (ie succ) starting at "x" and avoiding
       repetitions

       x : 'a
       dfs_braga x : 'a list *)

    let dfs_braga x = dfs x []

    (* dfs/dfs_braga do not always terminate, for instance
       when succ x = [1+x].

       Well-foundness of the relation (λ u v, u ∈ succ v)
       is sufficient for termination but NOT mandatory.

       For instance, when succ x = [x], then dfs/dfs_braga
       both terminate. The weakest precondition is described
       below:

       Since dfs_braga x computes a list of nodes containing x 
       and stable under succ, such an invariant must exist for 
       dfs_braga to terminate, and this is indeed a (the weakest)
       sufficient condition for termination.
       See the code below for justifications. *)

*)

Require Import List Relations Utf8 Extraction.

Import ListNotations.

(* We use the wf_sincl_maj induction principle, ie that
   strict reverse inclusion between lists is a well-founded
   relation when restricted by a fixed upper-bound. *)
Require Import induction dfs_abstract.

Section dfs_braga.

  Variable (X : Type).

  Implicit Type l : list X.

  Variables (in_dec : ∀ x l, {x ∈ l} + {x ∉ l})
            (succ : X → list X).

  Local Fact in_wdec l x : x ∈ l ∨ x ∉ l.
  Proof. destruct (in_dec x l); auto. Qed.

  Local Fact eq_wdec (x y : X) : x = y ∨ x ≠  y.
  Proof.
    destruct (in_dec x [y]) as [ [ <- | [] ] | C ]; auto.
    right; contradict C; subst; auto.
  Qed.

  Hint Resolve in_wdec eq_wdec : core.

  Unset Elimination Schemes.

  (** Because of nesting, the below inductive predicates Gdfs
      and Ddfs do not generate powerful enough recursors. We
      implement our own by hand, ie nested fixpoints.*)

  (* This is the computational graph of dfs (below),
     ie the computaional steps described as an inductive
     relation, here nested with that for (foldleft dfs). *)
  Inductive Gdfs : X → list X → list X → Prop :=
    | Gdfs_stop {x a} :     x ∈ a
                          → Gdfs x a a
    | Gdfs_next {x a o} :   x ∉ a
                          → Gfoldleft Gdfs (succ x) (x::a)  o
                          → Gdfs x a o.

  (* The inductive domain of dfs, used as a structural termination
     argument (however in Prop) for dfs. *)
  Inductive Ddfs : X → list X → Prop :=
    | Ddfs_stop {x a} :   x ∈ a
                        → Ddfs x a
    | Ddfs_next {x a} :   x ∉ a
                        → Dfoldleft Gdfs Ddfs (succ x) (x::a)
                        → Ddfs x a.

  Set Elimination Schemes.

  Local Fact Gdfs_inv0 x a o : Gdfs x a o → x ∈ a → a = o.
  Proof. now destruct 1. Qed.

  Local Fact Gdfs_inv1 x a o : Gdfs x a o → x ∉ a → Gfoldleft Gdfs (succ x) (x::a) o.
  Proof. now destruct 1. Qed.

  (* Second projection of the domain Ddfs when x ∉ a,
     inverting the second constructor

             h : x ∉ a   dfl : Dfoldleft Gdfs Ddfs (x::a) (succ x)
           ----------------------------------------------------------
                          d : Ddfs_next h dfl

     while providing precisely the strict sub-term dfl out
     of d : Ddfs_next h dfl . *)
  Local Definition Ddfs_pi {x a} (d : Ddfs x a) :
      x ∉ a → Dfoldleft Gdfs Ddfs (succ x) (x::a) :=
    match d with
    | Ddfs_stop h     => λ C, match C h with end
    | Ddfs_next _ dfl => λ _, dfl
    end.

  Hint Constructors Dfoldleft Gfoldleft Gdfs : core.

  (* We define dfs (with an accumulator of already visited nodes)
     by structural induction on the (inductive) domain argument,
     nested with an externam call to foldleft. *)
  Fixpoint dfs x a (d : Ddfs x a) {struct d} : {o | Gdfs x a o}.
  Proof.
    (* We separate the code from the logic *)
    refine (match in_dec x a with
    | left h  => exist _ a _
    | right h =>
              let (o,ho) := foldleft Gdfs dfs (succ x) (x::a) (Ddfs_pi d h)
              in exist _ o _
    end); eauto.
  Defined.

  Section termination_easy.

    (** Termination is somewhat easy under well-foundedness of succ.

        If we assume that _ ∈ succ _ is a well-founded relation
        then we can show that dfs terminates, in that case
        w/o using partial correctness. We could even drop the
        membership test (in_dec x a) in the code of dfs and
        still get termination in this case, but the output
        could then contain duplicates. *)

    Hypothesis wf_succ : well_founded (λ u v, u ∈ succ v).

    Theorem dfs_wf_termination x a : Ddfs x a.
    Proof.
      induction x as [ x IHx ]
        using (well_founded_induction wf_succ)
        in a |- *.
      destruct (in_dec x a) as [ | H ].
      + now constructor 1.
      + constructor 2; trivial.
        clear H.
        revert IHx; generalize (succ x) (x::a); clear x a.
        intro l; induction l; econstructor; eauto.
    Qed.

  End termination_easy.

  (** Below we do not assume the above strong termination criterium
      and show the properties of dfs by reasonning exclusively
      on the low-level specification of dfs via its computational
      graph Gdfs, ie w/o establishing fixpoint equations for dfs,
      which could be done as an alternative approach (using Gdfs_fun).

      We prove partial correctness and then termination under
      the weakest pre-condition of the existence of a specific
      invariant. dfs actually outputs a least of such invariant. *)

  Section Gdfs_ind.

    (** First, a useful mutual induction principle
        for (Gfoldleft Gdfs) / Gdfs which allows to show:
        - functionality of Gdfs
        - inclusion of Gdfs into Ddfs
        - partial correctness of dfs

        Notice that we have to use a nested fixpoint here. *)

    Variables (P : list X → list X → list X → Prop)
              (Q : X → list X → list X → Prop)

              (HP0 : ∀a, P [] a a)

              (HP1 : ∀ {y a l b o},
                         Gdfs y a b
                       → Q y a b
                       → Gfoldleft Gdfs l b o
                       → P l b o
                       → P (y::l) a o)

              (HQ0 : ∀ {x a},
                         x ∈ a
                       → Q x a a)

              (HQ1 : ∀ {x a o},
                         x ∉ a
                       → Gfoldleft Gdfs (succ x) (x::a) o
                       → P (succ x) (x::a) o
                       → Q x a o).

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

    Theorem Gdfs_mutual_ind : (∀ l a o, Gfoldleft Gdfs l a o → P l a o)
                            ∧ (∀ x a o, Gdfs x a o → Q x a o).
    Proof.
      split; eauto.
      + apply Gfoldleft_ind; eauto.
        intros; eapply HP1; eauto.
        apply Gdfs_ind; auto.
      + apply @Gdfs_ind.
    Qed.

    (* This is for completeness. The same proof term as Gdfs_ind,
       but using an Ltac script with nesting implemented via a call
       to "induction" (ie a call to Gfoldleft_ind). *)
    Local Fixpoint Gdfs_ind_script x a o (d : Gdfs x a o) {struct d} : Q x a o.
    Proof.
      destruct d as [ | ? ? ? H gfl ].
      + now apply HQ0.
      + apply HQ1; trivial.
        clear H.
        induction gfl; eauto.
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
    + intros ? ? ? ? ? ? ? ?%Gdfs_inv1; eauto.
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
     for the purpose of defining dfs by structural
     induction on it, is indeed (equivalent to) the 
     projection of the computational graph Gdfs, ie
     Ddfs indeed characterizes termination of dfs
     according to its description as Gdfs. *)
  Theorem Dfs_iff_Gdfs x a : Ddfs x a ↔ ∃o, Gdfs x a o.
  Proof.
    split.
    + intros (o & ?)%dfs; now exists o.
    + now intros (? & ?%Gdfs_incl_Ddfs).
  Qed.

  Notation next := (λ v u, u ∈ succ v).
  Notation crt_exclude_union R P L := (λ y, ∃i, L i ∧ crt_exclude R P i y).

  (* This is the direct proof of partial correctness of dfs 
     together with that of (foldleft dfs) obtained via their low-level 
     characterization (via Gdfs) to a high-level characterization. *)
  Theorem dfs_partially_correct_mutual :
        (∀ l a o, Gfoldleft Gdfs l a o → ⦃o⦄ ≡ ⦃a⦄ ∪ crt_exclude_union next ⦃a⦄ ⦃l⦄)
      ∧ (∀ x a o, Gdfs x a o           → ⦃o⦄ ≡ ⦃a⦄ ∪ crt_exclude next ⦃a⦄ x).
  Proof.
    apply Gdfs_mutual_ind.
    + intros; now rewrite crt_exclude_union_nil with (A := ⦃_⦄).
    + intros x a l b o _ E1 _ E2 y.
      rewrite E2, E1; split.
      * intros [ [] | (i & H1 & H2) ]; eauto.
        right; exists i; split; auto.
        revert H2; apply crt_exclude_mono.
        intros; apply E1; auto.
      * intros [ | (i & [ <- | Hi ] & H1) ]; auto.
        apply crt_exclude_special with (x := x) in H1
          as [ [ H1 | H1 ] | H1 ]; eauto.
        - right; exists i; split; auto.
          revert H1; apply crt_exclude_mono.
          intro; apply E1.
        - intro z; rewrite <- E1; destruct (in_dec z b); auto.
    + intros x a Hax y; split; auto.
      intros [ | H ]; auto.
      now destruct (crt_exclude_yes _ _ _ _ _ H Hax).
    + intros x a o Hax _ H1 z.
      rewrite H1; split.
      * intros [ [ <- | ] | (i & H2 & H3) ]; eauto.
        right; apply crt_exclude_step with i; auto.
        revert H3; apply crt_exclude_mono; auto.
      * intros [ | Hxz ]; auto.
        apply crt_exclude_last in Hxz
          as [ -> | ]; eauto.
  Qed.

  Corollary dfs_partially_correct x a o : Gdfs x a o → ⦃o⦄ ≡ ⦃a⦄ ∪ crt_exclude next ⦃a⦄ x.
  Proof. apply dfs_partially_correct_mutual. Qed.

  (** We study a more general termination criteria, THE MOST
      GENERAL in fact, using partial correctness, which is typical
      of the case of nested recursive schemes. The proof below
      is *much more involved* than the one assuming that succ is
      well-founded. It uses well-foundedness of strict reverse
      inclusion of lists (under a fixed upper-bound),
      induction principle quite not trivial in itself to
      implement constructivelly, eg w/o counting using decidable
      equality (see utils/sincl_induction.v for details).

      Notice that in that weakest pre-condition case, the membership
      test "in_dec x a" is mandatory otherwise loops inside the succ
      graph would make the dfs algorithm non-terminating.

      The proof proceeds first by well-founded induction on the
      accumulator "a" included in the fixed invariant "i" with
      reverse strict inclusion as wf relation.

      Then, when nesting foldleft, we proceed by structural
      induction on the list argument of foldleft.

      This proof has a similar structure as the one of
      (foldleft free) dfs in theories/dfs/dfs_term.v *)

  Theorem dfs_termination a i : ∀x, x ∈ i ∧ ⦃a⦄ ⊆ ⦃i⦄ ∧ dfs_invar succ ⦃a⦄ ⦃i⦄ → Ddfs x a.
  Proof.
    induction a as [ a IHa ] using (well_founded_induction (wf_sincl_maj i)).
    intros x (G1 & G2 & G3).
    destruct (in_dec x a) as [ H | H ].
    + now constructor 1.
    + constructor 2; trivial.
      assert (IH : ∀ y a', ⦃x::a⦄ ⊆ ⦃a'⦄ → y ∈ i → ⦃a'⦄ ⊆ ⦃i⦄ → dfs_invar succ ⦃a'⦄ ⦃i⦄ → Ddfs y a').
      1: intros; apply IHa; repeat split; eauto. 
      clear IHa; rename IH into IHa.
      assert (Hi : ⦃succ x⦄ ⊆ ⦃i⦄)
        by (destruct (G3 _ G1); now auto).
      cut (⦃x::a⦄ ⊆ ⦃i⦄).
      2: { intros ? [ <- | ]; eauto. }
      generalize (incl_refl (x::a)).
      clear H.
      revert Hi.
      generalize (x::a) at 2 3 4.
      generalize (succ x).
      intros l; induction l as [ | y l IHl ]; intros a' H1 H2 H3.
      * constructor 1.
      * constructor 2.
        - apply IHa; auto.
          intros ? []%G3; eauto.
        - intros o Ho.
          (* Here we use partial correctness for termination because of nesting *)
          generalize (dfs_partially_correct _ _ _ Ho); clear Ho; intros Ho.
          apply IHl; eauto.
          ++ intros z ?%H2; apply Ho; auto.
          ++ intros z Hz%Ho; revert z Hz.
             apply (smallest_crt_exclude _ succ _ _ (in_wdec _)).
             repeat split; eauto.
             revert G3; apply dfs_invar_mono; eauto.
  Qed.

  (** Now we switch to dfs_braga x := dfs x [] *)

  (* The partial correctness of dfs_braga x := dfs x [].
     When it terminates, it outputs a (smallest) succ-stable
     list of which x is a member. *)
  Corollary dfs_braga_partially_correct x o :
       Gdfs x [] o → ⦃o⦄ ≡ clos_refl_trans next x.
  Proof.
    intros H y.
    rewrite <- crt_exclude_empty, dfs_partially_correct; eauto.
    simpl; tauto.
  Qed.

  (* Hence, as a sufficient and necessary condition for dfs_braga to
     terminate, an invariant must exist. *)
  Corollary dfs_braga_weakest_pre_condition x :
      (∃o, Gdfs x [] o) ↔ ∃i, x ∈ i ∧ dfs_braga_invar succ ⦃i⦄.
  Proof.
    split.
    + intros (o & Ho).
      generalize (dfs_partially_correct _ _ _ Ho); clear Ho; intros Ho.
      apply dfs_post_condition in Ho; auto.
      apply smallest_braga_invar_equiv in Ho.
      exists o; apply Ho.
    + intros (i & ? & ?%dfs_braga_invar_iff).
      apply Dfs_iff_Gdfs, dfs_termination with i.
      repeat split; now auto.
  Qed.

  (* This is the total correctness statement of dfs_braga with 
     a high-level specification. Internally dfs_braga calls
     dfs (nested with foldleft). Notice that the domain is the 
     largest possible for dfs_braga because of 
     dfs_braga_weakest_pre_condition.

     The post-condition on the output value is that it
     is a list spanning exactly the reflexive and
     transitive closure of (λ v u, u ∈ succ v) starting
     from x. 
  *)
  Definition dfs_braga x (dx : ∃i, x ∈ i ∧ ∀ x y, x ∈ i → y ∈ succ x → y ∈ i) :
           {l | ⦃l⦄ ≡ clos_refl_trans next x}.
  Proof.
    (* We separate the code from the logic *)
    refine (let (m,hm) := dfs x [] _ in exist _ m _).
    + now apply Dfs_iff_Gdfs, dfs_braga_weakest_pre_condition.
    + now apply dfs_braga_partially_correct.
  Defined.

   (** Reminder:

      let dfs_book x =
        let rec dfs v l =
          match l with 
          | []   -> v
          | x::l ->
            match in_dec x v
            | true  -> dfs v l
            | false -> dfs (x::v) (succ x)@l
        in dfs [] [x] *)

  (* dfs_book as a computational graph *)
  Inductive Gdfs_book : list X → list X → list X → Prop :=
    | Gdfs_bk_stop v :        Gdfs_book v [] v
    | Gdfs_bk_in {v x l o} :  x ∈ v
                            → Gdfs_book v l o
                            → Gdfs_book v (x::l) o
    | Gdfs_bk_out {v x l o} : x ∉ v
                            → Gdfs_book (x::v) (succ x++l) o
                            → Gdfs_book v (x::l) o.

  Fact Gdfs_book_inv v l o :
         Gdfs_book v l o
       → match l with
         | []   => v = o
         | x::l => x ∈ v ∧ Gdfs_book v l o
                 ∨ x ∉ v ∧ Gdfs_book (x::v) (succ x++l) o
         end.
  Proof. destruct 1; auto. Qed.

  Hint Constructors Gdfs_book : core.

  Fact Gdfs_book_app v w l m o : Gdfs_book v l w → Gdfs_book w m o → Gdfs_book v (l++m) o.
  Proof.
    induction 1 in m, o |- *; simpl; eauto.
    constructor 3; eauto.
    rewrite <- app_ass; auto.
  Qed.

  Hint Resolve Gdfs_book_app : core.

  Lemma Gdfs_book_Gfoldleft_dfs v l o : Gdfs_book v l o → Gfoldleft Gdfs l v o.
  Proof. induction 1 as [ | | ? ? ? ? ? ? (? & [])%Gfoldleft_app_inv ]; eauto. Qed.

  Lemma Gdfs_Gdfs_book x a o : Gdfs x a o → Gdfs_book a [x] o.
  Proof.
    revert x a o; apply Gdfs_ind with (P := λ l a o, Gdfs_book a l o); eauto.
    intros ? ? ? ? ? _ [ (? & <-%Gdfs_book_inv) | (? & H2) ]%Gdfs_book_inv _ ?; eauto.
    rewrite <- app_nil_end in H2; eauto.
  Qed.

 (* The dfs_book algorithm and the dfs_braga algorithm have
    equivalent input/output relations. So they have the same
    domain and the same outputs. *)
  Theorem Gdfs_book_braga x o : Gdfs_book [] [x] o ↔ Gdfs x [] o.
  Proof.
    split.
    + now intros; apply Gfoldleft_sg_iff, Gdfs_book_Gfoldleft_dfs.
    + apply Gdfs_Gdfs_book.
  Qed.

  (** A self nested variant of dfs w/o List.app/@ :

      let dfs_book_self x =
        let rec dfs v l =
          match l with 
          | []   -> v
          | x::l ->
            match in_dec x v
            | true  -> dfs v l
            | false -> dfs (dfs (x::v) (succ x)) l
        in dfs [] [x] *)

  (* dfs_book_self as a computational graph *)
  Inductive Gdfs_bs : list X → list X → list X → Prop :=
    | Gdfs_bs_stop v :          Gdfs_bs v [] v
    | Gdfs_bs_in {v x l o} :    x ∈ v
                              → Gdfs_bs v l o
                              → Gdfs_bs v (x::l) o
    | Gdfs_bs_out {v x l w o} : x ∉ v
                              → Gdfs_bs (x::v) (succ x) w
                              → Gdfs_bs w l o
                              → Gdfs_bs v (x::l) o.

  Fact Gdfs_bs_inv v l o :
         Gdfs_bs v l o
       → match l with
         | []   => v = o
         | x::l => x ∈ v ∧ Gdfs_bs v l o
                 ∨ x ∉ v ∧ ∃w, Gdfs_bs (x::v) (succ x) w ∧ Gdfs_bs w l o
         end.
  Proof. destruct 1; eauto. Qed.

  Hint Constructors Gdfs_bs : core.

  Fact Gdfs_bs_app v w l m o : Gdfs_bs v l w → Gdfs_bs w m o → Gdfs_bs v (l++m) o.
  Proof. induction 1 in m, o |- *; simpl; eauto. Qed.

  Fact Gdfs_bs_app_inv v l m o : Gdfs_bs v (l++m) o → ∃w, Gdfs_bs v l w ∧ Gdfs_bs w m o.
  Proof. 
    induction l as [ | x l IHl ] in v,o |- *; simpl; eauto.
    intros [ (? & (? & [])%IHl) | (? & ? & ? & (? & [])%IHl) ]%Gdfs_bs_inv; eauto.
  Qed.

  Lemma Gdfs_bs_book v l o : Gdfs_bs v l o → Gdfs_book v l o.
  Proof. induction 1; eauto. Qed.

  Hint Resolve Gdfs_bs_app : core.

  Lemma Gdfs_book_bs v l o : Gdfs_book v l o → Gdfs_bs v l o.
  Proof. induction 1 as [ | | ? ? ? ? ? _ (? & ? & ?)%Gdfs_bs_app_inv ]; eauto. Qed.

  Hint Resolve Gdfs_bs_book Gdfs_book_bs : core.

 (* The dfs_book algorithm and the dfs_book_self algorithm have
    equivalent input/output relations. *)
  Theorem Gdfs_book_book_self v l o : Gdfs_book v l o ↔ Gdfs_bs v l o.
  Proof. split; auto. Qed.

  Lemma Gdfs_bs_fun {v l o₁ o₂} : Gdfs_bs v l o₁ → Gdfs_bs v l o₂ → o₁ = o₂.
  Proof.
    induction 1 as [ | | v x l w o H1 _ IH2 _ IH3 ] in o₂ |- *; intros G%Gdfs_bs_inv; auto;
      destruct G as [ [] | (H3 & ? & H4 & H5) ]; tauto || eauto.
    apply IH2 in H4; subst; auto.
  Qed.

  Inductive Ddfs_bs : list X → list X → Prop :=
    | Ddfs_bs_stop v :      Ddfs_bs v []
    | Ddfs_bs_in {v x l} :  x ∈ v
                          → Ddfs_bs v l
                          → Ddfs_bs v (x::l)
    | Ddfs_bs_out {v x l} : x ∉ v
                          → Ddfs_bs (x::v) (succ x)
                          → (∀w, Gdfs_bs (x::v) (succ x) w → Ddfs_bs w l)
                          → Ddfs_bs v (x::l).

  Hint Constructors Ddfs_bs : core.

  Fact Gdfs_bs_Ddfs_bs {v l} : (∃o, Gdfs_bs v l o) → Ddfs_bs v l.
  Proof.
    intros (o & H).
    induction H as [ | | v x l w o H1 H2 IH2 ]; eauto.
    constructor 3; auto.
    intros ? H3.
    now rewrite (Gdfs_bs_fun H3 H2).
  Qed.

  Let is_nnil l := match l with [] => False | _ => True end.

  Let dhead {l} : is_nnil l → X :=
    match l with
    | []   => λ void, match void with end
    | y::_ => λ _, y
    end.
  
  Let dtail {l} : is_nnil l → list X :=
    match l with
    | []   => λ void, match void with end
    | _::l => λ _, l
    end.

  Local Definition Ddfs_bs_pi1 {v x l} (d : Ddfs_bs v (x::l)) :
      x ∈ v → Ddfs_bs v l :=
    match d in Ddfs_bs v m return ∀ hm : is_nnil m, dhead hm ∈ v → Ddfs_bs v (dtail hm) with
    | Ddfs_bs_stop _    => λ C _, match C with end
    | Ddfs_bs_in _ d    => λ _ _, d
    | Ddfs_bs_out C _ _ => λ _ h, match C h with end
    end I.

  Local Definition Ddfs_bs_pi2 {v x l} (d : Ddfs_bs v (x::l)) :
      x ∉ v → Ddfs_bs (x::v) (succ x) :=
    match d in Ddfs_bs v m return ∀ hm : is_nnil m, dhead hm ∉ v → Ddfs_bs (dhead hm::v) (succ (dhead hm)) with
    | Ddfs_bs_stop _    => λ C _, match C with end
    | Ddfs_bs_in h _    => λ _ C, match C h with end
    | Ddfs_bs_out _ d _ => λ _ _, d
    end I.

  Local Definition Ddfs_bs_pi3 {v x l} (d : Ddfs_bs v (x::l)) :
      x ∉ v → ∀{w}, Gdfs_bs (x::v) (succ x) w → Ddfs_bs w l :=
    match d in Ddfs_bs v m return ∀ hm : is_nnil m, dhead hm ∉ v → ∀w, Gdfs_bs (dhead hm::v) (succ (dhead hm)) w → Ddfs_bs w (dtail hm) with
    | Ddfs_bs_stop _    => λ C _, match C with end
    | Ddfs_bs_in h _    => λ _ C, match C h with end
    | Ddfs_bs_out _ _ d => λ _ _, d
    end I.

  Fixpoint dfs_bs {v l} (d : Ddfs_bs v l) : {o | Gdfs_bs v l o}.
  Proof.
    refine (match l return Ddfs_bs _ l → _ with
    | []   => λ d, exist _ v _
    | x::l => λ d,
      match in_dec x v with
      | left hx  => let (o,ho) := dfs_bs v l (Ddfs_bs_pi1 d hx)
                    in exist _ o _
      | right hx => let (w,hw) := dfs_bs (x::v) (succ x) (Ddfs_bs_pi2 d hx) in
                    let (o,ho) := dfs_bs w l (Ddfs_bs_pi3 d hx hw)
                    in exist _ o _
      end
    end d); eauto.
  Defined.

  Definition dfs_braga_bs x : (∃o, Gdfs_bs [] [x] o) → {o | Gdfs_bs [] [x] o} :=
    λ hx, dfs_bs (Gdfs_bs_Ddfs_bs hx).

End dfs_braga.

Check dfs_braga.

Extraction Inline dfs.
Recursive Extraction dfs_braga.

Extraction Inline foldleft.
Extraction dfs_braga.

Check dfs_braga_bs.

Extraction Inline dfs_bs.
Extraction dfs_braga_bs.




