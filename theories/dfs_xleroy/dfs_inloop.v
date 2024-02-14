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

(* TODO: remove this comment
   Work in progress: consistency with [2] and the other files
   of the current directory
   DONE: accumulator at the end everywhere, Gfoldleft instead of iterel
   TODO: use only Braga_book techniques
 *)

(* The Braga method applied to dfs, expressed with an internal loop *)
(* Jean-François Monin, Verimag, Univ. Grenoble-Alpes, 2024         *)

(* Using ideas coming from
[1] Xavier Leroy, Well-founded recursion done right, CoqPL 2024
    https://inria.hal.science/hal-04356563/document
[2] Dominique Larchey-Wendling and Jean-François Monin
    The Braga Method https://cnrs.hal.science/hal-03338785v1
[3] Jean-François Monin, Smaller Inversions and Unleashed Recursion in Coq (talk)
    https://www-verimag.imag.fr/~monin/Talks/sir.pdf

The algorithm provided in [1] is not quite the usual dfs algorithm
Chapter 1 shows the use of the Braga method on the rectified version
of this algorithm.
Then Chapter 2 provides a number of transformations from
this algorithm to the one considered in [2].

We use small inversions explained in [3].

 *)

Require Import List Relations Utf8 Extraction.

Import ListNotations.

#[local] Infix "∈" := In (at level 70, no associativity).
#[local] Infix "∉" := (λ x a, ¬ In x a) (at level 70, no associativity).

Require Import dfs_abstract.

(* Gfoldleft is convenient for dfs_stack.
   Then we reuse it for Gdfs_list as well (but keep Ddfs_list mutual recursive) *)

(* Reminder
Inductive Gfoldleft (X Y : Type) (F : Y → X → X → Prop) : list Y → X → X → Prop :=
    Gfl_nil : ∀ a : X, Gfoldleft F [] a a
  | Gfl_cons : ∀ (y : Y) (a : X) (l : list Y) (b o : X),
                 F y a b → Gfoldleft F l b o → Gfoldleft F (y :: l) a o.
 *)

(* Small inversion of Gfoldleft *)
Inductive Gfoldleft_nil {X Y : Type} (R : Y → X → X → Prop) (a : X) : X → Prop :=
| Gfl_nil_nil : Gfoldleft_nil R a a.
Inductive Gfoldleft_cons {X Y : Type} (R : Y → X → X → Prop) y l (a : X) : X → Prop :=
| Gfl_cons_cons b c : R y a b → Gfoldleft R l b c → Gfoldleft_cons R y l a c.
Definition Gfoldleft_dispatch {X Y} (R : Y → X → X → Prop) l a : X → Prop :=
  match l with
  | [] => Gfoldleft_nil R a
  | y :: l => Gfoldleft_cons R y l a
  end.

Lemma Gfoldleft_inv {X Y : Type} {R : Y → X → X → Prop}
  {a l b} (i : Gfoldleft R l a b) : Gfoldleft_dispatch R l a b.
Proof. destruct i; econstructor; eassumption. Qed.
(* End of small inversion *)

(* TODO Diterel? *)

Lemma Gfoldleft_first {X Y} (R : Y → X → X → Prop) y1 {y2 a l b} :
  (R y1 a ⊆ R y2 a) → Gfoldleft R (y1 :: l) a b → Gfoldleft R (y2 :: l) a b.
Proof.
  intros rr i.
  destruct (Gfoldleft_inv i) as [b c r i0].
  apply (Gfl_cons (rr _ r) i0).
Qed.

Section dfs.

  Variable (X : Type).

  Implicit Type l : list X.

  Variables (in_dec : ∀ x l, {x ∈ l} + {x ∉ l})
            (succs : X → list X).

  (* Chapter 1. On the program provided in [1] *)

  (* Inductive definition of the intended input-output relation, à la Prolog *)

  (* Following naming conventions of [2] we name it Gdfs (graph of the relation),
     not to be confused with the graph to be traversed by dfs!
     In the sequel "graph" stands for the latter graph;
     we use "i/o relation" for Gdfs and similar relation such as Gdf_list.

     The original intended OCaml recursive function is expressed using
     an embedded fixpoint on lists, but could be as well be expressed using
     mutual recursion: the underlying i/o relation is the same.
     Using a basic embedded fixpoint on lists in Coq seems to be feasible at
     first sight (see [1]) but only if the structural decreasing of the special
     argument does not depend on the list argument of the internal fixpoint.
     It works in [1] because the decreasing argument considered ther is quite
     simple, actually too simple to scale up to the standard dfs algorithm,
     which is actually a *partial* recursive algorithm, whose termination
     depends on global properties of the traversed graph.

     As is well-known, when the structurally decreasing argument of a fixpoint
     is not just an input data, an additional inductive input argument of sort
     Prop is needed.
     For the sake of simplicity it is preferable to keep a simple type for
     the output (e.g., list X for dfs). This is possible when the recursive scheme
     is simple enough, including with the simple embedded fixpoint of [1].
     Unfortunately, in more general situations the structurally decreasing
     inductive domain depends on outputs provided by embedded recursive calls.
     This issue is dealt with in the Braga method by pairing the output with
     (a proof of) a postcondition, which is simply the i/o relation.
     A somewhat unpleasant consequence is that intended tail recursive calls
     tend to be decomposed into annoying "knitting/unknitting" steps
       let   (result, postcond) := terminal_recursive_call in
       exist result new_postcond
    Additional penalty : the Coq code is then no longer tail recursive.
    Considering extraction this is harmless since the extraction process is smart
    enough to recover tail recursion through a clever optimization step.
    However we show below a way to keep terminal recursivity at the Coq level
    using a propositional continuation.

    We try make the intended (OCaml) functional algorithm as apparent as possible,
    as well as structurally decreasing terms.
    For (proofs of) postconditions, a possible technique is to use the [refine]
    tactic, with jokers for postconditions.
    See for example the sibling file dfs_xleroy.v by Dominique.
    However the management of postconditions turns out to be quite simple
    in the present framework -- basically, constructors of the i/o relation.
    Here we choose to provide fully explicit terms, using greek letters
    for propositional arguments and ad-hoc spacing for better readibility.

    An additional interest of the sibling file dfs_xleroy.v is to formalize
    and experiment a partial version of List.fold_left, of independent interest.
    (Here we stick to mutual recursion, as in [1].)
    Extraction seems to behave better with mutual recursion -- no silent
    unused argument is introduced.
 *)

  Inductive Gdfs : X → list X → list X → Prop :=
  | Gdfs_stop {a x} :     x ∈ a
                        → Gdfs x a a
  | Gdfs_next {a x o} :   x ∉ a
                        → Gfoldleft Gdfs (succs x) (x :: a) o
                        → Gdfs x a o.

  Definition Gdfs_list : list X → list X → list X → Prop := Gfoldleft Gdfs.

  Definition Gdfs_simple := λ x, Gdfs x [].

  (* Corresponding inductive domain, but mutual recursive *)
  Inductive Ddfs : X → list X → Prop :=
  | Ddfs_stop {a x} :     x ∈ a
                        → Ddfs x a
  | Ddfs_next {a x} :     x ∉ a
                        → Ddfs_list (succs x) (x :: a)
                        → Ddfs x a

  with Ddfs_list : list X → list X → Prop :=
  | Ddfs_list_nil {a} :          Ddfs_list [] a
  | Ddfs_list_cons {y l a}  :    Ddfs y a
                               → (∀b, Gdfs y a b → Ddfs_list l b)
                               → Ddfs_list (y :: l) a.

  (* Structurally smaller projections *)
  Definition Ddfs_next_pi {x a} (δ : Ddfs x a) :
    x ∉ a → Ddfs_list (succs x) (x :: a) :=
    match δ in Ddfs x a return x ∉ a → Ddfs_list _ _ with
    | Ddfs_next _ δ  => λ _, δ
    | Ddfs_stop yes  => λ no, match no yes with end
    end.

  Definition Ddfs_list_cons_pi1 {y l a} (δ : Ddfs_list (y :: l) a) : Ddfs y a :=
    match δ in Ddfs_list yl a return
          let shape := match yl with y :: l => True | _ => False end in
          let y     := match yl with y :: l => y    | _ => y     end in
          shape → Ddfs y a with
    | Ddfs_list_cons δ₁ δ₂ => λ _, δ₁
    | _                    => λ absu, match absu with end
    end I.

  Definition Ddfs_list_cons_pi2 {y l a} (δ : Ddfs_list (y :: l) a) :
    ∀b, Gdfs y a b → Ddfs_list l b :=
    match δ in Ddfs_list yl a return
          let shape := match yl with y :: l => True | _ => False end in
          let y     := match yl with y :: l => y    | _ => y     end in
          let l     := match yl with y :: l => l    | _ => l     end in
          shape → ∀b, Gdfs y a b → Ddfs_list l b with
    | Ddfs_list_cons δ₁ δ₂ => λ _, δ₂
    | _                    => λ absu, match absu with end
    end I.

  Arguments exist {A P}.

  Fixpoint dfs (x: X) (a: list X)                         (* *) (δ: Ddfs x a) {struct δ}
    : {o | Gdfs x a o} :=
    match in_dec x a with
    | left yes => exist a                                 (* *) (Gdfs_stop yes)
    | right no =>
        let fix dfs_list l a                              (* *) (δ : Ddfs_list l a) {struct δ}
          : {o | Gdfs_list l a o} :=
          match l                                         (* *) return Ddfs_list l a -> _
          with
          | [] =>                                         (* *) λ _,
                  exist a                                 (* *) (Gfl_nil a)
          | y :: l =>                                     (* *) λ δ,
              let (b, γab) := dfs y a                     (* *) (Ddfs_list_cons_pi1 δ)
                                                          (* *) in let δ := Ddfs_list_cons_pi2 δ b γab
              in let (o, γbo) := dfs_list l b             (* *) δ
              in exist o                                  (* *) (Gfl_cons γab γbo)
          end                                             (* *) δ
        in let (o, γ) := dfs_list (succs x) (x :: a)      (* *) (Ddfs_next_pi δ no)
        in exist o                                        (* *) (Gdfs_next no γ)
    end.

  (* Main program: the inlined nested variant of dfs_cycle *)
  Definition dfs_cycle_inld x : Ddfs x [] → {o | Gdfs x [] o} := dfs x [].

  (* Elimination of (un-)knitting steps; intended tail-recursive calls are recovered *)
    Fixpoint dfs_tr (x: X) (a: list X)       (* *) (δ: Ddfs x a) {struct δ}
    : {o | Gdfs x a o} :=
    match in_dec x a with
    | left yes => exist a                    (* *) (Gdfs_stop yes)
    | right no =>
                                             (* *) let post o := Gdfs x a o (* keeps the global a *)
        in let fix dfs_list l a              (* *) (δ : Ddfs_list l a) {struct δ}
             :                               (* *) (∀ o, Gdfs_list l a o → post o) →
               {o | post o} :=
          match l                            (* *) return Ddfs_list l a -> _
          with
          | [] =>                            (* *) λ _ κ,
                  exist a                    (* *) (κ a (@Gfl_nil _ _ Gdfs a)) (*Gfl_nil a*)
          | y :: l =>                        (* *) λ δ κ,
              let (b, γab) := dfs_tr y a     (* *) (Ddfs_list_cons_pi1 δ)
                                             (* *) in let δ := Ddfs_list_cons_pi2 δ b γab
                                             (* *) in let κ := λ o γbo, κ o (Gfl_cons γab γbo)
              in dfs_list l b                (* *) δ κ
          end                                (* *) δ
        in dfs_list (succs x) (x :: a)       (* *) (Ddfs_next_pi δ no) (λ o g, Gdfs_next no g)
    end.

  (* Main *)
  Definition dfs_cycle_inld_tr x : Ddfs x [] → {o | Gdfs x [] o} := dfs_tr x [].

  (* Chapter 2. Derivation of fully tail-recursive algorithms, including the one in [2] *)

  (* 2.1 Compacting the 2 recursive functions into a single embedded recursive one *)

  (* Rearrangement of dfs_list above, where the call to dfs is inlined *)

  (* Ad-hoc versions of Gdfs etc. could be defined, but the previous ones
     can be re-used. Then there is no need to prove equivalence between
   specifications.  *)

  Lemma Gdfs_singleton {a x o} : x ∉ a → Gdfs_list [x] a o → Gdfs x a o.
  Proof.
    intros no γ. apply (Gdfs_next no).
    destruct (Gfoldleft_inv γ) as [b o γab γbo]; clear γ.
    destruct (Gfoldleft_inv γbo); clear γbo.
    destruct γab as [a x yes | a x b _no γ]; [case (no yes) | exact γ].
  Qed.

  Lemma Gdfs_singleton_nil {x o} : Gdfs_list [x] [] o → Gdfs x [] o.
  Proof. exact (λ γ, Gdfs_singleton (λ (absu : x ∈ []), absu) γ). Qed.

  Fixpoint dfs_list_self l a                  (* *) (δ : Ddfs_list l a) {struct δ}
    : {o | Gdfs_list l a o}  :=
    match l                                   (* *) return Ddfs_list l a -> _
    with
    | [] =>                                   (* *) λ _,
        exist a                               (* *) (Gfl_nil a)
    | x :: l =>                               (* *) λ δ,
        let (b, γab) :=
          match in_dec x a with
          | left yes => exist a               (* *) (Gdfs_stop yes)
          | right no =>
                                              (* *) let δ := Ddfs_list_cons_pi1 δ
                                              (* *) in let δ := Ddfs_next_pi δ no
              in let (o, γ) := dfs_list_self (succs x) (x :: a)
                                              (* *) δ
              in exist o                      (* *) (Gdfs_next no γ)
          end
                                              (* *) in let δ := Ddfs_list_cons_pi2 δ b γab
        in let (o, γbo) := dfs_list_self l b  (* *) δ
        in exist o                            (* *) (Gfl_cons γab γbo)
    end                                       (* *) δ.

  (* Main *)
  Definition dfs_cycle_self x                 (* *) (δ : Ddfs x [])
    : {o | Gdfs x [] o} :=
                                              (* *) let δ := Ddfs_list_cons δ (λ b _, Ddfs_list_nil)
    in let (o, γ) := dfs_list_self [x] []     (* *) δ
    in exist o                                (* *) (Gdfs_singleton_nil γ).

  (* Elimination of (un-)knitting steps:
     an additional parameter for post is needed in the (internal) dfs_listk *)
  Fixpoint dfs_list_self_tr
                        l a                (* *) (δ : Ddfs_list l a) {struct δ}
    :                                      (* *) ∀ (post : list X → Prop), (∀ o, Gdfs_list l a o → post o) →
      {o | post o} :=
                                           (* *) λ post,
    match l                                (* *) return Ddfs_list l a → _
    with
    | [] =>                                (* *) λ _ κ,
        exist a                            (* *) (κ a (@Gfl_nil _ _ Gdfs a))
    | x :: l =>                            (* *) λ δ κ,
      let (b, γab) :=
          match in_dec x a with
          | left yes => exist a            (* *) (Gdfs_stop yes)
          | right no =>
                                           (* *) let δ := Ddfs_list_cons_pi1 δ
                                           (* *) in let δ := Ddfs_next_pi δ no
            in dfs_list_self_tr (succs x) (x :: a)
                                           (* *) δ (Gdfs x a) (λ o γ, Gdfs_next no γ)
          end
                                           (* *) in let δ := Ddfs_list_cons_pi2 δ b γab
      in dfs_list_self_tr l b                  (* *) δ post (λ o γbo, κ o (Gfl_cons γab γbo))
    end                                    (* *) δ.

  (* Main *)
  Definition dfs_cycle_self_tr x           (* *) (δ : Ddfs x [])
    : {o | Gdfs x [] o} :=
                                           (* *) let δ := Ddfs_list_cons δ (λ b _, Ddfs_list_nil)
    in dfs_list_self_tr [x] []             (* *) δ (Gdfs x []) (λ o γ, Gdfs_singleton_nil γ).

  (* 2.2 Elimination of embedded recursion using a stack s *)

  (* Two versions can be considered.
  The first one looks closer to dfs_list in dfs_self above.
  let dfs =
    let rec dfs_list_stack l s a =
      match l with
      | [] ->
        ( match s with
          | [] -> a
          | l :: s -> dfs_list_stack l s a
        )
      | x :: l ->
        if in_dec x a then dfs_list_stack l s a
        else dfs_list_stack (succs x) (l :: s) (x :: a)
    in fun x -> dfs_list_stack [x] [] []

   The second version is close to the dfs algorithm given in [2]
   let dfs =
    let rec dfs_stack s a =
      match s with
      | [] -> a
      | [] :: [] -> a
      | [] :: s -> dfs_stack s a (* so s is itself a cons *)
      | (x :: l) :: s ->
          if in_dec x a then dfs_stack (l :: s) a
          else dfs_stack (succs x :: l :: s) (x :: a)
    in fun x -> dfs_stack [[x]] []


   *)

  Definition stack X := list (list X).

  (* The inductive domain is expressed with the following type instead of
     list X → stack X → list X → Prop, in order to be shared with dfs_stack *)
  Inductive Ddfs_stack : stack X → list X → Prop :=
  | Ddfs_stack_nil {a} :               Ddfs_stack [] a
  | Ddfs_stack_nil_emp {a} :           Ddfs_stack ([] :: []) a
  | Ddfs_stack_nil_push {l s a}  :     Ddfs_stack (l :: s) a
                                     → Ddfs_stack ([] :: l :: s) a
  | Ddfs_stack_cons_stop {x l s a} :   x ∈ a
                                     → Ddfs_stack (l :: s) a
                                     → Ddfs_stack ((x :: l) :: s) a
  | Ddfs_stack_cons_next {x l s a} :   x ∉ a
                                     → Ddfs_stack (succs x :: l :: s) (x :: a)
                                     → Ddfs_stack ((x :: l) :: s) a.

  (* Structurally smaller projections *)

  Definition Ddfs_stack_nil_push_pi {l s a} (δ : Ddfs_stack ([] :: l :: s) a) :
    Ddfs_stack (l :: s) a :=
    match δ in Ddfs_stack els a return
          let shape := match els with [] :: l :: s => True | _ => False end in
          let l     := match els with [] :: l :: s => l    | _ => l     end in
          let s     := match els with [] :: l :: s => s    | _ => s     end in
          shape → Ddfs_stack (l :: s) a with
    | Ddfs_stack_nil_push δ => λ _, δ
    | _               => λ absu, match absu with end
    end I.

  Definition Ddfs_stack_cons_stop_pi {x l s a} (δ : Ddfs_stack ((x :: l) :: s) a) :
    x ∈ a → Ddfs_stack (l :: s) a :=
    match δ in Ddfs_stack xls a return
          let shape := match xls with (x :: l) :: s => True | _ => False end in
          let x     := match xls with (x :: l) :: s => x    | _ => x     end in
          let l     := match xls with (x :: l) :: s => l    | _ => l     end in
          let s     := match xls with (x :: l) :: s => s    | _ => s     end in
          shape → x ∈ a → Ddfs_stack (l :: s) a with
    | Ddfs_stack_cons_stop yes δ => λ _ _, δ
    | Ddfs_stack_cons_next no δ  => λ _ yes, match no yes with end
    | _               => λ absu _, match absu with end
    end I.

  Definition Ddfs_stack_cons_next_pi {x l s a} (δ : Ddfs_stack ((x :: l) :: s) a) :
    x ∉ a → Ddfs_stack (succs x :: l :: s) (x :: a) :=
    match δ in Ddfs_stack xls a return
          let shape := match xls with (x :: l) :: s => True | _ => False end in
          let x     := match xls with (x :: l) :: s => x    | _ => x     end in
          let l     := match xls with (x :: l) :: s => l    | _ => l     end in
          let s     := match xls with (x :: l) :: s => s    | _ => s     end in
          shape → x ∉ a → Ddfs_stack (succs x :: l :: s) (x :: a) with
    | Ddfs_stack_cons_next no δ  => λ _ _, δ
    | Ddfs_stack_cons_stop yes δ => λ _ no, match no yes with end
    | _               => λ absu _, match absu with end
    end I.

  (* *)

  Inductive Gdfs_stack : stack X → list X → list X → Prop :=
  | Gdfs_stack_nil {a} :                 Gdfs_stack [] a a
  | Gdfs_stack_nil_emp {a} :             Gdfs_stack ([] :: []) a a
  | Gdfs_stack_nil_push {l s a o}  :     Gdfs_stack (l :: s) a o
                                       → Gdfs_stack ([] :: l :: s) a o
  | Gdfs_stack_cons_stop {x l s a o} :   x ∈ a
                                       → Gdfs_stack (l :: s) a o
                                       → Gdfs_stack ((x :: l) :: s) a o
  | Gdfs_stack_cons_next {x l s a o} :   x ∉ a
                                       → Gdfs_stack (succs x :: l :: s) (x :: a) o
                                       → Gdfs_stack ((x :: l) :: s) a o.

  Definition Gdfs_stack_list: list X → stack X → list X → list X → Prop :=
    λ l s, Gdfs_stack (l :: s).

  Fixpoint dfs_list_stack l s a (δ : Ddfs_stack (l :: s) a) {struct δ} : {o | Gdfs_stack_list l s a o} :=
    match l                                                             (* *) return Ddfs_stack (l :: s) a → _
    with
    | [] =>                                                             (* *) λ δ,
        match s                                                         (* *) return Ddfs_stack ([] :: s) a → _
        with
        | []     =>                                                     (* *) λ _,
                    exist a                                             (* *) Gdfs_stack_nil_emp
        | l :: s =>                                                     (* *) λ δ,
                    let (o, γ) := dfs_list_stack l s a                  (* *) (Ddfs_stack_nil_push_pi δ)
                    in exist o                                          (* *) (Gdfs_stack_nil_push γ)
        end                                                             (* *) δ
    | x :: l =>                                                         (* *) λ δ,
        match in_dec x a with
        | left yes =>
                    let (o, γ) := dfs_list_stack l s a                  (* *) (Ddfs_stack_cons_stop_pi δ yes)
                    in exist o                                          (* *) (Gdfs_stack_cons_stop yes γ)
        | right no =>
                    let (o, γ) := dfs_list_stack (succs x) (l :: s) (x :: a)
                                                                        (* *) (Ddfs_stack_cons_next_pi δ no)
                    in exist o                                          (* *) (Gdfs_stack_cons_next no γ)
        end
    end δ.

  (* Main *)
  Definition dfs_cycle_stack x :                                        (* *)  Ddfs_stack ([x] :: []) [] →
                                 {o | Gdfs_stack_list [x] [] [] o} := dfs_list_stack [x] [] [].

  (* *)

  Fixpoint dfs_stack s a (δ : Ddfs_stack s a) {struct δ} : {o | Gdfs_stack s a o} :=
    match s                                                                 (* *) return Ddfs_stack s a → _
    with
    | []     =>                                                             (* *) λ _,
              exist a                                                       (* *) Gdfs_stack_nil
    | [] :: [] =>                                                           (* *) λ δ,
              exist a                                                       (* *) Gdfs_stack_nil_emp
    | [] :: s =>                                                            (* *) λ δ,
              let (o, γ) := dfs_stack s a                                   (* *) (Ddfs_stack_nil_push_pi δ)
              in exist o                                                    (* *) (Gdfs_stack_nil_push γ)
    | (x :: l) :: s =>                                                      (* *) λ δ,
        match in_dec x a with
        | left yes => let (o, γ) := dfs_stack (l :: s) a                    (* *) (Ddfs_stack_cons_stop_pi δ yes)
                      in exist o                                            (* *) (Gdfs_stack_cons_stop yes γ)
        | right no => let (o, γ) := dfs_stack (succs x :: l :: s) (x :: a)  (* *) (Ddfs_stack_cons_next_pi δ no)
                      in exist o                                            (* *) (Gdfs_stack_cons_next no γ)
        end
    end δ.

  (* Main *)
  Definition dfs_book_eff x :                                               (* *)  Ddfs_stack ([[x]]) [] →
                              {o | Gdfs_stack [[x]] [] o} := dfs_stack [[x]] [].

  (* Specification and correctness of dfs_list_stack / Gdfs *)

  Definition Gdfs_list_star := Gfoldleft Gdfs_list.

  Inductive Gdfs_list_plus l s a o : Prop :=
  | Gdfs_list_plus_in b :   Gdfs_list l a b
                          → Gdfs_list_star s b o
                          → Gdfs_list_plus l s a o.

  (* From Gdfs_list_star to Gdfs_simple *)

  Lemma Gdfs_list_star_Gdfs x o : Gdfs_list_star [[x]] [] o → Gdfs_simple x o.
  Proof.
    intro γxo.
    destruct (Gfoldleft_inv γxo) as [c o γxc γco]; destruct (Gfoldleft_inv γco); clear γxo γco.
    destruct (Gfoldleft_inv γxc) as [b c γxb γbc]; destruct (Gfoldleft_inv γbc); clear γxc γbc.
    exact γxb.
  Qed.

  (* *)

  Fact Gdfs_list_plus_corr1 a :
    Gdfs_list_plus [] [] a a.
  Proof.
    exists a; exact (Gfl_nil a).
  Qed.

  Fact Gdfs_list_plus_corr2 {l s a o} :
      Gdfs_list_plus l s a o
    → Gdfs_list_plus [] (l :: s) a o.
  Proof.
    destruct 1 as [b γab γbo].
    exists a; [exact (Gfl_nil a) | exact (Gfl_cons γab γbo)].
  Qed.

  Fact Gdfs_list_plus_corr3 {x l s a o} (yes : x ∈ a) :
      Gdfs_list_plus l s a o
    → Gdfs_list_plus (x :: l) s a o.
  Proof.
    destruct 1 as [b γab γbo].
    exists b; [exact (Gfl_cons (Gdfs_stop yes) γab) | exact γbo].
  Qed.

  Fact Gdfs_list_plus_corr4 {x l s a o} (no : x ∉ a) :
      Gdfs_list_plus (succs x) (l :: s) (x :: a) o
    → Gdfs_list_plus (x :: l) s a o.
  Proof.
    destruct 1 as [b γxab γbo].
    destruct (Gfoldleft_inv γbo) as [c o γbc γco].
    exists c; [exact (Gfl_cons (Gdfs_next no γxab) γbc) | exact γco].
  Qed.

  Lemma Gdfs_list_stack_corr {l s a o} :   Gdfs_stack_list l s a o
                                        → Gdfs_list_plus l s a o.
  Proof.
    revert l s; intros l0 s0 γ;
    change (match l0 :: s0 with
            | [] => True
            | l :: s => Gdfs_list_plus l s a o
            end);
    induction γ as [a | a | l s a o γ Hγ
                   | x l s a o yes γ Hγ
                   | x l s a o no γ Hγ]; clear l0 s0.
    - exact I.
    - apply Gdfs_list_plus_corr1.
    - apply Gdfs_list_plus_corr2, Hγ.
    - apply (Gdfs_list_plus_corr3 yes), Hγ.
    - apply (Gdfs_list_plus_corr4 no), Hγ.
  Qed.

  Lemma Gdfs_list_stack_compl l s a o :   Gdfs_list_plus l s a o
                                        → Gdfs_stack_list l s a o.
  Proof.
    intros [b γab γbo]. red.
    (* Pas si facile ; peut-être faire dfs_stack_compl avant *)
  Abort.
    (*
    revert o γbo.
    induction γab as [ a | x a l b o γab _ γbo].
    - intros o γbo.
      induction γbo as [ a | l a s b o γab γ γbo].
      + constructor.
      + apply (Gdfs_stack_nil_push).
      induction s as [ | l s Hs].
      + destruct (Gfoldleft_inv γbo). constructor.
      + apply (Gdfs_stack_nil_push). γbo).
    - induction γab as [ a | x a l b o γab _ γbo].
      + constructor.
      + destruct γab as [a x yes | a x b no γxab].
        * exact (Gdfs_stack_cons_stop yes γbo).
        * apply (Gdfs_stack_cons_next no). admit.
*)

   (*
  (* ---------------------------------------------------------------------- *)
  (* Recursive equations of dfs_stack *)
  Fact dfs_stack_eqn0 {a} (δ : Ddfs_stack [] a) : dfs_stack [] a δ = a.
  Proof. destruct (Ddfs_stack_inv δ); cbn. reflexivity. Qed.

  Fact dfs_stack_eqn1 {a} (δ : Ddfs_stack [[]] a) : dfs_stack [[]] a δ = a.
  Proof. destruct (Ddfs_stack_inv δ); cbn. reflexivity. Qed.

  Fact dfs_stack_eqn2 {l s a} (δ : Ddfs_stack ([] :: l :: s) a) :
    dfs_stack ([] :: l :: s) a δ = dfs_stack (l :: s) a (Ddfs_stack_nil_push_pi δ).
  Proof. destruct (Ddfs_stack_inv δ); cbn. reflexivity. Qed.

  Fact dfs_stack_eqn3 {x l s a} (yes : x ∈ a) (δ : Ddfs_stack ((x :: l) :: s) a) :
    dfs_stack ((x :: l) :: s) a δ = dfs_stack (l :: s) a (Ddfs_stack_cons_stop_pi δ yes).
  Proof.
    destruct (Ddfs_stack_inv δ) as [yes' δ | no δ]; cbn.
    - destruct (in_dec x a) as [_ | no].
      + reflexivity.
      + case (no yes).
    - case (no yes).
  Qed.

  Fact dfs_stack_eqn4 {x l s a} (no : x ∉ a) (δ : Ddfs_stack ((x :: l) :: s) a) :
    dfs_stack ((x :: l) :: s) a δ =
    dfs_stack (succs x :: l :: s) (x :: a) (Ddfs_stack_cons_next_pi δ no).
   Proof.
     destruct (Ddfs_stack_inv δ) as [yes δ | no' δ]; cbn.
     - case (no yes).
     - destruct (in_dec x a) as [yes | _].
      + case (no yes).
      + reflexivity.
   Qed.
*)

  (* dfs_list_stack is a special case of dfs_stack
   Lemma dfs_list_stack_same {l s a} (δ δ' : Ddfs_stack (l :: s) a) :
     dfs_stack (l :: s) a δ = dfs_list_stack l s a δ'. *)
  (* Semble couvert par Gdfs_stack_list l s := Gdfs_stack (l :: s) *)

  (* Corollaire amusant : dfs_list_stack ne dépend pas de δ *)
  (* TODO determinisme de dfs_list_stack *)
(*   Corollary dfs_list_stack_domirr l s a (δ δ' : Ddfs_stack (l :: s) a) :
     dfs_list_stack l s a δ = dfs_list_stack l s a δ'.
   Proof.
     rewrite <- (dfs_list_stack_same δ δ), <-(dfs_list_stack_same δ δ').
     reflexivity.
   Qed.
*)
  Definition Ddfs_stack_nil_l {s a} : Ddfs_stack s a → Ddfs_stack ([] :: s) a :=
    match s with
    | [] => λ _, Ddfs_stack_nil_emp
    | l :: s => λ δ, (Ddfs_stack_nil_push δ)
    end.

  Lemma Gdfs_stack_case {s a o} (γ : Gdfs_stack s a o) :
    match s with [] => a = o | l :: s => Gdfs_stack_list l s a o end.
  Proof.
    destruct γ as [a | a | l s a o γ
                     | x l s a o yes γ
                     | x l s a o no γ]; try red.
    - reflexivity.
    - apply Gdfs_stack_nil_emp.
    - exact (Gdfs_stack_nil_push γ).
    - exact (Gdfs_stack_cons_stop yes γ).
    - exact (Gdfs_stack_cons_next no γ).
  Qed.

  (* A correctness proof of dfs_stack using correctness of dfs_list_stack / Gdfs *)

  Lemma Gdfs_stack_corr {s a o} :   Gdfs_stack s a o
                                  → Gdfs_list_star s a o.
  Proof.
    intro γ. generalize (Gdfs_stack_case γ).
    destruct s as [ | l s]; clear γ; intro γ.
    - case γ. apply Gfl_nil.
    - destruct (Gdfs_list_stack_corr γ) as [b γab γbo]. exact (Gfl_cons γab γbo).
  Qed.

  (*
  (* TODO cmplétude ? *)
  Lemma Gdfs_stack_compl {s a o} :   Gdfs_list_star s a o
                                   → Gdfs_stack s a o.
  Proof.
    induction 1 as [ a | l a s c o γac _ γco].
    - apply Gdfs_stack_nil.
    - revert o γco.
      induction γac as [ a | x a l b c γab γbc' fcb]; intros o γco.
      + generalize (Gdfs_stack_case γco).
        destruct s as [ | l s]; clear γco; intro γco.
        * case γco. apply Gdfs_stack_nil_emp.
        * exact (Gdfs_stack_nil_push γco).
      +
        destruct γab as [ a x yes | a x b no γxab].
        * apply (Gdfs_stack_cons_stop yes). apply fcb, γco.
        * apply (Gdfs_stack_cons_next no).
          Check (fcb o γco).

*)

   (* 2.3 Flattening s in dfs_stack provides the algorithm considered in [2] *)

   Fixpoint flatten {X : Type} (ll : list (list X)) : list X :=
     match ll with
     | [] => []
     | l :: ll => l ++ flatten ll
     end.

   (* Inductive domain of dfs_flatten *)

   Inductive Ddfs_flatten : list X → list X → Prop :=
   | Ddfs_flatten_nil {a} :              Ddfs_flatten [] a
   | Ddfs_flatten_cons_stop {x ls a} :   x ∈ a
                                      → Ddfs_flatten ls a
                                      → Ddfs_flatten (x :: ls) a
   | Ddfs_flatten_cons_next {x ls a} :   x ∉ a
                                      → Ddfs_flatten (succs x ++ ls) (x :: a)
                                      → Ddfs_flatten (x :: ls) a.

  (* Structurally smaller projections *)

  Definition Ddfs_flatten_cons_stop_pi {x ls a} (δ : Ddfs_flatten (x :: ls) a) :
    x ∈ a → Ddfs_flatten ls a :=
    match δ in Ddfs_flatten xls a return
          let shape := match xls with x :: ls => True | _ => False end in
          let x     := match xls with x :: ls => x    | _ => x     end in
          let ls    := match xls with x :: ls => ls   | _ => ls    end in
          shape → x ∈ a → Ddfs_flatten ls a with
    | Ddfs_flatten_cons_stop yes δ => λ _ _, δ
    | Ddfs_flatten_cons_next no δ  => λ _ yes, match no yes with end
    | _               => λ absu _, match absu with end
    end I.

  Definition Ddfs_flatten_cons_next_pi {x ls a} (δ : Ddfs_flatten (x :: ls) a) :
    x ∉ a → Ddfs_flatten (succs x ++ ls) (x :: a) :=
    match δ in Ddfs_flatten xls a return
          let shape := match xls with x :: ls => True | _ => False end in
          let x     := match xls with x :: ls => x    | _ => x     end in
          let ls    := match xls with x :: ls => ls   | _ => ls    end in
          shape → x ∉ a → Ddfs_flatten (succs x ++ ls) (x :: a) with
    | Ddfs_flatten_cons_next no δ  => λ _ _, δ
    | Ddfs_flatten_cons_stop yes δ => λ _ no, match no yes with end
    | _               => λ absu _, match absu with end
    end I.

  (* Syntactic specification of dfs_flatten *)

  Inductive Gdfs_flatten : list X → list X → list X → Prop :=
  | Gdfs_flatten_nil {a} :                  Gdfs_flatten [] a a
  | Gdfs_flatten_cons_stop {x ls a o} :     x ∈ a
                                          → Gdfs_flatten ls a o
                                          → Gdfs_flatten (x :: ls) a o
  | Gdfs_flatten_cons_next {x ls a o} :     x ∉ a
                                          → Gdfs_flatten (succs x ++ ls) (x :: a) o
                                          → Gdfs_flatten (x :: ls) a o.

  (* *)

  Fixpoint dfs_flatten lls a                                      (* *) (δ : Ddfs_flatten lls a) {struct δ}
    : {o | Gdfs_flatten lls a o} :=
    match lls                                                     (* *) return Ddfs_flatten lls a → _
    with
    | []     =>                                                   (* *) λ _,
                exist a                                           (* *) Gdfs_flatten_nil
    | x :: lls =>                                                 (* *) λ δ,
        match in_dec x a with
        | left yes =>
            let (o, γ) := dfs_flatten lls a                       (* *) (Ddfs_flatten_cons_stop_pi δ yes)
            in exist o                                            (* *) (Gdfs_flatten_cons_stop yes γ)
        | right no =>
            let (o, γ) := dfs_flatten (succs x ++ lls) (x :: a)   (* *) (Ddfs_flatten_cons_next_pi δ no)
            in exist o                                            (* *) (Gdfs_flatten_cons_next no γ)
        end
    end δ.

  (* Main *)
  Definition dfs_book x :                                         (* *)  Ddfs_flatten [x] [] →
                          {o | Gdfs_flatten [x] [] o} := dfs_flatten [x] [].

  (* Relating dfs_flatten with dfs_stack *)

  Remark Gdfs_stack_nil_all {s a o} : Gdfs_stack s a o → Gdfs_stack ([] :: s) a o.
  Proof.
    destruct 1 as [a | a | l s a o γ
                   | x l s a o yes γ
                   | x l s a o no  γ ]; cbn; try apply Gdfs_stack_nil_push.
    - apply Gdfs_stack_nil_emp.
    - apply Gdfs_stack_nil_emp.
    - apply (Gdfs_stack_nil_push γ).
    - apply (Gdfs_stack_cons_stop yes γ).
    - apply (Gdfs_stack_cons_next no γ).
  Qed.

  (* An inductive characterization of flatten in the spirit of Gdfs_stack *)
  Inductive iflatten : list (list X) → list X → Prop :=
  | ifl_nil : iflatten [] []
  | ifl_cons_nil {s ls} : iflatten s ls → iflatten ([] :: s) ls
  | ifl_cons_cons {x l s ls} : iflatten (l :: s) ls → iflatten ((x :: l) :: s) (x :: ls).

  (* Equivalence between iflatten and flatten *)
  Lemma iflatten_flatten s : iflatten s (flatten s).
  Proof.
    induction s as [ | l s Hs]; cbn.
    - constructor.
    - induction l as [ | x l Hl]; now constructor.
  Qed.

  Corollary iflatten_flatten_eq {s ls} : flatten s = ls → iflatten s ls.
  Proof. intro e. case e. apply iflatten_flatten. Qed.

  Lemma flatten_iflatten {s ls} : iflatten s ls → flatten s = ls.
  Proof.
    intro ifl. induction ifl as [ | s ls ifl Hifl | s x l ls ifl Hifl]; cbn.
    - reflexivity.
    - exact Hifl.
    - case Hifl; reflexivity.
  Qed.

  Corollary iflatten_app {s ls l} : iflatten s ls → iflatten (l :: s) (l ++ ls).
  Proof. intro ifl. case (flatten_iflatten ifl). apply iflatten_flatten. Qed.

  (* Recursive small inversion of iflatten on its second argument *)
  Inductive iflatten_nil : list (list X) → Prop :=
  | ifln_nil : iflatten_nil []
  | ifln_cons_nil {s} : iflatten_nil s → iflatten_nil ([] :: s).
  Inductive iflatten_cons x ls : list (list X) → Prop :=
  | iflc_cons_nil {s} : iflatten_cons x ls s → iflatten_cons x ls ([] :: s)
  | iflc_cons_cons {l s} : iflatten (l :: s) ls → iflatten_cons x ls ((x :: l) :: s).
  Definition iflatten_dispatch s ls :=
    match ls with
    | [] => iflatten_nil s
    | x :: ls => iflatten_cons x ls s
    end.

  Lemma iflatten_inv {s ls} : iflatten s ls → iflatten_dispatch s ls.
  Proof.
    intro ifl.
    induction ifl as [ | s ls ifl Hifl | x l s ls ifl Hifl]; try (constructor; exact ifl).
    destruct ls as [ | x ls]; constructor; exact Hifl.
  Qed.
  (* End of small inversion *)

  Lemma Gdfs_iflatten_corr {s a o ls} :
    Gdfs_flatten ls a o → iflatten s ls → Gdfs_stack s a o.
  Proof.
    intros γ ifl. generalize (iflatten_inv ifl). clear ifl. revert s.
    induction γ as [ a | x ls a o yes γ Hγ | x ls a o no γ Hγ]; cbn; intros s ifl.
    - induction ifl as [ s | s ifl Hifl].
      + apply Gdfs_stack_nil.
      + apply Gdfs_stack_nil_all. apply Hifl.
    - induction ifl as [ s ifl Hifl | l s ifl].
      + apply Gdfs_stack_nil_all. apply Hifl.
      + apply (Gdfs_stack_cons_stop yes), Hγ, iflatten_inv, ifl.
    - induction ifl as [ s ifl Hifl | l s ifl].
      + apply Gdfs_stack_nil_all. apply Hifl.
      + apply (Gdfs_stack_cons_next no), Hγ, iflatten_inv.
        apply iflatten_app, ifl.
  Qed.

  (* *)

  Lemma Gdfs_flatten_corr_eq {s a o ls} :
    Gdfs_flatten ls a o → flatten s = ls → Gdfs_stack s a o.
  Proof.
    intros γ e. exact (Gdfs_iflatten_corr γ (iflatten_flatten_eq e)).
  Qed.

  Corollary Gdfs_flatten_corr {s a o} :
    Gdfs_flatten (flatten s) a o → Gdfs_stack s a o.
  Proof. intro γ. apply (Gdfs_flatten_corr_eq γ eq_refl). Qed.

  Lemma Gdfs_flatten_compl {s a o} :
    Gdfs_stack s a o → Gdfs_flatten (flatten s) a o.
  Proof.
    induction 1 as [a | a | l s a o γ Hγ
                   | x l s a o yes γ Hγ
                   | x l s a o no γ Hγ]; cbn.
    - constructor.
    - constructor.
    - exact Hγ.
    - apply (Gdfs_flatten_cons_stop yes Hγ).
    - apply (Gdfs_flatten_cons_next no Hγ).
  Qed.

  (* Small inversion Gdfs_flatten *)

  Inductive Gdfs_flatten_part_nil : list X → list X → Prop :=
  | Gdfs_flatten_part_nil_nil {a} :                  Gdfs_flatten_part_nil a a.
  Inductive Gdfs_flatten_part_cons x ls : list X → list X → Prop :=
  | Gdfs_flatten_part_cons_stop {a o} :     x ∈ a
                                          → Gdfs_flatten ls a o
                                          → Gdfs_flatten_part_cons x ls a o
  | Gdfs_flatten_part_cons_next {a o} :     x ∉ a
                                          → Gdfs_flatten (succs x ++ ls) (x :: a) o
                                          → Gdfs_flatten_part_cons x ls a o.
  Definition Gdfs_flatten_dispatch (ls : list X) : list X → list X → Prop :=
    match ls with
    | []      => Gdfs_flatten_part_nil
    | x :: ls => Gdfs_flatten_part_cons x ls
    end.
  Definition Gdfs_flatten_inv {ls a o} (γ : Gdfs_flatten ls a o) : Gdfs_flatten_dispatch ls a o.
  Proof. destruct γ; constructor; assumption. Qed.
  (* End of small inversion *)

  Lemma dfs_flatten_same {s a o o'} :
    Gdfs_stack s a o → Gdfs_flatten (flatten s) a o' → o = o'.
  Proof.
    induction 1 as [a | a | l s a o γ Hγ
                   | x l s a o yes γ Hγ
                   | x l s a o no γ Hγ]; cbn; intro γ'.
    - destruct (Gdfs_flatten_inv γ') as [a]. reflexivity.
    - destruct (Gdfs_flatten_inv γ') as [a]. reflexivity.
    - cbn in Hγ. generalize γ'. destruct γ' as [ a | x ls a o' yes | x ls a o' no]; try clear γ'.
      + exact Hγ.
      + exact Hγ.
      + exact Hγ.
   - destruct (Gdfs_flatten_inv γ') as [a o' _ γ'0 | a o' no _ ].
      + apply (Hγ γ'0).
      + case (no yes).
   - destruct (Gdfs_flatten_inv γ') as [a o' yes _ | a o' _ γ'0 ].
      + case (no yes).
      + exact (Hγ γ'0).
  Qed.

  Ltac unflatten := repeat (change (?l ++ flatten ?s) with (flatten (l :: s))).

  Definition Ddfs_stack_flatten {a s} (δ : Ddfs_stack s a) : Ddfs_flatten (flatten s) a.
  Proof.
    refine ( (fix loop s a (δ : Ddfs_stack s a) {struct δ}: _ := _) s a δ).
    destruct δ as [a | a | l s a | x l s a yes δ | x l s a no δ]; cbn; unflatten.
    - constructor.
    - constructor.
    - apply loop, δ.
    - apply (Ddfs_flatten_cons_stop yes), loop, δ.
    - apply (Ddfs_flatten_cons_next no). unflatten. apply loop, δ.
  Defined.

  Lemma Gdfs_flatten_Gdfs {s a o} :
    Gdfs_flatten (flatten s) a o → Gdfs_list_star s a o.
  Proof. intro γ. apply Gdfs_stack_corr. apply (Gdfs_flatten_corr γ). Qed.

  (* Correctness of dfs_book_eff and dfs_book / Gdfs *)

  Corollary Gdfs_book_eff_Gdfs {x o} :
    Gdfs_stack [[x]] [] o → Gdfs_simple x o.
  Proof. intro γ. apply Gdfs_list_star_Gdfs, Gdfs_stack_corr, γ. Qed.

  Corollary dfs_book_Gdfs {x o} :
    Gdfs_flatten [x] [] o → Gdfs_simple x o.
  Proof. intro γ. apply Gdfs_book_eff_Gdfs, Gdfs_flatten_corr, γ. Qed.

End dfs.

Recursive Extraction
  dfs_cycle_inld dfs_cycle_inld_tr
  dfs_cycle_self dfs_cycle_self_tr
  dfs_cycle_stack dfs_book_eff dfs_book.

