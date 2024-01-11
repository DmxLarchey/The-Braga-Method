(* The Braga method applied to dfs, expressed with an internal loop *)
(* Jean-François Monin, Verimag, UGA, 2024                          *)

(* Using ideas coming from
- Xavier Leroy, CoqPL 2024 :
  [1] https://inria.hal.science/hal-04356563/document
- D. Larchey-Wendling and Jean-François Monin
  [2] The Braga Method https://cnrs.hal.science/hal-03338785v1

The algorithm provided in [1] is not quite the usual dfs algorithm
Chapter 1 shows the use of the Braga method on the rectified version
of this algorithm.
Then Chapter 2 provides a number of transformations from
this algorithm to the one considered in [2].

 *)

Require Import List Relations Utf8 Extraction.

Import ListNotations.

#[local] Infix "∈" := In (at level 70, no associativity).
#[local] Infix "∉" := (λ x a, ¬ In x a) (at level 70, no associativity).
#[local] Infix "⊆" := incl (at level 70, no associativity).

Section dfs.

  Variable (X : Type).

  Implicit Type l : list X.

  Variables (in_dec : ∀ x l, {x ∈ l} + {x ∉ l})
            (successors : X → list X).

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
    However the management of postconditions turn out to be quite simple
    in the present framework -- basically, constructors of the i/o relation.
    Here we choose to provide fully explicit terms, using greek letters
    for propositional arguments and ad-hoc spacing for better readibility.

    An additional interest of the sibling file dfs_xleroy.v is to formalize
    and experiment a partial version of List.fold_left, of independent interest.
    (Here we stick to mutual recursion, as in [1].)
    Extraction seems to behave better with mutual recursion -- no silent
    unused argument is introduced.
 *)

  Inductive Gdfs : list X → X → list X → Prop :=
  | Gdfs_stop {a x} :     x ∈ a
                        → Gdfs a x a
  | Gdfs_next {a x o} :   x ∉ a
                        → Gdfs_list (x :: a) (successors x) o
                        → Gdfs a x o

  with Gdfs_list : list X → list X → list X → Prop :=
  | Gdfs_list_nil {a} :            Gdfs_list a [] a
  | Gdfs_list_cons {a y l b o} :        Gdfs a y b
                                 → Gdfs_list b l o
                                 → Gdfs_list a (y :: l) o.

  (* Derivation of a useful small inversion principle [JF Monin 2022] *)
  (* No need to read this on first reading *)

  (* NB: the 1st indice also is promoted as a parameter for convenience *)
  Inductive Gdfs_list_2nil a  : list X → Prop :=
  | Gdfs_list_2nil_nil :           Gdfs_list_2nil a a.
  Inductive Gdfs_list_2cons a y l : list X → Prop :=
  | Gdfs_list_2cons_cons {b o} :   Gdfs a y b
                                 → Gdfs_list b l o
                                 → Gdfs_list_2cons a y l o.

  Definition Gdfs_list_dispatch a l : list X → Prop :=
    match l with
    | [] => Gdfs_list_2nil a
    | y :: l => Gdfs_list_2cons a y l
    end.

  Lemma Gdfs_list_inv {a l o} (γ : Gdfs_list a l o) : Gdfs_list_dispatch a l o.
  Proof. destruct γ; econstructor; eassumption. Qed.

  (* End of small inversion *)

  (* Corresponding inductive domain *)
  Inductive Ddfs : list X → X → Prop :=
  | Ddfs_stop {a x} :     x ∈ a
                        → Ddfs a x
  | Ddfs_next {a x} :     x ∉ a
                        → Ddfs_list (x :: a) (successors x)
                        → Ddfs a x

  with Ddfs_list : list X → list X → Prop :=
  | Ddfs_list_nil {a} :          Ddfs_list a []
  | Ddfs_list_cons {a y l}  :    Ddfs a y
                               → (∀b, Gdfs a y b → Ddfs_list b l)
                               → Ddfs_list a (y :: l).

  (* Structurally smaller projections *)
  Definition Ddfs_next_pi {a x} (δ : Ddfs a x) :
    x ∉ a → Ddfs_list (x :: a) (successors x) :=
    match δ in Ddfs a x return x ∉ a → Ddfs_list _ _ with
    | Ddfs_next _ δ  => λ _, δ
    | Ddfs_stop yes  => λ no, match no yes with end
    end.

  Definition Ddfs_list_cons_pi1 {a y l} (δ : Ddfs_list a (y :: l)) : Ddfs a y :=
    match δ in Ddfs_list a yl return
          let guard := match yl with y :: l => True | _ => False end in
          let y     := match yl with y :: l => y    | _ => y     end in
          guard → Ddfs a y with
    | Ddfs_list_cons δ₁ δ₂ => λ _, δ₁
    | _                    => λ absu, match absu with end
    end I.

  Definition Ddfs_list_cons_pi2 {a y l} (δ : Ddfs_list a (y :: l)) :
    ∀b, Gdfs a y b → Ddfs_list b l :=
    match δ in Ddfs_list a yl return
          let guard := match yl with y :: l => True | _ => False end in
          let y     := match yl with y :: l => y    | _ => y     end in
          let l     := match yl with y :: l => l    | _ => l     end in
          guard → ∀b, Gdfs a y b → Ddfs_list b l with
    | Ddfs_list_cons δ₁ δ₂ => λ _, δ₂
    | _                    => λ absu, match absu with end
    end I.

  Arguments exist {A P}.

  Fixpoint dfs (a: list X) (x: X)                         (* *) (δ: Ddfs a x) {struct δ}
    : {o | Gdfs a x o} :=
    match in_dec x a with
    | left yes => exist a                                 (* *) (Gdfs_stop yes)
    | right no =>
        let fix dfs_list a l                              (* *) (δ : Ddfs_list a l) {struct δ}
          : {o | Gdfs_list a l o} :=
          match l                                         (* *) return Ddfs_list a l -> _
          with
          | [] =>                                         (* *) λ _,
                  exist a                                 (* *) Gdfs_list_nil
          | y :: l =>                                     (* *) λ δ,
              let (b, γab) := dfs a y                     (* *) (Ddfs_list_cons_pi1 δ)
                                                          (* *) in let δ := Ddfs_list_cons_pi2 δ b γab
              in let (o, γbo) := dfs_list b l             (* *) δ
              in exist o                                  (* *) (Gdfs_list_cons γab γbo)
          end                                             (* *) δ
        in let (o, γ) := dfs_list (x :: a) (successors x) (* *) (Ddfs_next_pi δ no)
        in exist o                                        (* *) (Gdfs_next no γ)
    end.

  (* Elimination of (un-)knitting steps; intended tail-recursive calls are recovered *)
  Fixpoint dfs_tr (a: list X) (x: X)         (* *) (δ: Ddfs a x) {struct δ}
    : {o | Gdfs a x o} :=
    match in_dec x a with
    | left yes => exist a                    (* *) (Gdfs_stop yes)
    | right no =>
                                             (* *) let post o := Gdfs a x o (* keeps the global a *)
        in let fix dfs_list a l              (* *) (δ : Ddfs_list a l) {struct δ}
             :                               (* *) (∀ o, Gdfs_list a l o → post o) →
               {o | post o} :=
          match l                            (* *) return Ddfs_list a l -> _
          with
          | [] =>                            (* *) λ _ κ,
                  exist a                    (* *) (κ a Gdfs_list_nil)
          | y :: l =>                        (* *) λ δ κ,
              let (b, γab) := dfs a y        (* *) (Ddfs_list_cons_pi1 δ)
                                             (* *) in let δ := Ddfs_list_cons_pi2 δ b γab
                                             (* *) in let κ := λ o γbo, κ o (Gdfs_list_cons γab γbo)
              in dfs_list b l                (* *) δ κ
          end                                (* *) δ
        in dfs_list (x :: a) (successors x)  (* *) (Ddfs_next_pi δ no) (λ o g, Gdfs_next no g)
    end.

  (* (* Other possible presentation *)
  Fixpoint dfs (a: list X) (x: X) (δ: Ddfs a x) {struct δ}: {o | Gdfs a x o} :=
    match in_dec x a with
    | left yes => exist a  (* *)  (Gdfs_stop yes)
    | right no =>
        let fix dfs_list a l  (* *)  (δ : Ddfs_list a l) {struct δ} : {o | Gdfs_list a l o} :=
          match l return Ddfs_list a l -> _ with
          | [] => λ _, exist a                          (* *) Gdfs_list_nil
          | y :: l =>
              λ δ,
              let (b, γab) := dfs a y                   (* *) (Ddfs_list_cons_pi1 δ) in
              let δ := Ddfs_list_cons_pi2 δ b γab in
              let (o, γbo) := dfs_list b l              (* *) δ in
              exist o                                   (* *) (Gdfs_list_cons γab γbo)
          end δ in
        let (o, γ) := dfs_list (x :: a) (successors x)  (* *) (Ddfs_next_pi δ no) in
        exist o                                         (* *) (Gdfs_next no γ)
    end.

  (* Elimination of (un-)knitting steps; intended tail-recursive calls are recovered *)
  Fixpoint dfs_tr (a: list X) (x: X) (δ: Ddfs a x) {struct δ}: {o | Gdfs a x o} :=
    match in_dec x a with
    | left yes => exist a  (* *)  (Gdfs_stop yes)
    | right no =>
        let post o := Gdfs a x o (* keeps the global a *) in
        let fix dfs_list a l (δ : Ddfs_list a l) {struct δ} :
          (∀ o, Gdfs_list a l o → post o) → {o | post o} :=
          match l return Ddfs_list a l -> _ with
          | [] => λ _ κ, exist a                        (* *) (κ a Gdfs_list_nil)
          | y :: l =>
              λ δ κ,
              let (b, γab) := dfs_tr a y                (* *) (Ddfs_list_cons_pi1 δ) in
              let δ := Ddfs_list_cons_pi2 δ b γab in
              let κ := λ o γbo, κ o (Gdfs_list_cons γab γbo) in
              dfs_list b l                    (* *) δ κ
          end δ in
        dfs_list (x :: a) (successors x)      (* *) (Ddfs_next_pi δ no) (λ o g, Gdfs_next no g)
    end.
   *)

  (* Chapter 2. Derivation of fully tail-recursive algorithms, including the one in [2] *)

  (* 2.1 Compacting the 2 recursive functions into a single embedded recursive one *)

  (* Rearrangement of dfs_list above, where the call to dfs is inlined *)

  (* Ad-hoc versions of Gdfs etc. could be defined, but the previous ones
     can be re-used. Then there is no need to proive equivalence between
   specifications.  *)

  Lemma Gdfs_singleton {a x o} : x ∉ a → Gdfs_list a [x] o → Gdfs a x o.
  Proof.
    intros no γ. apply (Gdfs_next no).
    destruct (Gdfs_list_inv γ) as [b o γab γbo]; clear γ.
    destruct (Gdfs_list_inv γbo); clear γbo.
    destruct γab as [a x yes | a x b _no γ]; [case (no yes) | exact γ].
  Qed.

  Lemma Gdfs_singleton_nil {x o} : Gdfs_list [] [x] o → Gdfs [] x o.
  Proof. exact (λ γ, Gdfs_singleton (λ (absu : x ∈ []), absu) γ). Qed.

  Definition dfs1 x                          (* *) (δ : Ddfs [] x)
    : {o | Gdfs [] x o} :=
    let fix dfs_list a l                     (* *) (δ : Ddfs_list a l) {struct δ}
      : {o | Gdfs_list a l o}  :=
      match l                                (* *) return Ddfs_list a l -> _
      with
      | [] =>                                (* *) λ _,
          exist a                            (* *) Gdfs_list_nil
      | x :: l =>                            (* *) λ δ,
          let (b, γab) :=
            match in_dec x a with
            | left yes => exist a            (* *) (Gdfs_stop yes)
            | right no =>
                                             (* *) let δ := Ddfs_list_cons_pi1 δ
                                             (* *) in let δ := Ddfs_next_pi δ no
                in let (o, γ) := dfs_list (x :: a) (successors x)    (* *) δ
                in exist o                   (* *) (Gdfs_next no γ)
            end
                                             (* *) in let δ := Ddfs_list_cons_pi2 δ b γab
          in let (o, γbo) := dfs_list b l    (* *) δ
          in exist o                         (* *) (Gdfs_list_cons γab γbo)
      end                                    (* *) δ
                                             (* *) in let δ := Ddfs_list_cons δ (λ b _, Ddfs_list_nil)
    in let (o, γ) := dfs_list [] [x]         (* *) δ
    in exist o                               (* *) (Gdfs_singleton_nil γ).

  (* Elimination of (un-)knitting steps:
     an additional parameter for post is needed in the (internal) dfs_listk *)
  Definition dfs1_tr x                       (* *) (δ : Ddfs [] x)
    : {o | Gdfs [] x o} :=
  let fix dfs_listk (post : list X → Prop)
                     a l                     (* *) (δ : Ddfs_list a l) {struct δ}
         :                                   (* *) (∀ o, Gdfs_list a l o → post o) →
           {o | post o} :=
      match l                                (* *) return Ddfs_list a l -> _
      with
      | [] =>                                (* *) λ _ κ,
          exist a                            (* *) (κ a Gdfs_list_nil)
      | x :: l =>                            (* *) λ δ κ,
        let (b, γab) :=
            match in_dec x a with
            | left yes => exist a            (* *) (Gdfs_stop yes)
            | right no =>
                                             (* *) let δ := Ddfs_list_cons_pi1 δ
                                             (* *) in let δ := Ddfs_next_pi δ no
              in dfs_listk _ (x :: a) (successors x)    (* *) δ (λ o γ, Gdfs_next no γ)
            end
                                             (* *) in let δ := Ddfs_list_cons_pi2 δ b γab
        in dfs_listk post b l                (* *) δ (λ o γbo, κ o (Gdfs_list_cons γab γbo))
      end                                    (* *) δ
                                             (* *) in let δ := Ddfs_list_cons δ (λ b _, Ddfs_list_nil)
   in dfs_listk _ [] [x]                     (* *) δ (λ o γ, Gdfs_singleton_nil γ).

  (* 2.2 Elimination of embedded recursion using a stack s *)

  (* Two versions are proposed.
  The first one looks closer to dfs_list in dfs1 above.
  let dfs =
    let rec dfs_stack a l s =
      match l with
      | [] ->
        ( match s with
          | [] -> a
          | l :: s -> dfs_stack a l s
        )
      | x :: l ->
        if in_dec x a then dfs_stack a l s
        else dfs_stack (x :: a) (successors x) (l :: s)
    in fun x -> dfs_stack [] [x] []

   stack a [] []       = a
   stack a [] (l :: s) = stack a l s
   stack a (x :: l) s  = stack a l s                              if x ∈ a
   stack a (x :: l) s  = stack (x :: a) (successors x) (l :: s)   if x ∉ a

   Towards the 2nd version, let us compact the 2 last args into a single list
   stack a ([] :: [])      = a
   stack a ([] :: l :: s)  = stack a (l :: s)
   stack a ((x :: l) :: s) = stack a (l :: s)                          if x ∈ a
   stack a ((x :: l) :: s) = stack (x :: a) (successors x :: l :: s)   if x ∉ a

   The second version is close to the dfs algorithm given in [2]
   let dfs =
    let rec dfs_stack_alt a s =
      match s with
      | [] -> a
      | l :: s ->
        match l with
        | [] -> dfs_stack_alt a s
        | x :: l ->
          if in_dec x a then dfs_stack_alt a (l :: s)
          else dfs_stack_alt (x :: a) (successors x :: l :: s)
    in fun x -> dfs_stack_alt [] [[x]]

   alt a []              = a
   alt a ([] :: s)       = alt a s
   alt a ((x :: l) :: s) = alt a (l :: s)                          if x ∈ a
   alt a ((x :: l) :: s) = alt (x :: a) (successors x :: l :: s)   if x ∉ a

   In particular
   alt a ([] :: []) = alt a []  = a
   Then like stack, but in 2 steps, which breaks the possibility to share
   a common inductive domain (unless we add an ad_hoc Boolean parameter).

   So we slightly and conveniently rephrase it as :
   let dfs =
    let rec dfs_stack_alt a s =
      match s with
      | [] -> a
      | [] :: [] -> a
      | [] :: s -> dfs_stack_alt a s (* so s is itself a cons *)
      | (x :: l) :: s ->
          if in_dec x a then dfs_stack_alt a (l :: s)
          else dfs_stack_alt (x :: a) (successors x :: l :: s)
    in fun x -> dfs_stack_alt [] [[x]]
   *)

  Definition stack X := list (list X).

  (* The inductive domain is expressed with the following type instead of
     list X → list X → stack X → Prop, in order to be shared with dfs_stack_alt *)
  Inductive Ddfs_stack : list X → stack X → Prop :=
  | Ddfs_stack_nil {a} :               Ddfs_stack a []
  | Ddfs_stack_nil_emp {a} :           Ddfs_stack a ([] :: [])
  | Ddfs_stack_nil_push {a l s}  :     Ddfs_stack a (l :: s)
                                     → Ddfs_stack a ([] :: l :: s)
  | Ddfs_stack_cons_stop {a x l s} :   x ∈ a
                                     → Ddfs_stack a (l :: s)
                                     → Ddfs_stack a ((x :: l) :: s)
  | Ddfs_stack_cons_next {a x l s} :   x ∉ a
                                     → Ddfs_stack (x :: a) (successors x :: l :: s)
                                     → Ddfs_stack a ((x :: l) :: s).

  (* Structurally smaller projections *)

  Definition Ddfs_stack_nil_push_pi {a l s} (δ : Ddfs_stack a ([] :: l :: s)) :
    Ddfs_stack a (l :: s) :=
    match δ in Ddfs_stack a els return
          let guard := match els with [] :: l :: s => True | _ => False end in
          let l     := match els with [] :: l :: s => l    | _ => l     end in
          let s     := match els with [] :: l :: s => s    | _ => s     end in
          guard → Ddfs_stack a (l :: s) with
    | Ddfs_stack_nil_push δ => λ _, δ
    | _               => λ absu, match absu with end
    end I.

  Definition Ddfs_stack_cons_stop_pi {a x l s} (δ : Ddfs_stack a ((x :: l) :: s)) :
    x ∈ a → Ddfs_stack a (l :: s) :=
    match δ in Ddfs_stack a xls return
          let guard := match xls with (x :: l) :: s => True | _ => False end in
          let x     := match xls with (x :: l) :: s => x    | _ => x     end in
          let l     := match xls with (x :: l) :: s => l    | _ => l     end in
          let s     := match xls with (x :: l) :: s => s    | _ => s     end in
          guard → x ∈ a → Ddfs_stack a (l :: s) with
    | Ddfs_stack_cons_stop yes δ => λ _ _, δ
    | Ddfs_stack_cons_next no δ  => λ _ yes, match no yes with end
    | _               => λ absu _, match absu with end
    end I.

  Definition Ddfs_stack_cons_next_pi {a x l s} (δ : Ddfs_stack a ((x :: l) :: s)) :
    x ∉ a → Ddfs_stack (x :: a) (successors x :: l :: s) :=
    match δ in Ddfs_stack a xls return
          let guard := match xls with (x :: l) :: s => True | _ => False end in
          let x     := match xls with (x :: l) :: s => x    | _ => x     end in
          let l     := match xls with (x :: l) :: s => l    | _ => l     end in
          let s     := match xls with (x :: l) :: s => s    | _ => s     end in
          guard → x ∉ a → Ddfs_stack (x :: a) (successors x :: l :: s) with
    | Ddfs_stack_cons_next no δ  => λ _ _, δ
    | Ddfs_stack_cons_stop yes δ => λ _ no, match no yes with end
    | _               => λ absu _, match absu with end
    end I.

  (* *)

  Fixpoint dfs_stack a l s (δ : Ddfs_stack a (l :: s)) {struct δ} : list X :=
    match l                                                        (* *) return Ddfs_stack a (l :: s) → _
    with
    | [] =>                                                        (* *) λ δ,
        match s                                                    (* *) return Ddfs_stack a ([] :: s) → _
        with
        | []     =>                                                (* *) λ _,
                    a
        | l :: s =>                                                (* *) λ δ,
                    dfs_stack a l s                                (* *) (Ddfs_stack_nil_push_pi δ)
        end                                                        (* *) δ
    | x :: l =>                                                    (* *) λ δ,
        match in_dec x a with
        | left yes => dfs_stack a l s                              (* *) (Ddfs_stack_cons_stop_pi δ yes)
        | right no => dfs_stack (x :: a) (successors x) (l :: s)   (* *) (Ddfs_stack_cons_next_pi δ no)
        end
    end δ.

  (* *)

  Fixpoint dfs_stack_alt a s (δ : Ddfs_stack a s) {struct δ} : list X :=
    match s                                                           (* *) return Ddfs_stack a s → _
    with
    | []     =>                                                       (* *) λ _,
                a
    | [] :: [] =>                                                     (* *) λ δ,
                a
    | [] :: s =>                                                      (* *) λ δ,
              dfs_stack_alt a s                                       (* *) (Ddfs_stack_nil_push_pi δ)
    | (x :: l) :: s =>                                                (* *) λ δ,
        match in_dec x a with
        | left yes => dfs_stack_alt a (l :: s)                        (* *) (Ddfs_stack_cons_stop_pi δ yes)
        | right no => dfs_stack_alt (x :: a) (successors x :: l :: s) (* *) (Ddfs_stack_cons_next_pi δ no)
        end
    end δ.

  (* small inversions for smaller inversions for Ddfs_stack *)

  Inductive Ddfs_stack_n a : Ddfs_stack a [] → Prop :=
  | Ddfs_stack_n_nil :  Ddfs_stack_n a Ddfs_stack_nil.
  Inductive Ddfs_stack_ne a : Ddfs_stack a [[]] → Prop :=
  | Ddfs_stack_ne_nil_emp :  Ddfs_stack_ne a Ddfs_stack_nil_emp.
  Inductive Ddfs_stack_np a l s : Ddfs_stack a ([] :: l :: s) → Prop :=
  | Ddfs_stack_np_nil_push : ∀ (δ : Ddfs_stack a (l :: s)),
                             Ddfs_stack_np a l s (Ddfs_stack_nil_push δ).
  Inductive Ddfs_stack_c a x l s : Ddfs_stack a ((x :: l) :: s) → Prop :=
  | Ddfs_stack_cs_cons_stop : ∀ (yes : x ∈ a)
                                (δ : Ddfs_stack a (l :: s)),
                              Ddfs_stack_c a x l s (Ddfs_stack_cons_stop yes δ)
  | Ddfs_stack_cn_cons_next : ∀ (no : x ∉ a)
                                (δ : Ddfs_stack (x :: a) (successors x :: l :: s)),
                              Ddfs_stack_c a x l s (Ddfs_stack_cons_next no δ).

  Definition Ddfs_stack_dispatch {a s} : Ddfs_stack a s → Prop :=
    match s return Ddfs_stack a s → Prop with
    | [] => Ddfs_stack_n a
    | [[]] => Ddfs_stack_ne a
    | [] :: (l :: s) => Ddfs_stack_np a l s
    | (x :: l) :: s => Ddfs_stack_c a x l s 
    end.

  Definition Ddfs_stack_inv {a s} (δ : Ddfs_stack a s) : Ddfs_stack_dispatch δ.
  Proof. destruct δ; constructor. Defined.

  (* End of small inversions of Ddfs_stack *)

  (* Recursive equations of dfs_stack *)
  Lemma dfs_stack_eqn1 {a} (δ : Ddfs_stack a [[]]) : dfs_stack a [] [] δ = a.
  Proof. destruct (Ddfs_stack_inv δ); cbn. reflexivity. Qed.
 
  Lemma dfs_stack_eqn2 {a l s} (δ : Ddfs_stack a ([] :: l :: s)) :
    dfs_stack a [] (l :: s) δ = dfs_stack a l s (Ddfs_stack_nil_push_pi δ).
  Proof. destruct (Ddfs_stack_inv δ); cbn. reflexivity. Qed.

  Lemma dfs_stack_eqn3 {a x l s} (δ : Ddfs_stack a ((x :: l) :: s)) (yes : x ∈ a) :
    dfs_stack a (x :: l) s δ = dfs_stack a l s (Ddfs_stack_cons_stop_pi δ yes).
  Proof.
    destruct (Ddfs_stack_inv δ) as [yes' δ | no δ]; cbn.
    - destruct (in_dec x a) as [_ | no].
      + reflexivity.
      + case (no yes).
    - case (no yes).
  Qed.

  Lemma dfs_stack_eqn4 {a x l s} (δ : Ddfs_stack a ((x :: l) :: s)) (no : x ∉ a) :
    dfs_stack a (x :: l) s δ =
    dfs_stack (x :: a) (successors x) (l :: s) (Ddfs_stack_cons_next_pi δ no).
   Proof.
     destruct (Ddfs_stack_inv δ) as [yes δ | no' δ]; cbn.
     - case (no yes).
     - destruct (in_dec x a) as [yes | _].
      + case (no yes).
      + reflexivity.
   Qed.

  (* Recursive equations of dfs_stack_alt *)
  Lemma dfs_stack_alt_eqn0 {a} (δ : Ddfs_stack a []) : dfs_stack_alt a [] δ = a.
  Proof. destruct (Ddfs_stack_inv δ); cbn. reflexivity. Qed.

  Lemma dfs_stack_alt_eqn1 {a} (δ : Ddfs_stack a [[]]) : dfs_stack_alt a [[]] δ = a.
  Proof. destruct (Ddfs_stack_inv δ); cbn. reflexivity. Qed.
 
  Lemma dfs_stack_alt_eqn2 {a l s} (δ : Ddfs_stack a ([] :: l :: s)) :
    dfs_stack_alt a ([] :: l :: s) δ = dfs_stack_alt a (l :: s) (Ddfs_stack_nil_push_pi δ).
  Proof. destruct (Ddfs_stack_inv δ); cbn. reflexivity. Qed.

  Lemma dfs_stack_alt_eqn3 {a x l s} (δ : Ddfs_stack a ((x :: l) :: s)) (yes : x ∈ a) :
    dfs_stack_alt a ((x :: l) :: s) δ = dfs_stack_alt a (l :: s) (Ddfs_stack_cons_stop_pi δ yes).
  Proof.
    destruct (Ddfs_stack_inv δ) as [yes' δ | no δ]; cbn.
    - destruct (in_dec x a) as [_ | no].
      + reflexivity.
      + case (no yes).
    - case (no yes).
  Qed.

  Lemma dfs_stack_alt_eqn4 {a x l s} (δ : Ddfs_stack a ((x :: l) :: s)) (no : x ∉ a) :
    dfs_stack_alt a ((x :: l) :: s) δ =
    dfs_stack_alt (x :: a) (successors x :: l :: s) (Ddfs_stack_cons_next_pi δ no).
   Proof.
     destruct (Ddfs_stack_inv δ) as [yes δ | no' δ]; cbn.
     - case (no yes).
     - destruct (in_dec x a) as [yes | _].
      + case (no yes).
      + reflexivity.
   Qed.

   (* Show that dfs_stack_alt a (l :: s) = dfs_stack a l s *)
   Lemma dfs_stack_same {a l s} (δ δ' : Ddfs_stack a (l :: s)) :
     dfs_stack_alt a (l :: s) δ = dfs_stack a l s δ'.
   Proof.
     refine (
     (fix loop a l s (δ δ' : Ddfs_stack a (l :: s)) {struct δ} : _ :=
        match l return ∀ (δ δ' : Ddfs_stack a (l :: s)), _ with
        | [] => λ δ δ',
            match s return ∀ (δ δ' : Ddfs_stack a ([ ]:: s)), _ with
            | [] => λ δ δ', _
            | l :: s => λ δ δ', _
            end δ δ'
        | x :: l => λ δ δ',
            match in_dec x a with
            | left yes => _
            | right no => _
            end
        end δ δ'          
     ) a l s δ δ').
     - rewrite dfs_stack_eqn1, dfs_stack_alt_eqn1. reflexivity.
     - rewrite dfs_stack_eqn2, dfs_stack_alt_eqn2. apply loop.
     - rewrite (dfs_stack_eqn3 _ yes), (dfs_stack_alt_eqn3 _ yes). apply loop.
     - rewrite (dfs_stack_eqn4 _ no), (dfs_stack_alt_eqn4 _ no). apply loop.
   Qed.

   (* A more basic proof *)
   Fixpoint dfs_stack_same_destruct a l s (δ δ' : Ddfs_stack a (l :: s)) {struct δ} :
     dfs_stack_alt a (l :: s) δ = dfs_stack a l s δ'.
   Proof.
     destruct l as [ | x l Hl].
     - destruct s as [ | l s].
       + rewrite dfs_stack_eqn1, dfs_stack_alt_eqn1. reflexivity.
       + rewrite dfs_stack_eqn2, dfs_stack_alt_eqn2. apply dfs_stack_same.
     - destruct (in_dec x a) as [yes | no].
       + rewrite (dfs_stack_eqn3 _ yes), (dfs_stack_alt_eqn3 _ yes).
         apply dfs_stack_same.
       + rewrite (dfs_stack_eqn4 _ no), (dfs_stack_alt_eqn4 _ no).
         apply dfs_stack_same.
   Qed.

   (* Corollaire amusant *)
   Corollary dfs_stack_domirr a l s (δ δ' : Ddfs_stack a (l :: s)) :
     dfs_stack a l s δ = dfs_stack a l s δ'.
   Proof.
     rewrite <- (dfs_stack_same δ δ),  <- (dfs_stack_same δ δ').
     reflexivity.
   Qed.

   
  (* TODO:
     - show that Gdfs_list a l (dfs_stack a l [])
       Idea: something like   iter s Gdfs_list a l (dfs_stack a l s)
       where iter is a relational fold (s R iterates R on s).
   *)



  (* 2.3 Flattening s in dfs_stack_alt provides the algorithm considered in [2] *)

  (* TODO: see title of 2.3, et vérifier, car j'ai relu [2] très vite... *)

End dfs.

Recursive Extraction dfs dfs_tr dfs1 dfs1_tr dfs_stack dfs_stack_alt.
