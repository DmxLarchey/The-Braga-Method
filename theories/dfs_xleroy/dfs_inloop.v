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

(* The Braga method applied to dfs, expressed with an internal loop *)

(* Using ideas coming from
[1] Xavier Leroy, Well-founded recursion done right, CoqPL 2024
    https://inria.hal.science/hal-04356563/document
[2] Dominique Larchey-Wendling and Jean-François Monin
    The Braga Method https://cnrs.hal.science/hal-03338785v1

The algorithm provided in [1] is not quite the usual dfs algorithm
Chapter 1 shows the use of the Braga method on the rectified version
of this algorithm.
Then Chapter 2 provides a number of transformations from
this algorithm to the one considered in [2].

 *)

Require Import List Relations Utf8 Extraction.
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "( :: )" ].

Arguments exist {A P}.

Import ListNotations.

#[local] Infix "∈" := In (at level 70, no associativity).
#[local] Infix "∉" := (λ x a, ¬ In x a) (at level 70, no associativity).

Require Import dfs_abstract.
Arguments Gfl_nil {X Y F a}.

(* Reminder
Inductive Gfoldleft (X Y : Type) (F : Y → X → X → Prop) : list Y → X → X → Prop :=
    Gfl_nil : ∀ a : X, Gfoldleft F [] a a
  | Gfl_cons : ∀ (y : Y) (a : X) (l : list Y) (b o : X),
                 F y a b → Gfoldleft F l b o → Gfoldleft F (y :: l) a o.
 *)

(* Small inversion of Gfoldleft *)
Inductive Gfoldleft_nil {X Y : Type} (R : Y → X → X → Prop) (a : X) : X → Prop :=
| Gfl_nil_nil : Gfoldleft_nil R a a.
Inductive Gfoldleft_cons {X Y : Type} (R : Y → X → X → Prop) y l (a : X) (c : X) : Prop :=
| Gfl_cons_cons b : R y a b → Gfoldleft R l b c → Gfoldleft_cons R y l a c.
Definition Gfoldleft_dispatch {X Y} (R : Y → X → X → Prop) l a : X → Prop :=
  match l with
  | [] => Gfoldleft_nil R a
  | y :: l => Gfoldleft_cons R y l a
  end.

Definition Gfoldleft_inv {X Y : Type} {R : Y → X → X → Prop}
  {a l b} (i : Gfoldleft R l a b) : Gfoldleft_dispatch R l a b.
Proof. destruct i; econstructor; eassumption. Defined.
(* End of small inversion *)

Class Gcl (X : Type) := { in_dec : ∀ (x : X) (l : list X), {x ∈ l} + {x ∉ l};
                          succs :  X → list X}.

Generalizable Variable X.

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

Inductive Gdfs `{C : Gcl} : X → list X → list X → Prop :=
| Gdfs_stop {x a} :     x ∈ a
                      → Gdfs x a a
| Gdfs_next {x a o} :   x ∉ a
                      → Gdfs_list (succs x) (x :: a) o
                      → Gdfs x a o
with Gdfs_list `{C : Gcl} : list X → list X → list X → Prop :=
| Gdl_nil {a} :            Gdfs_list [] a a
| Gdl_cons {x l a b o} :   Gdfs x a b
                         → Gdfs_list l b o
                         → Gdfs_list (x :: l) a o.

Definition Gdfs_main `{C : Gcl} := λ x, Gdfs x [].


(* Small inversion of Gdfs_list *)
Section sec_small_inv.
  Context  `{C : Gcl}.
  Inductive Gdfs_list_nil (a : list X) : list X → Prop :=
  | Gdl_nil_nil : Gdfs_list_nil a a.
  Inductive Gdfs_list_cons x l (a : list X) (o : list X) : Prop :=
  | Gdl_cons_cons b : Gdfs x a b → Gdfs_list l b o → Gdfs_list_cons x l a o.
  Definition Gdfs_list_dispatch l a : list X → Prop :=
    match l with
    | []     => Gdfs_list_nil a
    | x :: l => Gdfs_list_cons x l a
    end.

  Definition Gdfs_list_inv {l a o} (γ : Gdfs_list l a o) : Gdfs_list_dispatch l a o.
  Proof. destruct γ; econstructor; eassumption. Defined.
End sec_small_inv.
(* End of small inversion *)

(* FYI but not used here *)
Lemma Gdfs_deterministic `{C : Gcl} {x a o} (γ : Gdfs x a o) : ∀ {o'}, Gdfs x a o' → o = o'.
Proof.
  revert x a o γ.
  refine (fix loop1 x a o γ {struct γ} : _ := _).
  destruct γ as [x a yes | x a o no γ]; intros o' γ'.
  - destruct γ' as [x a _ | x a o no γ']; [reflexivity | case (no yes)].
  - destruct γ' as [x a yes | x a o' _ γ']; [case (no yes) | clear no; revert o' γ'].
    refine (
        let fix loop2 l a o (γ : Gdfs_list l a o) {struct γ} : ∀ o', Gdfs_list l a o' → o = o' := _
        in loop2 (succs x) (x :: a) o γ).
    destruct γ as [a | x' l a b o γab γbo e]; intros o' γ'.
    + destruct (Gdfs_list_inv γ'). reflexivity.
    + destruct (Gdfs_list_inv γ') as [b' γab' γb'o'].
      apply (loop2 _ _ _ γbo).
      rewrite (loop1 x' a b γab b' γab').
      exact γb'o'.
Qed.

(* Correctness and completeness of Gdfs_list / Gdfs *)
Definition Gdfs_list_corr `{C : Gcl}  {x a o} : Gdfs_list [x] a o → Gdfs x a o.
Proof.
  intro γ.
  destruct (Gdfs_list_inv γ) as [b γab γbo]; destruct (Gdfs_list_inv γbo).
  exact γab.
Defined.

Definition Gdfs_list_compl `{C : Gcl}  {x a o} : Gdfs x a o → Gdfs_list [x] a o
  := λ γ, Gdl_cons γ Gdl_nil.

(* Corresponding inductive domain *)
Inductive Ddfs `{C : Gcl} : X → list X → Prop :=
| Ddfs_stop {x a} :    x ∈ a
                     → Ddfs x a
| Ddfs_next {x a} :     x ∉ a
                      → Ddfs_list (succs x) (x :: a)
                      → Ddfs x a

with Ddfs_list `{C : Gcl} : list X → list X → Prop :=
| Ddl_nil {a} :         Ddfs_list [] a
| Ddl_cons {x l a}  :   Ddfs x a
                      → (∀b, Gdfs x a b → Ddfs_list l b)
                      → Ddfs_list (x :: l) a.

(* Structurally smaller projections *)
Section sec_proj.
  Context `{C : Gcl}.

  Definition Ddfs_next_pi {x a} (δ : Ddfs x a) :
    x ∉ a → Ddfs_list (succs x) (x :: a) :=
    match δ in Ddfs x a return x ∉ a → Ddfs_list _ _ with
    | Ddfs_next _ δ  => λ _, δ
    | Ddfs_stop yes  => λ no, match no yes with end
    end.

  Definition Ddl_cons_pi1 {x l a} (δ : Ddfs_list (x :: l) a) : Ddfs x a :=
    match δ in Ddfs_list xl a return
          let shape := match xl with x :: l => True | _ => False end in
          let x     := match xl with x :: l => x    | _ => x     end in
          shape → Ddfs x a with
    | Ddl_cons δ₁ δ₂ => λ _, δ₁
    | _              => λ absu, match absu with end
    end I.

  Definition Ddl_cons_pi2 {x l a} (δ : Ddfs_list (x :: l) a) :
    ∀b, Gdfs x a b → Ddfs_list l b :=
    match δ in Ddfs_list xl a return
          let shape := match xl with x :: l => True | _ => False end in
          let x     := match xl with x :: l => x    | _ => x     end in
          let l     := match xl with x :: l => l    | _ => l     end in
          shape → ∀b, Gdfs x a b → Ddfs_list l b with
    | Ddl_cons δ₁ δ₂ => λ _, δ₂
    | _              => λ absu, match absu with end
    end I.
End sec_proj.

Fixpoint dfs `{C : Gcl} (x: X) (a: list X)              (* *) (δ: Ddfs x a) {struct δ}
  : {o | Gdfs x a o} :=
  match in_dec x a with
  | left yes => exist a                                 (* *) (Gdfs_stop yes)
  | right no =>
      let fix dfs_list l a                              (* *) (δ : Ddfs_list l a) {struct δ}
        : {o | Gdfs_list l a o} :=
        match l                                         (* *) return Ddfs_list l a -> _
        with
        | [] =>                                         (* *) λ _,
                exist a                                 (* *) Gdl_nil
        | x :: l =>                                     (* *) λ δ,
            let (b, γab) := dfs x a                     (* *) (Ddl_cons_pi1 δ)
                                                        (* *) in let δ := Ddl_cons_pi2 δ b γab
            in let (o, γbo) := dfs_list l b             (* *) δ
            in exist o                                  (* *) (Gdl_cons γab γbo)
        end                                             (* *) δ
      in let (o, γ) := dfs_list (succs x) (x :: a)      (* *) (Ddfs_next_pi δ no)
      in exist o                                        (* *) (Gdfs_next no γ)
  end.

(* Main program: the inlined nested variant of dfs_cycle *)
Definition dfs_cycle_inld `{C : Gcl} x : Ddfs x [] → {o | Gdfs_main x o} := dfs x [].

Recursive Extraction dfs_cycle_inld.

(* ============================================================================ *)
(* Chapter 2. Derivation of tail-recursive algorithms, including the one in [2] *)

(* 2.1 Compacting the 2 recursive functions into a single embedded recursive one *)

(* Rearrangement of dfs_list above, where the call to dfs is inlined *)

Inductive Gdfs_list_self `{C : Gcl}  : list X → list X → list X → Prop :=
| Gdls_nil {a} :               Gdfs_list_self [] a a
| Gdls_cons_yes {x l a o} :    x ∈ a
                             → Gdfs_list_self l a o
                             → Gdfs_list_self (x :: l) a o
| Gdls_cons_no {x l a b o} :   x ∉ a
                             → Gdfs_list_self (succs x) (x :: a) b
                             → Gdfs_list_self l b o
                             → Gdfs_list_self (x :: l) a o.

Inductive Ddfs_list_self `{C : Gcl}  : list X → list X → Prop :=
| Ddls_nil {a} :        Ddfs_list_self [] a
| Ddls_cons_yes [x l a] :   x ∈ a
                          → Ddfs_list_self l a
                          → Ddfs_list_self (x :: l) a
| Ddls_cons_no  [x l a] :   x ∉ a
                          → Ddfs_list_self (succs x) (x :: a)
                          → (∀ b, Gdfs_list_self (succs x) (x :: a) b → Ddfs_list_self l b)
                          → Ddfs_list_self (x :: l) a.
(* Structurally smaller projections *)
Section sec_proj.
  Context `{C : Gcl}.

  Definition Ddfs_list_self_cons_yes_pi {x l a} (δ : Ddfs_list_self (x :: l) a) :
    x ∈ a → Ddfs_list_self l a :=
    match δ in Ddfs_list_self xl a return
          let shape := match xl with x :: l => True | _ => False end in
          let x :=     match xl with x :: l => x    | _ => x end in
          let l :=     match xl with x :: l => l    | _ => l end in
          shape → x ∈ a → Ddfs_list_self l a
    with
    | Ddls_cons_yes _ δ => λ sh yes, δ
    | Ddls_cons_no no _ _ => λ sh yes, match no yes with end
    | _ => λ sh yes, match sh with end
    end I.

  Definition Ddfs_list_self_cons_no_pi1 {x l a} (δ : Ddfs_list_self (x :: l) a) :
    x ∉ a → Ddfs_list_self (succs x) (x :: a) :=
    match δ in Ddfs_list_self xl a return
          let shape := match xl with x :: l => True | _ => False end in
          let x :=     match xl with x :: l => x    | _ => x end in
          let l :=     match xl with x :: l => l    | _ => l end in
          shape → x ∉ a → Ddfs_list_self (succs x) (x :: a)
    with
    | Ddls_cons_no _ δ1 fδ2 => λ sh no, δ1
    | Ddls_cons_yes yes _ => λ sh no, match no yes with end
    | _ => λ sh no, match sh with end
    end I.

  Definition Ddfs_list_self_cons_no_pi2 {x l a} (δ : Ddfs_list_self (x :: l) a) :
    x ∉ a → (∀ b, Gdfs_list_self (succs x) (x :: a) b → Ddfs_list_self l b) :=
    match δ in Ddfs_list_self xl a return
          let shape := match xl with x :: l => True | _ => False end in
          let x :=     match xl with x :: l => x    | _ => x end in
          let l :=     match xl with x :: l => l    | _ => l end in
          shape → x ∉ a → (∀ b, Gdfs_list_self (succs x) (x :: a) b → Ddfs_list_self l b)
    with
    | Ddls_cons_no _ δ1 fδ2 => λ sh no, fδ2
    | Ddls_cons_yes yes _ => λ sh no, match no yes with end
    | _ => λ sh no, match sh with end
    end I.

End sec_proj.

Fixpoint dfs_list_self `{C : Gcl} l a           (* *) (δ : Ddfs_list_self l a) {struct δ}
  : {o | Gdfs_list_self l a o}  :=
  match l                                       (* *) return Ddfs_list_self l a -> _
  with
  | [] =>                                       (* *) λ _,
      exist a                                   (* *) Gdls_nil
  | x :: l =>                                   (* *) λ δ,
      match in_dec x a with
      | left yes =>                             (* *) let δ := Ddfs_list_self_cons_yes_pi δ yes in
          let (o, γao) := dfs_list_self l a     (* *) δ
          in exist o                            (* *) (Gdls_cons_yes yes γao)
      | right no =>                             (* *) let δ1 := Ddfs_list_self_cons_no_pi1 δ no in
          let (b, γab) := dfs_list_self (succs x) (x :: a)
                                                (* *) δ1
                                                (* *) in let δ2 := Ddfs_list_self_cons_no_pi2 δ no b γab
          in let (o, γbo) := dfs_list_self l b  (* *) δ2
          in exist o                            (* *) (Gdls_cons_no no γab γbo)
        end
  end                                           (* *) δ.

(* Main *)
Definition dfs_cycle_self `{C : Gcl} x          (* *) (δ : Ddfs_list_self [x] [])
  : {o | Gdfs_list_self [x] [] o} :=
  dfs_list_self [x] []                          (* *) δ.

Recursive Extraction dfs_cycle_self.

(* Correctness and completeness of Gdfs_list_self / Gdfs_list*)
Section sec_corr_compl.
  Context `{C : Gcl}.

  Lemma Gdfs_list_self_corr {l a o} :
    Gdfs_list_self l a o → Gdfs_list l a o.
  Proof.
    intro γ. induction γ as [a | x a l o yes γ Hγ | x a b l o no γab Hγab γbo Hγbo].
    - constructor.
    - exact (Gdl_cons (Gdfs_stop yes) Hγ).
    - exact (Gdl_cons (Gdfs_next no Hγab) Hγbo).
  Qed.

  Fixpoint Gdfs_list_self_compl_cons {x a l b} (γ : Gdfs x a b) {struct γ} :
    ∀ {o}, Gdfs_list_self l b o → Gdfs_list_self (x :: l) a o.
  Proof.
    destruct γ as [x ac yes | x a b no γ]; intros o γbo.
    - apply (Gdls_cons_yes yes), γbo.
    - refine (Gdls_cons_no no _ γbo).
      induction γ as [a0 | x0 l0 a0 c b γa0c γcb Hγcb].
      + constructor.
      + exact (Gdfs_list_self_compl_cons x0 a0 l0 c γa0c b (Hγcb γbo)).
  Qed.

  Lemma Gdfs_list_self_compl {l a o} :
    Gdfs_list l a o → Gdfs_list_self l a o.
  Proof.
    intro γ; induction γ as [a | x a l b c γab γbc Hγbc].
    - constructor.
    - exact (Gdfs_list_self_compl_cons γab Hγbc).
  Qed.

End sec_corr_compl.

(* ======================================================================== *)
(* 2.2 Elimination of embedded recursion using a stack s *)

(* Two versions can be considered.
The first one looks closer to dfs_list_self above.
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

Inductive Gdfs_list_stack `{C : Gcl} : list X → stack X → list X → list X → Prop :=
| Gls_nil_emp {a} :             Gdfs_list_stack [] [] a a
| Gls_nil_push {l s a o}  :     Gdfs_list_stack l s a o
                              → Gdfs_list_stack [] (l :: s) a o
| Gls_cons_stop {x l s a o} :   x ∈ a
                              → Gdfs_list_stack l s a o
                              → Gdfs_list_stack (x :: l) s a o
| Gls_cons_next {x l s a o} :   x ∉ a
                              → Gdfs_list_stack (succs x) (l :: s) (x :: a) o
                              → Gdfs_list_stack (x :: l) s a o.

(* The inductive domain is expressed with the following type instead of
   list X → stack X → list X → Prop, in order to be shared with dfs_stack *)
Inductive Ddfs_stack `{C : Gcl} : stack X → list X → Prop :=
| Ds_nil {a} :               Ddfs_stack [] a
| Ds_nil_emp {a} :           Ddfs_stack ([] :: []) a
| Ds_nil_push {l s a}  :     Ddfs_stack (l :: s) a
                           → Ddfs_stack ([] :: l :: s) a
| Ds_cons_stop {x l s a} :   x ∈ a
                           → Ddfs_stack (l :: s) a
                           → Ddfs_stack ((x :: l) :: s) a
| Ds_cons_next {x l s a} :   x ∉ a
                           → Ddfs_stack (succs x :: l :: s) (x :: a)
                           → Ddfs_stack ((x :: l) :: s) a.

(* Structurally smaller projections *)
Section sec_proj.
  Context `{C : Gcl}.

  Definition Ds_nil_push_pi {l s a} (δ : Ddfs_stack ([] :: l :: s) a) :
    Ddfs_stack (l :: s) a :=
    match δ in Ddfs_stack els a return
          let shape := match els with [] :: l :: s => True | _ => False end in
          let l     := match els with [] :: l :: s => l    | _ => l     end in
          let s     := match els with [] :: l :: s => s    | _ => s     end in
          shape → Ddfs_stack (l :: s) a with
    | Ds_nil_push δ => λ _, δ
    | _             => λ absu, match absu with end
    end I.

  Definition Ds_cons_stop_pi {x l s a} (δ : Ddfs_stack ((x :: l) :: s) a) :
    x ∈ a → Ddfs_stack (l :: s) a :=
    match δ in Ddfs_stack xls a return
          let shape := match xls with (x :: l) :: s => True | _ => False end in
          let x     := match xls with (x :: l) :: s => x    | _ => x     end in
          let l     := match xls with (x :: l) :: s => l    | _ => l     end in
          let s     := match xls with (x :: l) :: s => s    | _ => s     end in
          shape → x ∈ a → Ddfs_stack (l :: s) a with
    | Ds_cons_stop yes δ => λ _ _, δ
    | Ds_cons_next no δ  => λ _ yes, match no yes with end
    | _                  => λ absu _, match absu with end
    end I.

  Definition Ds_cons_next_pi {x l s a} (δ : Ddfs_stack ((x :: l) :: s) a) :
    x ∉ a → Ddfs_stack (succs x :: l :: s) (x :: a) :=
    match δ in Ddfs_stack xls a return
          let shape := match xls with (x :: l) :: s => True | _ => False end in
          let x     := match xls with (x :: l) :: s => x    | _ => x     end in
          let l     := match xls with (x :: l) :: s => l    | _ => l     end in
          let s     := match xls with (x :: l) :: s => s    | _ => s     end in
          shape → x ∉ a → Ddfs_stack (succs x :: l :: s) (x :: a) with
    | Ds_cons_next no δ  => λ _ _, δ
    | Ds_cons_stop yes δ => λ _ no, match no yes with end
    | _                  => λ absu _, match absu with end
    end I.

End sec_proj.

Fixpoint dfs_list_stack `{C : Gcl} l s a (δ : Ddfs_stack (l :: s) a) {struct δ} :
  {o | Gdfs_list_stack l s a o} :=
  match l                                                             (* *) return Ddfs_stack (l :: s) a → _
  with
  | [] =>                                                             (* *) λ δ,
      match s                                                         (* *) return Ddfs_stack ([] :: s) a → _
      with
      | []     =>                                                     (* *) λ _,
                  exist a                                             (* *) Gls_nil_emp
      | l :: s =>                                                     (* *) λ δ,
                  let (o, γ) := dfs_list_stack l s a                  (* *) (Ds_nil_push_pi δ)
                  in exist o                                          (* *) (Gls_nil_push γ)
      end                                                             (* *) δ
  | x :: l =>                                                         (* *) λ δ,
      match in_dec x a with
      | left yes =>
                  let (o, γ) := dfs_list_stack l s a                  (* *) (Ds_cons_stop_pi δ yes)
                  in exist o                                          (* *) (Gls_cons_stop yes γ)
      | right no =>
                  let (o, γ) := dfs_list_stack (succs x) (l :: s) (x :: a)
                                                                      (* *) (Ds_cons_next_pi δ no)
                  in exist o                                          (* *) (Gls_cons_next no γ)
      end
  end δ.

(* Main *)
Definition dfs_cycle_stack `{C : Gcl} x :                             (* *)  Ddfs_stack ([x] :: []) [] →
                           {o | Gdfs_list_stack [x] [] [] o} := dfs_list_stack [x] [] [].

(* Specification, correctness and completeness of dfs_list_stack / Gdfs_list_self *)

Definition Gdfs_list_self_star `{C : Gcl} := Gfoldleft Gdfs_list_self.

Inductive Gdfs_list_self_plus `{C : Gcl} l s a o : Prop :=
| Gls_plus b :   Gdfs_list_self l a b → Gdfs_list_self_star s b o
               → Gdfs_list_self_plus l s a o.
Arguments Gls_plus {X C l s a o}.

Fact Gls_plus1 `{C : Gcl} {l a o} : Gdfs_list_self l a o → Gdfs_list_self_plus l [] a o.
Proof. exact (λ γ, Gls_plus o γ Gfl_nil). Qed.

Fact Gls_plus1_inv `{C : Gcl} {l a o} : Gdfs_list_self_plus l [] a o → Gdfs_list_self l a o.
Proof. destruct 1 as [b γab γbo]. destruct (Gfoldleft_inv γbo). exact γab. Qed.

Section sec_corr_compl.
  Context `{C : Gcl}.

  (* Correctness *)
  Lemma Gdfs_list_stack_corr {l s a o} :
    Gdfs_list_stack l s a o → Gdfs_list_self_plus l s a o.
  Proof.
    induction 1 as [a | l s a o γ Hγ
                   | x l s a o yes γ Hγ
                   | x l s a o no γ Hγ].
    - exact (Gls_plus a Gdls_nil Gfl_nil).
    - exact (let (b, γab, γbo) := Hγ in Gls_plus a Gdls_nil (Gfl_cons γab γbo)).
    - exact (let (b, γab, γbo) := Hγ in Gls_plus b (Gdls_cons_yes yes γab) γbo).
    - exact (let (b, γxab, γbo) := Hγ in
             let (c, γbc, γco) := Gfoldleft_inv γbo in
             Gls_plus c (Gdls_cons_no no γxab γbc) γco).
  Qed.

  (* Completeness *)

  (* Key lemma *)
  Lemma list_self_cont_stack {l a b} (γab : Gdfs_list_self l a b) :
    ∀ {s o}, Gdfs_list_stack [] s b o → Gdfs_list_stack l s a o.
  Proof.
    induction γab as [a | x l a b yes γab Hγab | x l a b c no γxab Hγxab γbc Hγbc];
      intros s o γ.
    - exact γ.
    - exact (Gls_cons_stop yes (Hγab s o γ)).
    - exact (Gls_cons_next no (Hγxab (l :: s) o (Gls_nil_push (Hγbc s o γ)))).
  Qed.

  Lemma Gdfs_list_stack_compl_nil {s a o} :   Gdfs_list_self_star s a o
                                            → Gdfs_list_stack [] s a o.
  Proof.
    induction 1 as [a | l a s b o γab _ γbo].
    - exact Gls_nil_emp.
    - apply Gls_nil_push. exact (list_self_cont_stack γab γbo).
  Qed.

  Lemma Gdfs_list_stack_compl {l s a o} :
    Gdfs_list_self_plus l s a o → Gdfs_list_stack l s a o.
  Proof.
    intros [b γab γbo]. revert s γbo.
    induction γab as [ a | x l a b yes γab Hγab | x l a b c no γxab Hγxab γbc Hγbc]; intros s γ.
    - exact (Gdfs_list_stack_compl_nil γ).
    - exact (Gls_cons_stop yes (Hγab s γ)).
    - exact (Gls_cons_next no (Hγxab _ (Gfl_cons γbc γ))).
  Qed.

End sec_corr_compl.

(* ------------------------------------------------------------------------------------------ *)
(* dfs_stack *)

Inductive Gdfs_stack `{C : Gcl} : stack X → list X → list X → Prop :=
| Gs_nil {a} :          Gdfs_stack [] a a
| Gs_cons {l s a o} :   Gdfs_list_stack l s a o
                      → Gdfs_stack (l :: s) a o.

(* Fake constructors for Gdfs_stack an  *)
Section sec_Gdfs_stack.
  Context `{C : Gcl}.

  Definition promote {l s a o l' s' a' o'} (f : Gdfs_list_stack l s a o → Gdfs_list_stack l' s' a' o') :
    Gdfs_stack (l :: s) a o → Gdfs_stack (l' :: s') a' o'.
    refine (λ γ, Gs_cons (f match γ in Gdfs_stack ls a o return
                                  match ls with l :: s => Gdfs_list_stack l s a o | _ => IDProp end
                            with
                            | Gs_cons γ => γ
                            | _ => idProp
                            end)).
  Defined.

  Definition Gs_nil_push {l s a o}  :     Gdfs_stack (l :: s) a o
                                        → Gdfs_stack ([] :: l :: s) a o
    := promote Gls_nil_push.
  Definition Gs_cons_stop {x l s a o} :   x ∈ a
                                        → Gdfs_stack (l :: s) a o
                                        → Gdfs_stack ((x :: l) :: s) a o
    := λ yes, promote (Gls_cons_stop yes).
  Definition Gs_cons_next {x l s a o} :    x ∉ a
                                         → Gdfs_stack (succs x :: l :: s) (x :: a) o
                                         → Gdfs_stack ((x :: l) :: s) a o
    := λ no, promote (Gls_cons_next no).

End sec_Gdfs_stack.

Remark Gdfs_stack_nil_all `{C : Gcl} {s a o} : Gdfs_stack s a o → Gdfs_stack ([] :: s) a o.
Proof.
  intro γ. apply Gs_cons.
  destruct γ as [a | l s a o γ].
  - apply Gls_nil_emp.
  - apply (Gls_nil_push γ).
Qed.

(* *)

Fixpoint dfs_stack `{C : Gcl} s a (δ : Ddfs_stack s a) {struct δ} : {o | Gdfs_stack s a o} :=
  match s                                                                 (* *) return Ddfs_stack s a → _
  with
  | []     =>                                                             (* *) λ _,
            exist a                                                       (* *) Gs_nil
  | [] :: [] =>                                                           (* *) λ δ,
            exist a                                                       (* *) (Gs_cons Gls_nil_emp)
  | [] :: s =>                                                            (* *) λ δ,
            let (o, γ) := dfs_stack s a                                   (* *) (Ds_nil_push_pi δ)
            in exist o                                                    (* *) (Gs_nil_push γ)
  | (x :: l) :: s =>                                                      (* *) λ δ,
      match in_dec x a with
      | left yes => let (o, γ) := dfs_stack (l :: s) a                    (* *) (Ds_cons_stop_pi δ yes)
                    in exist o                                            (* *) (Gs_cons_stop yes γ)
      | right no => let (o, γ) := dfs_stack (succs x :: l :: s) (x :: a)  (* *) (Ds_cons_next_pi δ no)
                    in exist o                                            (* *) (Gs_cons_next no γ)
      end
  end δ.

(* Main *)
Definition dfs_book_eff `{C : Gcl} x :                                    (* *)  Ddfs_stack ([[x]]) [] →
                            {o | Gdfs_stack [[x]] [] o} := dfs_stack [[x]] [].

Recursive Extraction dfs_book_eff.

(* Correctness and completeness of Gdfs_stack / Gdfs_list_stack *)
Section sec_corr_compl.
  Context `{C : Gcl}.

  (* Correctness *)
  Definition Gdfs_stack_corr {l s a o} :
    Gdfs_stack (l :: s) a o → Gdfs_list_stack l s a o
    := λ γ, match γ in Gdfs_stack ls a o return
                  match ls with l :: s => Gdfs_list_stack l s a o | _ => IDProp end
            with
            | Gs_cons γ => γ
            | _ => idProp
            end.

  (* A more general statement (not used) *)
  Corollary Gdfs_stack_corr_list_self {s a o} :
    Gdfs_stack s a o → Gdfs_list_self_star s a o.
  Proof.
    destruct 1 as [a | l s a o γ].
    - apply Gfl_nil.
    - destruct (Gdfs_list_stack_corr γ) as [b γab γbo]. exact (Gfl_cons γab γbo).
  Qed.

  (* Completeness *)
  Lemma Gdfs_stack_compl {l s a o} :
    Gdfs_list_stack l s a o → Gdfs_stack (l :: s) a o.
  Proof. intro γ. exact (Gs_cons γ). Qed.

End sec_corr_compl.

(* ======================================================================== *)
(* 2.3 Flattening s in dfs_stack provides the algorithm considered in [2]   *)

Fixpoint flatten {X : Type} (ll : list (list X)) : list X :=
  match ll with
  | [] => []
  | l :: ll => l ++ flatten ll
  end.


Fact flatten1 {X : Type} {l : list X} : flatten [l] = l.
Proof. apply app_nil_r. Qed.


(* Syntactic specification of dfs_flatten *)
Inductive Gdfs_flatten `{C : Gcl} : list X → list X → list X → Prop :=
| Gf_nil {a} :                Gdfs_flatten [] a a
| Gf_cons_stop {x ls a o} :   x ∈ a
                            → Gdfs_flatten ls a o
                            → Gdfs_flatten (x :: ls) a o
| Gf_cons_next {x ls a o} :   x ∉ a
                            → Gdfs_flatten (succs x ++ ls) (x :: a) o
                            → Gdfs_flatten (x :: ls) a o.

(* Inductive domain of dfs_flatten *)
Inductive Ddfs_flatten `{C : Gcl} : list X → list X → Prop :=
| Df_nil {a} :              Ddfs_flatten [] a
| Df_cons_stop {x ls a} :   x ∈ a
                          → Ddfs_flatten ls a
                          → Ddfs_flatten (x :: ls) a
| Df_cons_next {x ls a} :   x ∉ a
                          → Ddfs_flatten (succs x ++ ls) (x :: a)
                          → Ddfs_flatten (x :: ls) a.

(* Structurally smaller projections *)
Section sec_proj.
  Context `{C : Gcl}.

  Definition Df_cons_stop_pi {x ls a} (δ : Ddfs_flatten (x :: ls) a) :
    x ∈ a → Ddfs_flatten ls a :=
    match δ in Ddfs_flatten xls a return
          let shape := match xls with x :: ls => True | _ => False end in
          let x     := match xls with x :: ls => x    | _ => x     end in
          let ls    := match xls with x :: ls => ls   | _ => ls    end in
          shape → x ∈ a → Ddfs_flatten ls a with
    | Df_cons_stop yes δ => λ _ _, δ
    | Df_cons_next no δ  => λ _ yes, match no yes with end
    | _                  => λ absu _, match absu with end
    end I.

  Definition Df_cons_next_pi {x ls a} (δ : Ddfs_flatten (x :: ls) a) :
    x ∉ a → Ddfs_flatten (succs x ++ ls) (x :: a) :=
    match δ in Ddfs_flatten xls a return
          let shape := match xls with x :: ls => True | _ => False end in
          let x     := match xls with x :: ls => x    | _ => x     end in
          let ls    := match xls with x :: ls => ls   | _ => ls    end in
          shape → x ∉ a → Ddfs_flatten (succs x ++ ls) (x :: a) with
    | Df_cons_next no δ  => λ _ _, δ
    | Df_cons_stop yes δ => λ _ no, match no yes with end
    | _                  => λ absu _, match absu with end
    end I.

End sec_proj.

Fixpoint dfs_flatten `{C : Gcl} lls a                           (* *) (δ : Ddfs_flatten lls a) {struct δ}
  : {o | Gdfs_flatten lls a o} :=
  match lls                                                     (* *) return Ddfs_flatten lls a → _
  with
  | []     =>                                                   (* *) λ _,
              exist a                                           (* *) Gf_nil
  | x :: lls =>                                                 (* *) λ δ,
      match in_dec x a with
      | left yes =>
          let (o, γ) := dfs_flatten lls a                       (* *) (Df_cons_stop_pi δ yes)
          in exist o                                            (* *) (Gf_cons_stop yes γ)
      | right no =>
          let (o, γ) := dfs_flatten (succs x ++ lls) (x :: a)   (* *) (Df_cons_next_pi δ no)
          in exist o                                            (* *) (Gf_cons_next no γ)
      end
  end δ.

(* Main *)
Definition dfs_book `{C : Gcl} x :                              (* *)  Ddfs_flatten [x] [] →
                        {o | Gdfs_flatten [x] [] o} := dfs_flatten [x] [].

Recursive Extraction dfs_book.

(* Relating dfs_flatten with dfs_stack *)

(* An inductive characterization of flatten in the spirit of Gdfs_stack *)
Inductive iflatten {X} : list (list X) → list X → Prop :=
| ifl_nil : iflatten [] []
| ifl_cons_nil {s ls} : iflatten s ls → iflatten ([] :: s) ls
| ifl_cons_cons {x l s ls} : iflatten (l :: s) ls → iflatten ((x :: l) :: s) (x :: ls).

(* Equivalence between iflatten and flatten *)
Lemma iflatten_flatten {X} (s : list (list X)) : iflatten s (flatten s).
Proof.
  induction s as [ | l s Hs]; cbn.
  - constructor.
  - induction l as [ | x l Hl]; now constructor.
Qed.

Lemma flatten_iflatten {X} {s : list (list X)} {ls} : iflatten s ls → flatten s = ls.
Proof.
  intro ifl. induction ifl as [ | s ls ifl Hifl | s x l ls ifl Hifl]; cbn.
  - reflexivity.
  - exact Hifl.
  - case Hifl; reflexivity.
Qed.

Corollary iflatten_app {X} {s : list (list X)} {ls l} : iflatten s ls → iflatten (l :: s) (l ++ ls).
Proof. intro ifl. case (flatten_iflatten ifl). exact (iflatten_flatten (l :: s)). Qed.

Section sec_small_inv.
  (* Recursive small inversion of iflatten on its second argument;
     recursion is performed only on the ifl_cons_nil clause,
     dedicated to the cancelation of empty elements in the stack *)
  Context {X : Type}.

  Inductive iflatten_nil : list (list X) → Prop :=
  | ifln_nil : iflatten_nil []
  | ifln_cons_nil {s} : iflatten_nil s → iflatten_nil ([] :: s).
  Inductive iflatten_cons x ls : list (list X) → Prop :=
  | iflc_cons_nil {s} : iflatten_cons x ls s → iflatten_cons x ls ([] :: s)
  | iflc_cons_cons {l s} : iflatten (l :: s) ls → iflatten_cons x ls ((x :: l) :: s).
  Definition iflatten_dispatch (s : list (list X)) ls :=
    match ls with
    | [] => iflatten_nil s
    | x :: ls => iflatten_cons x ls s
    end.

  Lemma iflatten_recinv {s ls} : iflatten s ls → iflatten_dispatch s ls.
  Proof.
    intro ifl.
    induction ifl as [ | s ls ifl Hifl | x l s ls ifl Hifl]; try (constructor; exact ifl).
    destruct ls as [ | x ls]; constructor; exact Hifl.
  Qed.

End sec_small_inv.

(* Correctness and completeness of Gdfs_flatten / Gdfs_stack *)
Section sec_corr_compl.
  Context `{C : Gcl}.

  Lemma Gdfs_iflatten_corr {s a o ls} :
    Gdfs_flatten ls a o → iflatten s ls → Gdfs_stack s a o.
  Proof.
    intros γ ifl. generalize (iflatten_recinv ifl); clear ifl. revert s.
    induction γ as [ a | x ls a o yes γ Hγ | x ls a o no γ Hγ]; cbn; intros s ifl.
    - induction ifl as [ | s ifl Hifl].
      + apply Gs_nil.
      + apply Gdfs_stack_nil_all. apply Hifl.
    - induction ifl as [ s ifl Hifl | l s ifl].
      + apply Gdfs_stack_nil_all. apply Hifl.
      + apply (Gs_cons_stop yes), Hγ, iflatten_recinv, ifl.
    - induction ifl as [ s ifl Hifl | l s ifl].
      + apply Gdfs_stack_nil_all. apply Hifl.
      + apply (Gs_cons_next no), Hγ, iflatten_recinv.
        apply iflatten_app, ifl.
  Qed.

(* Correctness *)
  Corollary Gdfs_flatten_corr {s a o} :
    Gdfs_flatten (flatten s) a o → Gdfs_stack s a o.
  Proof. exact (λ γ, Gdfs_iflatten_corr γ (iflatten_flatten s)). Qed.

  (* Completeness is much easier *)
  Lemma Gdfs_flatten_compl {s a o} :
    Gdfs_stack s a o → Gdfs_flatten (flatten s) a o.
  Proof.
    destruct 1 as [a | l s a o γ]; cbn.
    - exact Gf_nil.
    - induction γ as [a | l s a o γ Hγ
                   | x l s a o yes γ Hγ
                     | x l s a o no γ Hγ]; cbn.
      + exact Gf_nil.
      + exact Hγ.
      + exact (Gf_cons_stop yes Hγ).
      + exact (Gf_cons_next no Hγ).
  Qed.

End sec_corr_compl.

Print Gls_plus.

Section sec_global_corr_compl.
  (* ======================================================================== *)
  (* Correctness and completeness of Gdfs_stack and Gdfs_flatten / Gdfs_list  *)
  (* By chaining the previous lemmas, taking an initial singleton stack.      *)

  Context `{C : Gcl}.

  Lemma Gdfs_stack_corr_list {l a o} : Gdfs_stack [l] a o → Gdfs_list l a o.
  Proof.
    intro γ. apply Gdfs_list_self_corr, Gls_plus1_inv, Gdfs_list_stack_corr, Gdfs_stack_corr, γ.
  Qed.

  Lemma Gdfs_stack_compl_list {l a o} : Gdfs_list l a o → Gdfs_stack [l] a o.
  Proof.
    intro γ. apply Gdfs_stack_compl, Gdfs_list_stack_compl, Gls_plus1, Gdfs_list_self_compl, γ.
  Qed.

  Lemma Gdfs_flatten_corr_list {l a o} : Gdfs_flatten l a o → Gdfs_list l a o.
  Proof.
    intro γ; apply Gdfs_stack_corr_list, Gdfs_flatten_corr.
    rewrite flatten1. exact γ.
  Qed.

  Lemma Gdfs_flatten_compl_list {l a o} : Gdfs_list l a o → Gdfs_flatten l a o.
  Proof.
    intro γ;  rewrite <- flatten1.
    apply Gdfs_flatten_compl, Gdfs_stack_compl_list, γ.
  Qed.

  (* Correctness and completeness of dfs_book_eff and dfs_book / Gdfs *)

  Corollary Gdfs_book_eff_corr {x o} : Gdfs_stack [[x]] [] o → Gdfs_main x o.
  Proof. exact (λ γ, Gdfs_list_corr (Gdfs_stack_corr_list γ)). Qed.

  Corollary Gdfs_book_eff_compl {x o} : Gdfs_main x o → Gdfs_stack [[x]] [] o.
  Proof. exact (λ γ, Gdfs_stack_compl_list (Gdfs_list_compl γ)). Qed.

  Corollary Gdfs_book_Gdfs {x o} : Gdfs_flatten [x] [] o → Gdfs_main x o.
  Proof. exact (λ γ, Gdfs_list_corr (Gdfs_flatten_corr_list γ)). Qed.

  Corollary Gdfs_book_compl {x o} : Gdfs_main x o → Gdfs_flatten [x] [] o.
  Proof. exact (λ γ, Gdfs_flatten_compl_list (Gdfs_list_compl γ)). Qed.

End sec_global_corr_compl.

