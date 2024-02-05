(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*             Mozilla Public License MPL v2.0                *)
(**************************************************************)

(** Following a discussion with JC Filliâtre, here is
    a correct by construction recursive terminal algorithm 
    for computing the height of an undecorated rose tree via
    a zizaging Breadth First Traversal.

      type rtree = Rt of rtree list

      let rec rev_app n = function
      | []   -> n
      | x::l -> rev_app (x::n) l

      let rtree_ht_bfs t =
        let rec level h n = function
        | []      -> next (S h) n
        | Rt l::c -> level h (rev_app n l) c
        and next h n = match n with
        | [] -> h
        | _  -> level h [] n
        in level 0 [] [t] 

    "Surprise surprise" in the position where
     h should be increased.

     In particular, I could not prove the correctness
     of the following variant

        let rec level h n = function
        | []      -> next h n
        | ...     -> level h ...
        and next h n = match n with
        | [] -> h
        | _  -> level (S h) ...
        in level 1 [] [t]

     Possibly the spec was too cumbersome compared to 
     the more straightforward version above. *)

(** This file is self contained over StdLib *)

From Coq Require Import Arith Max Lia List Wellfounded Extraction Utf8.

Import ListNotations.

(** List sum and max utilities *)

(* rev_app with arguments ordered as in OCaml *)
Definition rev_app {X} :=
  fix loop (l m : list X) :=
    match m with
    | []   => l
    | x::m => loop (x::l) m
    end.

Section list_sum_max.

  Variables (X : Type) (f : X → nat).

  Definition list_sum := fold_right (λ x n, f x + n) 0.

  Fact list_sum_cons x l : list_sum (x::l) = f x + list_sum l.
  Proof. reflexivity. Qed.

  Fact list_sum_rev_app l m : list_sum (rev_app l m) = list_sum l + list_sum m.
  Proof. induction m as [ | ? ? IH ] in l |- *; simpl; auto; rewrite IH; simpl; lia. Qed.

  Definition list_max := fold_right (λ x n, Nat.max (f x) n) 0.

  Fact list_max_cons x l : list_max (x::l) = Nat.max (f x) (list_max l).
  Proof. reflexivity. Qed.

  Fact list_max_rev_app l m : list_max (rev_app l m) = Nat.max (list_max l) (list_max m).
  Proof. induction m as [ | ? ? IH ] in l |- *; simpl; auto; try lia; rewrite IH; simpl; lia. Qed.

End list_sum_max.

Arguments list_sum {_}.
Arguments list_max {_}.

(** Well foundedness utilities for termination *)

Section measure3_rect.

  Variable (X Y Z M : Type) (m : X → Y → Z → nat) (P : X → Y → Z → Type).

  Hypothesis F : (∀ x y z, (∀ x' y' z', m x' y' z' < m x y z → P x' y' z') → P x y z).

  Arguments F : clear implicits.

  Let m' (c : X * Y * Z) := match c with (x,y,z) => m x y z end.

  Notation R' := (λ c d, m' c < m' d).
  Local Fact Rwf : well_founded R'.
  Proof. apply wf_inverse_image with (f := m'), lt_wf. Qed.

  Definition measure3_rect x y z : P x y z :=
    (fix loop x y z (a : Acc R' (x,y,z)) { struct a } := 
      F x y z (λ x' y' z' H', loop x' y' z' (@Acc_inv _ _ _ a (_,_,_) H'))) _ _ _ (Rwf (_,_,_)).

End measure3_rect.

Tactic Notation "induction" "on" hyp(x) hyp(y) hyp(z) "as" ident(IH) "with" "measure" uconstr(f) :=
   pattern x, y, z; revert x y z; apply measure3_rect with (m := λ x y z, f); intros x y z IH.

(** The type of undecorated rose trees *)

Inductive rtree :=
| rt : list rtree → rtree.

#[local] Notation "⟨ l ⟩" := (rt l) (at level 1, format "⟨ l ⟩").

(* This is the non recursive terminal way of computing the size, via dfs *)
Fixpoint rtree_sz t := match t with ⟨l⟩ => S (list_sum rtree_sz l) end.

(* This is the non recursive terminal way of computing the height, via dfs *)
Fixpoint rtree_ht t := match t with ⟨l⟩ => S (list_max rtree_ht l) end.

Fact rtree_ht_ge_1 t : 1 ≤ rtree_ht t.
Proof. destruct t; simpl; lia. Qed.

Section rtree_ht_via_bfs.

  Implicit Types (h o : nat) (n c : list rtree).

  Inductive Glevel : nat → list rtree → list rtree → nat → Prop :=

  | Glevel_nil h n o :      Gnext (S h) n o
                          → Glevel h n [] o

  | Glevel_cons h n l c o : Glevel h (rev_app n l) c o
                          → Glevel h n (⟨l⟩::c) o

  with Gnext : nat → list rtree → nat → Prop :=

  | Gnext_nil h :           Gnext h [] h

  | Gnext_not h n o :       n ≠ []
                          → Glevel h [] n o
                          → Gnext h n o
  .

  Inductive Dlevel : nat → list rtree → list rtree → Prop :=

  | Dlevel_nil {h n} :      Dnext (S h) n
                          → Dlevel h n []

  | Dlevel_cons {h n l c} : Dlevel h (rev_app n l) c
                          → Dlevel h n (⟨l⟩::c)

  with Dnext : nat → list rtree → Prop :=

  | Dnext_nil {h} :         Dnext h []

  | Dnext_not {h n} :       n ≠ []
                          → Dlevel h [] n
                          → Dnext h n
  .

  Hint Constructors Glevel Gnext : core.

  (** Partial correctness of level/next *)

  Fixpoint level_partial_correctness h n c o (d : Glevel h n c o) { struct d } :

       o = h + Nat.max (1+list_max rtree_ht n) (list_max rtree_ht c)

  with next_partial_correctness h n o (d : Gnext h n o) { struct d } :

       o = h + list_max rtree_ht n.

  Proof.
  + destruct d as [ h n o H | h n l c o H ].
    * apply next_partial_correctness in H.
      simpl; lia.
    * apply level_partial_correctness in H.
      rewrite list_max_rev_app in H.
      rewrite list_max_cons; simpl rtree_ht.
      lia.
  + destruct d as [ h | h n o Hn Ho ].
    * simpl; lia. 
    * apply level_partial_correctness in Ho.
      simpl list_max in Ho.
      rewrite Nat.max_r in Ho; [ lia | ].
      destruct n as [ | x n ]; [ easy | ].
      generalize (rtree_ht_ge_1 x); simpl; lia.
  Qed.

  (** Termination, ie totality of level *)

  (* level h n []      ~~>  level (S h) [] n is n ≠ []
     level h n ⟨l⟩::c  ~~>  level h (rev_append n l) c

     We find a linear measure that decrease at
     the above two reduction steps:
     the sum of 
       1) total size of n and c
       2) the max of (1 + max height in n) and (max height in c) 

     Hence one could show termination in linear
     amount of recursive calls by indexing the
     domain Dlevel and the graph Glevel predicates
     with the number of steps. *)

  Theorem level_terminates h n c : Dlevel h n c.
  Proof.
    induction on h n c as IH
      with measure (          list_sum rtree_sz n + list_sum rtree_sz c
                 + Nat.max (1+list_max rtree_ht n) (list_max rtree_ht c)).
    destruct c as [ | [l] c ].
    + constructor.
      case_eq n; [ constructor 1 | intros r n' e ].
      constructor 2; [ easy | rewrite <- e ].
      apply IH.
      simpl list_sum; simpl list_max.
      rewrite Nat.max_r, Nat.max_l; try lia.
      subst; simpl.
      generalize (rtree_ht_ge_1 r); lia.
    + constructor 2.
      apply IH.
      rewrite list_sum_rev_app, list_max_rev_app, list_sum_cons, list_max_cons.
      simpl rtree_ht; simpl rtree_sz. 
      lia.
  Qed.

  (** Inversion lemmas for D{level,next} using small inversions *)

  Local Fact nnil_eq_nil {x c} : x::c ≠ [].
  Proof. discriminate. Qed.

  Local Fact cons_eq {l₁ l₂ c₁ c₂} : ⟨l₁⟩::c₁ = ⟨l₂⟩::c₂ → l₂ = l₁ ∧ c₂ = c₁.
  Proof. now inversion 1. Qed.

  Definition Dlevel_pi1 {h n} (d : Dlevel h n []) : Dnext (S h) n :=
    match d in Dlevel h n c return c = [] → Dnext (S h) n with
    | Dlevel_nil d  => λ _, d
    | Dlevel_cons _ => λ e, match nnil_eq_nil e with end
    end eq_refl.

  (** This inversion with mostly undecypherable code, is accepted
      in the fixpoint and does not introduce __/Obj.magic *)
  Definition Dlevel_pi2_inv {h n l c} (d : Dlevel h n (⟨l⟩::c)) : Dlevel h (rev_app n l) c.
  Proof. now inversion d. Defined.

  (** The below inversion the one actually used in the fixpoint,
      is readable and avoids __/Obj.magic as well *)

  Definition Dlevel_pi2 {h n l c} (d : Dlevel h n (⟨l⟩::c)) : Dlevel h (rev_app n l) c :=
    match d in Dlevel h' n' c' return ⟨l⟩::c = c' → Dlevel h' (rev_app n' l) c with
    | Dlevel_nil _  => λ e, match nnil_eq_nil e with end
    | Dlevel_cons d => λ e, match cons_eq e with
                            | conj e1 e2 =>
                              match e1, e2 with 
                              | eq_refl, eq_refl => d
                              end
                            end
    end eq_refl.

  (* An alternate but similar approach that works as well *)

  Inductive Dlevel_shape2 l c : list rtree -> Prop :=
  | Dlevel_shape2_intro : Dlevel_shape2 l c (⟨l⟩::c).

  Arguments Dlevel_shape2_intro {l c}.

  Local Fact Dlevel_shape2_inv {l c c'} :
         Dlevel_shape2 l c c'
      -> match c' with
         | []       => False
         | ⟨l'⟩::c' => l' = l ∧ c' = c
         end.
  Proof. destruct 1; eauto. Qed.

  Definition Dlevel_pi2' {h n l c} (d : Dlevel h n (⟨l⟩::c)) : Dlevel h (rev_app n l) c :=
    match d in Dlevel h' n' c' return Dlevel_shape2 l c c' → Dlevel h' (rev_app n' l) c with
    | Dlevel_nil _  => λ e, match Dlevel_shape2_inv e with end
    | Dlevel_cons d => λ e, match Dlevel_shape2_inv e with
                            | conj e1 e2 =>
                              match e1, e2 with
                              | eq_refl, eq_refl => d
                              end
                            end
    end Dlevel_shape2_intro.

  (** The attempt below is shortest and the one usually *favored* in Braga 
      but however gives *imperfect* extraction ie with __/Obj.magic  *)

  Let is_nnil c := match c with [] => False | _      => True end.
  Let head c    := match c with [] => []    | ⟨l⟩::_ => l end. (* Default value is [] *)
  Let tail c    := match c with [] => []    |   _::c => c end. (* Default value is [] *)

  Definition Dlevel_pi2'' {h n l c} (d : Dlevel h n (⟨l⟩::c)) : Dlevel h (rev_app n l) c :=
    match d in Dlevel h' n' c' return is_nnil c' → Dlevel h' (rev_app n' (head c')) (tail c') with
    | Dlevel_nil _  => λ C, match C with end
    | Dlevel_cons d => λ _, d
    end I.

  (** The last projection does not generate any problem *)

  Definition Dnext_pi1 {h n} (d : Dnext h n) : n ≠ [] → Dlevel h [] n :=
    match d with 
    | Dnext_nil     => λ C, match C eq_refl with end
    | Dnext_not _ d => λ _, d
    end.

  (** Implementation of the fully spec'd mutually recursive function.
      The above inversion lemmas D{level,next}_pi{1,2} can also
      be proved using the inversion tactic which works in this
      case. In the Braga method, we favor explicit terms obtained
      using the techniques of small inversions. *)

  Local Fixpoint level h n c (d : Dlevel h n c) { struct d } : sig (Glevel h n c) 
             with next h n   (d : Dnext h n)    { struct d } : sig (Gnext h n).
  Proof.
    + refine (match c return Dlevel _ _ c → _ with
      | []   =>  λ d, let (o,ho) := next (S h) n (Dlevel_pi1 d) in
                      exist _ o _
      | t::c => 
        match t return Dlevel _ _ (t::_) -> _ with
        | ⟨l⟩ => λ d, let (o,ho) := level h (rev_app n l) c (Dlevel_pi2 d) in
                      exist _ o _
        end
      end d); eauto.
    + refine (match n as n' return n = n' → _ with
      | []   => λ _, exist _ h _
      | t::l => λ e, let (o,ho) := level h [] n (Dnext_pi1 d _) in
                     exist _ o _
      end eq_refl); eauto; subst; easy || now constructor 2.
  Defined.

  (* This is extracted to a recursive terminal way of computing the height, via bfs *)
  Definition rtree_ht_bfs t := proj1_sig (level 0 [] [t] (level_terminates _ _ _)).

  Corollary rtree_ht_bfs_spec t : Glevel 0 [] [t] (rtree_ht_bfs t).
  Proof. apply (proj2_sig _). Qed.

  Theorem rtree_ht_bfs_total_correctness t : rtree_ht_bfs t = rtree_ht t.
  Proof.
    generalize (rtree_ht_bfs_spec t).
    intros ->%level_partial_correctness.
    rewrite Nat.max_r; simpl.
    + lia.
    + generalize (rtree_ht_ge_1 t); lia.
  Qed.

  Hint Resolve rtree_ht_bfs_total_correctness : core.

  Corollary rtree_ht_bfs_fix l : rtree_ht_bfs ⟨l⟩ = 1+list_max rtree_ht_bfs l.
  Proof.
    rewrite rtree_ht_bfs_total_correctness; simpl; f_equal.
    symmetry; induction l; simpl; f_equal; auto.
  Qed.

End rtree_ht_via_bfs.

Check rtree_ht_bfs_fix.

Extraction Inline level next.
Recursive Extraction rtree_ht_bfs.

