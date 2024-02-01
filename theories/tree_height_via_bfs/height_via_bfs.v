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

     In particular, the following variant 

        let rec level h n = function
        | []      -> next h n
        | ...     -> level h ...
        and next h n = match n with
        | [] -> h
        | _  -> level (S h) ...
        in level 1 [] [t]

     could not be proved correct. Possibly
     the spec was too cumbersome over the
     version above. *)

(** This file is self contained over StdLib *)

From Coq Require Import Arith Max Lia List Wellfounded Extraction Utf8.

Import ListNotations.

(** List sum and max utilities *)

Section list_sum_max.

  Variables (X : Type) (f : X → nat).

  Definition list_sum := fold_right (λ x n, f x + n) 0.

  Fact list_sum_cons x l : list_sum (x::l) = f x + list_sum l.
  Proof. reflexivity. Qed.

  Fact list_sum_rev_append l m : list_sum (rev_append l m) = list_sum l + list_sum m.
  Proof. induction l as [ | x l IHl ] in m |- *; simpl; auto; rewrite IHl; simpl; lia. Qed.

  Definition list_max := fold_right (λ x n, Nat.max (f x) n) 0.

  Fact list_max_cons x l : list_max (x::l) = Nat.max (f x) (list_max l).
  Proof. reflexivity. Qed.

  Fact list_max_rev_append l m : list_max (rev_append l m) = Nat.max (list_max l) (list_max m).
  Proof. induction l as [ | x l IHl ] in m |- *; simpl; auto; rewrite IHl; simpl; lia. Qed.

End list_sum_max.

Arguments list_sum {_}.
Arguments list_max {_}.

(** Well foundedness utilities for termination *)

Section measure3_rect.

  Variable (X Y Z M : Type) (R : M → M → Prop) (HR : well_founded R)
           (m : X → Y → Z → M) (P : X → Y → Z → Type).

  Hypothesis F : (∀ x y z, (∀ x' y' z', R (m x' y' z') (m x y z) → P x' y' z') → P x y z).

  Arguments F : clear implicits.

  Let m' (c : X * Y * Z) := match c with (x,y,z) => m x y z end.

  Notation R' := (λ c d, R (m' c) (m' d)).
  Local Fact Rwf : well_founded R'.
  Proof. apply wf_inverse_image with (f := m'), HR. Qed.

  Definition measure3_rect x y z : P x y z :=
    (fix loop x y z (a : Acc R' (x,y,z)) { struct a } := 
      F x y z (λ x' y' z' H', loop x' y' z' (@Acc_inv _ _ _ a (_,_,_) H'))) _ _ _ (Rwf (_,_,_)).

End measure3_rect.

Tactic Notation "induction" "on" hyp(x) hyp(y) hyp(z) "as" ident(IH) "with" "wf" constr(wf) "and" "measure" uconstr(f) :=
   pattern x, y, z; revert x y z; apply measure3_rect with (1 := wf) (m := λ x y z, f); intros x y z IH.

Inductive nat_lex : nat*nat -> nat*nat -> Prop :=
| nat_lex_lft a b c d : a < c → nat_lex (a,b) (c,d)
| nat_lex_rt  a b c d : a = c → b < d → nat_lex (a,b) (c,d).

Lemma nat_lex_wf : well_founded nat_lex.
Proof.
  intros (x,y).
  induction x in y |- * using (well_founded_induction lt_wf).
  induction y using (well_founded_induction lt_wf).
  constructor; inversion 1; subst; eauto.
Qed.

(** The type of undecorated rose trees *)

Unset Elimination Schemes.

Inductive rtree :=
| rt : list rtree -> rtree.

Set Elimination Schemes.

#[local] Notation "⟨ l ⟩" := (rt l) (at level 1, format "⟨ l ⟩").

Definition rtree_sons t :=
  match t with 
  | ⟨l⟩ => l
  end.

(* This is the non recursive terminal way of computing the size, via dfs *)
Fixpoint rtree_sz t :=
  match t with 
  | ⟨l⟩ => S (list_sum rtree_sz l)
  end.

(* This is the non recursive terminal way of computing the height, via dfs *)
Fixpoint rtree_ht t :=
  match t with 
  | ⟨l⟩ => S (list_max rtree_ht l)
  end.

Fact rtree_ht_ge_1 t : 1 ≤ rtree_ht t.
Proof. destruct t; simpl; lia. Qed.

Section rtree_ht_via_bfs.

  Implicit Types (h o : nat) (n c : list rtree).

  Inductive Glevel : nat → list rtree → list rtree → nat → Prop :=

  | Glevel_nil h n o :      Gnext (S h) n o
                          → Glevel h n [] o

  | Glevel_cons h n l c o : Glevel h (rev_append l n) c o
                          → Glevel h n (⟨l⟩::c) o

  with Gnext : nat → list rtree → nat → Prop :=

  | Gnext_nil h :     Gnext h [] h

  | Gnext_not h n o : n ≠ []
                    → Glevel h [] n o
                    → Gnext h n o
  .

  Inductive Dlevel : nat → list rtree → list rtree → Prop :=

  | Dlevel_nil {h n} :      Dnext (S h) n
                          → Dlevel h n []

  | Dlevel_cons {h n l c} : Dlevel h (rev_append l n) c
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
      rewrite list_max_rev_append in H.
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

     hence the lexicographic product of
      1) total size of n and c
      2) max of (1 + max height in n) and (max height in c)
     decreases on recursive calls. *)

  Theorem level_terminates h n c : Dlevel h n c.
  Proof.
    induction on h n c as IH
      with wf nat_lex_wf
      and measure (list_sum rtree_sz n + list_sum rtree_sz c, 
                   Nat.max (1+list_max rtree_ht n) (list_max rtree_ht c)).
    destruct c as [ | [l] c ].
    + constructor.
      case_eq n.
      * constructor 1.
      * intros r n' e; constructor 2; [ easy | rewrite <- e ].
        apply IH.
        constructor 2.
        - lia.
        - simpl plus.
          apply Nat.max_lt_iff; left.
          cut (1 <= list_max rtree_ht n); [ lia | ].
          subst; simpl.
          generalize (rtree_ht_ge_1 r); lia.
    + constructor 2.
      apply IH.
      constructor 1.
      rewrite list_sum_rev_append, list_sum_cons; simpl; lia.
  Qed.

  (** Inversion lemmas for D{level,next} using small inversions *)

  Local Fact nnil_eq_nil {x c} : x::c = [] → False.
  Proof. discriminate. Qed.

  Definition Dlevel_pi1 {h n} (d : Dlevel h n []) : Dnext (S h) n :=
    match d in Dlevel h n c return c = [] → Dnext (S h) n with
    | Dlevel_nil d  => λ _, d
    | Dlevel_cons _ => λ e, match nnil_eq_nil e with end
    end eq_refl.

  Let is_nnil c := match c with [] => False | _ => True end.

  Let head x c : rtree :=
    match c with
    | []   => x
    | t::_ => t
    end.

  Definition Dlevel_pi2_inv {h n l c} (d : Dlevel h n (⟨l⟩::c)) : Dlevel h (rev_append l n) c.
  Proof. now inversion d. Defined.

  Print Dlevel_pi2_inv.

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

  Definition Dlevel_pi2 {h n l c} (d : Dlevel h n (⟨l⟩::c)) : Dlevel h (rev_append l n) c :=
    match d in Dlevel h' n' c' return Dlevel_shape2 l c c' → Dlevel h' (rev_append l n') c with
    | Dlevel_nil _  => λ e, match Dlevel_shape2_inv e with end
    | Dlevel_cons d => λ e, match Dlevel_shape2_inv e with
                            | conj e1 e2 => 
                              match e1, e2 with 
                              | eq_refl, eq_refl => d
                              end
                            end
    end Dlevel_shape2_intro.

(* None of the attempts below give perfect extraction ie w/o __/obj.magic 
   contrary to the inversion tactic which, on the other hand, produces 
   a very difficult to term to decypher *)

  Definition Dlevel_pi2' {h n l c} (d : Dlevel h n (⟨l⟩::c)) : Dlevel h (rev_append l n) c.
  Proof.
    refine (match d in Dlevel h' n' c' return ⟨l⟩::c = c' → Dlevel h' (rev_append (rtree_sons (head ⟨l⟩ c')) n') (tail c') with
    | Dlevel_nil _  => λ e, match nnil_eq_nil e with end
    | Dlevel_cons d => λ e, d
    end eq_refl).
  Defined.

  Local Fact cons_eq l1 l2 c1 c2 : ⟨l1⟩::c1 = ⟨l2⟩::c2 → l1 = l2 ∧ c1 = c2.
  Proof. now inversion 1. Defined.

  Definition Dlevel_pi2'' {h n l c} (d : Dlevel h n (⟨l⟩::c)) : Dlevel h (rev_append l n) c.
  Proof.
    refine (match d in Dlevel h' n' c' return h = h' → n = n' → ⟨l⟩::c = c' → Dlevel h (rev_append l n) c with
    | Dlevel_nil _  => λ _  _  e3, match nnil_eq_nil e3 with end
    | Dlevel_cons d => λ e1 e2 e3, _
    end eq_refl eq_refl eq_refl).
    inversion e3; subst; exact d. (* if inversion is replaced with apply cons_eq in e3 as [], then __/Obj.Magic *)
  Defined.

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
        | ⟨l⟩ => λ d, let (o,ho) := level h (rev_append l n) c (Dlevel_pi2 d) in
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

End rtree_ht_via_bfs.

Extraction Inline level next.
Recursive Extraction rtree_ht_bfs.

