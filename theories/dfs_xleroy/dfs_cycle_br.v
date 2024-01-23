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

Require Import Arith Lia List Relations Utf8 Extraction.

Import ListNotations.

Require Import dfs_abstract dfs_cycle.

Inductive is_nth {X} : list X → X → nat → Prop :=
  | is_nth_stop l x : is_nth (x::l) x 0
  | is_nth_next y l x n : is_nth l x n → is_nth (y::l) x (S n).

#[local] Hint Constructors is_nth : core.

Section map_n.

  Variables (X Y : Type) (f : nat → X → Y).

  Let Fixpoint loop n l {struct l} :=
    match l with
    | []   => []
    | x::l => f n x :: loop (S n) l
    end.

  Local Fact in_loop_only y n l :
    y ∈ loop n l -> exists m x, y = f (m+n) x /\ is_nth l x m.
  Proof.
    induction l as [ | x l IHl ] in n |- *; simpl; try easy.
    intros [ <- | (m & z & -> & ?)%IHl ].
    + exists 0, x; eauto.
    + exists (S m), z; split; eauto; f_equal; lia.
  Qed.

  Local Fact in_loop_if l x m n : is_nth l x m -> f (m+n) x ∈ loop n l.
  Proof.
    induction 1 as [ l x | y l x m H1 IH1 ] in n |- *; simpl; eauto.
    right; specialize (IH1 (S n)).
    now rewrite Nat.add_succ_r in IH1.
  Qed.

  Definition map_n := loop 0.

  Theorem in_map_n y l : y ∈ map_n l <-> exists n x, y = f n x /\ is_nth l x n.
  Proof.
    split.
    + intros (n & x & -> & ?)%in_loop_only; exists n, x; split; auto; f_equal; lia.
    + intros (n & x & -> & H).
      apply in_loop_if with (n := 0) in H.
      now rewrite Nat.add_0_r in H.
  Qed.

End map_n.

Arguments map_n {X Y}.

Section dfs_cycle_br.

  Variable (X : Type).

  Implicit Type x : X.

  Variables (in_dec : ∀ x l, {x ∈ l} + {x ∉ l})
            (succs : X → list X).

  Local Fact in_wdec l x : x ∈ l ∨ x ∉ l.
  Proof. destruct (in_dec x l); auto. Qed.

  Local Fact eq_wdec (x y : X) : x = y ∨ x ≠  y.
  Proof.
    destruct (in_dec x [y]) as [ [ <- | [] ] | C ]; auto.
    right; contradict C; subst; auto.
  Qed.

  Hint Resolve in_wdec eq_wdec : core.

  Inductive is_path : X → list nat → X -> Prop :=
    | is_path_nil  x : is_path x [] x
    | is_path_cons x n y l z : is_nth (succs x) y n → is_path y l z → is_path x (n::l) z.

  (*

let dfs_cyc_paths succs =
  let rec dfs a ab = function
  | []          -> ab
  | (x,p,y)::l -> if in_dec y a then dfs a ab l
                  else let succs_paths = map_n (fun n z -> (x,p@[n],z)) (succs y) in
                       dfs (y::a) (p::ab) (succs_paths @ l)
  in fun x -> dfs [] [] [(x,[],x)];;

  *)

  Inductive Gdfs_paths : list X → list (X*list nat*X) → list (X*list nat*X) → list (X*list nat*X) → Prop :=
    | Gdfs_paths_stop v a :          Gdfs_paths v a [] a
    | Gdfs_paths_in {v a x p y l o} :  x ∈ v
                                    → Gdfs_paths v a l o
                                    → Gdfs_paths v a ((x,p,y)::l) o
    | Gdfs_paths_out {v a x p y l o} : x ∉ v
                                   → (let sp := map_n (fun n s => (x,p++[n],s)) (succs x)
                                      in Gdfs_paths (x::v) ((x,p,y)::a) (sp++l) o)
                                   → Gdfs_paths v a ((x,p,y)::l) o.

  Let ip : X*list nat*X -> Prop := fun '(x,p,y) => is_path x p y.

  Fact Gdfs_paths_prop v a l o : Gdfs_paths v a l o 
                               → Forall ip a 
                               → Forall ip l
                               → Forall ip o.
  Proof.
    induction 1 as [ | v a x p y l o H1 H2 IH2 | v a x p y l o H1 H2 IH2 ]; eauto;
      intros H3 [H4 H5]%Forall_cons_iff; auto.
    apply IH2; auto.
    apply Forall_app; split; auto.
    clear H1 H2 IH2 H3 H5.
    apply Forall_forall.
    intros c (n & x' & -> & ?)%in_map_n.
    red.
    (* is_path_app !! *)
  Admitted.

End dfs_cycle_br.
