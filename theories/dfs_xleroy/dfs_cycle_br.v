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

  Local Fixpoint loop n l {struct l} :=
    match l with
    | []   => []
    | x::l => f n x :: loop (S n) l
    end.

  Local Fact in_loop_only y n l :
    y ∈ loop n l → ∃ m x, y = f (m+n) x ∧ is_nth l x m.
  Proof.
    induction l as [ | x l IHl ] in n |- *; simpl; try easy.
    intros [ <- | (m & z & -> & ?)%IHl ].
    + exists 0, x; eauto.
    + exists (S m), z; split; eauto; f_equal; lia.
  Qed.

  Local Fact in_loop_if l x m n : is_nth l x m → f (m+n) x ∈ loop n l.
  Proof.
    induction 1 as [ l x | y l x m H1 IH1 ] in n |- *; simpl; eauto.
    right; specialize (IH1 (S n)).
    now rewrite Nat.add_succ_r in IH1.
  Qed.

  Definition map_n := loop 0.

  Theorem in_map_n y l : y ∈ map_n l ↔ ∃ n x, y = f n x ∧ is_nth l x n.
  Proof.
    split.
    + intros (n & x & -> & ?)%in_loop_only; exists n, x; split; auto; f_equal; lia.
    + intros (n & x & -> & H).
      apply in_loop_if with (n := 0) in H.
      now rewrite Nat.add_0_r in H.
  Qed.

End map_n.

Arguments loop {X Y}.
Arguments map_n {X Y}.

Local Fact map_loop X Y Z (f : nat → X → Y) (g : Y → Z) n l :
   map g (loop f n l) = loop (λ n x, g (f n x)) n l.
Proof. induction l in n |- *; simpl; f_equal; auto. Qed.

Local Fact loop_id X n l : loop (λ _ (x : X), x) n l = l.
Proof. induction l in n |- *; simpl; f_equal; auto. Qed.

Fact map_map_n X Y Z (f : nat → X → Y) (g : Y → Z) l : map g (map_n f l) = map_n (λ n x, g (f n x)) l.
Proof. apply map_loop. Qed.

Fact map_n_id X l : map_n (λ _ (x : X), x) l = l.
Proof. apply loop_id. Qed.

Local Definition π₁ {X Y Z} (c : X*Y*Z) := let '(x,_,_) := c in x.
Local Definition π₃ {X Y Z} (c : X*Y*Z) := let '(_,_,y) := c in y.

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

  Inductive is_path : X → list nat → X → Prop :=
    | is_path_nil  x : is_path x [] x
    | is_path_cons x n y l z : is_nth (succs x) y n → is_path y l z → is_path x (n::l) z.

  Hint Constructors is_path : core.

  Fact is_path_app x l y m z : is_path x l y → is_path y m z → is_path x (l++m) z.
  Proof. induction 1; simpl; eauto. Qed.

  Inductive is_prefix : X → list nat → X → X → list nat → X → Prop :=
    | is_prefix_app x l y m z : is_path x l y → is_path y m z → is_prefix x l y x (l++m) z.

  Hint Constructors is_prefix : core.

  Fact is_prefix_path_left x l y u m v : is_prefix x l y u m v → is_path x l y.
  Proof. now destruct 1. Qed.

  Hint Resolve is_path_app : core.

  Fact is_prefix_path_right x l y u m v : is_prefix x l y u m v → is_path u m v.
  Proof. destruct 1; eauto. Qed.

  Fact is_prefix_iff x l y u m v :
           is_prefix x l y u m v
         ↔ x = u ∧ ∃ r, m = l++r
                      ∧ is_path x l y
                      ∧ is_path y r v.
  Proof.
    split.
    + destruct 1; eauto.
    + intros (<- & r & -> & []); auto.
  Qed.

  (**

  let p3 (_,_,x) = x;;

  let dfs_cyc_paths succs =
    let rec dfs a  = function
    | []         -> a
    | (x,p,y)::l -> if in_dec y (map p3 a) then dfs a l
                    else let sp = map_n (fun n z -> (x,p@[n],z)) (succs y) 
                         in dfs ((x,p,y)::a) (sp @ l)
    in fun x -> dfs [] [(x,[],x)];;

  *)

  Notation path := (X*list nat*X)%type.

  Inductive Gdfs_paths : list path → list path → list path → Prop :=
    | Gdfs_paths_stop a :            Gdfs_paths a [] a
    | Gdfs_paths_in {a x p y l o} :  y ∈ map π₃ a
                                   → Gdfs_paths a l o
                                   → Gdfs_paths a ((x,p,y)::l) o
    | Gdfs_paths_out {a x p y l o} : y ∉ map π₃ a
                                    → (let sp := map_n (fun n s => (x,p++[n],s)) (succs y)
                                      in Gdfs_paths ((x,p,y)::a) (sp++l) o)
                                    → Gdfs_paths a ((x,p,y)::l) o.

  Hint Constructors Gdfs_paths : core.

  Let ipt : path → Prop := λ '(x,l,y), is_path x l y.
  Let ipf : path → path → Prop := λ '(x,l,y) '(x',m,y'), is_prefix x l y x' m y'. 

  Lemma Gdfs_paths_prefix a l o :
           Gdfs_paths a l o
         → Forall ipt a
         → Forall ipt l
         → Forall ipt o
         ∧ ∀p, p ∈ o
             → p ∈ a
             ∨ ∃ q, q ∈ l
                  ∧ ipf q p.
  Proof.
    induction 1 as [ a | a x p y l o H1 H2 IH2 | a x p y l o H1 H2 IH2 ]; simpl; intros Ha Hl; split; eauto;
      apply Forall_cons_iff in Hl as (Hl1 & Hl2); eauto.
    + apply IH2; auto.
    + intros q Hq; apply IH2 in Hq as [ | (? & []) ]; eauto.
    + apply IH2; eauto.
      apply Forall_app; split; auto.
      apply Forall_forall.
      intros c (n & x' & -> & ?)%in_map_n.
      apply is_path_app with (1 := Hl1); eauto.
    + intros q [ [ <- | ] | (r & H3 & H4) ]%IH2; eauto.
      * right; exists (x,p,y); split; auto.
        rewrite (app_nil_end p) at 2; red; eauto.
      * right.
        apply in_app_iff in H3 as [ (n & t & -> & H3)%in_map_n | H3 ].
        - destruct q as ((u,k),v).
          apply is_prefix_iff in H4 as (<- & q & -> & H4 & H5).
          exists (x,p,y); split; auto.
          rewrite -> app_ass; constructor; eauto.
        - exists r; eauto.
      * apply Forall_app; split; auto.
        apply Forall_forall.
        intros c (n & x' & -> & ?)%in_map_n.
        apply is_path_app with (1 := Hl1); eauto.
  Qed.

  (** The output of dfs_cyc_paths x is a list of paths starting at x *) 
  Corollary Gdfs_paths_source x o : Gdfs_paths [] [(x,[],x)] o → Forall (λ p, ipt p ∧ π₁ p = x) o.
  Proof.
    intros (_ & H)%Gdfs_paths_prefix; eauto.
    2: repeat constructor.
    apply Forall_forall.
    intros ((u,m),v) [ [] | (q & [ <- | [] ] & Hq) ]%H; split.
    + eapply is_prefix_path_right; eauto.
    + now apply is_prefix_iff in Hq as (<- & _).
  Qed.

  Hint Constructors Gdfs_book : core.

  (* We related the image of dfs_paths to that of dfs_book *)
  Fact Gdfs_paths_Gdfs_book {a l o} : Gdfs_paths a l o → Gdfs_book _ succs (map π₃ a) (map π₃ l) (map π₃ o).
  Proof.
    induction 1 as [ | a x p y l o H1 H2 IH2 | a x p y l o H1 H2 IH2 ]; simpl in *; eauto.
    constructor 3; auto.
    rewrite map_app, map_map_n in IH2; simpl in IH2.
    now rewrite map_n_id in IH2.
  Qed.

  Fact Gdfs_book_Gdfs_paths v l o :
          Gdfs_book _ succs v l o
        → ∀ a m, map π₃ a = v
               → map π₃ m = l
               → ∃p, map π₃ p = o
                   ∧ Gdfs_paths a m p.
  Proof.
    induction 1 as [ v | v x l o H1 H2 IH2 | v x l o H1 H2 IH2 ]; intros a m E1 E2.
    + apply map_eq_nil in E2; subst; eauto.
    + apply map_eq_cons in E2 as (((x',p),y) & m' & ? & ? & ?); subst.
      destruct (IH2 _ _ eq_refl eq_refl) as (o' & []); subst.
      exists o'; split; eauto.
    + apply map_eq_cons in E2 as (((x',p),y) & m' & ? & ? & ?); subst.
      destruct (IH2 ((x',p,y)::a) (map_n (fun n s => (x',p++[n],s)) (succs y)++m'))
        as (o' & <- & ?); auto.
      * rewrite map_app, map_map_n; f_equal; apply map_n_id.
      * exists o'; split; eauto.
  Qed.

  Theorem Gdfs_paths_iff_Gdfs_book a l o : Gdfs_book _ succs (map π₃ a) (map π₃ l) o ↔ ∃p, map π₃ p = o ∧ Gdfs_paths a l p.
  Proof.
    split.
    + intro; now apply Gdfs_book_Gdfs_paths with (2 := eq_refl) (3 := eq_refl).
    + intros (p & <- & ?); now apply Gdfs_paths_Gdfs_book.
  Qed.

  (** We get a proof that dfs_book and dfs_cyc_paths terminate on the same inputs
      and that both outputs are two lists (of the same length) where there is a two 
      by two relation described below *)

  (* Termination equivalence between dfs_paths and dfs_book *)
  Theorem Ddfs_book_Ddfs_paths x : ex (Gdfs_book _ succs [] [x]) ↔ ex (Gdfs_paths [] [(x,[],x)]).
  Proof.
    split.
    + intros (o & Ho).
      apply Gdfs_book_Gdfs_paths with (a := []) (m := [(x,[],x)]) in Ho
        as (p & []); auto; eauto.
    + intros (o & ?%Gdfs_paths_Gdfs_book); now exists (map π₃ o).
  Qed.

  (* Relation between the outputs of
          dfs_cyc_paths x = pl
          dfs_book = dl
     pl and dl are two lists of the same length such that
     2 by 2, for the element of p of pl and that d of dl,
     p is a path ffrom x to d *)
  Theorem Gdfs_paths_book_Forall2 x pl dl :
            Gdfs_paths [] [(x,[],x)] pl
          → Gdfs_book _ succs [] [x] dl
          → Forall2 (λ p d, π₁ p = x ∧ π₃ p = d ∧ ipt p) pl dl.
  Proof.
    intros H1 H2.
    generalize (Gdfs_paths_Gdfs_book H1); intros H3.
    rewrite (Gdfs_book_fun _ _ _ _ _ _ H2 H3).
    apply Gdfs_paths_source in H1.
    revert H1; clear H2 H3.
    induction 1; simpl; eauto.
    constructor 2; tauto.
  Qed.

End dfs_cycle_br.

Arguments is_path {_}.

Check Ddfs_book_Ddfs_paths.
Check Gdfs_paths_book_Forall2.
