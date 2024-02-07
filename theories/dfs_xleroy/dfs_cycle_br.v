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

Set Implicit Arguments.

Section is_nth.

  Variable (X : Type).

  Inductive is_nth : list X → X → nat → Prop :=
    | is_nth_stop l x : is_nth (x::l) x 0
    | is_nth_next y l x n : is_nth l x n → is_nth (y::l) x (S n).

  Fact is_nth_fun l x y n : is_nth l x n → is_nth l y n → x = y.
  Proof.
    intros H; revert H y.
    induction 1; inversion 1; auto.
  Qed.

End is_nth.

Arguments is_nth {_}.
Arguments is_nth_fun {_ _ _ _ _}.

#[local] Hint Constructors is_nth : core.

Definition stotal {X} (R : X → X → Prop) := ∀x y, R x y ∨ x = y ∨ R y x.

Section strict_lex_list.

  Variables (X : Type) (R : X → X → Prop).

  Reserved Notation "l '<s' m" (at level 70).

  Inductive strict_lex_list : list X → list X → Prop :=
    | sll_nil x l : [] <s x::l
    | sll_tail x l m : l <s m → x::l <s x::m
    | sll_head x y l m : R x y → x::l <s y::m
  where "l <s m" := (strict_lex_list l m).

  Hint Constructors strict_lex_list : core.

  Fact sll_app l m k : m <s k -> l++m <s l++k.
  Proof. induction l; simpl; eauto. Qed.

  Fact sll_inv l m :
       l <s m
     → match l, m with
       | []   , _::_ => True
       | x::l , y::m => R x y ∨ x = y ∧ l <s m
       | _    , _    => False
       end.
  Proof. intros []; eauto. Qed.

  Hypothesis Rtrans : ∀ x y z, R x y → R y z → R x z.

  Fact sll_trans l m k : l <s m → m <s k → l <s k.
  Proof.
    intros H; revert H k. 
    induction 1 as [ x l | x l m _ IH | x y l m H1 ]; intros [ | z k ] H2%sll_inv; easy || eauto.
    all: destruct H2 as [ | (<- & ?) ]; eauto.
  Qed.

  Hypothesis Rirrefl : ∀x, ~ R x x.

  Fact sll_irrefl : ∀l, ~ l <s l.
  Proof.
    intros l H; generalize (eq_refl l).
    revert H; generalize l at 2 4; intros m.
    induction 1; inversion 1; subst; eauto.
    eapply Rirrefl; eauto.
  Qed.

  Hypothesis Rtotal : stotal R.

  Fact sll_total : stotal strict_lex_list.
  Proof.
    intros l; induction l as [ | x l IHl ]; intros [ | y m ]; eauto.
    destruct (Rtotal x y) as [| [<- | ] ]; eauto.
    destruct (IHl m) as [| [<- | ] ]; eauto.
  Qed.

  Lemma sll_prefix_choose l m :
        l <s m
      → (∃ x k, m = l++x::k)
      ∨ (∃ p x u y v, l = p++x::u /\ m = p++y::v /\ R x y).
  Proof.
    induction 1 as [ x l | x l m _ IH | x y l m H ].
    + left; simpl; eauto.
    + destruct IH as [ (y & k & ->) | (p & y & u & z & v & -> & -> & ?) ].
      * left; simpl; eauto.
      * right.
        exists (x::p), y, u, z, v; simpl; auto.
    + right; exists [], x, l, y, m; simpl; auto.
  Qed.

End strict_lex_list.

Arguments strict_lex_list {_}.

#[local] Notation sll := strict_lex_list.

Section ordered.

  Variables (X : Type) (R : X → X → Prop).

  Inductive ordered : list X → Prop :=
    | ordered_nil : ordered []
    | ordered_cons x l : Forall (R x) l → ordered l → ordered (x::l).

  Hint Constructors ordered : core.

  Fact ordered_inv l :
       ordered l
     ↔ match l with
       | []   => True
       | x::l => Forall (R x) l ∧ ordered l
       end.
  Proof.
    split.
    + destruct 1; eauto.
    + destruct l; simpl; constructor; tauto.
  Qed.

  Fact ordered_cons_iff x l : ordered (x::l) ↔ Forall (R x) l ∧ ordered l.
  Proof. apply ordered_inv. Qed.

  Fact ordered_app l m :
       ordered (l++m)
     ↔ ordered l 
     ∧ ordered m
     ∧ Forall (λ x, Forall (R x) m) l.
  Proof.
    induction l as [ | x l IHl ]; simpl.
    + repeat split; eauto; tauto.
    + rewrite ordered_inv, IHl, ordered_cons_iff,
              Forall_app, Forall_cons_iff; tauto.
  Qed.

End ordered.

Arguments ordered {_}.

#[local] Hint Constructors ordered : core.

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

  Variables (R : Y → Y → Prop) (Hf : ∀ a b x y, a < b → R (f a x) (f b y)).

  Local Lemma loop_ordered n l : ordered R (loop n l).
  Proof.
    induction l as [ | x l IHl ] in n |- *; simpl; eauto.
    constructor; auto.
    clear IHl.
    generalize (S n) (Nat.lt_succ_diag_r n).
    induction l as [ | y l IHl ]; intros m Hm; simpl; eauto.
    constructor; auto.
  Qed.

  Lemma map_n_ordered l : ordered R (map_n l).
  Proof. apply loop_ordered. Qed.

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
Local Definition π₂ {X Y Z} (c : X*Y*Z) := let '(_,y,_) := c in y.
Local Definition π₃ {X Y Z} (c : X*Y*Z) := let '(_,_,z) := c in z.

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

  Fact is_path_inv x l y :
       is_path x l y 
     → match l with
       | []   => x = y
       | n::l => ∃u, is_nth (succs x) u n ∧ is_path u l y
       end.
  Proof. induction 1; eauto. Qed.

  Fact is_path_fun x l y z : is_path x l y → is_path x l z → y = z.
  Proof.
    intros H; revert H z.
    induction 1 as [ | ? ? ? ? ? H1 ]; intros ? G%is_path_inv; eauto.
    destruct G as (? & G1 & G2).
    rewrite (is_nth_fun G1 H1) in G2; auto.
  Qed.

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

  Local Definition npfx (l m : list nat) := ~ ∃k, m = l++k.

  Lemma Gdfs_path_sll a l o :
          Gdfs_paths a l o
        → ordered (sll lt) (map π₂ (rev a++l))
        → ordered npfx (map π₂ l) (** l is not of the form ...++[(_,l,_)]++...++[(_,l++_,_)]++... *)
        → ordered (sll lt) (map π₂ (rev o)).
  Proof.
    induction 1 as [ a | a x p y l o H1 H2 IH2 | a x p y l o H1 H2 IH2 ]; intros Hal Hl. 
    + now rewrite <- app_nil_end in Hal.
    + rewrite map_app, ordered_app, map_cons, ordered_cons_iff in Hal.
      destruct Hal as (G1 & (G2 & G3) & G4).
      apply IH2.
      * rewrite map_app, ordered_app; repeat split; auto.
        revert G4; apply Forall_impl.
        now intros ? []%Forall_cons_iff.
      * apply ordered_cons_iff in Hl as []; auto.
    + apply IH2.
      rewrite map_app, ordered_app.
      rewrite map_app, ordered_app, map_cons, ordered_cons_iff in Hal.
      destruct Hal as (G1 & (G2 & G3)& G4).
      repeat split; eauto.
      * simpl; rewrite map_app, ordered_app; repeat split; simpl; eauto.
        revert G4; apply Forall_impl.
        intros ? []%Forall_cons_iff; auto.
      * rewrite map_app, map_map_n, ordered_app; repeat split; eauto.
        - apply map_n_ordered.
          intros ? ? ? ? ?; apply sll_app; now constructor 3.
        - apply Forall_forall.
           intros ? (n & z & -> & G5)%in_map_n; simpl.
           simpl map in Hl.
           apply ordered_cons_iff in Hl as (Hl1 & _).
           revert G2 Hl1; simpl.
           generalize (map π₂ l).
           induction 1 as [ | u m IHm ]; auto.
           intros (F1 & F2)%Forall_cons_iff; constructor; auto.
           apply sll_prefix_choose in IHm
             as [ (xp & pp & ->) | (p1 & a1 & u1 & b1 & v1 & -> & -> & ?) ].
           ++ destruct F1; eauto.
           ++ rewrite app_ass; simpl.
              apply sll_app; now constructor 3.
      * simpl; rewrite !map_app, Forall_app; split.
        - revert G4; apply Forall_impl.
          intros k [G4 G5]%Forall_cons_iff.
          apply Forall_app; split; auto.
          rewrite map_map_n.
          apply Forall_forall.
          intros ? (n & z & -> & ?)%in_map_n.
          apply sll_trans with (1 := lt_trans) (2 := G4).
          simpl.
          rewrite (app_nil_end p) at 1.
          apply sll_app; constructor.
        - constructor; simpl; auto.
          rewrite map_map_n, Forall_app; split; auto.
          apply Forall_forall.
          intros ? (n & z & -> & ?)%in_map_n.
          simpl.
          rewrite (app_nil_end p) at 1.
          apply sll_app; constructor.
      * simpl in Hl; apply ordered_cons_iff in Hl as (Hl1 & Hl2).
        rewrite map_app, map_map_n, ordered_app.
        repeat split; auto.
        - apply map_n_ordered.
          intros ? ? ? ? H (k & e); simpl in e.
          rewrite app_ass in e.
          apply app_inv_head in e.
          inversion e; subst.
          revert H; apply lt_irrefl.
        - simpl.
          apply Forall_forall.
          intros ? (n & z & -> & ?)%in_map_n.
          revert Hl1; apply Forall_impl.
          intros q C (k & ->); apply C.
          exists (n::k); now rewrite app_ass.
  Qed.

  (** We get that the output of dfs_paths is a strictly ordered list of paths
      wrt the reverse of the lexicographic (strict & total) order *)
  Corollary Gdfs_path_ordered x o : Gdfs_paths [] [(x,[],x)] o → ordered (sll lt) (map π₂ (rev o)).
  Proof. intros ?%Gdfs_path_sll; auto; simpl; eauto. Qed.

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
