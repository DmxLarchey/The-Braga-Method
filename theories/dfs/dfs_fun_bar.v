(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Jean-François Monin        [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*            [+] Affiliation VERIMAG - Univ. Grenoble-Alpes  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Utf8.

Require Import dfs_graph_def.
(* Require Import list_facts. *)

Set Implicit Arguments.

Unset Elimination Schemes.

(* → λ ∀ ∃ *)

Inductive 𝔻dfs : list 𝓥 → list 𝓥 → Prop :=
  | 𝔻dfs_1 : ∀ v,        𝔻dfs v nil
  | 𝔻dfs_2 : ∀ v x l,    x ∈ v 
                       → 𝔻dfs v l 
                       → 𝔻dfs v (x::l)
  | 𝔻dfs_3 : ∀ v x l,    x ∉ v 
                       → 𝔻dfs (x::v) (succs x++l) 
                       → 𝔻dfs v (x::l).

Set Elimination Schemes.

Fact 𝔾dfs_𝔻dfs v l : (∃o, v ⊔ l ⟼d o) → 𝔻dfs v l.
Proof.
  intros (o & H); revert H.
  induction 1.
  + constructor.
  + constructor 2; auto.
  + constructor 3; auto.
Qed.

(* Now we define dfs by structural induction on d_dfs *)
 
Section dfs.

  (** We use a local and fully specified fixpoint. 
      At every point of the domain, we compute an
      image in the graph 

          dfs_pwc : forall v l, 𝔻dfs v l -> { o | v,l ⟼ o }.

   *)

  (* Beware that the following termination certicates CANNOT be 
     arbitrary terms, they must be structurally smaller that the
     original certificate to ensure termination. However,
     they can perfectly live in sort Prop.

     The "inversion" tactic does a superb job here !!!

     Also notice that the absurd case is implemented using
     exfalso with performs a match on a proof of False
     ensuring structural decrease
   *)

  (* Explicit definitions, 
     with systematic way for getting the components of 
     the list in argument of D *)

  (* is_cons replaced with shape *)
  Let shape b v l :=
    match l with
      | nil  => False
      | x::l => x ∈? v = b
    end.

  (* Getting components of l0 at the deepest place *)
  (* Be careful to scopes *)
  Let 𝜋_𝔻dfs_1_expl v x l (D : 𝔻dfs v (x::l)) :
                    x ∈? v = true → 𝔻dfs v l :=
    match D in 𝔻dfs v l0 return
          let l := match l0 with x::l => l | _ => l end 
          in  shape true v l0 → 𝔻dfs v l with
      | 𝔻dfs_1 v     => λ G, match G with end
      | 𝔻dfs_2 _ _ D => λ G, D
      | 𝔻dfs_3 _ N _ => λ G, match not_mem_true N G with end
    end.

  Let 𝜋_𝔻dfs_2_expl v x l (D : 𝔻dfs v (x::l)) :
                    x ∈? v = false → 𝔻dfs (x::v) (succs x ++ l) :=
    match D in 𝔻dfs v l0 return
          let x := match l0 with x::l => x | _ => x end in
          let l := match l0 with x::l => l | _ => l end 
          in  shape false v l0 → 𝔻dfs (x::v) (succs x ++ l) with
      | 𝔻dfs_1 v     => λ G, match G with end
      | 𝔻dfs_2 _ Y _ => λ G, match not_mem_false Y G with end
      | 𝔻dfs_3 _ _ D => λ G, D
    end.

  (* Automated mysterious definitions *)
  Let 𝜋_𝔻dfs_1_myst v x l : 𝔻dfs v (x::l) → x ∈? v = true → 𝔻dfs v l.
  Proof.
    inversion 1; auto.
    intros E; exfalso; revert E; rewrite mem_true_iff; tauto.
  Qed.

  Let 𝜋_𝔻dfs_2_myst v x l : 𝔻dfs v (x::l) 
                          → x ∈? v = false 
                          → 𝔻dfs (x::v) (succs x ++ l).
  Proof. inversion 1; auto. Qed.

  (* Pick up the mysterious or explicit version ... *)

  Definition 𝜋_𝔻dfs_1 := 𝜋_𝔻dfs_1_expl.  (* _myst also works *)
  Definition 𝜋_𝔻dfs_2 := 𝜋_𝔻dfs_2_expl.  (* _myst also works *)

  (* We separate the computational contents from the logical
     contents using the handy refine tactic. *)

  (* The explicit dependent pattern matching

     match l ** return 𝔻dfs _ l → _ ** with

     ** ... ** added below, is not needed any more for Coq 8.11+ *)

  Let Fixpoint dfs_pwc v l (D : 𝔻dfs v l) {struct D} : {o | v⊔l ⟼d o}.
  Proof. refine(
    match l return 𝔻dfs _ l → _ with
      | nil  => λ D,       exist _ v _
      | x::l => λ D, 
      match x ∈? v as b return x ∈? v = b → _ with
        | true  => λ E, 
             let (o,Go) := dfs_pwc v l _
             in            exist _ o _
        | false => λ E, 
             let (o,Go) := dfs_pwc (x::v) (succs x++l) _
             in            exist _ o _
      end eq_refl
    end D).
    1,2,4: cycle 1. (* reordering of proof obligations *)
    * now apply 𝜋_𝔻dfs_1 with (1 := D).
    * now apply 𝜋_𝔻dfs_2 with (1 := D).
    * constructor 1; auto.
    * constructor 2; auto; apply mem_iff; auto.
    * constructor 3; auto; apply mem_iff; auto.
  Qed.
    
  (* We get the dfs and its specification by projection.
     Notice that the specification is for the moment
     given by the graph *)
       
  Definition dfs v l D := proj1_sig (@dfs_pwc v l D).

  Definition dfs_spec v l D : v ⊔ l ⟼d @dfs v l D.
  Proof. apply (proj2_sig _). Qed.

End dfs.

(** The domain is exactly the projection of the graph *)

Theorem 𝔻dfs_eq_𝔾dfs v l : 𝔻dfs v l ↔ ∃o, v ⊔ l ⟼d o.
Proof.
  split.
  + intros D; exists (dfs D); apply dfs_spec.
  + apply 𝔾dfs_𝔻dfs.
Qed.

(* The graph g_dfs and dfs_spec are enough to characterizes 
   dfs but we rather avoid exposing g_dfs directly to the user 
   and transform the specification of d_dfs/dfs into a simulated 
   inductive/recursive definition.
      
   We get something which could be defined by 
  
     Inductive d_dfs : list X -> list X -> Prop :=
       | d_dfs_1 : forall v,                                            d_dfs v nil
       | d_dfs_2 : forall v x l,  x ∈ v -> d_dfs     v            l  -> d_dfs v (x::l)
       | d_dfs_3 : forall v x l,  x ∉ v -> d_dfs (x::v) (succs x++l) -> d_dfs v (x::l)
     with Fixpoint dfs v l (D : d_dfs v l) : list X :=
       match D with
         | d_dfs_1 v         => v
         | d_dfs_2 v x l H D => dfs D
         | d_dfs_3 v x l H D => dfs D
       end.
       
   But this will *never* work as is in Coq unless Prop is replaced by Set
   in the type of d_dfs. Indeed, pattern matching on Prop is forbidden when 
   computing in Set/Type. However, we do want d_dfs to be of Sort Prop
   so that extraction removes that argument. In fact, d_dfs is a trace
   of a full execution of dfs ...

   Notice that domain constructors d_dfs_[012] do not depend on
   dfs in this particular case, so this is a degenerate case of
   induction/recursion.
    
*)

(* → λ ∀ ∃ ↔ *)

Section d_dfs_rect.
  
  (* This is Type-bounded induction principle
       
     Notice HP0 which restricts the induction principle to
     proof irrelevant predicates ... no big deal because
     dfs is proof irrelevant anyway *)

  Variables (P   : ∀ v l, 𝔻dfs v l → Type)
            (HPi : ∀ v l D1 D2, @P v l D1 → @P v l D2)
            (HP1 : ∀ v, P (@𝔻dfs_1 v))
            (HP2 : ∀ v x l H D (_ : P D), P (@𝔻dfs_2 v x l H D))
            (HP3 : ∀ v x l H D (_ : P D), P (@𝔻dfs_3 v x l H D)).

  Fixpoint 𝔻dfs_rect v l D { struct D } : @P v l D.
  Proof.
    destruct l as [ | x l ].
    * apply HPi with (1 := HP1 _).
    * case_eq (mem x v); intros H.
      + refine (HPi _ (HP2 _ _ (𝔻dfs_rect _ _ _))).
        - revert H; apply mem_true_iff.
        - now apply 𝜋_𝔻dfs_1 with (1 := D).
      + refine (HPi _ (HP3 _ _ (𝔻dfs_rect _ _ _))).
        - revert H; apply mem_false_iff.
        - now apply 𝜋_𝔻dfs_2 with (1 := D).
  Qed.

End d_dfs_rect.

Definition 𝔻dfs_rec (P : ∀ v l, 𝔻dfs v l → Set) := 𝔻dfs_rect P.
Definition 𝔻dfs_ind (P : ∀ v l, 𝔻dfs v l → Prop) := 𝔻dfs_rect P.
