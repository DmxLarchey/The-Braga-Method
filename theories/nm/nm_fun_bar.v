(**************************************************************)
(*   Copyright Dominique Larchey-Wendling    [*]              *)
(*             Jean-François Monin           [+]              *)
(*                                                            *)
(*            [*] Affiliation LORIA -- CNRS                   *)
(*            [+] Affiliation VERIMAG - Univ. Grenoble-Alpes  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Utf8. (* → λ ∀ ∃ ↔ ∧ ∨ *)

Require Import nm_graph_def.

Set Implicit Arguments.

Unset Elimination Schemes.

Inductive 𝔻nm : Ω → Prop :=
  | in_dnm_0 :             𝔻nm α
  | in_dnm_1 : ∀ y z,      𝔻nm y 
                         → 𝔻nm z 
                         → 𝔻nm (ω α y z)
  | in_dnm_2 : ∀ a b c y z,
                           𝔻nm (ω b y z) 
                         → 𝔻nm (ω c y z) 
               → (∀ nb nc, ω b y z ⟼n nb  
                         → ω c y z ⟼n nc 
                         → 𝔻nm (ω a nb nc))
                         → 𝔻nm (ω (ω a b c) y z).

Section nm_pwc.

  (** The five next guarded projections
    
        prj_𝔻nm_1 y z : 𝔻 (ω α y z) -> 𝔻 y
        prj_𝔻nm_2 y z : 𝔻 (ω α y z) -> 𝔻 z
        prj_𝔻nm_3 a b c y z : 𝔻 (ω (ω a b c) y z) -> 𝔻 (ω b y z)
        prj_𝔻nm_4 a b c y z : 𝔻 (ω (ω a b c) y z) -> 𝔻 (ω c y z)
        prj_𝔻nm_5 a b c y z nb nc : 𝔻 (ω (ω a b c) y z)
                                  -> ω b y z ⟼ nb
                                  -> ω c y z ⟼ nc
                                  -> 𝔻 (ω a nb nc)
    
       construct a structurally simpler (ie. a sub-term) of the input domain
       term of type 𝔻.  This is *critically* important because these lemmas
       justify termination of the below fixpoint computation of nm_rec *)
        
  (* First we show how to get prj_𝔻nm_1 in a tightly controlled 
     way by hand writting its term using a variant of small inversions
       
       "Handcrafted Inversions Made Operational on Operational Semantics"
                by JF. Monin and X. Shi  (ITP 2013)
       
     The technique is based on dependent pattern-matching. 
       
     Looking at the code of prj_𝔻nm_1 below, it is obvious that
     every branch produces a sub-term of the input term.
     Notice that the "match F with end" has ZERO branches hence
     obviously satisfies a universal property over branches *)

  (* An arbitrary value of type Ω *)
  Let 𝔻nm_shape_1 x := match x with ω α y z => True | _ => False end.
  Let 𝔻nm_pred_1 x  := match x with ω α y z => y    | _ => x end.
  Local Definition prj_𝔻nm_1 {y z} (d : 𝔻nm (ω α y z)) : 𝔻nm y :=
    match d in 𝔻nm x return 𝔻nm_shape_1 x -> 𝔻nm (𝔻nm_pred_1 x) with
      | in_dnm_1 dy dz => λ _, dy 
      | _              => λ G, match G with end 
    end I.
      
  (* We could also proceed using the "inversion", which 
     also produces sub-terms in this case. This property did not
     always hold for the older versions of the tactic and we do
     not certify that it will work in any case *) 
           
  Local Definition prj_𝔻nm_2 {y z} : 𝔻nm (ω α y z) → 𝔻nm z.
  Proof. inversion 1; trivial. Defined.
    
  (** It could be interesting to compare the code of 𝔻nm_inv_1 and 𝔻nm_inv_2
    
        Print 𝔻nm_inv_1.
        Print 𝔻nm_inv_2. *)

  (* For the remaining projections we stick to small inversions style for
     sustainability reasons *)
    
  Let 𝔻nm_shape_2 x := match x with ω (ω a b c) y z => True | _ => False end.
  Let 𝔻nm_pred_3 x := match x with ω (ω a b c) y z => ω b y z | _ => x end.
  Local Definition prj_𝔻nm_3 {a b c y z} (d : 𝔻nm (ω (ω a b c) y z)) : 𝔻nm (ω b y z) :=
    match d in 𝔻nm x return 𝔻nm_shape_2 x → 𝔻nm (𝔻nm_pred_3 x) with
      | in_dnm_2 db dc da => λ _, db 
      | _                 => λ G, match G with end 
    end I.

  Let 𝔻nm_pred_4 x := match x with ω (ω a b c) y z => ω c y z | _ => x end.
  Local Definition prj_𝔻nm_4 {a b c y z} (d : 𝔻nm (ω (ω a b c) y z)) : 𝔻nm (ω c y z) :=
    match d in 𝔻nm x return 𝔻nm_shape_2 x → 𝔻nm (𝔻nm_pred_4 x) with
      | in_dnm_2 db dc da => λ _, dc 
      | _                 => λ G, match G with end 
    end I.

  Let 𝔻nm_pred_5 x := match x with ω (ω a b c) y z => a | _ => x end.
  Local Definition prj_𝔻nm_5 {a b c y z} nb nc (d : 𝔻nm (ω (ω a b c) y z)) :
                                   ω b y z ⟼n nb
                                →  ω c y z ⟼n nc
                                →  𝔻nm (ω a nb nc) :=
    match d in 𝔻nm x return
           (**) 𝔻nm_shape_2 x
             → 𝔻nm_pred_3 x ⟼n nb
             → 𝔻nm_pred_4 x ⟼n nc
             → 𝔻nm (ω (𝔻nm_pred_5 x) nb nc) with
      | in_dnm_2 db dc da => λ _, da nb nc
      | _                 => λ G, match G with end
    end I.

  (** We give the proof term directly (programming style)
      but it could be built progressively using refine tactics. 
      Using refine is the recommended method. Obtaining the code 
      directly is not for the faint of heart ... even though
      it looks nice in the end. 
      This proof term is a decoration of the OCaml code of nm 
      with extra typing information consisting in:
          1/ a pre-condition De : 𝔻 e which is a termination certificate (ie. prj_𝔻_nm_[1-5]), which is inlined in this version
          2/ a post-condition relating the input e to the output n : e ⟼ n *)

  (* The explicit dependent pattern matching

     match e ** return 𝔻nm e → _ ** with

     ** ... ** added below, is not needed any more for Coq 8.11+ *)

  Let Fixpoint nm_pwc e (D : 𝔻nm e) {struct D} : {n | e ⟼n n}.
  Proof. refine( 
    match e return 𝔻nm e → _ with
        | α               => λ _, 

                          exist _ α _

        | ω α y z         => λ D, 
          let (ny,Cy) := nm_pwc y (prj_𝔻nm_1 D) in
          let (nz,Cz) := nm_pwc z (prj_𝔻nm_2 D) in

                          exist _ (ω α ny nz) _

        | ω (ω a b c) y z => λ D,
          let (nb,Cb) := nm_pwc (ω b y z)   (prj_𝔻nm_3 D) in
          let (nc,Cc) := nm_pwc (ω c y z)   (prj_𝔻nm_4 D) in
          let (na,Ca) := nm_pwc (ω a nb nc) (prj_𝔻nm_5 D Cb Cc) in

                          exist _ na _
    end D).
    + constructor 1.
    + now constructor 2.
    + now constructor 3 with (3 := Ca).
  Qed.
      
  (** Then we derive nm and nm_spec by projection *)

  Definition nm e D := proj1_sig (@nm_pwc e D).
    
  Fact nm_spec e D : e ⟼n @nm e D.
  Proof. apply (proj2_sig _). Qed.

End nm_pwc.

Arguments nm e D : clear implicits.

(** Inductive-Recursive domain constructors *)

Fact 𝔻nm_1 : 𝔻nm α.
Proof. constructor; auto. Qed.

Fact 𝔻nm_2 y z : 𝔻nm y → 𝔻nm z → 𝔻nm (ω α y z).
Proof. constructor 2; assumption. Qed.

Fact 𝔻nm_3 u v w y z Dv Dw : 𝔻nm (ω u (nm (ω v y z) Dv) (nm (ω w y z) Dw)) 
                           → 𝔻nm (ω (ω u v w) y z).
Proof.
  constructor 3; auto.
  intros na nb nma nmb. 
  rewrite (𝔾nm_fun nma (nm_spec Dv)).
  rewrite (𝔾nm_fun nmb (nm_spec Dw)).
  assumption.
Qed.

(** Inductive-Recursive Type-bounded eliminator/induction principle *)

(* → λ ∀ ∃ ↔ ∧ ∨ *)
  
Section 𝔻nm_rect.

  Variables (P   : ∀ e, 𝔻nm e → Type)
            (HPi : ∀ e D1 D2, @P e D1 → @P e D2)
            (HP1 : P 𝔻nm_1)
            (HP2 : ∀ y z D1 (_ : P D1) D2 (_ : P D2), P (@𝔻nm_2 y z D1 D2))
            (HP3 : ∀ u v w y z D1 (_ : P D1) D2 (_ : P D2) D3 (_ : P D3), P (@𝔻nm_3 u v w y z D1 D2 D3)).

  Fixpoint 𝔻nm_rect e D { struct D } : @P e D.
  Proof.
    destruct e as [ | [ | u v w ] y z ].
    + apply HPi with (1 := HP1).
    + refine (HPi _ (HP2 (𝔻nm_rect _ _) (𝔻nm_rect _ _))); revert D.
      * apply prj_𝔻nm_1.
      * apply prj_𝔻nm_2.
    + refine (HPi _ (HP3 (𝔻nm_rect _ (prj_𝔻nm_3 D)) (𝔻nm_rect _ (prj_𝔻nm_4 D)) (𝔻nm_rect _ _))).
      apply prj_𝔻nm_5 with (1 := D); apply nm_spec.
  Qed.

End 𝔻nm_rect.
