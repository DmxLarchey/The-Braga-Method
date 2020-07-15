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

(* Version with a mutuall inductive domain 
   for one-step small inversions *)
(*
Inductive d_nm : Ω → Prop :=
  | in_dnm_0 :             d_nm α
  | in_dnm_1 : ∀ y z,      d_nm y 
                         → d_nm z 
                         → d_nm (ω α y z)
  | in_dnm_2 : ∀ a b c y z,
                           d_nm (ω b y z) 
                         → d_nm (ω c y z) 
               → (∀ nb nc, ω b y z ⟼n nb  
                         → ω c y z ⟼n nc 
                         → d_nm (ω a nb nc))
                         → d_nm (ω (ω a b c) y z).
*)

Inductive 𝔻nm1 (D: Ω → Prop) y z : Prop :=
  | in_dnm1 :       D y 
                         → D z 
                         → 𝔻nm1 D y z.
Inductive 𝔻nm2 (D: Ω → Prop) a b c y z : Prop :=
  | in_dnm2 :
                           D (ω b y z) 
                         → D (ω c y z) 
               → (∀ nb nc, ω b y z ⟼n nb  
                         → ω c y z ⟼n nc 
                         → D (ω a nb nc))
                         → 𝔻nm2 D a b c y z.
Inductive 𝔻nm : Ω → Prop :=
  | in_dnm_0 :                𝔻nm α
  | in_dnm_1 : ∀ y z, 𝔻nm1 𝔻nm y z → 𝔻nm (ω α y z)
  | in_dnm_2 : ∀ a b c y z, 𝔻nm2 𝔻nm a b c y z → 𝔻nm (ω (ω a b c) y z).

Local Definition 𝔻nm1' := 𝔻nm1 𝔻nm.
Local Definition 𝔻nm2' := 𝔻nm2 𝔻nm.

Section nm_pwc.

  (** TODO repair comment 
      The two next inversions 
    
        inv_𝔻nm_1 y z : 𝔻 (ω α y z) -> 𝔻1
        prj_𝔻nm_2 a b c y z : 𝔻 (ω (ω a b c) y z) -> 𝔻2

       construct a structurally simpler (ie. a sub-term) of the input domain
       term of type 𝔻.  This is *critically* important because these lemmas
       justify termination of the below fixpoint computation of nm_rec *)
        
  (* First we show how to get prj_𝔻nm_1 in a tightly controlled 
     way by hand writting its term using a variant of small inversions
       
       "Handcrafted Inversions Made Operational on Operational Semantics"
                by JF. Monin and X. Shi  (ITP 2013)
       
     The technique is based on dependent pattern-matching. 
       
     Looking at the code of inv_𝔻nm_1 below, it is obvious that
     every branch produces a sub-term of the input term.
     Notice that the "match C with end" has ZERO branches hence
     obviously satisfies a universal property over branches *)

  (* An arbitrary value of type Ω *)
  Let 𝔻nm_shape_1 x := match x with ω α y z => True | _ => False end.
  Let 𝔻nm_pred_1 x  := match x with ω α y z => y    | _ => x    end.
  Let 𝔻nm_pred_2 x  := match x with ω α y z => z    | _ => x    end.
  Let res_inv1 x := 𝔻nm1' (𝔻nm_pred_1 x) (𝔻nm_pred_2 x).
  Local Definition inv_𝔻nm_1 {y z} (d : 𝔻nm (ω α y z)) : 𝔻nm1' y z :=
    match d in 𝔻nm x return 𝔻nm_shape_1 x -> res_inv1 x with
      | in_dnm_1 d => λ _, d
      | _              => λ G, match G with end 
    end I.
   
  (* Fails, cf old letters with Bruno Barras *)
  Let res_inv1' x :=
    match x with ω α y z => True → 𝔻nm1' y z    | _ => False → False end.
  Local Definition inv_𝔻nm_1_no_struct {y z} (d : 𝔻nm (ω α y z)) : 𝔻nm1' y z :=
    match d in 𝔻nm x return res_inv1' x with
      | in_dnm_1 d => λ G', d
      | _              => λ G', match G' with end 
    end I.
    
  Let 𝔻nm_shape_2 x := match x with ω (ω a b c) y z => True | _ => False end.
  Let 𝔻nm_pred_a x := match x with ω (ω a b c) y z => a | _ => x  end.
  Let 𝔻nm_pred_b x := match x with ω (ω a b c) y z => b | _ => x  end.
  Let 𝔻nm_pred_c x := match x with ω (ω a b c) y z => c | _ => x  end.
  Let 𝔻nm_pred_y x := match x with ω (ω a b c) y z => y | _ => x  end.
  Let 𝔻nm_pred_z x := match x with ω (ω a b c) y z => z | _ => x  end.
  Let res_inv2 x := 𝔻nm2' (𝔻nm_pred_a x) (𝔻nm_pred_b x) (𝔻nm_pred_c x) (𝔻nm_pred_y x) (𝔻nm_pred_z x).
  Local Definition inv_𝔻nm_2 {a b c y z} (d : 𝔻nm (ω (ω a b c) y z)) : 𝔻nm2' a b c y z :=
    match d in 𝔻nm x return 𝔻nm_shape_2 x → res_inv2 x with
      | in_dnm_2 d => λ _, d
      | _          => λ G, match G with end 
    end I.



  Let Fixpoint nm_pwc e (D : 𝔻nm e) {struct D} : {n | e ⟼n n}.
  Proof. refine( 
    match e return 𝔻nm e → _ with
        | α               => λ _, 

                          exist _ α _

        | ω α y z         => λ D,
          let (dy, dz) := (inv_𝔻nm_1 D) in
          let (ny,Cy) := nm_pwc y dy in
          let (nz,Cz) := nm_pwc z  dz in

                          exist _ (ω α ny nz) _

        | ω (ω a b c) y z => λ D,
          let (db, dc, da) := (inv_𝔻nm_2 D) in
          let (nb,Cb) := nm_pwc (ω b y z)   db in
          let (nc,Cc) := nm_pwc (ω c y z)   dc in
          let (na,Ca) := nm_pwc (ω a nb nc) (da _ _ Cb Cc) in

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
Proof. constructor 2. constructor; assumption. Qed.

Fact 𝔻nm_3 u v w y z Dv Dw : 𝔻nm (ω u (nm (ω v y z) Dv) (nm (ω w y z) Dw)) 
                           → 𝔻nm (ω (ω u v w) y z).
Proof.
  constructor 3. constructor; auto.
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
    destruct e as [ | [ | a b c ] y z ].
    + apply HPi with (1 := HP1).
    + destruct (inv_𝔻nm_1 D) as [dy dz].
      refine (HPi _ (HP2 (𝔻nm_rect _ _) (𝔻nm_rect _ _))); assumption.
    + destruct (inv_𝔻nm_2 D) as [db dc da].
      refine (HPi _ (HP3 (𝔻nm_rect _ db) (𝔻nm_rect _ dc) (𝔻nm_rect _ (da _ _ _ _)))).
      all: apply nm_spec.
  Qed.

End 𝔻nm_rect.
