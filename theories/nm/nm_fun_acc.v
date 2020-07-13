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

(** Small tactic to identify the goal and and hypothesis *)

Tactic Notation "id" "with" hyp(H) := 
  match type of H with 
    | ?A => 
    match goal with 
      |- ?B => cut (A=B); [ intros <-; exact H | ]
    end 
  end. 

Tactic Notation "id" "with" hyp(H) "level" int(n) := 
  id with H; do n f_equal.

(** The sub recursive calls relation *)

Local Reserved Notation "x '<sc' y" (at level 70, no associativity).

Inductive nm_sub_calls : Ω → Ω → Prop :=
  | in_nm_sc0 : ∀ y z, y <sc ω α y z
  | in_nm_sc1 : ∀ y z, z <sc ω α y z 
  | in_nm_sc2 : ∀ u v w y z, ω v y z <sc ω (ω u v w) y z
  | in_nm_sc3 : ∀ u v w y z, ω w y z <sc ω (ω u v w) y z 
  | in_nm_sc4 : ∀ u v w y z na nb, ω v y z ⟼n na
                                 → ω w y z ⟼n nb
                                 → ω u na nb <sc ω (ω u v w) y z 
where "x <sc y" := (nm_sub_calls x y).

(** The domain are the Acc(essible) expressions under <sc *)

Definition d_nm := Acc nm_sub_calls.
Notation 𝔻nm := d_nm.

Section nm_pwc.
  
    (** We give the proof term directly (programming style)
        but it could be built progressively using refine tactics. 
        Using refine is the recommended method. Obtaining the code 
        directly is not for the faint of heart ... even though
        it looks nice in the end. 
        This proof term is a decoration of the OCaml code of nm 
        with extra typing information consisting in:
          1/ a pre-condition De : 𝔻 e which is a termination certificate (ie. d_nm_inv_[1-5])
          2/ a post-condition relating the input e to the output n : e ⟼ n *)

  (* → λ ∀ ∃ ↔ ∧ ∨ *)

  Let Fixpoint nm_pwc e (D : 𝔻nm e) {struct D} : {n | e ⟼n n}.
  Proof. refine( 
    match e with
        | α               => λ _, 
                          exist _ α _
        | ω α y z         => λ D, 
          let (ny,Cy) := nm_pwc y _ in
          let (nz,Cz) := nm_pwc z _ in
                          exist _ (ω α ny nz) _
        | ω (ω a b c) y z => λ D,
          let (nb,Cb) := nm_pwc (ω b y z)   _ in
          let (nc,Cc) := nm_pwc (ω c y z)   _ in
          let (na,Ca) := nm_pwc (ω a nb nc) _ in
                          exist _ na _
    end D).
    2-3,5-7: apply Acc_inv with (1 := D); constructor; auto.
    + constructor.
    + now constructor.
    + now constructor 3 with (3 := Ca).
  Qed.
      
  (** Then we derive nm and nm_spec by projection *)

  Definition nm e D := proj1_sig (@nm_pwc e D).
    
  Fact nm_spec e D : e ⟼n @nm e D.
  Proof. apply (proj2_sig _). Qed.

End nm_pwc.

Arguments nm e D : clear implicits.

(** Inductive-Recursive domain constructors *)

(* → λ ∀ ∃ ↔ ∧ ∨ *)

Fact 𝔻nm_1 : 𝔻nm α.
Proof. constructor; inversion 1. Qed.

Fact 𝔻nm_2 y z : 𝔻nm y → 𝔻nm z → 𝔻nm (ω α y z).
Proof. constructor; inversion 1; auto. Qed.

Fact 𝔻nm_3 u v w y z Dv Dw : 𝔻nm (ω u (nm (ω v y z) Dv) (nm (ω w y z) Dw)) 
                            → 𝔻nm (ω (ω u v w) y z).
Proof.
  constructor; inversion 1; auto.
  unfold d_nm in H.
  id with H level 2; apply 𝔾nm_fun with (1 := nm_spec _); auto.
Qed.

(** Inductive-Recursive Type-bounded eliminator/induction principle *)
  
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
    + refine (HPi _ (HP2 (𝔻nm_rect _ _) (𝔻nm_rect _ _))).
      all: apply Acc_inv with (1 := D); constructor.
    + assert (𝔻nm (ω v y z)) as Da by (apply Acc_inv with (1 := D); constructor).
      assert (𝔻nm (ω w y z)) as Db by (apply Acc_inv with (1 := D); constructor).
      refine (HPi _ (HP3 (𝔻nm_rect _ Da) (𝔻nm_rect _ Db) (𝔻nm_rect _ _))).
      apply Acc_inv with (1 := D); constructor; apply nm_spec.
  Qed.

End 𝔻nm_rect.
