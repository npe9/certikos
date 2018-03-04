(* *********************************************************************)
(*                                                                     *)
(*            The CertiKOS Certified Kit Operating System              *)
(*                                                                     *)
(*                   The FLINT Group, Yale University                  *)
(*                                                                     *)
(*  Copyright The FLINT Group, Yale University.  All rights reserved.  *)
(*  This file is distributed under the terms of the Yale University    *)
(*  Non-Commercial License Agreement.                                  *)
(*                                                                     *)
(* *********************************************************************)
Require Import Coq.ZArith.ZArith.
Require Import Coq.PArith.PArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Open Scope Z_scope.

(** MathClasses-style "Decision" class. *)

Class Decision (P: Prop) := decide: {P} + {~P}.
Arguments decide P {_}.

Definition isTrue P `{Decision P} :=
  if decide P then true else false.

Definition isTrue_correct P `{Decision P}:
  isTrue P = true -> P.
Proof.
  unfold isTrue.
  destruct (decide P).
  tauto.
  discriminate.
Qed.

Ltac decision :=
  eapply isTrue_correct;
  reflexivity.

Ltac obviously H P :=
  assert (H: P) by decision.

Ltac ensure P :=
  let H := fresh "H" in
  obviously H P; clear H.


(** * Instances *)

Instance decide_Zeq (m n: Z): Decision (m = n) := {decide := Z_eq_dec m n}.
Instance decide_Zle (m n: Z): Decision (m <= n) := {decide := Z_le_dec m n}.
Instance decide_Zlt (m n: Z): Decision (m < n) := {decide := Z_lt_dec m n}.
Instance decide_Zge (m n: Z): Decision (m >= n) := {decide := Z_ge_dec m n}.
Instance decide_Zgt (m n: Z): Decision (m > n) := {decide := Z_gt_dec m n}.
Instance decide_nateq m n: Decision (m = n) := { decide := eq_nat_dec m n }.
Instance decide_natle m n: Decision (m <= n)%nat := { decide := le_dec m n }.
Instance decide_natlt m n: Decision (m < n)%nat := { decide := lt_dec m n }.
Instance decide_poseq (m n: positive): Decision (m = n) := Pos.eq_dec m n.
Instance decide_booleq b1 b2: Decision (b1 = b2) := Bool.bool_dec b1 b2.
Instance decide_Neq (m n: N): Decision (m = n) := {decide := N.eq_dec m n}.

Instance decide_posle (m n: positive): Decision (Pos.le m n).
Proof.
  destruct (Pos.leb m n) eqn:leb.
  - left; apply Pos.leb_le, leb.
  - right; rewrite <- Pos.leb_le, leb; discriminate.
Defined.

Instance and_dec A B: Decision A -> Decision B -> Decision (A /\ B) := {
  decide :=
    match (decide A) with
      | left HA =>
          match (decide B) with
            | left HB => left (conj HA HB)
            | right HnB => right (fun H => HnB (proj2 H))
          end
      | right HnA => right (fun H => HnA (proj1 H))
    end
}.

Instance or_dec A B: Decision A -> Decision B -> Decision (A \/ B) := {
  decide :=
    match (decide A) with
      | left HA => left (or_introl HA)
      | right HnA =>
        match (decide B) with
          | left HB => left (or_intror HB)
          | right HnB => right (fun HAB => match HAB with
                                             | or_introl HA => HnA HA
                                             | or_intror HB => HnB HB
                                           end)
        end
    end
}.

Instance impl_dec P Q `(Pdec: Decision P) `(Qdec: Decision Q): Decision (P->Q) :=
  {
    decide :=
      match Qdec with
        | left HQ => left (fun _ => HQ)
        | right HnQ =>
          match Pdec with
            | left HP => right _
            | right HnP => left _
          end
      end
  }.
Proof.
  * abstract tauto.
  * abstract tauto.
Defined.

Instance not_dec P `(Pdec: Decision P): Decision (~P) :=
  {
    decide :=
      match Pdec with
        | left _ => right _
        | right _ => left _
      end
  }.
Proof.
  * abstract tauto.
  * abstract tauto.
Defined.

Program Instance decide_none {A} (a: option A): Decision (a = None) := {
  decide :=
    match a with
      | Some _ => right _
      | None => left _
    end
}.

Instance decide_option_eq {A}:
  (forall (x y : A), Decision (x = y)) ->
  (forall (x y : option A), Decision (x = y)) :=
  fun H x y =>
    match x, y with
      | Some x, Some y =>
        match decide (x = y) with
          | left H => left (f_equal _ H)
          | right H => right _
        end
      | None, None =>
        left eq_refl
      | _, _ =>
        right _
    end.
Proof.
  * abstract (injection; eauto).
  * abstract discriminate.
  * abstract discriminate.
Defined.

Section DECIDE_PROD.
  Context A `{Adec: forall x y: A, Decision (x = y)}.
  Context B `{Bdec: forall x y: B, Decision (x = y)}.

  Global Instance decide_eq_pair: forall (x y: A * B), Decision (x = y).
  Proof.
    intros [x1 x2] [y1 y2].
    destruct (decide (x1 = y1)).
    destruct (decide (x2 = y2)).
    left; congruence.
    right; intro H; inversion H; now auto.
    right; intro H; inversion H; now auto.
  Defined.
End DECIDE_PROD.

(** * Decision procedures for lists *)

Instance decide_In {A}:
  (forall (x y: A), Decision (x = y)) ->
  (forall (a: A) (l: list A), Decision (In a l)) :=
    @In_dec A.

Instance decide_Forall {A} (P: A -> Prop):
  (forall a, Decision (P a)) ->
  (forall l, Decision (Forall P l)).
Proof.
  intros HP l.
  induction l.
  * left.
    constructor.
  * destruct (decide (Forall P l)) as [Hl | Hl].
    destruct (decide (P a)) as [Ha | Ha].
    + left.
      constructor;
      assumption.
    + right.
      inversion 1.
      tauto.
    + right.
      inversion 1.
      tauto.
Defined.

(** * Decision procedures from [compare] *)

(** This takes care of many orders, which are defined as, say,
  [le x y := compare x y <> Gt]. *)

Instance comparison_eq_dec (x y: comparison): Decision (x = y).
Proof.
  red.
  decide equality.
Defined.

Program Instance comparison_ne_dec (x y: comparison): Decision (x <> y) :=
  match decide (x = y) with
    | left Hne => right _
    | right Hnne => left _
  end.

(** Decision and equivalence *)

Local Instance decide_rewrite P Q (Heq: P <-> Q) `(Decision P): Decision Q :=
  match decide P with
    | left _ => left _
    | right _ => right _
  end.
Proof.
  abstract tauto.
  abstract tauto.
Defined.

(** Decision and discriminable cases *)

Theorem decide_discr {A}
        (Q1 Q2 P: A -> Prop)
        (discr: forall i, {Q1 i} + {Q2 i})
        (dec_1: Decision (forall i, Q1 i -> P i))
        (dec_2: Decision (forall i, Q2 i -> P i)):
  Decision (forall i, P i).
Proof.
  unfold Decision in *.
  firstorder.
Defined.
