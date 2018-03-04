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
Require Import ZArith.
Require Import Decision.
Open Scope Z_scope.

(** * The [xomega] tactic *)

(** Calculations involving page addresses and the like involve some
  integer divisions, which [omega] and friends cannot handle as is.
  To remedy this, we can add a preprocessing step where we prove
  inequalities which characterize the subterms which [omega] does not
  understand.

  So for instance, if the subexpression [a / b] appears, we can add
  the hypothesis [0 <= a - a / b * b < b] to the context.  Then when
  [omega] abstracts the division as a variable [q], it will
  nonetheless know that [0 <= a - q * b < b] which is equivalent to
  [q = a / b].

  The [xomega] tactic applies this principle to enable [omega] to
  solve goals involving [Z.div], [Z.modulo] and [Z.max]. *)

Module XOmega.

  (** ** Inject [nat]'s into [Z] *)

  (** Although we mostly use [Z], occasionally some goals or hypotheses
    involving [nat] show up. This is the case for instance when doing
    induction on the [Calculate_foo] family of fixpoints. The rewrite
    base below makes sure everything is expressed in terms of [Z]:
    relations on [nat] are converted into relations on [Z], and the
    resulting [Z.of_nat]'s are pushed inwards in all expressions. *)

  (** Use [Z.max] to avoid side conditions. *)
  Lemma Nat2Z_inj_to_nat_max z:
    Z.of_nat (Z.to_nat z) = Z.max 0 z.
  Proof.
    destruct (decide (0 <= z)) as [Hz | Hz].
    * rewrite Z2Nat.id by assumption.
      rewrite Zmax_right by assumption.
      reflexivity.
    * destruct z.
      - elim Hz.
        reflexivity.
      - elim Hz.
        apply Pos2Z.is_nonneg.
      - rewrite Z2Nat.inj_neg.
        rewrite Nat2Z.inj_0.
        rewrite Zmax_left by omega.
        reflexivity.
  Qed.

  Hint Rewrite <-
    Nat2Z.inj_iff
    Nat2Z.inj_compare
    : nat2z.

  Hint Rewrite ->
    Nat2Z.inj_le
    Nat2Z.inj_lt
    Nat2Z.inj_ge
    Nat2Z.inj_gt
    Nat2Z.inj_0
    Nat2Z.inj_succ
    Nat2Z.inj_abs_nat
    Nat2Z.inj_add
    Nat2Z.inj_mul
    Nat2Z.inj_sub_max
    Nat2Z.inj_pred_max
    Nat2Z.inj_min
    Nat2Z.inj_max
    Nat2Z_inj_to_nat_max
    : nat2z.

  Ltac nat2z :=
    autorewrite with nat2z in *.

  (** ** Characterize [Z.div] and [Z.max] by inequalities *)

  (** Ensure that no hypothesis of type [P] already exists, then use
    the provided tactic to add one. *)
  Ltac assert_new P tac :=
    match goal with
      | H_already_there : P |- _ => fail 1
      | _ => assert P by tac
    end.

  (** Characterize [Z.div a b]. *)

  Notation DIVSPEC a b :=
    ((b < 0 /\ b < a - a / b * b <= 0) \/
     (b = 0 /\ a / b = 0) \/
     (b > 0 /\ 0 <= a - a / b * b < b))%Z.

  Lemma specify_division a b:
    DIVSPEC a b.
  Proof with try omega.
    destruct (decide (b < 0)) as [Hbn | Hbn]; [left | right;
    destruct (decide (b = 0)) as [Hbz | Hbz]; [left | right]];
    split...
    * rewrite <- Zmod_eq_full...
      apply Z.mod_neg_bound...
    * subst.
      apply Zdiv_0_r...
    * rewrite <- Zmod_eq_full...
      apply Z.mod_pos_bound...
  Qed.

  Ltac specify_division a b :=
    let tac := (apply specify_division) in
    assert_new (DIVSPEC a b) tac.

  (** Characterize [Z.modulo a b]. *)

  Notation MODSPEC a b :=
    ((b  = 0 /\ a mod b = 0) \/
     (b <> 0 /\ a mod b = a - a / b * b))%Z.

  Lemma specify_modulo a b:
    MODSPEC a b.
  Proof with try omega.
    destruct (decide (b = 0)); [left | right];
    split...
    * subst; apply Zmod_0_r.
    * apply Zmod_eq_full...
  Qed.

  Ltac specify_modulo a b :=
    let tac := (apply specify_modulo) in
    assert_new (MODSPEC a b) tac.

  (** Characterize [Z.max a b]. *)

  Notation MAXSPEC a b :=
    ((a >= b /\ Z.max a b = a) \/
     (a <  b /\ Z.max a b = b))%Z.

  Lemma specify_max a b:
    MAXSPEC a b.
  Proof.
    apply Zmax_spec.
  Qed.

  Ltac specify_max a b :=
    let tac := (apply specify_max) in
    assert_new (MAXSPEC a b) tac.

  (** Now look in the hypotheses and goal for occurences of division and
    max, then instantiate the corresponding hypotheses. *)

  Ltac instantiate_extra_hypotheses_for P :=
    match P with
      | context [Z.div ?a ?b] => specify_division a b
      | context [Z.modulo ?a ?b] => specify_modulo a b
      | context [Z.max ?a ?b] => specify_max a b
    end;
    (* If we found at least one, go on. *)
    try instantiate_extra_hypotheses_for P.

  Ltac instantiate_extra_hypotheses :=
    repeat
      match goal with
        | H: ?P |- _ => instantiate_extra_hypotheses_for P
        | |- ?G => instantiate_extra_hypotheses_for G
      end.

  (** ** Assembling the pieces *)

  Ltac omegify :=
    nat2z;
    instantiate_extra_hypotheses.

End XOmega.

(** Random hint: the extra hypotheses are a little hairy, so if you
  use [omegify] manually on its own, you may want to import the
  [XOmega] module to get the [FOOSPEC] notations. *)

Ltac xomega :=
  XOmega.omegify;
  omega.

(** These should work as well if we ever need them. *)

(*
Require Import Psatz.
Ltac xlia := XOmega.omegify; lia.
Ltac xnia := XOmega.omegify; nia.
*)

(** Finally, a quick test. *)

Goal
  forall (x: Z) (y: nat),
    (y >= max 2 17)%nat ->
    (~ Z.to_nat x < y)%nat ->
    - x * 5 / - 4 > x + x / 0.
Proof.
  intros.
  xomega.
Qed.
