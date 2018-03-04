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
(* *********************************************************************)
(*                                                                     *)
(*       Lemmas about the Clight used in various C level proofs        *)
(*                                                                     *)
(*                 Developed by Xiongnan (Newman) Wu                   *)
(*                                                                     *)
(*                         Yale University                             *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import EventsX.
Require Import Clight.
Require Import Cop.
Require Import Ctypes.
Require Import ZArith.

 Hint Unfold Int.max_unsigned.
 Hint Unfold Int.modulus.
 Hint Unfold Int.half_modulus.
 Hint Unfold Int64.max_unsigned.
 Hint Unfold Int64.modulus.
 Hint Unfold Int64.half_modulus.

 Open Scope Z_scope.

 (** * Frequently used lemmas in tactics. *)

 Lemma zadd_rm_head: forall n p q, p = q -> n + p = n + q.
 Proof.
   intros.
   rewrite H.
   trivial.
 Qed.

 Lemma zadd_rm_tail: forall n p q, p = q -> p + n = q + n.
 Proof.
   intros.
   rewrite H.
   trivial.
 Qed.

 Lemma zdiv_range_le_lt : forall a b c x: Z, a <= 0 -> b > 0 -> c > 0 -> a <= x < b -> a <= x/ c < b.
 Proof.
   intros.
   destruct H2.
   split.
   apply Zdiv_le_lower_bound.
   omega.
   assert(a * c <= a).
   assert(- a * c >= - a).
   rewrite <- Zmult_1_r.
   assert(c >= 1) by omega.
   apply Zmult_ge_compat_l.
   omega.
   omega.
   rewrite Zopp_mult_distr_l_reverse in H4.
   omega.
   omega.
   apply Zdiv_lt_upper_bound.
   omega.
   assert(b <= b * c).
   rewrite <- Zmult_1_r at 1.
   assert(1 <= c) by omega.
   apply Zmult_le_compat_l.
   omega.
   omega.
   omega.
 Qed.

 Lemma zdiv_range_le_le : forall a b c x: Z, a <= 0 -> b > 0 -> c > 0 -> a <= x <= b -> a <= x/ c <= b.
 Proof.
   intros.
   destruct H2.
   split.
   apply Zdiv_le_lower_bound.
   omega.
   assert(a * c <= a).
   assert(- a * c >= - a).
   rewrite <- Zmult_1_r.
   assert(c >= 1) by omega.
   apply Zmult_ge_compat_l.
   omega.
   omega.
   rewrite Zopp_mult_distr_l_reverse in H4.
   omega.
   omega.
   apply Zdiv_le_upper_bound.
   omega.
   assert(b <= b * c).
   rewrite <- Zmult_1_r at 1.
   assert(1 <= c) by omega.
   apply Zmult_le_compat_l.
   omega.
   omega.
   omega.
 Qed.

 Lemma max_unsigned_gt0: Int.max_unsigned > 0.
 Proof.
   repeat autounfold.
   simpl.
   omega.
 Qed.

 Lemma max_unsigned_val: Int.max_unsigned  = 4294967295.
 Proof.
   repeat autounfold; reflexivity.
 Qed.

 Lemma unsigned_inj : forall a b, Int.unsigned a = Int.unsigned b -> a = b.
 Proof.
   intros. rewrite <- (Int.repr_unsigned a).
   rewrite <- (Int.repr_unsigned b).
   f_equal.
   trivial.
 Qed.

 Lemma max_unsigned64_gt0: Int64.max_unsigned > 0.
 Proof.
   repeat autounfold.
   simpl.
   omega.
 Qed.

 Lemma max_unsigned64_val: Int64.max_unsigned  = 18446744073709551615.
 Proof.
   repeat autounfold; reflexivity.
 Qed.

 Lemma unsigned64_inj : forall a b, Int64.unsigned a = Int64.unsigned b -> a = b.
 Proof.
   intros. rewrite <- (Int64.repr_unsigned a).
   rewrite <- (Int64.repr_unsigned b).
   f_equal.
   trivial.
 Qed.

 Lemma minus1lt: forall i:Z, i - 1 < i.
 Proof.
   intro.
   omega.
 Qed.

 Lemma Z_land_range_lo: forall x y, 0 <= x -> 0 <= Z.land x y.
 Proof.
   intros.
   rewrite Z.land_nonneg.
   left.
   assumption.
 Qed. 

 Lemma Z_land_range_lo_r: forall x y, 0 <= y -> 0 <= Z.land x y.
 Proof.
   intros.
   rewrite Z.land_nonneg.
   right.
   assumption.
 Qed.

 Lemma Z_land_range_hi: forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned -> Z.land x y <= Int.max_unsigned.
 Proof.
   rewrite max_unsigned_val.
   intros.
   assert(Z.land x y < 4294967296).
     apply Z.log2_lt_cancel.
     assert(Z.log2 (Z.land x y) <= Z.min (Z.log2 x) (Z.log2 y)).
       apply Z.log2_land.
       omega.
       omega.
     rewrite Zmin_spec in H1.
     destruct (zlt (Z.log2 x) (Z.log2 y)).
     assert(Z.log2 x <= Z.log2 4294967295).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
     assert(Z.log2 y <= Z.log2 4294967295).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
   omega.
 Qed.   

 Lemma Z_land_range: forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned -> 0 <= Z.land x y <= Int.max_unsigned.
 Proof.
   split.
   apply Z_land_range_lo; omega.
   apply Z_land_range_hi; omega.
 Qed.

 Lemma Z64_land_range_hi: forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned -> Z.land x y <= Int64.max_unsigned.
 Proof.
   rewrite max_unsigned64_val.
   intros.
   assert (Z.land x y < 18446744073709551616).
     apply Z.log2_lt_cancel.
     assert(Z.log2 (Z.land x y) <= Z.min (Z.log2 x) (Z.log2 y)).
       apply Z.log2_land.
       omega.
       omega.
     rewrite Zmin_spec in H1.
     destruct (zlt (Z.log2 x) (Z.log2 y)).
     assert(Z.log2 x <= Z.log2 18446744073709551615).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
     assert(Z.log2 y <= Z.log2 18446744073709551615).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
   omega.
 Qed.

 Lemma Z64_land_range: forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned -> 0 <= Z.land x y <= Int64.max_unsigned.
 Proof.
   split.
   apply Z_land_range_lo; omega.
   apply Z64_land_range_hi; omega.
 Qed.

 Lemma Z_lor_range_lo: forall x y, 0 <= x -> 0 <= y -> 0 <= Z.lor x y.
 Proof.
   intros.
   apply Z.lor_nonneg; auto.
 Qed.

 Lemma Z_lor_range_hi: forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned -> Z.lor x y <= Int.max_unsigned.
 Proof.
   rewrite max_unsigned_val; simpl.
   intros.
   assert(Z.lor x y < 4294967296).
     apply Z.log2_lt_cancel.
     assert(Z.log2 (Z.lor x y) = Z.max (Z.log2 x) (Z.log2 y)).
       apply Z.log2_lor.
       omega.
       omega.
     rewrite H1.
     rewrite Zmax_spec in *.
     destruct (zlt (Z.log2 y) (Z.log2 x)).
     assert(Z.log2 x <= Z.log2 4294967295).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
     assert(Z.log2 y <= Z.log2 4294967295).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
   omega.
 Qed.

 Lemma Z_lor_range: forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned -> 0 <= Z.lor x y <= Int.max_unsigned.
 Proof.
   intros.
   split.
   apply Z_lor_range_lo; omega.
   apply Z_lor_range_hi; omega.
 Qed.

 Lemma Z64_lor_range_hi: forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned -> Z.lor x y <= Int64.max_unsigned.
 Proof.
   rewrite max_unsigned64_val; simpl.
   intros.
   assert(Z.lor x y < 18446744073709551616).
     apply Z.log2_lt_cancel.
     assert(Z.log2 (Z.lor x y) = Z.max (Z.log2 x) (Z.log2 y)).
       apply Z.log2_lor.
       omega.
       omega.
     rewrite H1.
     rewrite Zmax_spec in *.
     destruct (zlt (Z.log2 y) (Z.log2 x)).
     assert(Z.log2 x <= Z.log2 18446744073709551615).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
     assert(Z.log2 y <= Z.log2 18446744073709551615).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
   omega.
 Qed.

 Lemma Z64_lor_range: forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned -> 0 <= Z.lor x y <= Int64.max_unsigned.
 Proof.
   split.
   apply Z_lor_range_lo; omega.
   apply Z64_lor_range_hi; omega.
 Qed.

 Lemma Z_lxor_range :
   forall x y,
     0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
     0 <= Z.lxor x y <= Int.max_unsigned.
 Proof.
   rewrite max_unsigned_val; simpl.
   intros.
   split.
   rewrite Z.lxor_nonneg.
   split; omega.
   assert(Z.lxor x y < 4294967296).
     apply Z.log2_lt_cancel.
     assert(Z.log2 (Z.lxor x y) <= Z.max (Z.log2 x) (Z.log2 y)).
       apply Z.log2_lxor.
       omega.
       omega.
     apply Z.le_lt_trans with (m := Z.max (Z.log2 x) (Z.log2 y)); auto.
     rewrite Zmax_spec in *.
     destruct (zlt (Z.log2 y) (Z.log2 x)).
     assert(Z.log2 x <= Z.log2 4294967295).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
     assert(Z.log2 y <= Z.log2 4294967295).
       apply Z.log2_le_mono.
       omega.
     simpl in *.
     omega.
   omega.
 Qed.

 Lemma Z_shiftl_16_range :
   forall x,
     0 <= x < 65536 -> 0 <= Z.shiftl x 16 <= Int.max_unsigned.
 Proof.
   unfold Int.max_unsigned. simpl (Int.modulus - 1).
   intros.
   split.
   rewrite Z.shiftl_nonneg. omega.

   assert (Z.shiftl x 16 < 4294967296).
     case_eq (zeq x 0); intros; subst.

     (* x = 0 *)
     simpl. omega.

     (* x <> 0 *)
     apply Z.log2_lt_cancel.
     rewrite Z.log2_shiftl; try omega.

     assert (Z.log2 x <= Z.log2 65535).
       apply Z.log2_le_mono. omega.
     simpl in *. omega.

   omega.
 Qed.

 Lemma Z_shiftl_32_range :
   forall x,
     0 <= x <= Int.max_unsigned -> 0 <= Z.shiftl x 32 <= Int64.max_unsigned.
 Proof.
   unfold Int.max_unsigned, Int64.max_unsigned.
   simpl (Int.modulus - 1); simpl (Int64.modulus - 1).
   intros x H; simpl in H.
   split.
   - (*"0 <= (x << 32)"*)
     rewrite Z.shiftl_nonneg; omega.
   - (*"(x << 32) <= Int64.max_unsigned"*)
     assert (Hx32: Z.shiftl x 32 < 18446744073709551616).
     + (*"assertion"*)
       case_eq (zeq x 0); intros; subst.
       * (*"x == 0"*)
         simpl. omega.
       *  (*"x <> 0"*)
         apply Z.log2_lt_cancel.
         rewrite Z.log2_shiftl; try omega.
         assert (Z.log2 x <= Z.log2 4294967295).
         {
           (*"assertion"*)
           apply Z.log2_le_mono; omega.
         }
         simpl in *; omega.
     + omega.
 Qed.


  (** * Hints for autorewrite *)

  Lemma unsigned_zero: Int.unsigned Int.zero = 0.
  Proof. reflexivity. Qed.

  Lemma unsigned_one: Int.unsigned Int.one = 1.
  Proof. reflexivity. Qed.

  Lemma eq_one_zero: Int.eq Int.one Int.zero = false.
  Proof. reflexivity. Qed.

  Lemma eq_zero_zero: Int.eq Int.zero Int.zero = true.
  Proof. reflexivity. Qed.

  Lemma negb_true: negb true = false.
  Proof. reflexivity. Qed.

  Lemma negb_false: negb false = true.
  Proof. reflexivity. Qed.

  Lemma repr_zero: Int.repr 0 = Int.zero.
  Proof. reflexivity. Qed.

  Lemma repr_one: Int.repr 1 = Int.one.
  Proof. reflexivity. Qed.

  Lemma and_zero_zero: Z.land 0 0 = 0.
  Proof. reflexivity. Qed.

  Lemma and_one_zero: Z.land 1 0 = 0.
  Proof. reflexivity. Qed.

  Lemma and_zero_one: Z.land 0 1 = 0.
  Proof. reflexivity. Qed.

  Lemma and_one_one: Z.land 1 1 = 1.
  Proof. reflexivity. Qed.

  Lemma or_zero_zero: Z.lor 0 0 = 0.
  Proof. reflexivity. Qed.

  Lemma or_one_zero: Z.lor 1 0 = 1.
  Proof. reflexivity. Qed.

  Lemma or_zero_one: Z.lor 0 1 = 1.
  Proof. reflexivity. Qed.

  Lemma or_one_one: Z.lor 1 1 = 1.
  Proof. reflexivity. Qed.

  Hint Rewrite unsigned_zero unsigned_one eq_one_zero eq_zero_zero negb_true negb_false repr_zero repr_one: arith.
  Hint Rewrite and_zero_zero and_zero_one and_one_zero and_one_one or_zero_zero or_zero_one or_one_zero or_one_one : arith.


  Lemma list_disjoint_nil: forall (A: Type) (l1: list A), list_disjoint l1 nil.
  Proof.
    intros.
    unfold list_disjoint.
    simpl.
    intros.
    contradiction.
  Qed.


  (** * Common useful tactics *)

  Ltac Caseeq H := generalize H; apply or_ind; clear H.

  Require String. Open Scope string_scope.

  Ltac move_to_top x :=
    match reverse goal with
      | H : _ |- _ => try move x after H
    end.

  Tactic Notation "assert_eq" ident(x) constr(v) :=
    let H := fresh in
    assert (x = v) as H by reflexivity;
      clear H.

  Tactic Notation "Case_aux" ident(x) constr(name) :=
    first [
        set (x := name); move_to_top x
      | assert_eq x name; move_to_top x
      | fail 1 "because we are working on a different case" ].

  Tactic Notation "Case" constr(name) := Case_aux Case name.
  Tactic Notation "SCase" constr(name) := Case_aux SCase name.
  Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
  Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
  Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
  Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
  Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
  Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.