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
(*              Layers of VMM                                          *)
(*                                                                     *)
(*          Refinement proof for MALInit layer                         *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MBoot layer and MALInit layer*)
Require Import Coqlib.
Require Import XOmega.
Require Import AST.
Require Import LAsm.
Require Import AuxStateDataType.
Require Import Integers.
Require Import Constant.
Require Import AuxLemma.

Lemma size_chunk_range:
  forall chunk,
    size_chunk chunk <= 8.
Proof.
  induction chunk; simpl; omega.
Qed.

Lemma list_forall2_sep:
  forall {A B: Type} (f: A -> B -> Prop) a2 b2 a1 b1,
    list_forall2 f (a1 ++ a2) (b1 ++ b2) ->
    length a1 = length b1 ->
    list_forall2 f a1 b1 /\ list_forall2 f a2 b2.
Proof.
  induction a1; simpl; intros.
  - destruct b1. 
    + simpl in H. split; auto. constructor.
    + inv H0.
  - destruct b1.
    + inv H0.
    + inv H.
      assert (Heq: length a1 = length b1).
      { 
        simpl in H0. omega.
      }
      specialize (IHa1 _ H6 Heq).
      destruct IHa1 as [IH1 IH2].
      split; trivial.
      constructor; assumption.
Qed.

Lemma PTADDR_range:
  forall i i1 chunk,
    (i mod PgSize) <= PgSize - size_chunk chunk ->
    0 <= (PTADDR (Int.unsigned i1 / 4096) i) <= adr_max - size_chunk chunk.
Proof.
  unfold PTADDR. intros.
  specialize (Int.unsigned_range_2 i1).
  rewrite int_max. 
  intros.
  xomega.
Qed.

Lemma PTX_range:
  forall i,
    0 <= PTX (Int.unsigned i) <= 1023.
Proof.
  unfold PTX. intros.
  specialize (Z_mod_lt (Int.unsigned i/PgSize) one_k).
  omega.
Qed.

Lemma PTX_Addr_range:
  forall i i1,
    0 <= Int.unsigned i / PgSize * PgSize + PTX (Int.unsigned i1) * 4 <= adr_max - 4.
Proof.
  intros. specialize (Int.unsigned_range_2 i).
  specialize (PTX_range i1). rewrite int_max.
  intros. xomega.
Qed.

Lemma divide_chunk_PgSize:
  forall chunk,
    (align_chunk chunk | PgSize).
Proof.
  intros.
  assert (1 | 4096).
  {
    unfold Z.divide.
    exists 4096; reflexivity.
  }
  assert (2 | 4096).
  {
    unfold Z.divide.
    exists 2048; reflexivity.
  }
  assert (4 | 4096).
  {
    unfold Z.divide.
    exists 1024; reflexivity.
  }
  assert (8 | 4096).
  {
    unfold Z.divide.
    exists 512; reflexivity.
  }
  destruct chunk; simpl; assumption.
Qed.

Lemma PTADDR_divide:
  forall i i1 chunk,
    (align_chunk chunk | i mod PgSize) ->
    (align_chunk chunk | PTADDR (Int.unsigned i1 / PgSize) i).
Proof.
  unfold PTADDR. 
  intros. specialize (divide_chunk_PgSize chunk). intros.
  unfold Z.divide in *.
  destruct H as [z1 H]. rewrite H.
  destruct H0 as [z2 H0].
  set (Int.unsigned i1 / 4096) as v.
  rewrite H0. exists (v * z2 + z1).
  rewrite Z.mul_add_distr_r.
  rewrite <- Z.mul_assoc.
  reflexivity.
Qed.

Lemma PTX_Addr_divide:
  forall i i1,
    (4 | Int.unsigned i / PgSize * PgSize + PTX (Int.unsigned i1) * 4).
Proof.
  intros. apply Zdivide_plus_r.
  - apply Zdivide_mult_r. unfold Z.divide. exists 1024. reflexivity.
  - apply Zdivide_mult_r. apply Zdivide_refl.
Qed.

Lemma PTX_Addr_range':
  forall i i1, 
    0 <= Int.unsigned i / PgSize * PgSize + PTX (Int.unsigned i1) * 4 <= Int.max_unsigned.
Proof.
  intros. specialize (PTX_Addr_range i i1). intros.
  rewrite int_max. omega.
Qed.

Lemma list_forall2_memval_undef:
  forall f n b,
    length b = n ->
    list_forall2 (memval_inject f) (list_repeat n Undef) b.
Proof.
  induction n; simpl; destruct b. 
  - constructor.
  - inversion 1. 
  - inversion 1.
  - constructor.
    + constructor.
    + inv H. eapply IHn; trivial.
Qed.

Lemma list_forall2_memval_undef_chunk:
  forall f v1 v2 chunk,
    list_forall2 (memval_inject f) (list_repeat (length (encode_val chunk v1)) Undef)
                 (encode_val chunk v2).
Proof.
  intros. apply list_forall2_memval_undef.
  repeat rewrite encode_val_length.
  reflexivity.
Qed.
