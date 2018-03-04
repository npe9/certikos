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
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import RealParams.
Require Import CommonTactic.
Require Import AuxLemma.

(** * Example instance for [RealParams] *)

Instance sample_realparams_ops: RealParamsOps :=
  {
    real_mm := ZMap.set 0 (MMValid 0 1073745920 MMUsable) (ZMap.init MMUndef);
    real_size := 1;
    real_vmxinfo := ZMap.init 0
  }.

Global Instance sample_realparams: RealParams.
Proof.
  constructor.
  - (*MM_valid real_mm real_size*)
    unfold MM_valid, MM_range.
    intros. simpl in *.
    destruct (zeq i 0); subst.
    + rewrite ZMap.gss.
      refine_split'; try reflexivity.
      omega.
    + omega.
  - (*MM_correct real_mm real_size*)
    unfold MM_correct. 
    intros. simpl in *.
    destruct (zeq i 0); subst.
    + destruct (zeq j 0); subst.
      * rewrite ZMap.gss in *.
        inv H1. inv H2.
        constructor.
      * omega.
    + omega.
  - (*MM_kern real_mm real_size *)
    unfold MM_kern, MM_kern_range.
    intros.
    unfold MM_kern_valid. simpl.
    exists 0, 0, 1073745920.
    split. omega.
    split. rewrite ZMap.gss. reflexivity.
    split. omega.
    omega.
  - (*0 < real_size <= Integers.Int.max_unsigned*)
    simpl. rewrite int_max.
    omega.
  - intros.
    simpl.
    rewrite ZMap.gi.
    unfold Integers.Int.max_unsigned.
    simpl.
    omega.
Qed.

