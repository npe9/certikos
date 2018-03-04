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
Require Export AuxStateDataType.
Require Import Constant.
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import XOmega.
Require Import CLemmas.

Section Real_SMSPOOL.

  Function Calculate_smsp_inner_at_j (i: Z) (j: Z) (smsp: SharedMemSTPool) : SharedMemSTPool :=
    ZMap.set i
             (ZMap.set j (SHRDValid SHRDDEAD true 0) (ZMap.get i smsp))
             smsp.

  Fixpoint Calculate_smsp_inner (i: Z) (j: nat) (smsp: SharedMemSTPool) : SharedMemSTPool := 
    match j with
      | O => Calculate_smsp_inner_at_j i 0 smsp
      | S k => Calculate_smsp_inner_at_j i (Z.of_nat (S k)) (Calculate_smsp_inner i k smsp)
    end.

  Function Calculate_smsp_at_i (i: Z) (smsp: SharedMemSTPool) : SharedMemSTPool :=
    Calculate_smsp_inner i (Z.to_nat (num_proc - 1)) smsp.

  Fixpoint Calculate_smsp (i: nat) (smsp: SharedMemSTPool) : SharedMemSTPool := 
    match i with
      | O => Calculate_smsp_at_i 0 smsp
      | S k => Calculate_smsp_at_i (Z.of_nat (S k)) (Calculate_smsp k smsp)
    end.

  Definition real_smspool (smsp: SharedMemSTPool) := Calculate_smsp (Z.to_nat (num_proc - 1)) smsp.

End Real_SMSPOOL.
