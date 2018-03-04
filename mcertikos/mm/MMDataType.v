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
(*              Definitions of MMDataType                              *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Constant.
Require Import Maps.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Import AsmX.
Require Import CommonTactic.

(** *Data types for abstract data*)

Section MM.

  Inductive DeviceAction :=
  | OUT (n: Z).

  Definition DeviceOutput := ZMap.t (list DeviceAction).

  Definition DeviceOutput_update (d: DeviceOutput) (from to: Z) (a: DeviceAction): DeviceOutput :=
    ZMap.set to (a :: (ZMap.get to d)) d.

End MM.    
