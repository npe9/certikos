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
(*              Tactics                                                *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the tactic for refinement proof between layers*)

Require Import Coqlib.
Require Import Integers.

Definition Z64ofwords (i1 i2: Z) :=
  (Z.lor (Z.shiftl i1 32) i2).

Definition Z64_lo_int (i: Z) : int :=
  Int.repr i.

Definition Z64_hi_int (i: Z) : int :=
  Int.repr (Z.shiftr i 32).
