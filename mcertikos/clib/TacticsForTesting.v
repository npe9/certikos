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

Ltac d1 t := do 1 t.
Ltac d2 t := do 2 t.
Ltac d3 t := do 3 t.
Ltac d4 t := do 4 t.
Ltac d5 t := do 5 t.
Ltac d6 t := do 6 t.
Ltac d7 t := do 7 t.
Ltac d8 t := do 8 t.
Ltac d9 t := do 9 t.
Ltac d10 t := do 10 t.
Ltac d11 t := do 11 t.
Ltac d12 t := do 12 t.
Ltac d13 t := do 13 t.
Ltac d14 t := do 14 t.
Ltac d15 t := do 15 t.

Require Import Coqlib.
Require Import VCGen.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.  
Require Import liblayers.compat.CompatClightSem.
Require Import liblayers.compcertx.MakeProgram.
Require Import Globalenvs.
Require Import CompatClightSem.
Require Export CLemmas.
Require Import Integers.

Ltac fbigsteptest l m := exploit l; simpl; destruct m; ptreesolve; eauto; autorewrite with lift_simpl lens_simpl; repeat progress (unfold lift, set; simpl); eauto; repeat progress (try rewrite Int.unsigned_repr); repeat progress discharge_unsigned_range; simpl in *; 
  repeat progress match goal with
                    | [H: ?x = _ |- context[?x]] => try rewrite H
  end.