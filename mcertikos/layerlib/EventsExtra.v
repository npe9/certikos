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
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*          Jérémie Koenig <jk@jk.fr.eu.org>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide to the extension to the [Compcert] events*)
Require Import Coqlib.
Require Intv.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import ASTExtra.
Require Import MemoryExtra.
Require Import GlobalenvsExtra.
Require Export Events.

Ltac xauto :=
  auto;
  try congruence.

Ltac inv_one_val_inject :=
  match goal with
  | H:Val.lessdef_list _ _ |- _ => inv H
  | H:Val.lessdef _ _ |- _ => inv H
  | H:val_list_inject _ _ _ |- _ => inv H
  | H:val_inject _ _ _ |- _ => inv H
  end; xauto.

Ltac inv_one_val_inject_one :=
  inv_one_val_inject; [ idtac ].

Ltac inv_val_inject' :=
  repeat inv_one_val_inject_one;
  try (now inv_one_val_inject).

Ltac inv_val_inject :=
  inv_val_inject';
  repeat match goal with
    | [HFB: ?f ?b' = Some (?b', 0), HFB': ?f ?b' = Some (?b2, ?delta) |- _ ] =>
      rewrite HFB in HFB'; inv HFB'; rewrite Int.add_zero in *
  end.
