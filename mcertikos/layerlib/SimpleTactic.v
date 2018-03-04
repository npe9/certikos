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
Require Import AsmExtra.

Ltac my_do2 tac:= do 2 tac.
Ltac my_do3 tac:= do 3 tac.
Ltac my_do4 tac:= do 4 tac.
Ltac my_do5 tac:= do 5 tac.
Ltac my_do6 tac:= do 6 tac.
Ltac my_do7 tac:= do 7 tac.
Ltac my_do8 tac:= do 8 tac.
Ltac my_do9 tac:= do 9 tac.
Ltac my_do10 tac:= do 10 tac.
Ltac my_do11 tac:= do 11 tac.
Ltac my_do12 tac:= do 12 tac.
Ltac my_do13 tac:= do 13 tac.
Ltac my_do14 tac:= do 14 tac.
Ltac my_do15 tac:= do 15 tac.
Ltac my_do16 tac:= do 16 tac.
Ltac my_do17 tac:= do 17 tac.

Ltac reg_destruct :=
  repeat match goal with
           | [ |- context[Pregmap.elt_eq ?a ?b]] 
             => destruct (Pregmap.elt_eq a b); try constructor
         end.
