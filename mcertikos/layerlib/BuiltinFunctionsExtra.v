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
(** This file defines the raw abstract data and the primitives for the MBoot layer, which is also the bottom layer of memory management*)
Require Import Coqlib.
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import MemoryExtra.
Require Import EventsExtra.
Require Import GlobalenvsExtra.
Require Import MemWithData.
Require Export BuiltinFunctions.

Section WITHBASE.
   Context `{Hmem: Mem.WithDataModel}.

   Lemma volatile_store_abstract_data:
     forall {F V: Type} (ge: _ F V) chunk m b ofs v t m',
       volatile_store ge chunk m b ofs v t m' ->
       Mem.get_abstract_data m' = Mem.get_abstract_data m.
   Proof.
     inversion 1; subst; try congruence; symmetry; eauto using Mem.store_get_abstract_data.
   Qed.

   Theorem builtin_abstract_data:
     forall (b: builtin_function),
       forall {F V: Type} (ge: Genv.t F V) args (m: mem) t res m',
         builtin_call b ge args m t res m' ->
         Mem.get_abstract_data m' = Mem.get_abstract_data m.
   Proof.
     destruct b; inversion 1; subst; try congruence; eauto using volatile_store_abstract_data; symmetry; eauto using Mem.storebytes_get_abstract_data.
   Qed.
End WITHBASE.

(* The same for memory injections, here. Cf. LayerTemplate* *)
