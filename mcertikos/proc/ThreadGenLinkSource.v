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
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatClightSem.
Require Import LAsmModuleSemDef.
Require Import CompCertiKOS.
Require Import GlobIdent.
Require Import CDataTypes.
Require Import ThreadGenAsmSource.


Definition PThread_impl: res LAsm.module :=
  (** watch out parentheses here: *)
  ret (
      ( (** group primitives according to the global variables that they use *)
        ((thread_yield ↦ threadyield_function) ⊕ (thread_sleep ↦ threadsleep_function))
      ) ⊕ ∅ (** for L64 and other passthrough primitives *)
    ).