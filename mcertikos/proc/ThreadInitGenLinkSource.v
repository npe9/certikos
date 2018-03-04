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
Require Import PThreadIntroCSource.

Require Import CompCertiKOSproof.
Require Import RealParams.
Require Import I64Layer.

Require Import PThreadIntro.

Section WITHCOMPCERTIKOS.

Context `{compcertikos_prf: CompCertiKOS}.

Context `{real_params_prf : RealParams}.



Definition PThreadInit_impl: res LAsm.module :=
  (* M_thread_free <- CompCertiKOS.transf_module (thread_free ↦ f_thread_free); *)
  M_thread_init <- CompCertiKOS.transf_module (thread_init ↦ f_thread_init);
  (** watch out parentheses here: *)
  M <- ret (
      ( (** group primitives according to the global variables that they use *)
        ((*M_thread_free ⊕*) M_thread_init)
      ) ⊕ ∅ (** for L64 and other passthrough primitives *)
    );
  _ <- eassert nil (LayerOK (〚M〛 (pthreadintro ⊕ L64) ⊕ pthreadintro ⊕ L64));
  ret M.

End WITHCOMPCERTIKOS.
