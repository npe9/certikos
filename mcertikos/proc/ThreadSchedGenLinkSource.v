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
Require Import PCurIDCSource.
Require Import ThreadSchedGenAsmSource.

Require Import CompCertiKOSproof.
Require Import RealParams.
Require Import I64Layer.

Require Import PCurID.

Section WITHCOMPCERTIKOS.

Context `{compcertikos_prf: CompCertiKOS}.

Context `{real_params_prf : RealParams}.



Definition PThreadSched_impl: res LAsm.module :=
  (*
  M_thread_kill <- CompCertiKOS.transf_module (thread_kill ↦ f_thread_kill);
  *)
  M_thread_spawn <- CompCertiKOS.transf_module (thread_spawn ↦ f_thread_spawn);
  M_thread_wakeup <- CompCertiKOS.transf_module (thread_wakeup ↦ f_thread_wakeup);
  M_sched_init <- CompCertiKOS.transf_module (sched_init ↦ f_sched_init);
  (** watch out parentheses here: *)
  M <- ret (
      ( (** group primitives according to the global variables that they use *)
        ((*M_thread_kill ⊕*) M_thread_spawn ⊕ M_thread_wakeup ⊕ M_sched_init)
        ⊕ (thread_sched ↦ threadsched_function)
      ) ⊕ ∅ (** for L64 and other passthrough primitives *)
    );
  _ <- eassert nil (LayerOK (〚M〛 (pcurid ⊕ L64) ⊕ pcurid ⊕ L64));
  ret M.

End WITHCOMPCERTIKOS.
