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
Require Import PQueueIntroCSource.

Require Import CompCertiKOSproof.
Require Import RealParams.
Require Import I64Layer.

Require Import PQueueIntro.

Section WITHCOMPCERTIKOS.
Context `{compcertikos_prf: CompCertiKOS}.
Context `{real_params_prf : RealParams}.

Definition PQueueInit_impl: res LAsm.module :=
  M_enqueue <- CompCertiKOS.transf_module (enqueue ↦ f_enqueue);
  M_dequeue <- CompCertiKOS.transf_module (dequeue ↦ f_dequeue);
  M_queue_rmv <- CompCertiKOS.transf_module (queue_rmv ↦ f_queue_rmv);
  M_tdqueue_init <- CompCertiKOS.transf_module (tdqueue_init ↦ f_tdqueue_init);
  M <- ret ((M_enqueue ⊕ M_dequeue ⊕ M_queue_rmv ⊕ M_tdqueue_init) ⊕ ∅);
  _ <- eassert nil (LayerOK (〚M〛 (pqueueintro ⊕ L64) ⊕ pqueueintro ⊕ L64));
  ret M.

End WITHCOMPCERTIKOS.
