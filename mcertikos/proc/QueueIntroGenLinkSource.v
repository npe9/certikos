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
Require Import PThreadInitCSource.

Require Import CompCertiKOSproof.
Require Import RealParams.
Require Import I64Layer.

Require Import PThreadInit.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

Definition PQueueIntro_impl: res LAsm.module :=
  M1 <- ( M_get_head <- CompCertiKOS.transf_module (get_head ↦ f_get_head);
          M_get_tail <- CompCertiKOS.transf_module (get_tail ↦ f_get_tail);
          M_set_head <- CompCertiKOS.transf_module (set_head ↦ f_set_head);
          M_set_tail <- CompCertiKOS.transf_module (set_tail ↦ f_set_tail);
          M_tdq_init  <- CompCertiKOS.transf_module (tdq_init ↦ f_tdq_init);
          _ <- eassert nil (LayerOK ((〚M_get_head ⊕ M_get_tail ⊕ M_set_head ⊕ M_set_tail ⊕ M_tdq_init〛 
                                        ((pthreadinit ⊕ L64) ⊕ TDQPool_LOC ↦ tdqpool_loc_type)
                                        ⊕ (pthreadinit ⊕ L64) ⊕ TDQPool_LOC ↦ tdqpool_loc_type)));
          ret ((M_get_head ⊕ M_get_tail ⊕ M_set_head ⊕ M_set_tail ⊕ M_tdq_init) ⊕ TDQPool_LOC ↦ tdqpool_loc_type));
    M <- ret (M1 ⊕ ∅ );
    _ <- eassert nil (LayerOK (〚M 〛 (pthreadinit ⊕ L64) ⊕ pthreadinit ⊕ L64));
    (** watch out parentheses here: *)
    ret (
        (** group primitives according to the global variables that they use *)
        M(** for L64 and other passthrough primitives *)
      ).

End WITHCOMPCERTIKOS.