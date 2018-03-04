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
Require Import PIPCCSource.
Require Import UCtxtIntroGenAsmSource.

Require Import CompCertiKOSproof.
Require Import RealParams.
Require Import I64Layer.

Require Import PIPC.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Definition PUCtxtIntro_impl: res LAsm.module :=
    M1 <- (M_uctx_get <- CompCertiKOS.transf_module (uctx_get ↦ f_uctx_get);
           M_uctx_set <- CompCertiKOS.transf_module (uctx_set ↦ f_uctx_set);
           M_uctx_set_eip <- CompCertiKOS.transf_module (uctx_set_eip ↦ f_uctx_set_eip);
           M_save_uctx <- CompCertiKOS.transf_module (save_uctx ↦ f_save_uctx);
           _ <- eassert nil (LayerOK ((〚M_uctx_get ⊕ M_uctx_set ⊕ M_uctx_set_eip ⊕ M_save_uctx〛 
                                         ((pipc ⊕ L64) ⊕ UCTX_LOC ↦ uctx_loc_type)
                                         ⊕ (pipc ⊕ L64) ⊕ UCTX_LOC ↦ uctx_loc_type)));
           ret ((M_uctx_get ⊕ M_uctx_set ⊕ M_uctx_set_eip ⊕ M_save_uctx) ⊕ UCTX_LOC ↦ uctx_loc_type));
    M <- ret ((M1 ⊕ (restore_uctx ↦ restoreuctx_function ⊕ elf_load ↦ elfload_function)) ⊕ ∅);
    _ <- eassert nil (LayerOK (〚M 〛 (pipc ⊕ L64) ⊕ pipc ⊕ L64));
    (** watch out parentheses here: *)
    ret (
        (** group primitives according to the global variables that they use *)
        M(** for L64 and other passthrough primitives *)
      ).

End WITHCOMPCERTIKOS.