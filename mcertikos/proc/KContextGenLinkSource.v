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
Require Import MShareCSource.
Require Import KContextGenAsmSource.

Require Import CompCertiKOSproof.
Require Import RealParams.
Require Import I64Layer.

Require Import MShare.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Definition PKContext_impl: res LAsm.module :=
    M1 <- (M_set_RA <- CompCertiKOS.transf_module (set_RA ↦ f_set_RA);
           M_set_SP <- CompCertiKOS.transf_module (set_SP ↦ f_set_SP);
           _ <- eassert nil (LayerOK ((〚M_set_RA ⊕ M_set_SP〛 
                                         ((mshare ⊕ L64) ⊕ KCtxtPool_LOC ↦ kctxtpool_loc_type)
                                         ⊕ (mshare ⊕ L64) ⊕ KCtxtPool_LOC ↦ kctxtpool_loc_type)));
           ret ((M_set_RA ⊕ M_set_SP) ⊕ KCtxtPool_LOC ↦ kctxtpool_loc_type));
    M <- ret (M1 ⊕ ((kctxt_switch ↦ cswitch_function) ⊕ ∅) );
    _ <- eassert nil (LayerOK (〚M 〛 (mshare ⊕ L64) ⊕ mshare ⊕ L64));
    (** watch out parentheses here: *)
    ret (
        (** group primitives according to the global variables that they use *)
        M(** for L64 and other passthrough primitives *)
      ).

End WITHCOMPCERTIKOS.