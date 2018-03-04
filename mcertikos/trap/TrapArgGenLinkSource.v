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

Require Import CompCertiKOSproof.
Require Import RealParams.
Require Import I64Layer.

Require Import PProc.
Require Import PProcCSource.

Section WITHCOMPCERTIKOS.

Context `{compcertikos_prf: CompCertiKOS}.
Context `{real_params_prf : RealParams}.

Definition TTrapArg_impl: res LAsm.module :=
  (*M_la2pa_resv <- CompCertiKOS.transf_module (la2pa_resv ↦ f_la2pa_resv);*)
  M_uctx_arg1 <- CompCertiKOS.transf_module (uctx_arg1 ↦ f_uctx_arg1);
  M_uctx_arg2 <- CompCertiKOS.transf_module (uctx_arg2 ↦ f_uctx_arg2);
  M_uctx_arg3 <- CompCertiKOS.transf_module (uctx_arg3 ↦ f_uctx_arg3);
  M_uctx_arg4 <- CompCertiKOS.transf_module (uctx_arg4 ↦ f_uctx_arg4);
  M_uctx_arg5 <- CompCertiKOS.transf_module (uctx_arg5 ↦ f_uctx_arg5);
  M_uctx_arg6 <- CompCertiKOS.transf_module (uctx_arg6 ↦ f_uctx_arg6);
  M_uctx_set_errno <- CompCertiKOS.transf_module (uctx_set_errno ↦ f_uctx_set_errno);
  M_uctx_set_retval1 <- CompCertiKOS.transf_module (uctx_set_retval1 ↦ f_uctx_set_retval1);
  M_uctx_set_retval2 <- CompCertiKOS.transf_module (uctx_set_retval2 ↦ f_uctx_set_retval2);
  M_uctx_set_retval3 <- CompCertiKOS.transf_module (uctx_set_retval3 ↦ f_uctx_set_retval3);
  M_uctx_set_retval4 <- CompCertiKOS.transf_module (uctx_set_retval4 ↦ f_uctx_set_retval4);
  (** watch out parentheses here: *)
  M <- ret (
      ( (** group primitives according to the global variables that they use *)
        (*M_la2pa_resv ⊕*) M_uctx_arg1 ⊕ M_uctx_arg2 ⊕ M_uctx_arg3 ⊕ M_uctx_arg4 ⊕ M_uctx_arg5 ⊕ M_uctx_arg6 ⊕
                           M_uctx_set_errno ⊕ M_uctx_set_retval1 ⊕ M_uctx_set_retval2 ⊕ M_uctx_set_retval3 ⊕ M_uctx_set_retval4
      ) ⊕ ∅ (** for L64 and other passthrough primitives *)
    );
  _ <- eassert nil (LayerOK (〚M 〛 (pproc ⊕ L64) ⊕ pproc ⊕ L64));
  ret M.

End WITHCOMPCERTIKOS.
