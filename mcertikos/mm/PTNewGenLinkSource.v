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
Require Import MPTInitCSource.

Require Import CompCertiKOSproof.
Require Import RealParams.
Require Import I64Layer.

Require Import MPTInit.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

Definition MPTNew_impl: res LAsm.module :=
  M_pt_resv <- CompCertiKOS.transf_module (pt_resv ↦ f_pt_resv);
  M_pt_resv2 <- CompCertiKOS.transf_module (pt_resv2 ↦ f_pt_resv2);
  M_pt_new <- CompCertiKOS.transf_module (pt_new ↦ f_pt_new);
  (* M_pt_free <- CompCertiKOS.transf_module (pt_free ↦ f_pt_free); *)
  M_pmap_init <- CompCertiKOS.transf_module (pmap_init ↦ f_pmap_init);
  M <- ret ((M_pt_resv ⊕ M_pt_resv2 ⊕ M_pt_new ⊕ (*M_pt_free ⊕*) M_pmap_init) ⊕ ∅);
  _ <- eassert nil (LayerOK (〚M 〛 (mptinit ⊕ L64) ⊕ mptinit ⊕ L64));
  (** watch out parentheses here: *)
  ret (
      (** group primitives according to the global variables that they use *)
      M (** for L64 and other passthrough primitives *)
    ).

End WITHCOMPCERTIKOS.