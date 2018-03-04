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
Require Import MALOpCSource.

Require Import CompCertiKOSproof.
Require Import RealParams.
Require Import I64Layer.

Require Import MALOp.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Definition MALT_impl: res LAsm.module :=
    M_palloc <- CompCertiKOS.transf_module (palloc ↦ f_palloc);
    M_pfree <- CompCertiKOS.transf_module (pfree ↦ f_pfree);
    M <- ret ((M_palloc ⊕ M_pfree) ⊕ ∅) ;
    _ <- eassert nil (LayerOK (〚M 〛 (malop ⊕ L64) ⊕ malop ⊕ L64));
    (** watch out parentheses here: *)
    ret (
        (** group primitives according to the global variables that they use *)
        M (** for L64 and other passthrough primitives *)
      ).

End WITHCOMPCERTIKOS.