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
Require Import PKContextCSource.

Require Import CompCertiKOSproof.
Require Import RealParams.
Require Import I64Layer.

Require Import PKContext.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Definition PKContextNew_impl: res LAsm.module :=
    M_kctxt_new <- CompCertiKOS.transf_module (kctxt_new ↦ f_kctxt_new);
    M <- ret (M_kctxt_new ⊕ ∅);
    _ <- eassert nil (LayerOK (〚M 〛 (pkcontext ⊕ L64) ⊕ pkcontext ⊕ L64));
    (** watch out parentheses here: *)
    ret (
        (** group primitives according to the global variables that they use *)
        M (** for L64 and other passthrough primitives *)
      ).

End WITHCOMPCERTIKOS.