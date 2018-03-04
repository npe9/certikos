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
Require Import PAbQueueCSource.

Require Import CompCertiKOSproof.
Require Import RealParams.
Require Import I64Layer.

Require Import PAbQueue.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Definition PCurID_impl: res LAsm.module :=
    M1 <- (M_get_curid <- CompCertiKOS.transf_module (get_curid ↦ f_get_curid);
           M_set_curid <- CompCertiKOS.transf_module (set_curid ↦ f_set_curid);
           _ <- eassert nil (LayerOK ((〚M_get_curid ⊕ M_set_curid〛 
                                         ((pabqueue ⊕ L64) ⊕ CURID_LOC ↦ curid_loc_type)
                                         ⊕ (pabqueue ⊕ L64) ⊕ CURID_LOC ↦ curid_loc_type)));
           ret ((M_get_curid ⊕ M_set_curid) ⊕ CURID_LOC ↦ curid_loc_type));
    M <- ret (M1 ⊕ ∅ );
    _ <- eassert nil (LayerOK (〚M 〛 (pabqueue ⊕ L64) ⊕ pabqueue ⊕ L64));
    (** watch out parentheses here: *)
    ret (
        (** group primitives according to the global variables that they use *)
        M(** for L64 and other passthrough primitives *)
      ).

End WITHCOMPCERTIKOS.