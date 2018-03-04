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
Require Import LAsmModuleSem.
Require Import CompCertiKOS.
Require Import GlobIdent.
Require Import CDataTypes.
Require Import I64Layer.
Require Import CompCertiKOSproof.
Require Import RealParams.

Require Import MALT.
Require Import MALTCSource.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Definition MContainer_impl: res LAsm.module :=
    M1 <- (M_container_init <- CompCertiKOS.transf_module (container_init ↦ f_container_init);
           M_container_get_parent <- CompCertiKOS.transf_module (container_get_parent ↦ f_container_get_parent);
           M_container_get_nchildren <- CompCertiKOS.transf_module (container_get_nchildren ↦ f_container_get_nchildren);
           M_container_get_quota <- CompCertiKOS.transf_module (container_get_quota ↦ f_container_get_quota);
           M_container_get_usage <- CompCertiKOS.transf_module (container_get_usage ↦ f_container_get_usage);
           M_container_can_consume <- CompCertiKOS.transf_module (container_can_consume ↦ f_container_can_consume);
           M_container_split <- CompCertiKOS.transf_module (container_split ↦ f_container_split);
           M_container_alloc <- CompCertiKOS.transf_module (container_alloc ↦ f_container_alloc);
           _ <- eassert nil (LayerOK (〚M_container_init ⊕ M_container_get_parent ⊕
                                        M_container_get_nchildren ⊕
                                        M_container_get_quota ⊕ M_container_get_usage ⊕
                                        M_container_can_consume ⊕ M_container_split ⊕
                                        M_container_alloc〛((malt ⊕ L64) ⊕ AC_LOC ↦ container_loc_type)
                                    ⊕ ((malt ⊕ L64) ⊕ AC_LOC ↦ container_loc_type)));
           ret ((M_container_init ⊕ M_container_get_parent  
                                           ⊕ M_container_get_nchildren ⊕ M_container_get_quota 
                                           ⊕ M_container_get_usage ⊕ M_container_can_consume
                                           ⊕ M_container_split ⊕ M_container_alloc) ⊕ AC_LOC ↦ container_loc_type));
    M <- ret (M1 ⊕ ∅);
    _ <- eassert nil (LayerOK (〚M 〛 (malt ⊕ L64) ⊕ malt ⊕ L64));
    (** watch out parentheses here: *)
    ret (
        (** group primitives according to the global variables that they use *)
        M(** for L64 and other passthrough primitives *)
      ).

End WITHCOMPCERTIKOS.