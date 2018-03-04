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
Require Import MBootCSource.
Require Import MBoot.
Require Import I64Layer.
Require Import CompCertiKOSproof.
Require Import RealParams.

Section WITHCOMPCERTIKOS.
Set Printing All.
  
  Context `{compcertikos_prf: CompCertiKOS}.
  Context `{real_params_prf : RealParams}.

  Definition MALInit_impl: res LAsm.module :=
    M1 <- (M_get_at_u <- CompCertiKOS.transf_module (at_get ↦ f_at_get);
           M_is_norm <- CompCertiKOS.transf_module (is_norm ↦ f_is_norm);
           M_at_get_c <- CompCertiKOS.transf_module (at_get_c ↦ f_at_get_c);
           M_set_at_u <- CompCertiKOS.transf_module (at_set ↦ f_at_set);
           M_set_norm <- CompCertiKOS.transf_module (set_norm ↦ f_set_norm);
           M_at_set_c <- CompCertiKOS.transf_module (at_set_c ↦ f_at_set_c);
           _ <- eassert nil (LayerOK ( (〚M_get_at_u ⊕ M_is_norm ⊕ M_at_get_c ⊕ M_set_at_u ⊕ M_set_norm ⊕ M_at_set_c〛 
                                          ((mboot ⊕ L64) ⊕ AT_LOC ↦ at_loc_type)
                                          ⊕ (mboot ⊕ L64) ⊕ AT_LOC ↦ at_loc_type)));
          ret ((M_get_at_u ⊕ M_is_norm ⊕ M_at_get_c ⊕ M_set_at_u ⊕ M_set_norm ⊕ M_at_set_c) ⊕ (AT_LOC ↦ at_loc_type)));

    M2 <- (M_set_nps  <- CompCertiKOS.transf_module (set_nps ↦ f_set_nps);
           M_get_nps  <- CompCertiKOS.transf_module (get_nps ↦ f_get_nps);
           _ <- eassert nil ( LayerOK
                                (〚M_set_nps ⊕ M_get_nps 〛 
                                   ((mboot ⊕ L64) ⊕ NPS_LOC ↦ nps_loc_type)
                                   ⊕ (mboot ⊕ L64) ⊕ NPS_LOC ↦ nps_loc_type));
           ret ((M_set_nps ⊕ M_get_nps) ⊕ (NPS_LOC ↦ nps_loc_type)));
    M <- ret ((M1 ⊕ M2) ⊕ ∅ );
    _ <- eassert nil (LayerOK (〚M 〛 (mboot ⊕ L64) ⊕ mboot ⊕ L64));
    (** watch out parentheses here: *)
    ret (
        (** group primitives according to the global variables that they use *)
        M(** for L64 and other passthrough primitives *)
      ).

End WITHCOMPCERTIKOS.