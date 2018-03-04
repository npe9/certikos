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
Require Import PKContextNewCSource.

Require Import CompCertiKOSproof.
Require Import RealParams.
Require Import I64Layer.

Require Import PKContextNew.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Definition PThreadIntro_impl: res LAsm.module :=
    M1 <- (M_get_state <- CompCertiKOS.transf_module (get_state ↦ f_get_state);
           M_get_prev <- CompCertiKOS.transf_module (get_prev ↦ f_get_prev);
           M_get_next <- CompCertiKOS.transf_module (get_next ↦ f_get_next);
           M_set_state <- CompCertiKOS.transf_module (set_state ↦ f_set_state);
           M_set_prev <- CompCertiKOS.transf_module (set_prev ↦ f_set_prev);
           M_set_next <- CompCertiKOS.transf_module (set_next ↦ f_set_next);
           M_tcb_init <- CompCertiKOS.transf_module (tcb_init ↦ f_tcb_init);
           _ <- eassert nil (LayerOK ((〚M_get_state ⊕ M_get_prev ⊕ M_get_next ⊕ M_set_state ⊕ M_set_prev
                                                     ⊕ M_set_next ⊕ M_tcb_init〛 
                                         ((pkcontextnew ⊕ L64) ⊕ TCBPool_LOC ↦ tcbpool_loc_type)
                                         ⊕ (pkcontextnew ⊕ L64) ⊕ TCBPool_LOC ↦ tcbpool_loc_type)));
           ret ((M_get_state ⊕ M_get_prev ⊕ M_get_next ⊕ M_set_state ⊕ M_set_prev ⊕ M_set_next 
                             ⊕ M_tcb_init) ⊕ TCBPool_LOC ↦ tcbpool_loc_type));
    M <- ret (M1 ⊕ ∅ );
    _ <- eassert nil (LayerOK (〚M 〛 (pkcontextnew ⊕ L64) ⊕ pkcontextnew ⊕ L64));
    (** watch out parentheses here: *)
    ret (
        (** group primitives according to the global variables that they use *)
        M(** for L64 and other passthrough primitives *)
      ).

End WITHCOMPCERTIKOS.
