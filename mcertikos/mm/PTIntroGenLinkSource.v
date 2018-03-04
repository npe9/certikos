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
Require Import LinkSourceTemplate.
Require Import CDataTypes.
Require Import MContainer.
Require Import MContainerCSource.
Require Import PTIntroGenAsmSource.

Definition MPTIntro_module: link_module :=
  {|
    lm_cfun :=
      (lcf set_pt f_set_pt)::
      (lcf get_PDE f_get_PDE)::
      (lcf set_PDE f_set_pde)::
      (lcf rmv_PDE f_rmv_pde)::
      (lcf set_PDEU f_set_pdeu)::
      (lcf get_PTE f_get_pte)::
      (lcf set_PTE f_set_pte)::
      (lcf rmv_PTE f_rmv_pte)::
      (lcf set_IDPTE f_set_idpte)::
      nil;
    lm_gvar :=
      (lgv PTPool_LOC ptpool_loc_type)::
      (lgv IDPMap_LOC idpmap_loc_type)::
      nil;
    lm_asmfun :=
      (laf pt_in ptin_function)::
      (laf pt_out ptout_function)::
      nil
  |}.
      
Definition MPTIntro_impl `{CompCertiKOS} `{RealParams} :=
  link_impl MPTIntro_module mcontainer.
