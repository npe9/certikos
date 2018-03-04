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
Require Import MPTIntroCSource.
Require Import MPTIntro.

Definition MPTOp_module: link_module :=
  {|
    lm_cfun :=
      lcf pt_read f_pt_read ::
      lcf pt_read_pde f_pt_read_pde ::
      lcf pt_insert_aux f_pt_insert_aux ::
      lcf pt_insert_pde f_pt_insert_pde ::
      lcf pt_rmv_aux f_pt_rmv_aux ::
      lcf pt_rmv_pde f_pt_rmv_pde ::
      lcf idpde_init f_idpde_init ::
      nil;
    lm_asmfun :=
      nil;
    lm_gvar :=
      nil
  |}.

Definition MPTOp_impl `{CompCertiKOS} `{RealParams}: res LAsm.module :=
  link_impl MPTOp_module mptintro.
