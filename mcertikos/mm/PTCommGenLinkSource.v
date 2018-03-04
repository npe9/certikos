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
Require Import MPTOp.
Require Import MPTOpCSource.

Definition MPTCommon_module :=
  {|
    lm_cfun :=
      lcf pt_alloc_pde f_pt_alloc_pde ::
      lcf pt_free_pde f_pt_free_pde ::
      lcf pt_init_comm f_pt_init_comm ::
      nil;
    lm_asmfun :=
      nil;
    lm_gvar :=
      nil
  |}.

Definition MPTCommon_impl `{CompCertiKOS} `{RealParams} :=
  link_impl MPTCommon_module mptop.
