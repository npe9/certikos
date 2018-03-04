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
Require Import MPTCommonCSource.
Require Import MPTCommon.

Definition MPTKern_module: link_module :=
  {|
    lm_cfun :=
      lcf pt_insert f_pt_insert ::
      lcf pt_rmv f_pt_rmv ::
      lcf pt_init_kern f_pt_init_kern ::
      nil;
    lm_asmfun :=
      nil;
    lm_gvar :=
      nil
  |}.

Definition MPTKern_impl `{CompCertiKOS} `{RealParams} :=
  link_impl MPTKern_module mptcommon.

