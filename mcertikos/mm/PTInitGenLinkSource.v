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
Require Import MPTKernCSource.
Require Import MPTKern.

Definition MPTInit_module :=
  {|
    lm_cfun :=
      lcf pt_init f_pt_init ::
      nil;
    lm_asmfun :=
      nil;
    lm_gvar :=
      nil
  |}.

Definition MPTInit_impl `{CompCertiKOS} `{RealParams} :=
  link_impl MPTInit_module mptkern.
