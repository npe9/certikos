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
Require Import MShareIntro.
Require Import MShareIntroCSource.

Definition MShareOp_module: link_module :=
  {|
    lm_cfun :=
      lcf shared_mem_to_pending f_shared_mem_to_pending ::
      lcf shared_mem_to_dead f_shared_mem_to_dead ::
      lcf shared_mem_to_ready f_shared_mem_to_ready ::
      lcf get_shared_mem_status_seen f_get_shared_mem_status_seen ::
      lcf shared_mem_init f_shared_mem_init ::
      nil;
    lm_asmfun :=
      nil;
    lm_gvar :=
      nil
  |}.

Definition MShareOp_impl `{CompCertiKOS} `{RealParams} :=
  link_impl MShareOp_module mshareintro.
