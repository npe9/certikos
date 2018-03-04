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
Require Import MPTNew.
Require Import MPTNewCSource.

Definition MShareIntro_module: link_module :=
  {|
    lm_cfun :=
      lcf clear_shared_mem f_clear_shared_mem ::
      lcf get_shared_mem_state f_get_shared_mem_state ::
      lcf get_shared_mem_seen f_get_shared_mem_seen ::
      lcf get_shared_mem_loc f_get_shared_mem_loc ::
      lcf set_shared_mem_state f_set_shared_mem_state ::
      lcf set_shared_mem_seen f_set_shared_mem_seen ::
      lcf set_shared_mem_loc f_set_shared_mem_loc ::
      nil;
    lm_asmfun :=
      nil;
    lm_gvar :=
      lgv SHRDMEMPOOL_LOC smspool_loc_type ::
      nil
  |}.

Definition MShareIntro_impl `{CompCertiKOS} `{RealParams} :=
  link_impl MShareIntro_module mptnew.
