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
Require Import PThread.
Require Import PThreadCSource.
Require Import CDataTypes.

Definition PIPCIntro_module: link_module :=
  {|
    lm_cfun :=
      lcf get_sync_chan_to f_get_sync_chan_to ::
      lcf get_sync_chan_paddr f_get_sync_chan_paddr ::
      lcf get_sync_chan_count f_get_sync_chan_count ::
      lcf set_sync_chan_to f_set_sync_chan_to ::
      lcf set_sync_chan_paddr f_set_sync_chan_paddr ::
      lcf set_sync_chan_count f_set_sync_chan_count ::
      lcf init_sync_chan f_init_sync_chan ::
      lcf get_kernel_pa f_get_kernel_pa ::
      nil;
    lm_asmfun :=
      nil;
    lm_gvar :=
      lgv SYNCCHPOOL_LOC syncchpool_loc_type ::
      nil
  |}.

Definition PIPCIntro_impl `{CompCertiKOS} `{RealParams} :=
  link_impl PIPCIntro_module pthread.
