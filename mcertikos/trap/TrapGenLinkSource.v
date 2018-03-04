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
Require Import TTrapArg.
Require Import TTrapArgCSource.

Definition TTrap_module: link_module :=
  {|
    lm_cfun :=
      lcf ptfault_resv f_ptfault_resv ::
      lcf sys_proc_create f_sys_proc_create ::
      lcf sys_get_quota f_sys_get_quota ::
      (*lcf sys_is_chan_ready f_sys_is_chan_ready ::
      lcf sys_sendto_chan f_sys_sendto_chan ::*)
      lcf sys_receive_chan f_sys_receive_chan ::
      lcf sys_offer_shared_mem f_sys_offer_shared_mem ::
      lcf print f_print ::
      (*lcf sys_inject_event f_sys_inject_event ::
      lcf sys_check_int_shadow f_sys_check_int_shadow ::
      lcf sys_check_pending_event f_sys_check_pending_event ::
      lcf sys_intercept_int_window f_sys_set_intercept_intwin ::
      lcf sys_get_next_eip f_sys_get_next_eip ::
      lcf sys_get_reg f_sys_get_reg ::
      lcf sys_set_reg f_sys_set_reg ::
      lcf sys_set_seg f_sys_set_seg ::
      lcf sys_get_tsc_offset f_sys_get_tsc_offset ::
      lcf sys_set_tsc_offset f_sys_set_tsc_offset ::
      lcf sys_get_exitinfo f_sys_get_exitinfo ::
      lcf sys_handle_rdmsr f_sys_handle_rdmsr ::
      lcf sys_handle_wrmsr f_sys_handle_wrmsr ::
      lcf sys_mmap f_sys_mmap ::*)
      nil;
    lm_asmfun :=
      nil;
    lm_gvar :=
      nil
  |}.

Definition TTrap_impl `{CompCertiKOS} `{RealParams} :=
  link_impl TTrap_module ttraparg.