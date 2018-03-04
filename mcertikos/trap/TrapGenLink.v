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
Require Import LinkTemplate.
Require Import TTrap.
Require Import TrapGen.
Require Import TrapGenLinkSource.
Require Import TTrapArg.
Require Import TTrapArgCSource.
Require Import TTrapArgCode.
Require Import TTrapArgCode2.

Section WITHCOMPCERTIKOS.
  Context `{compcertikos_prf: CompCertiKOS} `{real_params_prf: RealParams}.

  Lemma init_correct:
    init_correct_type TTrap_module ttraparg ttrap.
  Proof.
    init_correct.
  Qed.

  Lemma link_correct_aux:
    link_correct_aux_type TTrap_module ttraparg ttrap.
  Proof.
    link_correct_aux.
    - link_cfunction
        ptf_resv_spec_ref
        TTRAPARGCODE2.ptfault_resv_code_correct.
    - link_cfunction
        trap_proc_create_spec_ref
        TTRAPARGCODE2.sys_proc_create_code_correct.
    - link_cfunction
        trap_get_quota_spec_ref
        TTRAPARGCODE.sys_get_quota_code_correct.

    (*
    - link_cfunction
        trap_ischanready_spec_ref
        TTRAPARGCODE.sys_is_chan_ready_code_correct.
    - link_cfunction
        trap_sendtochan_spec_ref
        TTRAPARGCODE.sys_sendto_chan_code_correct.
    *)
    - link_cfunction
        trap_receivechan_spec_ref
        TTRAPARGCODE.sys_receive_chan_code_correct.

    - link_cfunction
        trap_offer_shared_mem_spec_ref
        TTRAPARGCODE.sys_offer_shared_mem_code_correct.

    - link_cfunction
        print_spec_ref
        TTRAPARGCODE.print_code_correct.

    (*- link_cfunction
        trap_inject_event_spec_ref
        TTRAPARGCODE.sys_inject_event_code_correct.
    - link_cfunction
        trap_check_int_shadow_spec_ref
        TTRAPARGCODE.sys_check_int_shadow_code_correct.
    - link_cfunction
        trap_check_pending_event_spec_ref
        TTRAPARGCODE.sys_check_pending_event_code_correct.
    - link_cfunction
        trap_intercept_int_window_spec_ref
        TTRAPARGCODE.sys_intercept_int_window_code_correct.
    - link_cfunction
        trap_get_next_eip_spec_ref
        TTRAPARGCODE.sys_get_next_eip_code_correct.
    - link_cfunction
        trap_get_reg_spec_ref
        TTRAPARGCODE.sys_get_reg_body_code_correct.
    - link_cfunction
        trap_set_reg_spec_ref
        TTRAPARGCODE.sys_set_reg_body_code_correct.
    - link_cfunction
        trap_set_seg_spec_ref
        TTRAPARGCODE.sys_set_seg_body_code_correct.
    - link_cfunction
        trap_get_tsc_offset_spec_ref
        TTRAPARGCODE.sys_get_tsc_offset_body_code_correct.
    - link_cfunction
        trap_set_tsc_offset_spec_ref
        TTRAPARGCODE.sys_set_tsc_offset_body_code_correct.
    - link_cfunction
        trap_get_exitinfo_spec_ref
        TTRAPARGCODE.sys_get_exitinfo_body_code_correct.
    - link_cfunction
        trap_handle_rdmsr_spec_ref
        TTRAPARGCODE.sys_handle_rdmsr_body_code_correct.
    - link_cfunction
        trap_handle_wrmsr_spec_ref
        TTRAPARGCODE.sys_handle_wrmsr_body_code_correct.
    - link_cfunction
        trap_mmap_spec_ref
        TTRAPARGCODE2.sys_mmap_code_correct.*)
    - apply passthrough_correct.
  Qed.

  Theorem cl_simulation:
    cl_simulation_type TTrap_module ttraparg ttrap.
  Proof.
    cl_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_forward_simulation:
    cl_forward_simulation_type TTrap_module ttraparg ttrap.
  Proof.
    cl_forward_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_backward_simulation:
    cl_backward_simulation_type TTrap_module ttraparg ttrap.
  Proof.
    cl_backward_simulation init_correct link_correct_aux.
  Qed.

  Theorem make_program_exists:
    make_program_exist_type TTrap_module ttraparg ttrap.
  Proof.
    make_program_exists link_correct_aux.
  Qed.

End WITHCOMPCERTIKOS.
