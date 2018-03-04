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
Require Import TDispatch.
Require Import DispatchGen.
Require Import DispatchGenLinkSource.
Require Import TTrap.
Require Import TTrapCSource.
Require Import TTrapCode.

Section WITHCOMPCERTIKOS.
  Context `{compcertikos_prf: CompCertiKOS} `{real_params_prf: RealParams}.

  Lemma init_correct:
    init_correct_type TDispatch_module ttrap tdispatch.
  Proof.
    init_correct.
  Qed.

  Lemma link_correct_aux:
    link_correct_aux_type TDispatch_module ttrap tdispatch.
  Proof.
    link_correct_aux.
    - link_cfunction
        sys_dispatch_c_spec_ref
        TTRAPCODE.syscall_dispatch_c_code_correct.
    - link_cfunction
        trap_sendtochan_pre_spec_ref
        TTRAPCODE.trap_sendtochan_pre_code_correct.
    - link_cfunction
        trap_sendtochan_post_spec_ref
        TTRAPCODE.trap_sendtochan_post_code_correct.
    - apply passthrough_correct.
  Qed.

  Theorem cl_simulation:
    cl_simulation_type TDispatch_module ttrap tdispatch.
  Proof.
    cl_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_forward_simulation:
    cl_forward_simulation_type TDispatch_module ttrap tdispatch.
  Proof.
    cl_forward_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_backward_simulation:
    cl_backward_simulation_type TDispatch_module ttrap tdispatch.
  Proof.
    cl_backward_simulation init_correct link_correct_aux.
  Qed.

  Theorem make_program_exists:
    make_program_exist_type TDispatch_module ttrap tdispatch.
  Proof.
    make_program_exists link_correct_aux.
  Qed.
End WITHCOMPCERTIKOS.
