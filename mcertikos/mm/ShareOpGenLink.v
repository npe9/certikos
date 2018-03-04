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
Require Import MShareOp.
Require Import ShareOpGen.
Require Import ShareOpGenLinkSource.
Require Import MShareIntro.
Require Import MShareIntroCSource.
Require Import MShareIntroCode.
Require Import MShareIntroCodeSharedMemInit.

Section WITHCOMPCERTIKOS.
  Context `{compcertikos_prf: CompCertiKOS} `{real_params_prf: RealParams}.

  Lemma link_correct_aux:
    link_correct_aux_type MShareOp_module mshareintro mshareop.
  Proof.
    link_correct_aux.
    - link_cfunction
        shared_mem_to_pending_spec_ref
        MSHAREOPCODE.shared_mem_to_pending_code_correct.
    - link_cfunction
        shared_mem_to_dead_spec_ref
        MSHAREOPCODE.shared_mem_to_dead_code_correct.
    - link_cfunction
        shared_mem_to_ready_spec_ref
        MSHAREOPCODE.shared_mem_to_ready_code_correct.
    - link_cfunction
        get_shared_mem_status_seen_spec_ref
        MSHAREOPCODE.get_shared_mem_status_seen_code_correct.
    - link_cfunction
        shared_mem_init_spec_ref
        MSHAREINTROCODESHAREDMEMINIT.shared_mem_init_code_correct.
    - apply passthrough_correct.
  Qed.

  Lemma init_correct:
    init_correct_type MShareOp_module mshareintro mshareop.
  Proof.
    init_correct.
  Qed.

  Theorem cl_simulation:
    cl_simulation_type MShareOp_module mshareintro mshareop.
  Proof.
    cl_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_forward_simulation:
    cl_forward_simulation_type MShareOp_module mshareintro mshareop.
  Proof.
    cl_forward_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_backward_simulation:
    cl_backward_simulation_type MShareOp_module mshareintro mshareop.
  Proof.
    cl_backward_simulation init_correct link_correct_aux.
  Qed.

  Theorem make_program_exists:
    make_program_exist_type MShareOp_module mshareintro mshareop.
  Proof.
    make_program_exists link_correct_aux.
  Qed.
End WITHCOMPCERTIKOS.
