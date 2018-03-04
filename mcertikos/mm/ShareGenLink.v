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
Require Import MShare.
Require Import ShareGen.
Require Import ShareGenLinkSource.
Require Import MShareOp.
Require Import MShareOpCSource.
Require Import MShareOpCode.

Section WITHCOMPCERTIKOS.
  Context `{compcertikos_prf: CompCertiKOS} `{real_params_prf: RealParams}.

  Lemma link_correct_aux:
    link_correct_aux_type MShare_module mshareop mshare.
  Proof.
    link_correct_aux.
    - link_cfunction
        shared_mem_status_spec_ref
        MSHARECODE.shared_mem_status_code_correct.
    - link_cfunction
        offer_shared_mem_spec_ref
        MSHARECODE.offer_shared_mem_code_correct.
    - apply passthrough_correct.
  Qed.

  Lemma init_correct:
    init_correct_type MShare_module mshareop mshare.
  Proof.
    init_correct.
  Qed.

  Theorem cl_simulation:
    cl_simulation_type MShare_module mshareop mshare.
  Proof.
    cl_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_forward_simulation:
    cl_forward_simulation_type MShare_module mshareop mshare.
  Proof.
    cl_forward_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_backward_simulation:
    cl_backward_simulation_type MShare_module mshareop mshare.
  Proof.
    cl_backward_simulation init_correct link_correct_aux.
  Qed.

  Theorem make_program_exists:
    make_program_exist_type MShare_module mshareop mshare.
  Proof.
    make_program_exists link_correct_aux.
  Qed.
End WITHCOMPCERTIKOS.
