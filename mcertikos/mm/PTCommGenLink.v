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
Require Import MPTOp.
Require Import MPTCommon.
Require Import MPTOpCode.
Require Import PTCommGen.
Require Import PTCommGenSpec.
Require Import MPTOpCSource.
Require Import PTCommGenLinkSource.

Section WITHCOMPCERTIKOS.
  Context `{compcertikos_prf: CompCertiKOS}.
  Context `{real_params_prf : RealParams}.

  Lemma init_correct:
    init_correct_type MPTCommon_module mptop mptcommon.
  Proof.
    init_correct.
  Qed.

  Lemma link_correct_aux:
    link_correct_aux_type MPTCommon_module mptop mptcommon.
  Proof.
    link_correct_aux.
    - link_cfunction ptAllocPDE_spec_ref MPTOPCODE.pt_alloc_pde_code_correct.
    - link_cfunction ptFreePDE_spec_ref MPTOPCODE.pt_free_pde_code_correct.
    - link_cfunction pt_init_comm_spec_ref MPTOPCODE.pt_init_comm_code_correct.
    - apply passthrough_correct.
  Qed.

  Theorem cl_simulation:
    cl_simulation_type MPTCommon_module mptop mptcommon.
  Proof.
    cl_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_forward_simulation:
    cl_forward_simulation_type MPTCommon_module mptop mptcommon.
  Proof.
    cl_forward_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_backward_simulation:
    cl_backward_simulation_type MPTCommon_module mptop mptcommon.
  Proof.
    cl_backward_simulation init_correct link_correct_aux.
  Qed.

  Theorem make_program_exists:
    make_program_exist_type MPTCommon_module mptop mptcommon.
  Proof.
    make_program_exists link_correct_aux.
  Qed.
End WITHCOMPCERTIKOS.
