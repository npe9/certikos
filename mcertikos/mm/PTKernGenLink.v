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
Require Import MPTCommon.
Require Import MPTKern.
Require Import MPTCommonCode.
Require Import PTKernGen.
Require Import PTKernGenSpec.
Require Import MPTCommonCSource.
Require Import PTKernGenLinkSource.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.
  Context `{real_params_prf : RealParams}.

  Lemma link_correct_aux:
    link_correct_aux_type MPTKern_module mptcommon mptkern.
  Proof.
    link_correct_aux.
    - link_cfunction ptInsert_spec_ref MPTCOMMONCODE.pt_insert_code_correct.
    - link_cfunction ptRmv_spec_ref MPTCOMMONCODE.pt_rmv_code_correct.
    - link_cfunction pt_init_kern_spec_ref MPTCOMMONCODE.pt_init_kern_code_correct.
    - eapply passthrough_correct.
  Qed.

  Lemma init_correct:
    init_correct_type MPTKern_module mptcommon mptkern.
  Proof.
    init_correct.
  Qed.

  Theorem cl_simulation:
    cl_simulation_type MPTKern_module mptcommon mptkern.
  Proof.
    cl_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_forward_simulation:
    cl_forward_simulation_type MPTKern_module mptcommon mptkern.
  Proof.
    cl_forward_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_backward_simulation:
    cl_backward_simulation_type MPTKern_module mptcommon mptkern.
  Proof.
    cl_backward_simulation init_correct link_correct_aux.
  Qed.

  Theorem make_program_exists:
    make_program_exist_type MPTKern_module mptcommon mptkern.
  Proof.
    make_program_exists link_correct_aux.
  Qed.

End WITHCOMPCERTIKOS.
