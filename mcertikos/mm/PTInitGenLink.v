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
Require Import MPTKern.
Require Import MPTInit.
Require Import MPTKernCode.
Require Import PTInitGen.
Require Import PTInitGenSpec.
Require Import MPTKernCSource.
Require Import PTInitGenLinkSource.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.
  Context `{real_params_prf : RealParams}.

  Lemma link_correct_aux:
    link_correct_aux_type MPTInit_module mptkern mptinit.
  Proof.
    link_correct_aux.
    - link_cfunction pt_init_spec_ref MPTKERNCODE.pt_init_code_correct.
    - apply passthrough_correct.
  Qed.

  Lemma init_correct:
    init_correct_type MPTInit_module mptkern mptinit.
  Proof.
    init_correct.
    - intros i.
      rewrite !Maps.ZMap.gi.
      constructor.
  Qed.

  Theorem cl_simulation:
    cl_simulation_type MPTInit_module mptkern mptinit.
  Proof.
    cl_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_forward_simulation:
    cl_forward_simulation_type MPTInit_module mptkern mptinit.
  Proof.
    cl_forward_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_backward_simulation:
    cl_backward_simulation_type MPTInit_module mptkern mptinit.
  Proof.
    cl_backward_simulation init_correct link_correct_aux.
  Qed.

  Theorem make_program_exists:
    make_program_exist_type MPTInit_module mptkern mptinit.
  Proof.
    make_program_exists link_correct_aux.
  Qed.

End WITHCOMPCERTIKOS.
