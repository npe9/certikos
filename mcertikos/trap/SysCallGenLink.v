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
Require Import TSysCall.
Require Import SysCallGen.
Require Import SysCallGenLinkSource.
Require Import TDispatch.
Require Import SysCallGenAsm.
Require Import SysCallGenAsm2.

Section WITHCOMPCERTIKOS.
  Context `{compcertikos_prf: CompCertiKOS} `{real_params_prf: RealParams}.

  Lemma init_correct:
    init_correct_type TSysCall_module tdispatch tsyscall.
  Proof.
    init_correct.
  Qed.

  Lemma link_correct_aux:
    link_correct_aux_type TSysCall_module tdispatch tsyscall.
  Proof.
    link_correct_aux.
    - match goal with |- cl_sim _ _ ?R ?x ?y => change (sim R x y) end.
      apply lower_bound.
    - link_asmfunction syscall_dispatch_spec_ref sys_dispatch_code_correct.
    - link_asmfunction pagefault_handler_spec_ref pgf_handler_code_correct.
    - link_asmfunction sys_yield_spec_ref sys_yield_code_correct.
    - apply passthrough_correct.
  Qed.

  Theorem cl_simulation:
    cl_simulation_type TSysCall_module tdispatch tsyscall.
  Proof.
    cl_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_forward_simulation:
    cl_forward_simulation_type TSysCall_module tdispatch tsyscall.
  Proof.
    cl_forward_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_backward_simulation:
    cl_backward_simulation_type TSysCall_module tdispatch tsyscall.
  Proof.
    cl_backward_simulation init_correct link_correct_aux.
  Qed.

  Theorem make_program_exists:
    make_program_exist_type TSysCall_module tdispatch tsyscall.
  Proof.
    make_program_exists link_correct_aux.
  Qed.

End WITHCOMPCERTIKOS.
