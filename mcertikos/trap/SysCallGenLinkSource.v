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
Require Import TDispatch.
Require Import SysCallGenAsmSource.

Definition TSysCall_module: link_module :=
  {|
    lm_cfun :=
      nil;
    lm_asmfun :=
      laf syscall_dispatch sys_dispatch_function ::
      laf pgf_handler pgf_handler_function ::
      laf sys_yield sys_yield_function ::
      (*laf sys_run_vm sys_run_vm_function ::*)
      nil;
    lm_gvar :=
      nil
  |}.

Definition TSysCall_impl `{CompCertiKOS} `{RealParams} :=
  link_impl TSysCall_module tdispatch.