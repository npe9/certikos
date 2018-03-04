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
Require Import TTrap.
Require Import TTrapCSource.

Definition TDispatch_module: link_module :=
  {|
    lm_cfun :=
      lcf syscall_dispatch_C f_syscall_dispatch_c ::
      lcf trap_sendtochan_pre f_trap_sendtochan_pre ::
      lcf trap_sendtochan_post f_trap_sendtochan_post ::
      nil;
    lm_asmfun :=
      nil;
    lm_gvar :=
      nil
  |}.

Definition TDispatch_impl `{CompCertiKOS} `{RealParams} :=
  link_impl TDispatch_module ttrap.
