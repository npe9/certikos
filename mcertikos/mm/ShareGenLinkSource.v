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
Require Import MShareOp.
Require Import MShareOpCSource.

Definition MShare_module: link_module :=
  {|
    lm_cfun :=
      lcf shared_mem_status f_shared_mem_status ::
      lcf offer_shared_mem f_offer_shared_mem ::
      nil;
    lm_asmfun :=
      nil;
    lm_gvar :=
      nil
  |}.

Definition MShare_impl `{CompCertiKOS} `{RealParams} :=
  link_impl MShare_module mshareop.
