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
Require Import CDataTypes.
Require Import PreInit.
Require Import PreInitCSource.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Definition MBoot_module: link_module :=
    {|
      lm_cfun :=
        lcf fload f_fload ::
        lcf fstore f_fstore ::
        nil;
      lm_asmfun :=
        nil;
      lm_gvar :=
        lgv FlatMem_LOC flatmem_loc_type ::
        nil
    |}.

  Definition MBoot_impl: res LAsm.module :=
    link_impl MBoot_module preinit.

End WITHCOMPCERTIKOS.
