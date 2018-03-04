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
Require Import PIPCIntro.
Require Import PIPCIntroCSource.

Definition PIPC_module: link_module :=
  {|
    lm_cfun :=
      lcf syncreceive_chan f_syncreceive_chan ::
      lcf syncsendto_chan_pre f_syncsendto_chan_pre ::
      lcf syncsendto_chan_post f_syncsendto_chan_post ::
      lcf proc_init f_proc_init ::
      nil;
    lm_asmfun :=
      nil;
    lm_gvar :=
      nil
  |}.

Definition PIPC_impl `{CompCertiKOS} `{RealParams} :=
  link_impl PIPC_module pipcintro.
