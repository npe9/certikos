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
Require Import PIPC.
Require Import IPCGen.
Require Import IPCGenLinkSource.
Require Import PIPCIntro.
Require Import PIPCIntroCSource.
Require Import PIPCIntroCode.

Section WITHCOMPCERTIKOS.
  Context `{compcertikos_prf: CompCertiKOS} `{real_params_prf: RealParams}.

  Lemma init_correct:
    init_correct_type PIPC_module pipcintro pipc.
  Proof.
    init_correct.
  Qed.

  Lemma link_correct_aux:
    link_correct_aux_type PIPC_module pipcintro pipc.
  Proof.
    link_correct_aux.
    - link_cfunction
        syncreceive_chan_spec_ref
        PIPCINTROCODE.syncreceive_chan_code_correct.
    - link_cfunction
        syncsendto_chan_pre_spec_ref
        PIPCINTROCODE.syncsendto_chan_pre_code_correct.
    - link_cfunction
        syncsendto_chan_post_spec_ref
        PIPCINTROCODE.syncsendto_chan_post_code_correct.
    - link_cfunction
        proc_init_spec_ref
        PIPCINTROCODE.proc_init_code_correct.
    - apply passthrough_correct.
  Qed.

  Theorem cl_simulation:
    cl_simulation_type PIPC_module pipcintro pipc.
  Proof.
    cl_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_forward_simulation:
    cl_forward_simulation_type PIPC_module pipcintro pipc.
  Proof.
    cl_forward_simulation init_correct link_correct_aux.
  Qed.

  Theorem cl_backward_simulation:
    cl_backward_simulation_type PIPC_module pipcintro pipc.
  Proof.
    cl_backward_simulation init_correct link_correct_aux.
  Qed.

  Theorem make_program_exists:
    make_program_exist_type PIPC_module pipcintro pipc.
  Proof.
    make_program_exists link_correct_aux.
  Qed.
End WITHCOMPCERTIKOS.
