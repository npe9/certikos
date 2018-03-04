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
(* *********************************************************************)
(*                                                                     *)
(*              Layers of VMM                                          *)
(*                                                                     *)
(*          Refinement Proof for TrapArg                               *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import Asm.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Values.
Require Import Memory.
Require Import Maps.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import FlatMemory.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import RealParams.
Require Import AsmImplLemma.
Require Import GenSem.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import XOmega.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import compcert.cfrontend.Ctypes.

(*Require Import LAsmModuleSemAux.*)
Require Import LayerCalculusLemma.
Require Import AbstractDataType.

Require Import LoadStoreSem2.

Require Import TDispatch.
Require Export TrapGen.
Require Import DispatchGenSpec.

(** * Definition of the refinement relation*)
Section Refinement.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.
  
  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := pproc_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := pproc_data_ops) LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** * Proofs the one-step forward simulations for the low level specifications*)
    Section OneStep_Forward_Relation.

      Section FRESH_PIM.

        Lemma sys_dispatch_c_kernel_mode:
          forall d2 d2' v1 v2,
            sys_dispatch_c_spec v1 v2 d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          unfold sys_dispatch_c_spec. intros.
          destruct (uctx_arg1_spec d2) eqn:Hdestruct; try discriminate.
          functional inversion Hdestruct; subst; simpl; auto.
        Qed.

        Lemma sys_dispatch_c_spec_ref:
          compatsim (crel HDATA LDATA) (trap_proccreate_compatsem sys_dispatch_c_spec) sys_dispatch_c_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit sys_dispatch_c_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply sys_dispatch_c_kernel_mode; eassumption.
          - constructor.
        Qed.

        Lemma trap_sendtochan_post_kernel_mode:
          forall d2 d2',
            trap_sendtochan_post_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          unfold trap_sendtochan_post_spec. intros.
          subdestruct. unfold syncsendto_chan_post_spec in *.
          subdestruct; eauto.
        Qed.

        Lemma trap_sendtochan_post_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_sendtochan_post_spec) trap_sendtochan_post_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_sendtochan_post_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_sendtochan_post_kernel_mode; eassumption.
          - constructor.
        Qed.

        Lemma trap_sendtochan_pre_kernel_mode:
          forall d2 d2' r,
            trap_sendtochan_pre_spec d2 = Some (d2', r)
            -> kernel_mode d2.
        Proof.
          unfold trap_sendtochan_pre_spec. intros.
          subdestruct. unfold syncsendto_chan_pre_spec in *.
          subdestruct; eauto.
        Qed.

        Lemma trap_sendtochan_pre_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_sendtochan_pre_spec) trap_sendtochan_pre_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_sendtochan_pre_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_sendtochan_pre_kernel_mode; eassumption.
          - constructor.
        Qed.

      End FRESH_PIM.

      Lemma passthrough_correct:
        sim (crel HDATA LDATA) tdispatch_passthrough ttrap.
      Proof.
        sim_oplus.
        - apply fload_sim.
        - apply fstore_sim.
        (*- apply print_sim.*)
        (*- apply pfree_sim.*)
        - apply ptRead_sim.
        - apply alloc_sim.
        (*- apply shared_mem_status_sim.
        - apply offer_shared_mem_sim.*)
        - apply get_curid_sim.
        - apply thread_wakeup_sim.

        - apply syncsendto_chan_pre_sim.
        - apply syncsendto_chan_post_sim.

        - apply uctx_get_sim.
        - apply uctx_set_sim.
        (*- apply vm_run_sim, VMX_INJECT.
        - apply vmx_return_from_guest_sim, VMX_INJECT.
        - apply vmx_init_sim.*)
        - apply proc_init_sim.
        - apply uctx_arg1_sim.
          intros. eapply valid_curid; eauto.
        - apply uctx_arg2_sim.
          intros. eapply valid_curid; eauto.
        - apply uctx_arg3_sim.
          intros. eapply valid_curid; eauto.
        - apply uctx_arg4_sim.
          intros. eapply valid_curid; eauto.
        - apply uctx_arg5_sim.
          intros. eapply valid_curid; eauto.
        - apply uctx_set_errno_sim.
          intros. eapply valid_curid; eauto.
        - apply uctx_set_retval1_sim.
          intros. eapply valid_curid; eauto.
        - apply ptfault_resv_sim.
          intros. eapply valid_curid; eauto.
        - apply trap_info_get_sim.
        - apply trap_info_ret_sim.
        - apply thread_yield_sim.
        - apply thread_sleep_sim.
        - apply proc_start_user_sim.
          intros. eapply valid_curid; eauto.
        - apply proc_exit_user_sim. 
        - layer_sim_simpl.
          + eapply load_correct2.
          + eapply store_correct2.
      Qed.

    End OneStep_Forward_Relation.

  End WITHMEM.

End Refinement.