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

Require Import TTrap.
Require Export TrapArgGen.
Require Import TrapGenSpec.

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

        Lemma trap_get_quota_kernel_mode:
          forall d2 d2',
            trap_get_quota_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          unfold trap_get_quota_spec. intros.
          destruct (get_curid_spec d2) eqn:Hdestruct; try discriminate.
          functional inversion Hdestruct; subst; simpl; auto.
        Qed.

        Lemma trap_get_quota_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_get_quota_spec) trap_get_quota_spec_low.
        Proof.
          compatsim_simpl (@match_AbData).
          exploit trap_get_quota_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_get_quota_kernel_mode; eassumption.
          - constructor.
        Qed.

        Lemma trap_offer_shared_mem_kernel_mode:
          forall d2 d2',
            trap_offer_shared_mem_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          unfold trap_offer_shared_mem_spec. intros.
          destruct (uctx_arg2_spec d2) eqn:Hdestruct; try discriminate.
          functional inversion Hdestruct; subst; simpl; auto.
        Qed.

        Lemma trap_offer_shared_mem_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_offer_shared_mem_spec) trap_offer_shared_mem_spec_low.
        Proof.
          compatsim_simpl (@match_AbData).
          exploit trap_offer_shared_mem_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_offer_shared_mem_kernel_mode; eassumption.
          - constructor.
        Qed.

        Lemma print_kernel_mode:
          forall d d',
            print_spec d = Some d'
            -> kernel_mode d.
        Proof.
          unfold print_spec; intros.
          destruct (uctx_arg2_spec d) eqn:Hdestruct; try discriminate.
          functional inversion Hdestruct; subst; simpl; auto.
        Qed.

        Lemma print_spec_ref:
          compatsim (crel HDATA LDATA) (gensem print_spec) print_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit print_exist; eauto 1.
          try eapply valid_curid; eauto 1.
          intros (labd' & HP  & HM).
          refine_split; try econstructor; eauto. 
          - eapply print_kernel_mode; eauto.
          - constructor.
        Qed.

        (*Lemma trap_ischanready_kernel_mode:
          forall d2 d2',
            trap_ischanready_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H. functional inversion H1;
          subst; simpl; auto.
        Qed.

        Lemma trap_ischanready_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_ischanready_spec) trap_ischanready_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_ischanready_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_ischanready_kernel_mode; eassumption.
          - constructor.
        Qed.*)

        (*Lemma trap_mmap_kernel_mode:
          forall d2 d2',
            trap_mmap_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H;
          functional inversion H1; subst; simpl; auto.
        Qed.

        Lemma trap_mmap_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_mmap_spec) trap_mmap_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_mmap_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_mmap_kernel_mode; eassumption.
          - constructor.
        Qed.*)

        (*Lemma trap_sendtochan_kernel_mode:
          forall d2 d2',
            trap_sendtochan_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H.
          functional inversion H1; subst; simpl; auto.
        Qed.

        Lemma trap_sendtochan_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_sendtochan_spec) trap_sendtochan_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_sendtochan_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_sendtochan_kernel_mode; eassumption.
          - constructor.
        Qed.*)

        Lemma trap_receivechan_kernel_mode:
          forall d2 d2',
            trap_receivechan_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H.
          functional inversion H1; subst; simpl; auto.
        Qed.

        Lemma trap_receivechan_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_receivechan_spec) trap_receivechan_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_receivechan_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_receivechan_kernel_mode; eassumption.
          - constructor.
        Qed.

        (*Lemma trap_intercept_int_window_kernel_mode:
          forall d2 d2',
            trap_intercept_int_window_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H.
          functional inversion H1; subst; simpl; auto.
        Qed.

        Lemma trap_intercept_int_window_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_intercept_int_window_spec) trap_intercept_int_window_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_intercept_int_window_exist; try apply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_intercept_int_window_kernel_mode; eassumption.
          - constructor.
        Qed.

        Lemma trap_inject_event_kernel_mode:
          forall d2 d2',
            trap_inject_event_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H.
          functional inversion H2; subst; simpl; auto.
        Qed.

        Lemma trap_inject_event_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_inject_event_spec) trap_inject_event_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_inject_event_exist; try apply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_inject_event_kernel_mode; eassumption.
          - constructor.
        Qed.

        Lemma trap_check_int_shadow_kernel_mode:
          forall d2 d2',
            trap_check_int_shadow_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H.
          functional inversion H2; subst; simpl; auto.
        Qed.

        Lemma trap_check_int_shadow_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_check_int_shadow_spec) trap_check_int_shadow_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_check_int_shadow_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_check_int_shadow_kernel_mode; eassumption.
          - constructor.
        Qed.

        Lemma trap_check_pending_event_kernel_mode:
          forall d2 d2',
            trap_check_pending_event_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H.
          functional inversion H2; subst; simpl; auto.
        Qed.

        Lemma trap_check_pending_event_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_check_pending_event_spec) trap_check_pending_event_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_check_pending_event_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_check_pending_event_kernel_mode; eassumption.
          - constructor.
        Qed.

        Lemma trap_get_next_eip_kernel_mode:
          forall d2 d2',
            trap_get_next_eip_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H.
          functional inversion H1; subst; simpl; auto.
        Qed.

        Lemma trap_get_next_eip_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_get_next_eip_spec) trap_get_next_eip_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_get_next_eip_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_get_next_eip_kernel_mode; eassumption.
          - constructor.
        Qed.

        Lemma trap_get_reg_kernel_mode:
          forall d2 d2',
            trap_get_reg_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H;
          functional inversion H1; subst; simpl; auto.
        Qed.

        Lemma trap_get_reg_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_get_reg_spec) trap_get_reg_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_get_reg_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM  & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_get_reg_kernel_mode; eauto.
          - constructor.
        Qed.

        Lemma trap_set_reg_kernel_mode:
          forall d2 d2',
            trap_set_reg_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H;
          functional inversion H1; subst; simpl; auto.
        Qed.

        Lemma trap_set_reg_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_set_reg_spec) trap_set_reg_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_set_reg_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_set_reg_kernel_mode; eassumption.
          - constructor.
        Qed.

        Lemma trap_set_seg_kernel_mode:
          forall d2 d2',
            trap_set_seg_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H;
          functional inversion H1; subst; simpl; auto.
        Qed.

        Lemma trap_set_seg_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_set_seg_spec) trap_set_seg_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_set_seg_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_set_seg_kernel_mode; eassumption.
          - constructor.
        Qed.

        Lemma trap_get_tsc_offset_kernel_mode:
          forall d2 d2',
            trap_get_tsc_offset_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H.
          functional inversion H2; subst; simpl; auto.
        Qed.

        Lemma trap_get_tsc_offset_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_get_tsc_offset_spec) trap_get_tsc_offset_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_get_tsc_offset_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_get_tsc_offset_kernel_mode; eassumption.
          - constructor.
        Qed.

        Lemma trap_set_tsc_offset_kernel_mode:
          forall d2 d2',
            trap_set_tsc_offset_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H.
          clear dependent ofs.
          functional inversion H1; subst; simpl; auto.
        Qed.

        Lemma trap_set_tsc_offset_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_set_tsc_offset_spec) trap_set_tsc_offset_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_set_tsc_offset_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_set_tsc_offset_kernel_mode; eassumption.
          - constructor.
        Qed.

        Lemma trap_get_exitinfo_kernel_mode:
          forall d2 d2',
            trap_get_exitinfo_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H;
          functional inversion H1; subst; simpl; auto.
        Qed.

        Lemma trap_get_exitinfo_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_get_exitinfo_spec) trap_get_exitinfo_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_get_exitinfo_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_get_exitinfo_kernel_mode; eassumption.
          - constructor.
        Qed.

        Lemma trap_handle_rdmsr_kernel_mode:
          forall d2 d2',
            trap_handle_rdmsr_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H.
          functional inversion H1; subst; simpl; auto.
        Qed.

        Lemma trap_handle_rdmsr_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_handle_rdmsr_spec) trap_handle_rdmsr_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_handle_rdmsr_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_handle_rdmsr_kernel_mode; eassumption.
          - constructor.
        Qed.

        Lemma trap_handle_wrmsr_kernel_mode:
          forall d2 d2',
            trap_handle_wrmsr_spec d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H.
          functional inversion H1; subst; simpl; auto.
        Qed.

        Lemma trap_handle_wrmsr_spec_ref:
          compatsim (crel HDATA LDATA) (gensem trap_handle_wrmsr_spec) trap_handle_wrmsr_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_handle_wrmsr_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_handle_wrmsr_kernel_mode; eassumption.
          - constructor.
        Qed.*)

        Lemma ptfault_resv_kernel_mode:
          forall d2 d2' v,
            ptfault_resv_spec v d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H.
          - functional inversion H5.
            + functional inversion H8; subst; simpl; auto.
            + functional inversion H7; subst; simpl; auto.
          - subst; simpl; auto.
        Qed.

        Lemma ptf_resv_spec_ref:
          compatsim (crel HDATA LDATA) (gensem ptfault_resv_spec) ptf_resv_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit ptfault_resv_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply ptfault_resv_kernel_mode; eassumption.
          - constructor.
        Qed.

        Lemma trap_proc_create_kernel_mode:
          forall d2 d2' v1 v2,
            trap_proc_create_spec v1 v2 d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          unfold trap_proc_create_spec. intros.
          destruct (uctx_arg2_spec d2) eqn:Hdestruct; try discriminate.
          functional inversion Hdestruct; subst; simpl; auto.
          unfold uctx_set_errno_spec in H; subdestruct; auto.
        Qed.

        Lemma trap_proc_create_spec_ref:
          compatsim (crel HDATA LDATA) (trap_proccreate_compatsem trap_proc_create_spec) trap_proc_create_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit trap_proc_create_exist; try eapply valid_curid; eauto 1.
          intros (labd' & HM & HR).
          refine_split; try econstructor; eauto.
          - eapply trap_proc_create_kernel_mode; eassumption.
          - constructor.
        Qed.

        (*Lemma ptfault_resv_spec_ref:
          compatsim (crel HDATA LDATA) (gensem (fun a d => ptfault_resv_spec d a)) ptf_resv_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit ptfault_resv_exist; eauto 1.
          intros [labd' [labd0[s1[s2[HM Hkern]]]]].
          refine_split; try econstructor; eauto. constructor.
        Qed.

        Lemma trap_proc_create_spec_ref:
          compatsim (crel HDATA LDATA) trap_proccreate_compatsem trap_proc_create_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit uctx_arg1_exist; eauto.
          intros [HW1 HK]. 
          exploit proc_create_exist; eauto.
          intros [labd0[s1[Hr1 _]]]. 
          
          assert (high_level_invariant abd').
          {
            destruct proc_create_inv.
            eapply pcreate_high_level_invariant; eauto.
          }
          exploit uctx_set_retval1_exist; eauto.
          intros [labd' [Hpt [Hr _]]].
          exploit uctx_set_errno_exist; eauto.
          eapply uctx_set_retval1_high_inv; eauto.
          intros [labd'' [Hpt' [Hr' _]]].
          refine_split; try econstructor; eauto. 
          - destruct HFUNID as [fun_id HFUNID].
            exploit (stencil_find_symbol_inject' s ι ELF_ENTRY_LOC bentry); eauto.
            intros HFB. eapply Mem.load_inject in H8; eauto.
            destruct H8 as [v2[HLD HV]].
            rewrite Z.add_0_r in HLD.
            rewrite HLD.
            inv HV; eauto.
            eapply inject_forward_equal' in H2; eauto.
            inv H2. rewrite Int.add_zero. trivial.
          - constructor.
        Qed.*)

      End FRESH_PIM.

      Lemma passthrough_correct:
        sim (crel HDATA LDATA) ttrap_passthrough ttraparg.
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
