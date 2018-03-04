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
(*              Layers of Trap: TTrapArg                               *)
(*                                                                     *)
(*          Provide the initialization of vmcb                         *)
(*                                                                     *)
(*          Haozhong Zhang <haozhong.zhang@yale.edu>                   *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)
Require Import Coqlib.
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Stacklayout.
Require Import Globalenvs.
Require Import AsmX.
Require Import Smallstep.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import FlatMemory.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import PrimSemantics.
Require Import LAsm.
Require Import XOmega.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import CalRealPTPool.
Require Import CalRealPT.
Require Import CalRealIDPDE.
Require Import CalRealInitPTE.
Require Import CalRealSMSPool.
Require Import CalRealProcModule.

Require Import INVLemmaMemory.
Require Import INVLemmaThread.
Require Import INVLemmaProc.
(*Require Import INVLemmaIntel.*)

Require Import AbstractDataType.

Require Import LoadStoreSem2.
Require Export PProc.
Require Export ObjArg.

(** * Abstract Data and Primitives at this layer*)
Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section INV.

    Lemma uctxt_inject_neutral_gss_arg:
      forall up n,
        uctxt_inject_neutral up n ->
        forall i ii v,
          uctxt_inject_neutral (ZMap.set i (ZMap.set ii (Vint v) (ZMap.get i up)) up) n.
    Proof.
      unfold uctxt_inject_neutral. intros.
      destruct (zeq i ii0); subst.
      - rewrite ZMap.gss; eauto.
        destruct (zeq ii ii'); subst.
        + rewrite ZMap.gss. split; constructor.
        + rewrite ZMap.gso; eauto.
      - rewrite ZMap.gso; eauto.
    Qed.

    Section SET_ERRNO.

      Lemma uctx_set_errno_high_inv:
        forall d d' i0,
          uctx_set_errno_spec i0 d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. inv H0; functional inversion H; subst; simpl.
        constructor; simpl; intros; try congruence; eauto 2.
      Qed.

      Lemma uctx_set_errno_low_inv:
        forall d d' i0 n,
          uctx_set_errno_spec i0 d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. inv H0; functional inversion H; subst; simpl.
        constructor; simpl; intros; try congruence; eauto 2.
        eapply uctxt_inject_neutral_gss_arg; eauto.
      Qed.

      Lemma uctx_set_errno_kernel_mode:
        forall d d' i0,
          uctx_set_errno_spec i0 d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; constructor; trivial.
      Qed.

    Global Instance uctx_set_errno_inv: PreservesInvariants uctx_set_errno_spec.
    Proof.
      preserves_invariants_simpl'.
      - eapply uctx_set_errno_low_inv; eauto.
      - eapply uctx_set_errno_high_inv; eauto.
      - eapply uctx_set_errno_kernel_mode; eauto.
    Qed.

    End SET_ERRNO.

    Section SET_RETVAL1.

      Lemma uctx_set_retval1_high_inv:
        forall d d' i0,
          uctx_set_retval1_spec i0 d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. inv H0; functional inversion H; subst; simpl.
        constructor; simpl; intros; try congruence; eauto 2.
      Qed.

      Lemma uctx_set_retval1_low_inv:
        forall d d' i0 n,
          uctx_set_retval1_spec i0 d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. inv H0; functional inversion H; subst; simpl.
        constructor; simpl; intros; try congruence; eauto 2.
        eapply uctxt_inject_neutral_gss_arg; eauto.
      Qed.

      Lemma uctx_set_retval1_kernel_mode:
        forall d d' i0,
          uctx_set_retval1_spec i0 d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; constructor; trivial.
      Qed.

      Global Instance uctx_set_retval1_inv: PreservesInvariants uctx_set_retval1_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply uctx_set_retval1_low_inv; eauto.
        - eapply uctx_set_retval1_high_inv; eauto.
        - eapply uctx_set_retval1_kernel_mode; eauto.
      Qed.

    End SET_RETVAL1.

    Section SET_RETVAL2.

      Lemma uctx_set_retval2_high_inv:
        forall d d' i0,
          uctx_set_retval2_spec i0 d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. inv H0; functional inversion H; subst; simpl.
        constructor; simpl; intros; try congruence; eauto 2.
      Qed.

      Lemma uctx_set_retval2_low_inv:
        forall d d' i0 n,
          uctx_set_retval2_spec i0 d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. inv H0; functional inversion H; subst; simpl.
        constructor; simpl; intros; try congruence; eauto 2.
        eapply uctxt_inject_neutral_gss_arg; eauto.
      Qed.

      Lemma uctx_set_retval2_kernel_mode:
        forall d d' i0,
          uctx_set_retval2_spec i0 d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; constructor; trivial.
      Qed.

      Global Instance uctx_set_retval2_inv: PreservesInvariants uctx_set_retval2_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply uctx_set_retval2_low_inv; eauto.
        - eapply uctx_set_retval2_high_inv; eauto.
        - eapply uctx_set_retval2_kernel_mode; eauto.
      Qed.

    End SET_RETVAL2.

    Section SET_RETVAL3.

      Lemma uctx_set_retval3_high_inv:
        forall d d' i0,
          uctx_set_retval3_spec i0 d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. inv H0; functional inversion H; subst; simpl.
        constructor; simpl; intros; try congruence; eauto 2.
      Qed.

      Lemma uctx_set_retval3_low_inv:
        forall d d' i0 n,
          uctx_set_retval3_spec i0 d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. inv H0; functional inversion H; subst; simpl.
        constructor; simpl; intros; try congruence; eauto 2.
        eapply uctxt_inject_neutral_gss_arg; eauto.
      Qed.

      Lemma uctx_set_retval3_kernel_mode:
        forall d d' i0,
          uctx_set_retval3_spec i0 d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; constructor; trivial.
      Qed.

      Global Instance uctx_set_retval3_inv: PreservesInvariants uctx_set_retval3_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply uctx_set_retval3_low_inv; eauto.
        - eapply uctx_set_retval3_high_inv; eauto.
        - eapply uctx_set_retval3_kernel_mode; eauto.
      Qed.

    End SET_RETVAL3.

    Section SET_RETVAL4.

      Lemma uctx_set_retval4_high_inv:
        forall d d' i0,
          uctx_set_retval4_spec i0 d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. inv H0; functional inversion H; subst; simpl.
        constructor; simpl; intros; try congruence; eauto 2.
      Qed.

      Lemma uctx_set_retval4_low_inv:
        forall d d' i0 n,
          uctx_set_retval4_spec i0 d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. inv H0; functional inversion H; subst; simpl.
        constructor; simpl; intros; try congruence; eauto 2.
        eapply uctxt_inject_neutral_gss_arg; eauto.
      Qed.

      Lemma uctx_set_retval4_kernel_mode:
        forall d d' i0,
          uctx_set_retval4_spec i0 d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; constructor; trivial.
      Qed.

      Global Instance uctx_set_retval4_inv: PreservesInvariants uctx_set_retval4_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply uctx_set_retval4_low_inv; eauto.
        - eapply uctx_set_retval4_high_inv; eauto.
        - eapply uctx_set_retval4_kernel_mode; eauto.
      Qed.

    End SET_RETVAL4.

  End INV.

  (** These should be put into mcertikos.layerlib.GlobIdent *)  
  Definition ttraparg_fresh : compatlayer (cdata RData) :=
    uctx_arg1  ↦ gensem uctx_arg1_spec
               ⊕ uctx_arg2  ↦ gensem uctx_arg2_spec
               ⊕ uctx_arg3  ↦ gensem uctx_arg3_spec
               ⊕ uctx_arg4  ↦ gensem uctx_arg4_spec
               ⊕ uctx_arg5  ↦ gensem uctx_arg5_spec
               ⊕ uctx_arg6  ↦ gensem uctx_arg6_spec
               ⊕ uctx_set_errno  ↦ gensem uctx_set_errno_spec
               ⊕ uctx_set_retval1  ↦ gensem uctx_set_retval1_spec
               ⊕ uctx_set_retval2  ↦ gensem uctx_set_retval2_spec
               ⊕ uctx_set_retval3  ↦ gensem uctx_set_retval3_spec
               ⊕ uctx_set_retval4  ↦ gensem uctx_set_retval4_spec.
               (*⊕ la2pa_resv  ↦ gensem (fun a d => la2pa_resv_spec d a).*)

  Definition ttraparg_passthrough : compatlayer (cdata RData) :=
    fload ↦ gensem fload_spec
          ⊕ fstore ↦ gensem fstore_spec
          ⊕ device_output ↦ gensem device_output_spec
          ⊕ pt_read ↦ gensem ptRead_spec
          ⊕ pt_resv ↦ gensem ptResv_spec
          ⊕ shared_mem_status ↦ gensem shared_mem_status_spec
          ⊕ offer_shared_mem ↦ gensem offer_shared_mem_spec
          ⊕ get_curid ↦ gensem get_curid_spec
          ⊕ thread_wakeup ↦ gensem thread_wakeup_spec

          (*⊕ is_chan_ready ↦ gensem is_chan_ready_spec
          ⊕ sendto_chan ↦ gensem sendto_chan_spec
          ⊕ receive_chan ↦ gensem receive_chan_spec*)
          ⊕ syncreceive_chan ↦ gensem syncreceive_chan_spec
          ⊕ syncsendto_chan_pre ↦ gensem syncsendto_chan_pre_spec
          ⊕ syncsendto_chan_post ↦ gensem syncsendto_chan_post_spec

          ⊕ uctx_get ↦ gensem uctx_get_spec
          ⊕ uctx_set ↦ gensem uctx_set_spec
          ⊕ proc_create ↦ proc_create_compatsem proc_create_spec
          (*⊕ rdmsr ↦ gensem rdmsr_spec
          ⊕ wrmsr ↦ gensem wrmsr_spec

          ⊕ vmx_set_intercept_intwin ↦ gensem vmx_set_intercept_intwin_spec
          ⊕ vmx_set_desc ↦ gensem vmx_set_desc_spec
          ⊕ vmx_inject_event ↦ gensem vmx_inject_event_spec
          ⊕ vmx_set_tsc_offset ↦ gensem vmx_set_tsc_offset_spec
          ⊕ vmx_get_tsc_offset ↦ gensem vmx_get_tsc_offset_spec
          ⊕ vmx_get_exit_reason ↦ gensem vmx_get_exit_reason_spec
          ⊕ vmx_get_exit_fault_addr ↦ gensem vmx_get_exit_fault_addr_spec
          ⊕ vmx_check_pending_event ↦ gensem vmx_check_pending_event_spec
          ⊕ vmx_check_int_shadow ↦ gensem vmx_check_int_shadow_spec
          ⊕ vmx_get_reg ↦ gensem vmx_get_reg_spec
          ⊕ vmx_set_reg ↦ gensem vmx_set_reg_spec
          ⊕ vmx_get_next_eip ↦ gensem vmx_get_next_eip_spec
          ⊕ vmx_get_io_width ↦ gensem vmx_get_io_width_spec
          ⊕ vmx_get_io_write ↦ gensem vmx_get_io_write_spec
          ⊕ vmx_get_exit_io_rep ↦ gensem vmx_get_exit_io_rep_spec
          ⊕ vmx_get_exit_io_str ↦ gensem vmx_get_exit_io_str_spec
          ⊕ vmx_get_exit_io_port ↦ gensem vmx_get_exit_io_port_spec
          ⊕ vmx_set_mmap ↦ gensem vmx_set_mmap_spec
          ⊕ vmx_run_vm ↦ primcall_vmx_enter_compatsem vm_run_spec vmx_run_vm
          ⊕ vmx_return_from_guest ↦ primcall_vmx_return_compatsem vmx_return_from_guest_spec vmx_return_from_guest
          ⊕ vmx_init ↦ vmcs_set_defaults_compatsem vmx_init_spec
          ⊕ vmx_return_from_guest ↦ primcall_vmx_return_compatsem vmx_return_from_guest_spec vmx_return_from_guest*)
          ⊕ proc_init ↦ gensem proc_init_spec
          ⊕ container_get_nchildren ↦ gensem container_get_nchildren_spec
          ⊕ container_get_quota ↦ gensem container_get_quota_spec
          ⊕ container_get_usage ↦ gensem container_get_usage_spec
          ⊕ container_can_consume ↦ gensem container_can_consume_spec
          ⊕ container_alloc ↦ gensem alloc_spec
          ⊕ trap_get ↦ primcall_trap_info_get_compatsem trap_info_get_spec
          ⊕ trap_set ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec
          ⊕ thread_yield ↦ primcall_thread_schedule_compatsem thread_yield_spec (prim_ident:= thread_yield)
          ⊕ thread_sleep ↦ primcall_thread_transfer_compatsem thread_sleep_spec
          ⊕ proc_start_user ↦ primcall_start_user_compatsem proc_start_user_spec
          ⊕ proc_exit_user ↦ primcall_exit_user_compatsem proc_exit_user_spec
          (*⊕ vmcs_read ↦ primcall_vmcs_read_compatsem vmcs_read_spec
          ⊕ vmcs_write ↦ primcall_vmcs_write_compatsem vmcs_write_spec*)
          ⊕ accessors ↦ {| exec_load := (@exec_loadex _ _ Hmwd); 
                           exec_store := (@exec_storeex _ _ Hmwd) |}.

  Definition ttraparg : compatlayer (cdata RData) := ttraparg_fresh ⊕ ttraparg_passthrough.

End WITHMEM.
