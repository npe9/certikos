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
(*              Layers of Trap: Trap                                   *)
(*                                                                     *)
(*          Provide the initialization of vmcb                         *)
(*                                                                     *)
(*          Haozhong Zhang <haozhong.zhang@yale.edu>                   *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the abstract data and the primitives for the VVMCBInit layer,
which will introduce the primtives of thread*)
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
Require Export TTrap.

(** * Abstract Data and Primitives at this layer*)
Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section Prim.
 
    Section TRAP_CHAN_SENDTOPOST.

      Lemma trap_sendtochan_post_high_inv:
        forall d d',
          trap_sendtochan_post_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_high_inv; eauto.
        eapply uctx_set_retval1_high_inv; eauto.
        eapply syncsendto_chan_post_high_inv; eauto.
      Qed.

      Lemma trap_sendtochan_post_low_inv:
        forall d d' n,
          trap_sendtochan_post_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_low_inv; eauto.
        eapply uctx_set_retval1_low_inv; eauto.
        eapply syncsendto_chan_post_low_inv; eauto.
      Qed.

      Lemma trap_sendtochan_post_kernel_mode:
        forall d d',
          trap_sendtochan_post_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst.
        eapply uctx_set_errno_kernel_mode; eauto.
        eapply uctx_set_retval1_kernel_mode; eauto.
        eapply syncsendto_chan_post_kernel_mode; eauto.
      Qed.

      Global Instance trap_sendtochan_post_inv: PreservesInvariants trap_sendtochan_post_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_sendtochan_post_low_inv; eauto.
        - eapply trap_sendtochan_post_high_inv; eauto.
        - eapply trap_sendtochan_post_kernel_mode; eauto.
      Qed.

    End TRAP_CHAN_SENDTOPOST.

    Section TRAP_CHAN_SENDTOPRE.

      Lemma trap_sendtochan_pre_high_inv:
        forall d d' r,
          trap_sendtochan_pre_spec d = Some (d', r)->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply syncsendto_chan_pre_high_inv; eauto.
      Qed.

      Lemma trap_sendtochan_pre_low_inv:
        forall d d' n r,
          trap_sendtochan_pre_spec d = Some (d', r)->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply syncsendto_chan_pre_low_inv; eauto.
      Qed.

      Lemma trap_sendtochan_pre_kernel_mode:
        forall d d' r,
          trap_sendtochan_pre_spec d = Some (d', r)->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst.
        eapply syncsendto_chan_pre_kernel_mode; eauto.
      Qed.

      Global Instance trap_sendtochan_pre_inv: PreservesInvariants trap_sendtochan_pre_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_sendtochan_pre_low_inv; eauto.
        - eapply trap_sendtochan_pre_high_inv; eauto.
        - eapply trap_sendtochan_pre_kernel_mode; eauto.
      Qed.

    End TRAP_CHAN_SENDTOPRE.

    Global Instance sys_dispatch_c_inv: TrapProcCreateINV sys_dispatch_c_spec.
    Proof.
      destruct trap_proc_create_inv.
      split; unfold sys_dispatch_c_spec; intros.
      - (* high level inv *)
        subdestruct; try (eapply uctx_set_errno_high_inv; eauto; fail).
        + eapply trap_proc_create_high_inv; eauto.
        (*+ eapply trap_get_tsc_offset_high_inv; eauto.
        + eapply trap_set_tsc_offset_high_inv; eauto.
        + eapply trap_get_exitinfo_high_inv; eauto.
        + eapply trap_mmap_high_inv; eauto.
        + eapply trap_set_reg_high_inv; eauto.
        + eapply trap_get_reg_high_inv; eauto.
        + eapply trap_set_seg_high_inv; eauto.
        + eapply trap_get_next_eip_high_inv; eauto.
        + eapply trap_inject_event_high_inv; eauto.
        + eapply trap_check_pending_event_high_inv; eauto.
        + eapply trap_check_int_shadow_high_inv; eauto.
        + eapply trap_intercept_int_window_high_inv; eauto.
        + eapply trap_handle_rdmsr_high_inv; eauto.
        + eapply trap_handle_wrmsr_high_inv; eauto.          *)
        + eapply trap_get_quota_high_inv; eauto.
        (*+ eapply trap_ischanready_high_inv; eauto.
        + eapply trap_sendtochan_high_inv; eauto.
        + eapply trap_receivechan_high_inv; eauto.*)

        + eapply trap_offer_shared_mem_high_inv; eauto.
        + eapply print_high_inv; eauto.

      - (* low level inv *)
        subdestruct; try (eapply uctx_set_errno_low_inv; eauto; fail).
        + eapply trap_proc_create_low_inv; eauto.
        (*+ eapply trap_get_tsc_offset_low_inv; eauto.
        + eapply trap_set_tsc_offset_low_inv; eauto.
        + eapply trap_get_exitinfo_low_inv; eauto.
        + eapply trap_mmap_low_inv; eauto.
        + eapply trap_set_reg_low_inv; eauto.
        + eapply trap_get_reg_low_inv; eauto.
        + eapply trap_set_seg_low_inv; eauto.
        + eapply trap_get_next_eip_low_inv; eauto.
        + eapply trap_inject_event_low_inv; eauto.
        + eapply trap_check_pending_event_low_inv; eauto.
        + eapply trap_check_int_shadow_low_inv; eauto.
        + eapply trap_intercept_int_window_low_inv; eauto.
        + eapply trap_handle_rdmsr_low_inv; eauto.
        + eapply trap_handle_wrmsr_low_inv; eauto.          *)
        + eapply trap_get_quota_low_inv; eauto.
        (*+ eapply trap_ischanready_low_inv; eauto.
        + eapply trap_sendtochan_low_inv; eauto.
        + eapply trap_receivechan_low_inv; eauto.*)

        + eapply trap_offer_shared_mem_low_inv; eauto.
        + eapply print_low_inv; eauto.

      - (* kernel mode *)
        subdestruct; try (eapply uctx_set_errno_kernel_mode; eauto; fail).
        + eapply trap_proc_create_kernel_mode; eauto.
        (*+ eapply trap_get_tsc_offset_kernel_mode; eauto.
        + eapply trap_set_tsc_offset_kernel_mode; eauto.
        + eapply trap_get_exitinfo_kernel_mode; eauto.
        + eapply trap_mmap_kernel_mode; eauto.
        + eapply trap_set_reg_kernel_mode; eauto.
        + eapply trap_get_reg_kernel_mode; eauto.
        + eapply trap_set_seg_kernel_mode; eauto.
        + eapply trap_get_next_eip_kernel_mode; eauto.
        + eapply trap_inject_event_kernel_mode; eauto.
        + eapply trap_check_pending_event_kernel_mode; eauto.
        + eapply trap_check_int_shadow_kernel_mode; eauto.
        + eapply trap_intercept_int_window_kernel_mode; eauto.
        + eapply trap_handle_rdmsr_kernel_mode; eauto.
        + eapply trap_handle_wrmsr_kernel_mode; eauto.          *)
        + eapply trap_get_quota_kernel_mode; eauto.
        (*+ eapply trap_ischanready_kernel_mode; eauto.
        + eapply trap_sendtochan_kernel_mode; eauto.
        + eapply trap_receivechan_kernel_mode; eauto.*)

        + eapply trap_offer_shared_mem_kernel_mode; eauto.
        + eapply print_kernel_mode; eauto.

      - (* Mem.extend *)
        subdestruct; eauto.
      - (* Mem.inject *)
        subdestruct; eauto.
    Qed.

  End Prim.

  (** * Layer Definition *)
  Definition tdispatch_fresh : compatlayer (cdata RData) :=
    syscall_dispatch_C  ↦ trap_proccreate_compatsem sys_dispatch_c_spec
                        ⊕ trap_sendtochan_pre  ↦ gensem trap_sendtochan_pre_spec
                        ⊕ trap_sendtochan_post  ↦ gensem trap_sendtochan_post_spec.

  (** * Layer Definition *)
  Definition tdispatch_passthrough : compatlayer (cdata RData) :=
    fload ↦ gensem fload_spec
          ⊕ fstore ↦ gensem fstore_spec
          (*⊕ print ↦ gensem print_spec*)
          ⊕ pt_read ↦ gensem ptRead_spec
          ⊕ container_alloc ↦ gensem alloc_spec
          (*⊕ shared_mem_status ↦ gensem shared_mem_status_spec
          ⊕ offer_shared_mem ↦ gensem offer_shared_mem_spec*)
          ⊕ get_curid ↦ gensem get_curid_spec
          ⊕ thread_wakeup ↦ gensem thread_wakeup_spec

          ⊕ syncsendto_chan_pre ↦ gensem syncsendto_chan_pre_spec
          ⊕ syncsendto_chan_post ↦ gensem syncsendto_chan_post_spec

          ⊕ uctx_get ↦ gensem uctx_get_spec
          ⊕ uctx_set ↦ gensem uctx_set_spec

          (*⊕ vmx_run_vm ↦ primcall_vmx_enter_compatsem vm_run_spec vmx_run_vm
          ⊕ vmx_return_from_guest ↦ primcall_vmx_return_compatsem vmx_return_from_guest_spec vmx_return_from_guest
          ⊕ vmx_init ↦ vmcs_set_defaults_compatsem vmx_init_spec*)
          ⊕ proc_init ↦ gensem proc_init_spec
          ⊕ uctx_arg1  ↦ gensem uctx_arg1_spec
          ⊕ uctx_arg2  ↦ gensem uctx_arg2_spec
          ⊕ uctx_arg3  ↦ gensem uctx_arg3_spec
          ⊕ uctx_arg4  ↦ gensem uctx_arg4_spec
          ⊕ uctx_arg5  ↦ gensem uctx_arg5_spec
          ⊕ uctx_set_errno  ↦ gensem uctx_set_errno_spec
          ⊕ uctx_set_retval1  ↦ gensem uctx_set_retval1_spec
          ⊕ ptfault_resv  ↦ gensem ptfault_resv_spec

          ⊕ trap_get ↦ primcall_trap_info_get_compatsem trap_info_get_spec
          ⊕ trap_set ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec
          ⊕ thread_yield ↦ primcall_thread_schedule_compatsem thread_yield_spec (prim_ident:= thread_yield)
          ⊕ thread_sleep ↦ primcall_thread_transfer_compatsem thread_sleep_spec
          ⊕ proc_start_user ↦ primcall_start_user_compatsem proc_start_user_spec
          ⊕ proc_exit_user ↦ primcall_exit_user_compatsem proc_exit_user_spec
          ⊕ accessors ↦ {| exec_load := (@exec_loadex _ _ Hmwd); 
                           exec_store := (@exec_storeex _ _ Hmwd) |}.

  (** * Layer Definition *)
  Definition tdispatch : compatlayer (cdata RData) := tdispatch_fresh ⊕ tdispatch_passthrough.

End WITHMEM.