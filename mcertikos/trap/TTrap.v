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
Require Export TTrapArg.
Require Export ObjTrap.
Require Export TrapPrimSemantics.

(** * Abstract Data and Primitives at this layer*)
Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section Prim.

    Section TRAP_GET_QUOTA.

      Lemma trap_get_quota_high_inv:
        forall d d',
          trap_get_quota_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H.
        eapply uctx_set_errno_high_inv; try eassumption.
        eapply uctx_set_retval1_high_inv; eassumption.
      Qed.

      Lemma trap_get_quota_low_inv:
        forall d d' n,
          trap_get_quota_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H.
        eapply uctx_set_errno_low_inv; try eassumption.
        eapply uctx_set_retval1_low_inv; eassumption.
      Qed.

      Lemma trap_get_quota_kernel_mode:
        forall d d',
          trap_get_quota_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H.
        eapply uctx_set_errno_kernel_mode; try eassumption.
        eapply uctx_set_retval1_kernel_mode; eassumption.
      Qed.

      Global Instance trap_get_quota_inv: PreservesInvariants trap_get_quota_spec.
      Proof.
        preserves_invariants_simpl';
          [ eapply trap_get_quota_low_inv
          | eapply trap_get_quota_high_inv
          | eapply trap_get_quota_kernel_mode ];
          eassumption.
      Qed.

    End TRAP_GET_QUOTA.


    Section PRINT.

      Lemma print_high_inv:
        forall d d',
          print_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H. subst; simpl.
        eapply uctx_set_errno_high_inv; try eassumption.
        inv H0; split; trivial.
      Qed.

      Lemma print_low_inv:
        forall d d' n,
          print_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_low_inv; try eassumption.
        inv H0; split; trivial.
      Qed.

      Lemma print_kernel_mode:
        forall d d',
          print_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst.
        eapply uctx_set_errno_kernel_mode; try eassumption.
      Qed.

      Global Instance print_inv: PreservesInvariants print_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply print_low_inv; eauto.
        - eapply print_high_inv; eauto.
        - eapply print_kernel_mode; eauto.
      Qed.

    End PRINT.

    (*Section TRAP_HANDLE_RDMSR.

      Lemma trap_handle_rdmsr_high_inv:
        forall d d',
          trap_handle_rdmsr_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_high_inv; eauto.
        eapply vmx_set_reg_high_inv; eauto.
        eapply vmx_set_reg_high_inv; eauto.
        eapply vmx_set_reg_high_inv; eauto.
      Qed.

      Lemma trap_handle_rdmsr_low_inv:
        forall d d' n,
          trap_handle_rdmsr_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_low_inv; eauto.
        eapply vmx_set_reg_low_inv; eauto.
        eapply vmx_set_reg_low_inv; eauto.
        eapply vmx_set_reg_low_inv; eauto.
      Qed.

      Lemma trap_handle_rdmsr_kernel_mode:
        forall d d',
          trap_handle_rdmsr_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst;
        eapply uctx_set_errno_kernel_mode; eauto.
        eapply vmx_set_reg_kernel_mode; eauto.
        eapply vmx_set_reg_kernel_mode; eauto.
        eapply vmx_set_reg_kernel_mode; eauto.
      Qed.

      Global Instance trap_handle_rdmsr_inv: PreservesInvariants trap_handle_rdmsr_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_handle_rdmsr_low_inv; eauto.
        - eapply trap_handle_rdmsr_high_inv; eauto.
        - eapply trap_handle_rdmsr_kernel_mode; eauto.
      Qed.

    End TRAP_HANDLE_RDMSR.

    Section TRAP_HANDLE_WRMSR.

      Lemma trap_handle_wrmsr_high_inv:
        forall d d',
          trap_handle_wrmsr_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_high_inv; eauto.
        eapply vmx_set_reg_high_inv; eauto.
      Qed.

      Lemma trap_handle_wrmsr_low_inv:
        forall d d' n,
          trap_handle_wrmsr_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_low_inv; eauto.
        eapply vmx_set_reg_low_inv; eauto.
      Qed.

      Lemma trap_handle_wrmsr_kernel_mode:
        forall d d',
          trap_handle_wrmsr_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst;
        eapply uctx_set_errno_kernel_mode; eauto.
        eapply vmx_set_reg_kernel_mode; eauto.
      Qed.

      Global Instance trap_handle_wrmsr_inv: PreservesInvariants trap_handle_wrmsr_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_handle_wrmsr_low_inv; eauto.
        - eapply trap_handle_wrmsr_high_inv; eauto.
        - eapply trap_handle_wrmsr_kernel_mode; eauto.
      Qed.

    End TRAP_HANDLE_WRMSR.*)

    (*Section TRAP_CHAN_READY.

      Lemma trap_ischanready_high_inv:
        forall d d',
          trap_ischanready_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_high_inv; eauto.
        eapply uctx_set_retval1_high_inv; eauto.
      Qed.

      Lemma trap_ischanready_low_inv:
        forall d d' n,
          trap_ischanready_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_low_inv; eauto.
        eapply uctx_set_retval1_low_inv; eauto.
      Qed.

      Lemma trap_ischanready_kernel_mode:
        forall d d',
          trap_ischanready_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst.
        eapply uctx_set_errno_kernel_mode; eauto.
        eapply uctx_set_retval1_kernel_mode; eauto.
      Qed.

      Global Instance trap_ischanready_inv: PreservesInvariants trap_ischanready_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_ischanready_low_inv; eauto.
        - eapply trap_ischanready_high_inv; eauto.
        - eapply trap_ischanready_kernel_mode; eauto.
      Qed.

    End TRAP_CHAN_READY.

    Section TRAP_CHAN_SEND.

      Lemma trap_sendtochan_high_inv:
        forall d d',
          trap_sendtochan_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_high_inv; eauto.
        eapply uctx_set_retval1_high_inv; eauto.
        eapply sendto_chan_high_inv; eauto.
      Qed.

      Lemma trap_sendtochan_low_inv:
        forall d d' n,
          trap_sendtochan_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_low_inv; eauto.
        eapply uctx_set_retval1_low_inv; eauto.
        eapply sendto_chan_low_inv; eauto.
      Qed.

      Lemma trap_sendtochan_kernel_mode:
        forall d d',
          trap_sendtochan_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst.
        eapply uctx_set_errno_kernel_mode; eauto.
        eapply uctx_set_retval1_kernel_mode; eauto.
        eapply sendto_chan_kernel_mode; eauto.
      Qed.

      Global Instance trap_sendtochan_inv: PreservesInvariants trap_sendtochan_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_sendtochan_low_inv; eauto.
        - eapply trap_sendtochan_high_inv; eauto.
        - eapply trap_sendtochan_kernel_mode; eauto.
      Qed.

    End TRAP_CHAN_SEND.*)

    Section TRAP_CHAN_RECEIVE.

      Lemma trap_receivechan_high_inv:
        forall d d',
          trap_receivechan_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_high_inv; eauto.
        eapply uctx_set_retval1_high_inv; eauto.
        eapply syncreceive_chan_high_level_inv; eauto.
      Qed.

      Lemma trap_receivechan_low_inv:
        forall d d' n,
          trap_receivechan_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_low_inv; eauto.
        eapply uctx_set_retval1_low_inv; eauto.
        eapply syncreceive_chan_low_level_inv; eauto.
      Qed.

      Lemma trap_receivechan_kernel_mode:
        forall d d',
          trap_receivechan_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst.
        eapply uctx_set_errno_kernel_mode; eauto.
        eapply uctx_set_retval1_kernel_mode; eauto.
        eapply syncreceive_chan_kernel_mode; eauto.
      Qed.

      Global Instance trap_receivechan_inv: PreservesInvariants trap_receivechan_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_receivechan_low_inv; eauto.
        - eapply trap_receivechan_high_inv; eauto.
        - eapply trap_receivechan_kernel_mode; eauto.
      Qed.

    End TRAP_CHAN_RECEIVE.

    (*Section TRAP_INTERCEPT_INT_WINDOW.

      Lemma trap_intercept_int_window_high_inv:
        forall d d',
          trap_intercept_int_window_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_high_inv; eauto.
        eapply vmx_set_intercept_intwin_high_inv; eauto.
      Qed.

      Lemma trap_intercept_int_window_low_inv:
        forall d d' n,
          trap_intercept_int_window_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_low_inv; eauto.
        eapply vmx_set_intercept_intwin_low_inv; eauto.
      Qed.

      Lemma trap_intercept_int_window_kernel_mode:
        forall d d',
          trap_intercept_int_window_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst.
        eapply uctx_set_errno_kernel_mode; eauto.
        eapply vmx_set_intercept_intwin_kernel_mode; eauto.
      Qed.

      Global Instance trap_intercept_int_window_inv: PreservesInvariants trap_intercept_int_window_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_intercept_int_window_low_inv; eauto.
        - eapply trap_intercept_int_window_high_inv; eauto.
        - eapply trap_intercept_int_window_kernel_mode; eauto.
      Qed.

    End TRAP_INTERCEPT_INT_WINDOW.
 
    Section TRAP_CHECK_PENDING_EVENT.

      Lemma trap_check_pending_event_high_inv:
        forall d d',
          trap_check_pending_event_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_high_inv; eauto.
        eapply uctx_set_retval1_high_inv; eauto.
      Qed.

      Lemma trap_check_pending_event_low_inv:
        forall d d' n,
          trap_check_pending_event_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_low_inv; eauto.
        eapply uctx_set_retval1_low_inv; eauto.
      Qed.

      Lemma trap_check_pending_event_kernel_mode:
        forall d d',
          trap_check_pending_event_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst.
        eapply uctx_set_errno_kernel_mode; eauto.
        eapply uctx_set_retval1_kernel_mode; eauto.
      Qed.

      Global Instance trap_check_pending_event_inv: PreservesInvariants trap_check_pending_event_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_check_pending_event_low_inv; eauto.
        - eapply trap_check_pending_event_high_inv; eauto.
        - eapply trap_check_pending_event_kernel_mode; eauto.
      Qed.

    End TRAP_CHECK_PENDING_EVENT.

    Section TRAP_CHECK_INT_SHADOW.

      Lemma trap_check_int_shadow_high_inv:
        forall d d',
          trap_check_int_shadow_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_high_inv; eauto.
        eapply uctx_set_retval1_high_inv; eauto.
      Qed.

      Lemma trap_check_int_shadow_low_inv:
        forall d d' n,
          trap_check_int_shadow_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_low_inv; eauto.
        eapply uctx_set_retval1_low_inv; eauto.
      Qed.

      Lemma trap_check_int_shadow_kernel_mode:
        forall d d',
          trap_check_int_shadow_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst.
        eapply uctx_set_errno_kernel_mode; eauto.
        eapply uctx_set_retval1_kernel_mode; eauto.
      Qed.

      Global Instance trap_check_int_shadow_inv: PreservesInvariants trap_check_int_shadow_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_check_int_shadow_low_inv; eauto.
        - eapply trap_check_int_shadow_high_inv; eauto.
        - eapply trap_check_int_shadow_kernel_mode; eauto.
      Qed.

    End TRAP_CHECK_INT_SHADOW.


    Section TRAP_INJECT_EVENT.

      Lemma trap_inject_event_high_inv:
        forall d d',
          trap_inject_event_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_high_inv; eauto.
        eapply vmx_inject_event_high_inv; eauto.
      Qed.

      Lemma trap_inject_event_low_inv:
        forall d d' n,
          trap_inject_event_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_low_inv; eauto.
        eapply vmx_inject_event_low_inv; eauto.
      Qed.

      Lemma trap_inject_event_kernel_mode:
        forall d d',
          trap_inject_event_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst;
        eapply uctx_set_errno_kernel_mode; eauto.
        eapply vmx_inject_event_kernel_mode; eauto.
      Qed.

      Global Instance trap_inject_event_inv: PreservesInvariants trap_inject_event_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_inject_event_low_inv; eauto.
        - eapply trap_inject_event_high_inv; eauto.
        - eapply trap_inject_event_kernel_mode; eauto.
      Qed.

    End TRAP_INJECT_EVENT.


    Section TRAP_GET_NEXT_EIP.

      Lemma trap_get_next_eip_high_inv:
        forall d d',
          trap_get_next_eip_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_high_inv; eauto.
        eapply uctx_set_retval1_high_inv; eauto.
      Qed.

      Lemma trap_get_next_eip_low_inv:
        forall d d' n,
          trap_get_next_eip_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        eapply uctx_set_errno_low_inv; eauto.
        eapply uctx_set_retval1_low_inv; eauto.
      Qed.

      Lemma trap_get_next_eip_kernel_mode:
        forall d d',
          trap_get_next_eip_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst.
        eapply uctx_set_errno_kernel_mode; eauto.
        eapply uctx_set_retval1_kernel_mode; eauto.
      Qed.

      Global Instance trap_get_next_eip_inv: PreservesInvariants trap_get_next_eip_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_get_next_eip_low_inv; eauto.
        - eapply trap_get_next_eip_high_inv; eauto.
        - eapply trap_get_next_eip_kernel_mode; eauto.
      Qed.

    End TRAP_GET_NEXT_EIP.


    Section TRAP_GET_REG.

      Lemma trap_get_reg_high_inv:
        forall d d',
          trap_get_reg_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_high_inv; eauto.
        eapply uctx_set_retval1_high_inv; eauto.
      Qed.

      Lemma trap_get_reg_low_inv:
        forall d d' n,
          trap_get_reg_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_low_inv; eauto.
        eapply uctx_set_retval1_low_inv; eauto.
      Qed.

      Lemma trap_get_reg_kernel_mode:
        forall d d',
          trap_get_reg_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst;
        eapply uctx_set_errno_kernel_mode; eauto.
        eapply uctx_set_retval1_kernel_mode; eauto.
      Qed.

      Global Instance trap_get_reg_inv: PreservesInvariants trap_get_reg_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_get_reg_low_inv; eauto.
        - eapply trap_get_reg_high_inv; eauto.
        - eapply trap_get_reg_kernel_mode; eauto.
      Qed.

    End TRAP_GET_REG.

    Section TRAP_SET_REG.

      Lemma trap_set_reg_high_inv:
        forall d d',
          trap_set_reg_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_high_inv; eauto.
        eapply vmx_set_reg_high_inv; eauto.
      Qed.

      Lemma trap_set_reg_low_inv:
        forall d d' n,
          trap_set_reg_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_low_inv; eauto.
        eapply vmx_set_reg_low_inv; eauto.
      Qed.

      Lemma trap_set_reg_kernel_mode:
        forall d d',
          trap_set_reg_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst;
        eapply uctx_set_errno_kernel_mode; eauto.
        eapply vmx_set_reg_kernel_mode; eauto.
      Qed.

      Global Instance trap_set_reg_inv: PreservesInvariants trap_set_reg_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_set_reg_low_inv; eauto.
        - eapply trap_set_reg_high_inv; eauto.
        - eapply trap_set_reg_kernel_mode; eauto.
      Qed.

    End TRAP_SET_REG.

    Section TRAP_SET_SEG.

      Lemma trap_set_seg_high_inv:
        forall d d',
          trap_set_seg_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_high_inv; eauto.
        eapply vmx_set_desc_high_inv; eauto.
      Qed.

      Lemma trap_set_seg_low_inv:
        forall d d' n,
          trap_set_seg_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_low_inv; eauto.
        eapply vmx_set_desc_low_inv; eauto.
      Qed.

      Lemma trap_set_seg_kernel_mode:
        forall d d',
          trap_set_seg_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst;
        eapply uctx_set_errno_kernel_mode; eauto.
        eapply vmx_set_desc_kernel_mode; eauto.
      Qed.

      Global Instance trap_set_seg_inv: PreservesInvariants trap_set_seg_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_set_seg_low_inv; eauto.
        - eapply trap_set_seg_high_inv; eauto.
        - eapply trap_set_seg_kernel_mode; eauto.
      Qed.

    End TRAP_SET_SEG.

    Section TRAP_GET_TSC_OFFSET.

      Lemma trap_get_tsc_offset_high_inv:
        forall d d',
          trap_get_tsc_offset_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_high_inv; eauto.
        eapply uctx_set_retval2_high_inv; eauto.
        eapply uctx_set_retval1_high_inv; eauto.
      Qed.

      Lemma trap_get_tsc_offset_low_inv:
        forall d d' n,
          trap_get_tsc_offset_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_low_inv; eauto.
        eapply uctx_set_retval2_low_inv; eauto.
        eapply uctx_set_retval1_low_inv; eauto.
      Qed.

      Lemma trap_get_tsc_offset_kernel_mode:
        forall d d',
          trap_get_tsc_offset_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst;
        eapply uctx_set_errno_kernel_mode; eauto.
        eapply uctx_set_retval2_kernel_mode; eauto.
        eapply uctx_set_retval1_kernel_mode; eauto.
      Qed.

      Global Instance trap_get_tsc_offset_inv: PreservesInvariants trap_get_tsc_offset_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_get_tsc_offset_low_inv; eauto.
        - eapply trap_get_tsc_offset_high_inv; eauto.
        - eapply trap_get_tsc_offset_kernel_mode; eauto.
      Qed.

    End TRAP_GET_TSC_OFFSET.

    Section TRAP_SET_TSC_OFFSET.

      Lemma trap_set_tsc_offset_high_inv:
        forall d d',
          trap_set_tsc_offset_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_high_inv; eauto.
        eapply vmx_set_tsc_offset_high_inv; eauto.
      Qed.

      Lemma trap_set_tsc_offset_low_inv:
        forall d d' n,
          trap_set_tsc_offset_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_low_inv; eauto.
        eapply vmx_set_tsc_offset_low_inv; eauto.
      Qed.

      Lemma trap_set_tsc_offset_kernel_mode:
        forall d d',
          trap_set_tsc_offset_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst;
        eapply uctx_set_errno_kernel_mode; eauto.
        eapply vmx_set_tsc_offset_kernel_mode; eauto.
      Qed.

      Global Instance trap_set_tsc_offset_inv: PreservesInvariants trap_set_tsc_offset_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_set_tsc_offset_low_inv; eauto.
        - eapply trap_set_tsc_offset_high_inv; eauto.
        - eapply trap_set_tsc_offset_kernel_mode; eauto.
      Qed.

    End TRAP_SET_TSC_OFFSET.

    Section TRAP_GET_EXITINFO.

      Lemma trap_get_exitinfo_high_inv:
        forall d d',
          trap_get_exitinfo_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_high_inv; eauto.
        - eapply uctx_set_retval4_high_inv; eauto.
          eapply uctx_set_retval3_high_inv; eauto.
          eapply uctx_set_retval2_high_inv; eauto.
          eapply uctx_set_retval1_high_inv; eauto.
        - eapply uctx_set_retval2_high_inv; eauto.
          eapply uctx_set_retval1_high_inv; eauto.
        - eapply uctx_set_retval1_high_inv; eauto.
      Qed.

      Lemma trap_get_exitinfo_low_inv:
        forall d d' n,
          trap_get_exitinfo_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl;
        eapply uctx_set_errno_low_inv; eauto.
        - eapply uctx_set_retval4_low_inv; eauto.
          eapply uctx_set_retval3_low_inv; eauto.
          eapply uctx_set_retval2_low_inv; eauto.
          eapply uctx_set_retval1_low_inv; eauto.
        - eapply uctx_set_retval2_low_inv; eauto.
          eapply uctx_set_retval1_low_inv; eauto.
        - eapply uctx_set_retval1_low_inv; eauto.
      Qed.

      Lemma trap_get_exitinfo_kernel_mode:
        forall d d',
          trap_get_exitinfo_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst;
        eapply uctx_set_errno_kernel_mode; eauto.
        - eapply uctx_set_retval4_kernel_mode; eauto.
          eapply uctx_set_retval3_kernel_mode; eauto.
          eapply uctx_set_retval2_kernel_mode; eauto.
          eapply uctx_set_retval1_kernel_mode; eauto.
        - eapply uctx_set_retval2_kernel_mode; eauto.
          eapply uctx_set_retval1_kernel_mode; eauto.
        - eapply uctx_set_retval1_kernel_mode; eauto.
      Qed.

      Global Instance trap_get_exitinfo_inv: PreservesInvariants trap_get_exitinfo_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_get_exitinfo_low_inv; eauto.
        - eapply trap_get_exitinfo_high_inv; eauto.
        - eapply trap_get_exitinfo_kernel_mode; eauto.
      Qed.

    End TRAP_GET_EXITINFO.

    Section TRAP_MMAP.

      Lemma trap_mmap_high_inv:
        forall d d',
          trap_mmap_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros; functional inversion H; subst; simpl;
        eapply uctx_set_errno_high_inv; eauto;
        eapply vmx_set_mmap_high_inv; eauto.
        eapply ptResv_high_level_inv; eauto.
      Qed.

      Lemma trap_mmap_low_inv:
        forall d d' n,
          trap_mmap_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros; functional inversion H; subst; simpl;
        eapply uctx_set_errno_low_inv; eauto;
        eapply vmx_set_mmap_low_inv; eauto.
        eapply ptResv_low_level_inv; eauto.
      Qed.

      Lemma trap_mmap_kernel_mode:
        forall d d',
          trap_mmap_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros; functional inversion H; subst;
        eapply uctx_set_errno_kernel_mode; eauto;
        eapply vmx_set_mmap_kernel_mode; eauto.
        eapply ptResv_kernel_mode; eauto.
      Qed.

      Global Instance trap_mmap_inv: PreservesInvariants trap_mmap_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_mmap_low_inv; eauto.
        - eapply trap_mmap_high_inv; eauto.
        - eapply trap_mmap_kernel_mode; eauto.
      Qed.

    End TRAP_MMAP.*)
    
    Section PTFault_RESV_INV.

      Lemma ptfault_resv_high_inv:
        forall d d' i,
          ptfault_resv_spec i d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros; functional inversion H; subst; simpl; trivial.        
        eapply ptResv_high_level_inv; eauto.
      Qed.

      Lemma ptfault_resv_low_inv:
        forall d d' i n,
          ptfault_resv_spec i d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros; functional inversion H; subst; simpl; trivial.
        eapply ptResv_low_level_inv; eauto.
      Qed.

      Lemma ptfault_resv_kernel_mode:
        forall d d' i,
          ptfault_resv_spec i d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros; functional inversion H; subst; trivial;
        eapply ptResv_kernel_mode; eauto.
      Qed.

      Global Instance ptfault_resv_inv: PreservesInvariants ptfault_resv_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply ptfault_resv_low_inv; eauto.
        - eapply ptfault_resv_high_inv; eauto.
        - eapply ptfault_resv_kernel_mode; eauto.
      Qed.

    End PTFault_RESV_INV.

    Global Instance trap_proc_create_inv: TrapProcCreateINV trap_proc_create_spec.
    Proof.
      destruct proc_create_inv.
      split; unfold trap_proc_create_spec; intros;
        destruct (uctx_arg3_spec d); try discriminate H;
        destruct (zle_le 0 z
                         (cquota (ZMap.get (cid d) (AC d)) -
                          cusage (ZMap.get (cid d) (AC d)))) eqn:Hquota; subdestruct; auto.
      - eapply uctx_set_errno_high_inv; eauto.
        eapply uctx_set_retval1_high_inv; eauto.
        eapply pcreate_high_level_invariant; eauto.
      - eapply uctx_set_errno_high_inv; eauto.
      - eapply uctx_set_errno_high_inv; eauto.
      - eapply uctx_set_errno_high_inv; eauto.
      - eapply uctx_set_errno_low_inv; eauto.
        eapply uctx_set_retval1_low_inv; eauto.
        eapply pcreate_low_level_invariant; eauto;
        eapply stencil_find_symbol_inject'; eauto;
        eapply flat_inj_inject_incr; assumption.
      - eapply uctx_set_errno_low_inv; eauto.
      - eapply uctx_set_errno_low_inv; eauto.
      - eapply uctx_set_errno_low_inv; eauto.
      - eapply uctx_set_errno_kernel_mode; eauto.
        eapply uctx_set_retval1_kernel_mode; eauto.
      - eapply uctx_set_errno_kernel_mode; eauto.
      - eapply uctx_set_errno_kernel_mode; eauto.
      - eapply uctx_set_errno_kernel_mode; eauto.
      - eapply Mem.load_extends in Hdestruct9; eauto.
        destruct Hdestruct9 as [v2[HLD HV]].
        inv HV. subrewrite'.
      - pose proof H1 as Hsymbol. apply H1 in Hdestruct8.
        eapply Mem.load_inject in Hdestruct9; eauto.
        destruct Hdestruct9 as [v2[HLD HV]].
        rewrite Z.add_0_r in HLD. subst.
        rewrite HLD. inv HV; eauto.
        rewrite H4 in Hdestruct8.
        inv Hdestruct8. rewrite Int.add_zero.
        subrewrite'.
    Qed.

    Section TRAP_SHARE.

      Lemma trap_offer_shared_mem_high_inv:
        forall d d',
          trap_offer_shared_mem_spec d = Some d'->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H. subst; simpl.
        - eapply uctx_set_errno_high_inv; try eassumption.
          eapply uctx_set_retval1_high_inv; try eassumption.
          eapply offer_shared_mem_high_level_inv; eauto.
        - eapply uctx_set_errno_high_inv; try eassumption.
      Qed.

      Lemma trap_offer_shared_mem_low_inv:
        forall d d' n,
          trap_offer_shared_mem_spec d = Some d'->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; simpl.
        - eapply uctx_set_errno_low_inv; try eassumption.
          eapply uctx_set_retval1_low_inv; try eassumption.
          eapply offer_shared_mem_low_level_inv; eauto.
        - eapply uctx_set_errno_low_inv; try eassumption.
      Qed.

      Lemma trap_offer_shared_mem_kernel_mode:
        forall d d',
          trap_offer_shared_mem_spec d = Some d'->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst.
        - eapply uctx_set_errno_kernel_mode; try eassumption.
          eapply uctx_set_retval1_kernel_mode; try eassumption.
          eapply offer_shared_mem_kernel_mode; eauto.
        - eapply uctx_set_errno_kernel_mode; try eassumption.
      Qed.

      Global Instance trap_offer_shared_mem_inv: PreservesInvariants trap_offer_shared_mem_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply trap_offer_shared_mem_low_inv; eauto.
        - eapply trap_offer_shared_mem_high_inv; eauto.
        - eapply trap_offer_shared_mem_kernel_mode; eauto.
      Qed.

    End TRAP_SHARE.

  End Prim.

  (** * Layer Definition *)
  Definition ttrap_fresh : compatlayer (cdata RData) :=
    ptfault_resv  ↦ gensem ptfault_resv_spec
                  ⊕ sys_proc_create  ↦ trap_proccreate_compatsem trap_proc_create_spec
                  ⊕ sys_get_quota  ↦ gensem trap_get_quota_spec
                  (*⊕ sys_is_chan_ready  ↦ gensem trap_ischanready_spec
                  ⊕ sys_sendto_chan  ↦ gensem trap_sendtochan_spec*)
                  ⊕ sys_receive_chan  ↦ gensem trap_receivechan_spec
                  ⊕ sys_offer_shared_mem  ↦ gensem trap_offer_shared_mem_spec
                  ⊕ print ↦ gensem print_spec
                  (*⊕ sys_inject_event  ↦ gensem trap_inject_event_spec
                  ⊕ sys_check_int_shadow  ↦ gensem trap_check_int_shadow_spec
                  ⊕ sys_check_pending_event  ↦ gensem trap_check_pending_event_spec
                  ⊕ sys_intercept_int_window  ↦ gensem trap_intercept_int_window_spec
                  ⊕ sys_get_next_eip  ↦ gensem trap_get_next_eip_spec
                  ⊕ sys_get_reg  ↦ gensem trap_get_reg_spec
                  ⊕ sys_set_reg  ↦ gensem trap_set_reg_spec
                  ⊕ sys_set_seg  ↦ gensem trap_set_seg_spec
                  ⊕ sys_get_tsc_offset  ↦ gensem trap_get_tsc_offset_spec
                  ⊕ sys_set_tsc_offset  ↦ gensem trap_set_tsc_offset_spec
                  ⊕ sys_get_exitinfo  ↦ gensem trap_get_exitinfo_spec
                  ⊕ sys_handle_rdmsr  ↦ gensem trap_handle_rdmsr_spec
                  ⊕ sys_handle_wrmsr  ↦ gensem trap_handle_wrmsr_spec
                  ⊕ sys_mmap  ↦ gensem trap_mmap_spec*).

  (** * Layer Definition *)
  Definition ttrap_passthrough : compatlayer (cdata RData) :=
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

          ⊕ trap_get ↦ primcall_trap_info_get_compatsem trap_info_get_spec
          ⊕ trap_set ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec
          ⊕ thread_yield ↦ primcall_thread_schedule_compatsem thread_yield_spec (prim_ident:= thread_yield)
          ⊕ thread_sleep ↦ primcall_thread_transfer_compatsem thread_sleep_spec
          ⊕ proc_start_user ↦ primcall_start_user_compatsem proc_start_user_spec
          ⊕ proc_exit_user ↦ primcall_exit_user_compatsem proc_exit_user_spec
          ⊕ accessors ↦ {| exec_load := (@exec_loadex _ _ Hmwd); 
                           exec_store := (@exec_storeex _ _ Hmwd) |}.

  (** * Layer Definition *)
  Definition ttrap : compatlayer (cdata RData) := ttrap_fresh ⊕ ttrap_passthrough.

End WITHMEM.
