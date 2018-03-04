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
(*              Lemmas for invariants                                  *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Maps.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import FlatMemory.
Require Import CommonTactic.
Require Import AuxLemma.

Require Import Values.
Require Import AsmX.
Require Import Integers.
Require Import liblayers.compat.CompatLayers.
Require Import AST.

Section VMCS_INV.

  Lemma VMCS_inject_neutral_gso':
    forall r a d n,
      VMCS_inject_neutral (VMCSValid r a d) n ->
      forall r' a',
        VMCS_inject_neutral (VMCSValid r' a' d) n.
  Proof.
    intros. inv H. constructor; trivial.
  Qed.

  Lemma VMCS_inject_neutral_gso:
    forall v r a d n,
      VMCS_inject_neutral v n ->
      v = (VMCSValid r a d) ->
      forall r' a',
        VMCS_inject_neutral (VMCSValid r' a' d) n.
  Proof.
    intros. subst. eapply VMCS_inject_neutral_gso'; eauto.
  Qed.

  Lemma VMCS_inject_neutral_gss':
    forall r a d n,
      VMCS_inject_neutral (VMCSValid r a d) n ->
      forall v,
        (Val.has_type v Tint /\ val_inject (Mem.flat_inj n) v v) ->
        forall r' a' i,
          VMCS_inject_neutral (VMCSValid r' a' (ZMap.set i v d)) n.
  Proof.
    intros. inv H. constructor; trivial; intros. 
    subst v0. destruct (zeq i ofs); subst.
    - rewrite ZMap.gss. trivial.
    - rewrite ZMap.gso; eauto. 
  Qed.

  Lemma VMCS_inject_neutral_gss_same:
    forall r a d n,
      VMCS_inject_neutral (VMCSValid r a d) n ->
      forall v,
        (Val.has_type v Tint /\ val_inject (Mem.flat_inj n) v v) ->
        forall i,
          VMCS_inject_neutral (VMCSValid r a (ZMap.set i v d)) n.
  Proof.
    intros. eapply VMCS_inject_neutral_gss'; eauto.
  Qed.

  Lemma VMCS_inject_neutral_gss:
    forall r a d n vm,
      VMCS_inject_neutral vm n ->
      vm = (VMCSValid r a d) ->
      forall v,
        (Val.has_type v Tint /\ val_inject (Mem.flat_inj n) v v) ->
        forall r' a' i,
          VMCS_inject_neutral (VMCSValid r' a' (ZMap.set i v d)) n.
  Proof.
    intros. subst. eapply VMCS_inject_neutral_gss'; eauto.
  Qed.

  Lemma VMCS_inject_neutral_gss_Vint':
    forall r a d n,
      VMCS_inject_neutral (VMCSValid r a d) n ->
      forall r' a' i v,
        VMCS_inject_neutral (VMCSValid r' a' (ZMap.set i (Vint v) d)) n.
  Proof.
    intros. eapply VMCS_inject_neutral_gss'; eauto.
    split; constructor.
  Qed.

  Lemma VMCS_inject_neutral_gss_Vint_same:
    forall r a d n,
      VMCS_inject_neutral (VMCSValid r a d) n ->
      forall i v,
        VMCS_inject_neutral (VMCSValid r a (ZMap.set i (Vint v) d)) n.
  Proof.
    intros. eapply VMCS_inject_neutral_gss_Vint'; eauto.
  Qed.

  Lemma VMCS_inject_neutral_gss_Vint:
    forall v r a d n,
      VMCS_inject_neutral v n ->
      v = (VMCSValid r a d) ->
      forall r' a' i v,
        VMCS_inject_neutral (VMCSValid r' a' (ZMap.set i (Vint v) d)) n.
  Proof.
    intros. subst. eapply VMCS_inject_neutral_gss_Vint'; eauto.
  Qed.

  Lemma VMCS_inject_neutral_gss_VMX:
    forall vm vvmx n revid abrtid data,
      VMCS_inject_neutral vm n ->
      vm = VMCSValid revid abrtid data ->
      VMX_inject_neutral vvmx n ->
      forall i1 i2,
        VMCS_inject_neutral
          (VMCSValid revid abrtid (ZMap.set i1 (ZMap.get i2 vvmx) data)) n.
  Proof.
    intros. inv H1. eapply VMCS_inject_neutral_gss; eauto.
  Qed.      

End VMCS_INV.

Section VMX_INV.

  Lemma VMX_inject_neutral_gss:
    forall d n,
      VMX_inject_neutral d n ->
      forall v,
        (Val.has_type v Tint /\ val_inject (Mem.flat_inj n) v v) ->
        forall i,
          VMX_inject_neutral (ZMap.set i v d) n.
  Proof.
    intros. inv H. constructor; trivial; intros. 
    subst v0. destruct (zeq i ofs); subst.
    - rewrite ZMap.gss. trivial.
    - rewrite ZMap.gso; eauto. 
  Qed.

  Lemma VMX_inject_neutral_gss_Vint:
    forall d n,
      VMX_inject_neutral d n ->
      forall i v,
        VMX_inject_neutral (ZMap.set i (Vint v) d) n.
  Proof.
    intros. eapply VMX_inject_neutral_gss; eauto.
    split; constructor.
  Qed.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.

    Local Open Scope Z_scope.
    Require Import IntelPrimSemantics.

    Lemma VMX_inject_neutral_gss_enter:
      forall vvmx rs m,
        VMX_inject_neutral vvmx (Mem.nextblock m) ->
        (forall r,
           is_vmx_enter_reg r ->
           Val.has_type (rs r) Tint /\
           val_inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r)) ->
        let vvmx1 := ZMap.set VMX_HOST_EBP' (rs EBP) vvmx in
        let vvmx2 := ZMap.set VMX_HOST_EDI' (rs EDI) vvmx1 in
        VMX_inject_neutral vvmx2 (Mem.nextblock m).
    Proof.
      intros. 
      repeat eapply VMX_inject_neutral_gss; eauto;
      split; eauto; eapply H0; constructor.
    Qed.

    Lemma VMX_inject_neutral_gss_exit:
      forall vvmx rs m,
        VMX_inject_neutral vvmx (Mem.nextblock m) ->
        (forall r,
           is_vmx_exit_reg r ->
           Val.has_type (rs r) Tint /\
           val_inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r)) ->
        let vvmx1 := ZMap.set VMX_G_RDI' (rs EDI) vvmx in
        let vvmx2 := ZMap.set VMX_G_RAX' (rs EAX) vvmx1 in
        let vvmx3 := ZMap.set VMX_G_RBX' (rs EBX) vvmx2 in
        (*let vvmx4 := ZMap.set VMX_G_RCX' (rs ECX) vvmx3 in*)
        let vvmx5 := ZMap.set VMX_G_RDX' (rs EDX) vvmx3 in
        let vvmx6 := ZMap.set VMX_G_RSI' (rs ESI) vvmx5 in
        let vvmx7 := ZMap.set VMX_G_RBP' (rs EBP) vvmx6 in
        VMX_inject_neutral vvmx7 (Mem.nextblock m).
    Proof.
      intros. 
      repeat eapply VMX_inject_neutral_gss; eauto;
      split; eauto; eapply H0; constructor.
    Qed.

    Lemma VMX_inject_neutral_gss_exit':
      forall vm revid abrtid d vvmx rs m,
        VMX_inject_neutral vvmx (Mem.nextblock m) ->
        VMCS_inject_neutral vm (Mem.nextblock m) ->
        vm = VMCSValid revid abrtid d ->
        (forall r,
           is_vmx_exit_reg r ->
           Val.has_type (rs r) Tint /\
           val_inject (Mem.flat_inj (Mem.nextblock m)) (rs r) (rs r)) ->
        let vvmx1 := ZMap.set VMX_G_RDI' (rs EDI) vvmx in
        let vvmx2 := ZMap.set VMX_G_RAX' (rs EAX) vvmx1 in
        let vvmx3 := ZMap.set VMX_G_RBX' (rs EBX) vvmx2 in
        (*let vvmx4 := ZMap.set VMX_G_RCX' (rs ECX) vvmx3 in*)
        let vvmx5 := ZMap.set VMX_G_RDX' (rs EDX) vvmx3 in
        let vvmx6' := ZMap.set VMX_G_RSI' (rs ESI) vvmx5 in
        let vvmx6 := ZMap.set VMX_G_RBP' (rs EBP) vvmx6' in
        let vvmx7 := ZMap.set VMX_G_RIP' (ZMap.get C_VMCS_GUEST_RIP d) vvmx6 in
        let vvmx8 := ZMap.set VMX_EXIT_REASON' (ZMap.get C_VMCS_EXIT_REASON d) vvmx7 in
        let vvmx9 := ZMap.set VMX_EXIT_QUALIFICATION' (ZMap.get C_VMCS_EXIT_QUALIFICATION d) vvmx8 in
        let vvmx10 := ZMap.set VMX_LAUNCHED' Vone vvmx9 in
        VMX_inject_neutral vvmx10 (Mem.nextblock m).
    Proof.
      intros. inv H0. inv H4.
      repeat eapply VMX_inject_neutral_gss; eauto;
      split; eauto; try eapply H2; econstructor.
    Qed.

  End WITHMEM.

End VMX_INV.