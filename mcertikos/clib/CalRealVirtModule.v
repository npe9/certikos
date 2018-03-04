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
(*    Definitions used in verification of virt module initialization   *)
(*                                                                     *)
(*                       Xiongnan (Newman) Wu                          *)
(*                                                                     *)
(*                         Yale University                             *)
(*                                                                     *)
(* *********************************************************************)
Require Export AuxStateDataType.
Require Import Constant.
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import XOmega.
Require Import CLemmas.
Require Import VCGen.
Require Import Decision.


Section CInitSpecsVNPTINTRO.

  Context `{real_params_ops : RealParamsOps}.

  (** npt_init *)

  Fixpoint Calculate_npt (i: nat) (npt: NPT) : NPT :=
    match i with 
      | O => ZMap.set 0 (NPDEValid (ZMap.init NPTEUndef)) npt
      | S k => ZMap.set (Z.of_nat (S k)) (NPDEValid (ZMap.init NPTEUndef)) (Calculate_npt k npt)
    end.

  Definition real_npt (npt: NPT) := Calculate_npt (Z.to_nat (one_k - 1)) npt.

  Lemma real_npt_valid: forall npt, NPT_valid (real_npt npt) 0 Int.max_unsigned.
  Proof.
    generalize max_unsigned_val; intro muval.
    unfold NPT_valid.
    intros.
    unfold NPDE_valid.
    unfold real_npt.
    assert(0 <= PDX i < one_k).
      unfold PDX.
      repeat discharge_unsigned_range.
      apply Zdiv_lt_upper_bound.
      omega.
      rewrite muval in H.
      simpl.
      omega.
    assert(0 <= PDX i <= one_k - 1) by omega.
    rewrite <- Z2Nat.id with (one_k - 1) in H1; try omega.
    induction (Z.to_nat (one_k - 1)).
    simpl.
    rewrite Nat2Z.inj_0 in H1.
    replace (PDX i) with 0 by omega.
    rewrite ZMap.gss.
    esplit; reflexivity.
    Opaque Z.of_nat.
    simpl.
    rewrite ZMap.gsspec. 
    destruct (ZIndexed.eq (PDX i) (Z.of_nat (S n))).
    esplit; reflexivity.
    rewrite Nat2Z.inj_succ in *.
    unfold Z.succ in *.
    apply IHn.
    omega.
  Qed.

End CInitSpecsVNPTINTRO.


Section CInitSpecsVVMCBINTRO.

  Context `{real_params_ops : RealParamsOps}.

  (** imcb_init *)

  Function Calculate_vmcb_z_at_i (i: Z) (vmcb_z: VMCB_Z) : VMCB_Z := 
    if (is_VMCB_Z_ofs i) then
      ZMap.set i (VMCBEntryZValid 0) vmcb_z
    else
      vmcb_z.

  Fixpoint Calculate_vmcb_z (i: nat) (vmcb_z: VMCB_Z) : VMCB_Z :=
    match i with 
      | O => vmcb_z
      | S k => Calculate_vmcb_z_at_i (Z.of_nat k) (Calculate_vmcb_z k vmcb_z)
    end.

  (** Show that the blank VMCB_Z obtained with [Calculate_vmcb_z] is valid. *)

  Lemma Calculate_vmcb_z_valid vmcb_z:
    VMCB_Z_Valid (Calculate_vmcb_z (Z.to_nat 1024) vmcb_z).
  Proof.
    cut (forall i, 0 <= i < 1024 ->
                   is_VMCB_Z_ofs i = true ->
                   VMCB_Entry_Z_Valid (Calculate_vmcb_z (Z.to_nat 1024) vmcb_z) i).

    (** First, we show that it is enough for indices in the range
      [0, 1024) to satisfy the invariant. *)

    * intros H ofs Hofs.
      functional inversion Hofs;
        apply (H ofs);
        assumption || omega.

    (** Then we prove by induction that indeed, they do. *)

    * change 1024 with (Z.of_nat 1024).
      rewrite Nat2Z.id.
      generalize 1024%nat.
      intro n.
      induction n.
      - rewrite Nat2Z.inj_0.
        intros i Hi.
        omega.
      - intros i Hi Hi'.
        simpl.
        unfold Calculate_vmcb_z_at_i.
        destruct (decide (Z.of_nat n = i)) as [Hi'' | Hi''].
        + rewrite Hi''.
          rewrite Hi'.
          red.
          rewrite ZMap.gss.
          exists 0.
          now auto using AuxLemma.int_max_unsigned.
        + rewrite Nat2Z.inj_succ in *.
          destruct (is_VMCB_Z_ofs (Z.of_nat n)).
          red.
          rewrite ZMap.gso by now auto.
          apply IHn; omega || now auto.
          apply IHn; omega || now auto.
  Qed.

  (** Most entries will be zero, except for the following. *)
  Definition VMCB_Z_initial_entries: list (Z * VMCB_Entry_Z) :=
    (  4, VMCBEntryZValid 7391)::
    (  3, VMCBEntryZValid 151273473)::
    ( 24, VMCBEntryZValid 16777216)::
    ( 36, VMCBEntryZValid 1)::
    ( 22, VMCBEntryZValid 1)::
    (411, VMCBEntryZValid 459782)::
    (410, VMCBEntryZValid 459782)::
    (308, VMCBEntryZValid 4096)::
    (344, VMCBEntryZValid 1024)::
    (346, VMCBEntryZValid 4294905840)::
    nil.

  Definition initialize_VMCB_Z_entry (ie: Z * VMCB_Entry_Z) :=
    match ie with (i, e) => ZMap.set i e end.

  (** Show that overwriting some entries with appropriate values
    does not compromise the validity of the whole thing. *)

  Lemma initialize_VMCB_Z_entry_preserves_valid vmcb_z i v:
    0 <= v <= Int.max_unsigned ->
    VMCB_Z_Valid vmcb_z ->
    VMCB_Z_Valid (initialize_VMCB_Z_entry (i, VMCBEntryZValid v) vmcb_z).
  Proof.
    intros Hv H k Hk.
    red. simpl.
    destruct (decide (k = i)).
    * subst.
      rewrite ZMap.gss.
      exists v; tauto.
    * rewrite ZMap.gso by assumption.
      apply H.
      assumption.
  Qed.

  (** Now we glue those together: compute an initial table with
    [Calculate_vmcb_z], then overwrite the entries as directed by the
    [VMCB_Z_initial_entries] list. *)

  Definition real_vmcbz (vmcb_z: VMCB_Z) :=
    fold_right initialize_VMCB_Z_entry
               (Calculate_vmcb_z (Z.to_nat 1024) vmcb_z)
               VMCB_Z_initial_entries.

  Lemma real_vmcbz_valid: forall vmcb_z, VMCB_Z_Valid (real_vmcbz vmcb_z).
  Proof.
    intro.
    unfold real_vmcbz.
    apply initialize_VMCB_Z_entry_preserves_valid; try (split; discriminate).
    repeat match goal with
      | [ |- VMCB_Z_Valid (initialize_VMCB_Z_entry _ _) ] =>
        apply initialize_VMCB_Z_entry_preserves_valid; try (split; discriminate)
    end.
    apply Calculate_vmcb_z_valid.
  Qed.

End CInitSpecsVVMCBINTRO.