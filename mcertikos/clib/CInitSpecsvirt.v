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
Require Import Coqlib.
Require Import ZArith.Zwf.
Require Import DataType.
Require Import ProcDataType.
Require Import VirtDataType.
Require Import MemoryExtra.
Require Import Maps.
Require Import Integers.
Require Import CDataTypes.
Require Import LayerDefinition.
Require Import RealParams.
Require Import CInitSpecsMPTOp.
Require Import CInitSpecsMPTCommon.
Require Import CInitSpecsMPTBit.
Require Import CInitSpecsproc.
Require Import VNPTIntro.
Require Import VVMCBIntro.
Require Import Decision.


Section CInitSpecsVNPTINTRO.

  Context `{real_params_ops : RealParamsOps}.

  Notation DATA := (VNPTINTRO.AbData (PgSize:= PgSize) (num_proc:= num_proc) (kern_high:= kern_high) (kern_low := kern_low) (maxpage:= maxpage) (num_chan:= num_chan)).

  Local Instance dataOp:AbstractDataOps DATA:= (VNPTINTRO.abstract_data (Hnpc:= Hnpc)).

  Context {VNPTINTRO_mem} 
              `{Hlmmh: !LayerMemoryModel DATA VNPTINTRO_mem}.

  (** npt_init *)

  Fixpoint Calculate_npt (i: nat) (npt: NPT) : NPT :=
    match i with 
      | O => ZMap.set 0 (NPDEValid (ZMap.init NPTEUndef)) npt
      | S k => ZMap.set (Z.of_nat (S k)) (NPDEValid (ZMap.init NPTEUndef)) (Calculate_npt k npt)
    end.

  Definition real_npt (npt: NPT) := Calculate_npt (Z.to_nat (one_k - 1)) npt.

  Lemma real_npt_valid: forall npt, NPT_valid (PgSize:= PgSize) (real_npt npt) 0 Int.max_unsigned.
  Proof.
    generalize one_k_val; intro onekval.
    generalize max_unsigned_val; intro muval.
    unfold NPT_valid.
    intros.
    unfold NPDE_valid.
    unfold real_npt.
    assert(0 <= PDX i < one_k).
      unfold DataType.PDX.
      repeat discharge_unsigned_range.
      apply Zdiv_lt_upper_bound.
      omega.
      rewrite onekval.
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


  Definition npt_init_madt (m: VNPTINTRO_mem) := VNPTINTRO.ADT (Mem.get_abstract_data m).

  Definition npt_init_mk_rdata (m: VNPTINTRO_mem) (index: Z) := let adt := (npt_init_madt m) in (VNPTINTRO.mkRData (VNPTINTRO.HP adt) (VNPTINTRO.AT adt) (VNPTINTRO.nps adt) (VNPTINTRO.ti adt) (VNPTINTRO.PT adt) (VNPTINTRO.ptpool adt) (VNPTINTRO.pb adt) (VNPTINTRO.kctxt adt) (VNPTINTRO.abtcb adt) (VNPTINTRO.abq adt) (VNPTINTRO.uctxt adt) (Calculate_npt (Z.to_nat index) (VNPTINTRO.npt adt)) (VNPTINTRO.cid adt) (VNPTINTRO.chpool adt) (VNPTINTRO.pe adt) (VNPTINTRO.ikern adt) true).
    
  Lemma npt_init_mk_rinv  (m: VNPTINTRO_mem) (index: Z):
    VNPTINTRO.RInv  (kern_low:= kern_low) (kern_high:= kern_high) (maxpage:= maxpage) (num_proc:= num_proc) (PgSize:= PgSize) (num_chan:= num_chan) (npt_init_mk_rdata m index).
  Proof.
    unfold npt_init_mk_rdata.
    generalize (VNPTINTRO.INV (Mem.get_abstract_data m)).
    intro HRINV.
    inv HRINV.
    unfold npt_init_madt.
    constructor; simpl; auto.
    intro contra; discriminate contra.
  Qed.

  Lemma npt_init_ABD_EX (m: VNPTINTRO_mem) (index: Z):
    {abd | (VNPTINTRO.ADT (kern_low:= kern_low) (kern_high:= kern_high) (maxpage:= maxpage) (num_proc:= num_proc) (PgSize:= PgSize) (num_chan:= num_chan) abd) = (npt_init_mk_rdata m index)}. 
  Proof.
    unfold npt_init_mk_rdata.
    exists (VNPTINTRO.mkAbData (npt_init_mk_rdata m index) (npt_init_mk_rinv m index)).
    simpl.
    trivial.
  Qed.

  Definition npt_init_mk_abdata (m: VNPTINTRO_mem) (index: Z) := match (npt_init_ABD_EX m index) with
    | exist a _ => a
  end. 

End CInitSpecsVNPTINTRO.


Section CInitSpecsVVMCBINTRO.

  Context `{real_params_ops : RealParamsOps}.

  Notation DATA := (VVMCBINTRO.AbData (PgSize:= PgSize) (num_proc:= num_proc) (kern_high:= kern_high) (kern_low := kern_low) (maxpage:= maxpage) (num_chan:= num_chan)).

  Local Instance vdataOp:AbstractDataOps DATA:= (VVMCBINTRO.abstract_data (Hnpc:= Hnpc)).

  Context {VVMCBINTRO_mem} 
              `{Hlmmh: !LayerMemoryModel DATA VVMCBINTRO_mem}.

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
    (  4, VirtDataType.VMCBEntryZValid 7391)::
    (  3, VirtDataType.VMCBEntryZValid 151273473)::
    ( 24, VirtDataType.VMCBEntryZValid 16777216)::
    ( 36, VirtDataType.VMCBEntryZValid 1)::
    ( 22, VirtDataType.VMCBEntryZValid 1)::
    (411, VirtDataType.VMCBEntryZValid 459782)::
    (410, VirtDataType.VMCBEntryZValid 459782)::
    (308, VirtDataType.VMCBEntryZValid 4096)::
    (344, VirtDataType.VMCBEntryZValid 1024)::
    (346, VirtDataType.VMCBEntryZValid 4294905840)::
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

  Definition vmcb_init_madt (m: VVMCBINTRO_mem) := VVMCBINTRO.ADT (Mem.get_abstract_data m).

  Definition vmcb_init_mk_rdata (m: VVMCBINTRO_mem) (index: Z) := let adt := (vmcb_init_madt m) in (VVMCBINTRO.mkRData (VVMCBINTRO.HP adt) (VVMCBINTRO.AT adt) (VVMCBINTRO.nps adt) (VVMCBINTRO.ti adt) (VVMCBINTRO.PT adt) (VVMCBINTRO.ptpool adt) (VVMCBINTRO.pb adt) (VVMCBINTRO.kctxt adt) (VVMCBINTRO.abtcb adt) (VVMCBINTRO.abq adt) (VVMCBINTRO.uctxt adt) (VVMCBINTRO.npt adt) (VVMCBINTRO.hctx adt) (VVMCBINTRO.cid adt) (VVMCBINTRO.chpool adt) (VVMCBINTRO.pe adt) (VVMCBINTRO.ikern adt) true (VVMCBINTRO.vmcb_v adt) (Calculate_vmcb_z (Z.to_nat index) (VVMCBINTRO.vmcb_z adt))).
    
  Lemma vmcb_init_mk_rinv  (m: VVMCBINTRO_mem) (index: Z):
    VVMCBINTRO.RInv  (kern_low:= kern_low) (kern_high:= kern_high) (maxpage:= maxpage) (num_proc:= num_proc) (PgSize:= PgSize) (num_chan:= num_chan) (vmcb_init_mk_rdata m index).
  Proof.
    unfold vmcb_init_mk_rdata.
    generalize (VVMCBINTRO.INV (Mem.get_abstract_data m)).
    intro HRINV.
    inv HRINV.
    unfold vmcb_init_madt.
    constructor; simpl; auto.
    intro contra; discriminate contra.
  Qed.

  Lemma vmcb_init_ABD_EX (m: VVMCBINTRO_mem) (index: Z):
    {abd | (VVMCBINTRO.ADT (kern_low:= kern_low) (kern_high:= kern_high) (maxpage:= maxpage) (num_proc:= num_proc) (PgSize:= PgSize) (num_chan:= num_chan) abd) = (vmcb_init_mk_rdata m index)}. 
  Proof.
    unfold vmcb_init_mk_rdata.
    exists (VVMCBINTRO.mkAbData (vmcb_init_mk_rdata m index) (vmcb_init_mk_rinv m index)).
    simpl.
    trivial.
  Qed.

  Definition vmcb_init_mk_abdata (m: VVMCBINTRO_mem) (index: Z) := match (vmcb_init_ABD_EX m index) with
    | exist a _ => a
  end. 

End CInitSpecsVVMCBINTRO.
