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
(*              Object Primitives                                      *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Maps.
Require Import AuxStateDataType.
Require Import FlatMemory.
Require Import AbstractDataType.
Require Import Integers.
Require Import Values.
Require Import RealParams.

Section PRIM_MM.

  Context `{real_params: RealParams}.

  (** primitve: returns whether i-th piece of memory in MMTable is usable or not*)
  Definition is_mm_usable_spec (i: Z) (adt: RData) : option Z := 
    match (ikern adt, ihost adt) with 
      | (true, true) =>
        match ZMap.get i (MM adt) with
          | MMValid _ _ MMUsable => Some 1
          | MMValid _ _ _ => Some 0 
          | _ => None
        end
      | _ => None
    end.

  (** primitve: returns the start address of the i-th piece of memory in MMTable*)
  Definition get_mm_s_spec (i: Z) (adt: RData): option Z :=
    match (ikern adt, ihost adt, ZMap.get i (MM adt)) with 
      | (true, true, MMValid s _ _) => Some s
      | _ => None
    end.

  (** primitve: returns the length of the i-th piece of memory in MMTable*)
  Definition get_mm_l_spec (i: Z) (adt: RData): option Z :=
    match (ikern adt, ihost adt, ZMap.get i (MM adt)) with 
      | (true, true, MMValid _ l _) => Some l
      | _ => None
    end.

  (** primitve: the first primitive that should be called during the initialization. 
    It will initial the MMTable and MMSize, which will not be verified *)
  Function bootloader_spec (mbi: Z) (adt: RData): option RData :=
    match (pg adt, ikern adt, ihost adt) with
      | (false, true, true) => Some adt {MM: real_mm} {MMSize: real_size} {vmxinfo: real_vmxinfo}
      | _ => None
    end.  

  (** primitve: the first primitive that should be called during the initialization. 
     It will initial the MMTable and MMSize, which will not be verified*)
  Function bootloader0_spec (mbi_adr:Z) (adt: RData)  : option RData :=
    match (pg adt, ikern adt, ihost adt, init adt) with
      | (false, true, true, false) => Some adt {MM: real_mm} {MMSize: real_size} {vmxinfo: real_vmxinfo} {init: true}
      | _ => None
    end.  

End PRIM_MM.

Require Import liblayers.compat.CompatGenSem.
Require Import liblayers.compat.CompatLayers.
Require Import CommonTactic.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import AuxLemma.
Require Import Observation.

Section OBJ_SIM.

  Context `{Hobs: Observation}.

  Context `{data : CompatData(Obs:=Obs) RData}.
  Context `{data0 : CompatData(Obs:=Obs) RData}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Notation HDATAOps := (cdata (cdata_prf := data) RData).
  Notation LDATAOps := (cdata (cdata_prf := data0) RData).

  Context `{rel_prf: CompatRel _ (Obs:=Obs) (memory_model_ops:= memory_model_ops) _
                               (stencil_ops:= stencil_ops) HDATAOps LDATAOps}.


  Section BOOTLOADER_SIM.

    Context `{real_params: RealParams}.

    Context {re1: relate_impl_iflags}.
    Context {re5: relate_impl_MM}.
    Context {re6: relate_impl_vmxinfo}.

    Lemma bootloader_exist:
      forall s habd habd' labd i f,
        bootloader_spec i habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', bootloader_spec i labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold bootloader_spec; intros. 
      exploit relate_impl_iflags_eq; eauto. inversion 1. 
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.

      apply relate_impl_vmxinfo_update.
      apply relate_impl_MMSize_update.
      apply relate_impl_MM_update. assumption.
    Qed.

    Context {mt4: match_impl_MM}.
    Context {mt5: match_impl_vmxinfo}.

    Lemma bootloader_match:
      forall s d d' m i f,
        bootloader_spec i d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold bootloader_spec; intros. subdestruct. inv H. 
      eapply match_impl_vmxinfo_update.
      eapply match_impl_MMSize_update.
      eapply match_impl_MM_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) bootloader_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) bootloader_spec}.

    Lemma bootloader_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem bootloader_spec)
            (id ↦ gensem bootloader_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit bootloader_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply bootloader_match; eauto.
    Qed.

  End BOOTLOADER_SIM.

  Section BOOTLOADER0_SIM.

    Context `{real_params: RealParams}.

    Context {re1: relate_impl_iflags}.
    Context {re2: relate_impl_MM}.
    Context {re3: relate_impl_vmxinfo}.
    Context {re4: relate_impl_init}.

    Lemma bootloader0_exist:
      forall s habd habd' labd i f,
        bootloader0_spec i habd = Some habd'
        -> relate_AbData s f habd labd
        -> exists labd', bootloader0_spec i labd = Some labd' 
                         /\ relate_AbData s f habd' labd'.
    Proof.
      unfold bootloader0_spec; intros.
      exploit relate_impl_iflags_eq; eauto. inversion 1.
      exploit relate_impl_init_eq; eauto. intros.
      revert H; subrewrite. subdestruct.
      inv HQ. refine_split'; trivial.

      apply relate_impl_init_update.
      apply relate_impl_vmxinfo_update.
      apply relate_impl_MMSize_update.
      apply relate_impl_MM_update. assumption.
    Qed.

    Context {mt4: match_impl_MM}.
    Context {mt5: match_impl_vmxinfo}.
    Context {mt6: match_impl_init}.

    Lemma bootloader0_match:
      forall s d d' m i f,
        bootloader0_spec i d = Some d'
        -> match_AbData s d m f
        -> match_AbData s d' m f.
    Proof.
      unfold bootloader0_spec; intros. subdestruct. inv H. 
      eapply match_impl_init_update.
      eapply match_impl_vmxinfo_update.
      eapply match_impl_MMSize_update.
      eapply match_impl_MM_update. assumption.
    Qed.

    Context {inv: PreservesInvariants (HD:= data) bootloader0_spec}.
    Context {inv0: PreservesInvariants (HD:= data0) bootloader0_spec}.

    Lemma bootloader0_sim :
      forall id,
        sim (crel RData RData) (id ↦ gensem bootloader0_spec)
            (id ↦ gensem bootloader0_spec).
    Proof.
      intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
      exploit bootloader0_exist; eauto 1; intros [labd' [HP HM]].
      match_external_states_simpl.
      eapply bootloader0_match; eauto.
    Qed.

  End BOOTLOADER0_SIM.

  Context {re1: relate_impl_MM}.
  Context {re1': relate_impl_MM'}.

  Lemma get_size_sim:
    forall id,
      sim (crel RData RData) (id ↦ gensem MMSize) (id ↦ gensem MMSize).
  Proof.
    intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
    match_external_states_simpl.
    erewrite <- relate_impl_MMSize_eq; eauto. subrewrite'.
  Qed.

  Context {re2: relate_impl_iflags}.

  Lemma is_mm_usable_sim:
    forall id,
      sim (crel RData RData) (id ↦ gensem is_mm_usable_spec) (id ↦ gensem is_mm_usable_spec).
  Proof.
    intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
    match_external_states_simpl.
    unfold is_mm_usable_spec in *.
    exploit relate_impl_iflags_eq; eauto. inversion 1. 
    exploit relate_impl_MM_eq; eauto; intros.
    revert H2; subrewrite. subdestruct.
    - inv HQ. refine_split'; trivial.
    - inv HQ. refine_split'; trivial.
  Qed.

  Lemma get_mm_s_sim:
    forall id,
      sim (crel RData RData) (id ↦ gensem get_mm_s_spec) (id ↦ gensem get_mm_s_spec).
  Proof.
    intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
    match_external_states_simpl.
    unfold get_mm_s_spec in *.
    exploit relate_impl_iflags_eq; eauto. inversion 1. 
    exploit relate_impl_MM_eq; eauto; intros.
    revert H2; subrewrite. subdestruct.
    inv HQ. refine_split'; trivial.
  Qed.

  Lemma get_mm_l_sim:
    forall id,
      sim (crel RData RData) (id ↦ gensem get_mm_l_spec) (id ↦ gensem get_mm_l_spec).
  Proof.
    intros. layer_sim_simpl. compatsim_simpl (@match_AbData). intros.
    match_external_states_simpl.
    unfold get_mm_l_spec in *.
    exploit relate_impl_iflags_eq; eauto. inversion 1. 
    exploit relate_impl_MM_eq; eauto; intros.
    revert H2; subrewrite. subdestruct.
    inv HQ. refine_split'; trivial.
  Qed.

End OBJ_SIM.
