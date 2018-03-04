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
(*              Layers of VMM: MPTNew                                  *)
(*                                                                     *)
(*          Create and Remove a Page Map                               *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the abstract data and the primitives for the MPTNew layer, which will introduce the primitves to find and free a page table from the page table pool*)
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
Require Import LoadStoreSem2.
Require Import XOmega.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import CalRealPTPool.
Require Import CalRealPT.
Require Import CalRealIDPDE.
Require Import CalRealInitPTE.

Require Import INVLemmaContainer.
Require Import INVLemmaMemory.

Require Export MPTInit.
Require Import AbstractDataType.

Section WITHMEM.
 
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section INV.

    Global Instance pt_new_inv: PreservesInvariants pt_new_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      exploit split_container_valid; eauto.
      eapply container_split_some; eauto.
      auto.
    Qed.

    Global Instance pmap_init_inv: PreservesInvariants pmap_init_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant.
      - apply real_nps_range.
      - apply real_lat_kern_valid.
      - apply real_lat_usr_valid.
      - apply real_container_valid.
      - rewrite init_pperm; try assumption.
        apply Lreal_pperm_valid.
      - eapply real_pt_PMap_valid; eauto.
      - apply real_pt_PMap_kern.
      - omega.
      - assumption.
      - apply real_idpde_init.
      - apply real_pt_consistent_pmap. 
      - apply real_pt_consistent_pmap_domain. 
      - apply Lreal_at_consistent_lat_domain.
      - eapply LATable_nil_real; eauto.
    Qed.

    Section PTRESV.

      Lemma ptResv_high_level_inv:
        forall d d' n vadr p v,
          ptResv_spec n vadr p d = Some (d', v) ->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.     
        intros. functional inversion H; subst; eauto; clear H.
        eapply ptInsert_high_level_inv; try eassumption.
        eapply alloc_high_level_inv; eassumption.
      Qed.

      Lemma ptResv_low_level_inv:
        forall d d' n vadr p n' v,
          ptResv_spec n vadr p d = Some (d', v) ->
          low_level_invariant n' d ->
          low_level_invariant n' d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        eapply ptInsert_low_level_inv; try eassumption.
        eapply alloc_low_level_inv; eassumption.
      Qed.

      Lemma ptResv_kernel_mode:
        forall d d' n vadr p v,
          ptResv_spec n vadr p d = Some (d', v) ->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        eapply ptInsert_kernel_mode; try eassumption.
        eapply alloc_kernel_mode; eassumption.
      Qed.

      Global Instance ptResv_inv: PreservesInvariants  ptResv_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply ptResv_low_level_inv; eassumption.
        - eapply ptResv_high_level_inv; eassumption.
        - eapply ptResv_kernel_mode; eassumption.
      Qed.

    End PTRESV.

    Section PTRESV2.

      Lemma ptResv2_high_level_inv:
        forall d d' n vadr p n' vadr' p' v,
          ptResv2_spec n vadr p n' vadr' p' d = Some (d', v) ->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros; functional inversion H; subst; eauto; clear H.
        eapply ptInsert_high_level_inv; try eassumption.
        eapply alloc_high_level_inv; eassumption.
        eapply ptInsert_high_level_inv; try eassumption.
        eapply ptInsert_high_level_inv; try eassumption.
        eapply alloc_high_level_inv; eassumption.
      Qed.

      Lemma ptResv2_low_level_inv:
        forall d d' n vadr p n' vadr' p' l v,
          ptResv2_spec n vadr p n' vadr' p' d = Some (d', v) ->
          low_level_invariant l d ->
          low_level_invariant l d'.
      Proof.
        intros; functional inversion H; subst; eauto;
        eapply ptInsert_low_level_inv; try eassumption.
        - eapply alloc_low_level_inv; eassumption.
        - eapply ptInsert_low_level_inv; try eassumption.
          eapply alloc_low_level_inv; eassumption.
      Qed.

      Lemma ptResv2_kernel_mode:
        forall d d' n vadr p n' vadr' p' v,
          ptResv2_spec n vadr p n' vadr' p' d = Some (d', v) ->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros; functional inversion H; subst; eauto;
        eapply ptInsert_kernel_mode; try eassumption.
        - eapply alloc_kernel_mode; eassumption.
        - eapply ptInsert_kernel_mode; try eassumption.
          eapply alloc_kernel_mode; eassumption.
      Qed.

      Global Instance ptResv2_inv: PreservesInvariants  ptResv2_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply ptResv2_low_level_inv; eassumption.
        - eapply ptResv2_high_level_inv; eassumption.
        - eapply ptResv2_kernel_mode; eassumption.
      Qed.

    End PTRESV2.

    Global Instance alloc_inv: PreservesInvariants alloc_spec.
    Proof.
      preserves_invariants_simpl'.
      - eapply alloc_low_level_inv; eassumption.
      - eapply alloc_high_level_inv; eassumption.
      - eapply alloc_kernel_mode; eassumption.
    Qed.

    Global Instance pfree_inv: PreservesInvariants pfree_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      - intros; eapply LAT_kern_norm; eauto. 
      - intros; eapply LAT_usr_norm; eauto.
      - eapply Lconsistent_ppage_norm_undef; eauto.
      - eapply dirty_ppage_gso_undef; eauto.
      - eapply consistent_pmap_gso_pperm_alloc; eauto.
      - eapply consistent_pmap_domain_gso_at_0; eauto.
      - eapply consistent_lat_domain_gss_nil; eauto.
      - eapply LATable_nil_gss_nil; eauto.
    Qed.

  End INV.

  (** * Specification of primitives that will be implemented at this layer*)
  Definition exec_loadex {F V} := exec_loadex2 (F := F) (V := V).

  Definition exec_storeex {F V} :=  exec_storeex2 (flatmem_store:= flatmem_store) (F := F) (V := V).

  Global Instance flatmem_store_inv: FlatmemStoreInvariant (flatmem_store:= flatmem_store).
  Proof.
    split; inversion 1; intros. 
    - functional inversion H0. split; trivial.
    - functional inversion H1. 
      split; simpl; try (eapply dirty_ppage_store_unmaped'; try reflexivity; try eassumption); trivial.
  Qed.

  Global Instance trapinfo_set_inv: TrapinfoSetInvariant.
  Proof.
    split; inversion 1; intros; constructor; auto.
  Qed.

  (** * Layer Definition *)
  (** ** Layer Definition newly introduced  *)
  Definition mptnew_fresh : compatlayer (cdata RData) :=
    pt_resv ↦ gensem ptResv_spec
            ⊕ pt_resv2 ↦ gensem ptResv2_spec
            ⊕ pt_new ↦ gensem pt_new_spec
            (*⊕ pt_free ↦ gensem pt_free_spec*)
            ⊕ pmap_init ↦ gensem pmap_init_spec.

  (** ** Layer Definition passthrough  *)
  Definition mptnew_passthrough : compatlayer (cdata RData) :=
    fload ↦ gensem fload_spec
          ⊕ fstore ↦ gensem fstore_spec
          ⊕ flatmem_copy ↦ gensem flatmem_copy_spec
          ⊕ vmxinfo_get ↦ gensem vmxinfo_get_spec
          ⊕ device_output ↦ gensem device_output_spec
          ⊕ pfree ↦ gensem pfree_spec
          ⊕ set_pt ↦ gensem setPT_spec
          ⊕ pt_read ↦ gensem ptRead_spec
          ⊕ pt_read_pde ↦ gensem ptReadPDE_spec
          ⊕ pt_free_pde ↦ gensem ptFreePDE0_spec
          ⊕ pt_rmv ↦ gensem ptRmv0_spec
          ⊕ pt_in ↦ primcall_general_compatsem' ptin_spec (prim_ident:= pt_in)
          ⊕ pt_out ↦ primcall_general_compatsem' ptout_spec (prim_ident:= pt_out)
          ⊕ clear_cr2 ↦ gensem clearCR2_spec
          ⊕ container_get_nchildren ↦ gensem container_get_nchildren_spec
          ⊕ container_get_quota ↦ gensem container_get_quota_spec
          ⊕ container_get_usage ↦ gensem container_get_usage_spec
          ⊕ container_can_consume ↦ gensem container_can_consume_spec
          ⊕ container_alloc ↦ gensem alloc_spec
          ⊕ trap_in ↦ primcall_general_compatsem trapin_spec
          ⊕ trap_out ↦ primcall_general_compatsem trapout_spec
          ⊕ host_in ↦ primcall_general_compatsem hostin_spec
          ⊕ host_out ↦ primcall_general_compatsem hostout_spec
          ⊕ trap_get ↦ primcall_trap_info_get_compatsem trap_info_get_spec
          ⊕ trap_set ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec
          ⊕ accessors ↦ {| exec_load := @exec_loadex; 
                           exec_store := @exec_storeex |}.

  (** * Layer Definition *)
  Definition mptnew : compatlayer (cdata RData) := mptnew_fresh ⊕ mptnew_passthrough.

End WITHMEM.
