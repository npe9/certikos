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
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the abstract data and the primitives for the MPTComm layer, which will initialize the common part (0-1G, 3G-4G) of all the page tables*)
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

Require Import CalRealPTPool.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import INVLemmaContainer.
Require Import INVLemmaMemory.
Require Import CalRealIDPDE.
Require Import CalRealPT.
Require Import CalRealInitPTE.

Require Import AbstractDataType.

Require Export MPTOp.

Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section INV.

    Section PTALLOCPDE.

      Lemma ptAllocPDE_high_level_inv:
        forall d d' n vadr v,
          ptAllocPDE_spec n vadr d = Some (d', v) ->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        inv H0; constructor_gso_simpl_tac.
        - intros; eapply AT_kern_norm'; eauto.
        - intros; eapply AT_usr_norm; eauto.
        - eapply alloc_container_valid'; eauto.
        - apply ptAllocPDE_quota_bounded_AT in H; auto.
        - apply consistent_ppage_norm_hide; try assumption. 
        - intros; congruence.
        - eapply dirty_ppage_gss; eauto.
        - intros; congruence.
      Qed.

      Lemma ptAllocPDE_low_level_inv:
        forall d d' n vadr v n',
          ptAllocPDE_spec n vadr d = Some (d', v) ->
          low_level_invariant n' d ->
          low_level_invariant n' d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        inv H0. constructor; eauto.
      Qed.

      Lemma ptAllocPDE_kernel_mode:
        forall d d' n vadr v,
          ptAllocPDE_spec n vadr d = Some (d', v) ->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; eauto.
      Qed.

      Global Instance ptAllocPDE_inv: PreservesInvariants ptAllocPDE_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply ptAllocPDE_low_level_inv; eassumption.
        - eapply ptAllocPDE_high_level_inv; eassumption.
        - eapply ptAllocPDE_kernel_mode; eassumption.
      Qed.

    End PTALLOCPDE.

    Section PTPFREEPDE.

      Lemma ptFreePDE_high_level_inv:
        forall d d' n vadr,
          ptFreePDE_spec n vadr d = Some d' ->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; eauto. 
        inv H0; constructor_gso_simpl_tac.
        - intros; eapply AT_kern_norm; eauto. 
        - intros; eapply AT_usr_norm; eauto.
        - apply pfree_quota_bounded_AT; auto.
        - apply consistent_ppage_norm_undef; try assumption. 
        - intros; congruence.
        - eapply dirty_ppage_gso_undef; eauto.
        - intros; congruence.
      Qed.

      Lemma ptFreePDE_low_level_inv:
        forall d d' n vadr n',
          ptFreePDE_spec n vadr d = Some d' ->
          low_level_invariant n' d ->
          low_level_invariant n' d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        inv H0. constructor; eauto.
      Qed.

      Lemma ptFreePDE_kernel_mode:
        forall d d' n vadr,
          ptFreePDE_spec n vadr d = Some d' ->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; eauto.
      Qed.

      Global Instance ptFreePDE_inv: PreservesInvariants ptFreePDE_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply ptFreePDE_low_level_inv; eassumption.
        - eapply ptFreePDE_high_level_inv; eassumption.
        - eapply ptFreePDE_kernel_mode; eassumption.
      Qed.

    End PTPFREEPDE.
    
    Global Instance pt_init_comm_inv: PreservesInvariants pt_init_comm_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      - apply real_nps_range.
      - apply real_at_kern_valid.
      - apply real_at_usr_valid.
      - apply real_container_valid.
      - apply real_quota_bounded_AT.
      - rewrite init_pperm; try assumption.
        apply real_pperm_valid.        
    Qed.

  End INV.

  (** * Layer Definition *)
  (** ** Layer Definition newly introduced  *)
  Definition mptcommon_fresh : compatlayer (cdata RData) :=
    pt_alloc_pde ↦ gensem ptAllocPDE_spec
                 ⊕ pt_free_pde ↦ gensem ptFreePDE_spec
                 ⊕ pt_init_comm ↦ gensem pt_init_comm_spec.

  (** ** Layer Definition passthrough  *)
  Definition mptcommon_passthrough : compatlayer (cdata RData) :=
    fload ↦ gensem fload_spec
          ⊕ fstore ↦ gensem fstore_spec
          ⊕ flatmem_copy ↦ gensem flatmem_copy_spec
          ⊕ vmxinfo_get ↦ gensem vmxinfo_get_spec
          ⊕ device_output ↦ gensem device_output_spec
          ⊕ set_pg ↦ gensem setPG1_spec
          ⊕ at_get_c ↦ gensem get_at_c_spec
          ⊕ at_set_c ↦ gensem set_at_c0_spec
          ⊕ pfree ↦ gensem pfree'_spec
          ⊕ set_pt ↦ gensem setPT'_spec
          ⊕ set_PDE ↦ gensem setPDE_spec

          ⊕ pt_read ↦ gensem ptRead_spec
          ⊕ pt_read_pde ↦ gensem ptReadPDE_spec
          ⊕ pt_insert_aux ↦ gensem ptInsertAux_spec
          ⊕ pt_rmv_aux ↦ gensem ptRmvAux_spec

          ⊕ pt_in ↦ primcall_general_compatsem' ptin'_spec (prim_ident:= pt_in)
          ⊕ pt_out ↦ primcall_general_compatsem' ptout_spec (prim_ident:= pt_out)
          ⊕ clear_cr2 ↦ gensem clearCR2_spec
          ⊕ container_get_parent ↦ gensem container_get_parent_spec
          ⊕ container_get_nchildren ↦ gensem container_get_nchildren_spec
          ⊕ container_get_quota ↦ gensem container_get_quota_spec
          ⊕ container_get_usage ↦ gensem container_get_usage_spec
          ⊕ container_can_consume ↦ gensem container_can_consume_spec
          ⊕ container_split ↦ gensem container_split_spec
          ⊕ container_alloc ↦ gensem container_alloc_spec
          ⊕ trap_in ↦ primcall_general_compatsem trapin_spec
          ⊕ trap_out ↦ primcall_general_compatsem trapout_spec
          ⊕ host_in ↦ primcall_general_compatsem hostin_spec
          ⊕ host_out ↦ primcall_general_compatsem hostout_spec
          ⊕ trap_get ↦ primcall_trap_info_get_compatsem trap_info_get_spec
          ⊕ trap_set ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec
          ⊕ accessors ↦ {| exec_load := (@exec_loadex _ _ Hmwd); 
                           exec_store := (@exec_storeex _ _ Hmwd) |}.

  (** * Layer Definition *)
  Definition mptcommon : compatlayer (cdata RData) := mptcommon_fresh ⊕ mptcommon_passthrough.

End WITHMEM.
