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
(*              Layers of VMM: MPTKern                                 *)
(*                                                                     *)
(*          initialize the page map of the kernel thread               *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the abstract data and the primitives for the MPTKern layer, which will initialize kernel's page table ([0th page table])*)
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
Require Import CalRealPT.
Require Import INVLemmaContainer.
Require Import INVLemmaMemory.
Require Import CalRealIDPDE.
Require Import CalRealInitPTE.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import AbstractDataType.
Require Export MPTCommon.

Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section INV.

    Section PTINSERT.
 
      Section PTINSERT_PTE.

        Lemma ptInsertPTE_high_level_inv:
          forall d d' n vadr padr p,
            ptInsertPTE_spec n vadr padr p d = Some d' ->
            high_level_invariant d ->
            high_level_invariant d'.
        Proof.
          intros. functional inversion H; subst; eauto. 
          inv H0; constructor_gso_simpl_tac.
          - intros; eapply AT_kern_norm; eauto. 
          - intros; eapply AT_usr_norm; eauto.
          - apply ptInsertPTE_quota_bounded_AT in H; auto.
          - eapply consistent_ppage_norm; eassumption.
          - intros. congruence.
        Qed.

        Lemma ptInsertPTE_low_level_inv:
          forall d d' n vadr padr p n',
            ptInsertPTE_spec n vadr padr p d = Some d' ->
            low_level_invariant n' d ->
            low_level_invariant n' d'.
        Proof.
          intros. functional inversion H; subst; eauto.
          inv H0. constructor; eauto.
        Qed.

        Lemma ptInsertPTE_kernel_mode:
          forall d d' n vadr padr p,
            ptInsertPTE_spec n vadr padr p d = Some d' ->
            kernel_mode d ->
            kernel_mode d'.
        Proof.
          intros. functional inversion H; subst; eauto.
        Qed.

      End PTINSERT_PTE.

      Lemma ptInsert_high_level_inv:
        forall d d' n vadr padr p v,
          ptInsert_spec n vadr padr p d = Some (d', v) ->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; eauto. 
        - eapply ptInsertPTE_high_level_inv; eassumption.
        - eapply ptAllocPDE_high_level_inv; eassumption.
        - eapply ptInsertPTE_high_level_inv; try eassumption.
          eapply ptAllocPDE_high_level_inv; eassumption.
      Qed.

      Lemma ptInsert_low_level_inv:
        forall d d' n vadr padr p n' v,
          ptInsert_spec n vadr padr p d = Some (d', v) ->
          low_level_invariant n' d ->
          low_level_invariant n' d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        - eapply ptInsertPTE_low_level_inv; eassumption.
        - eapply ptAllocPDE_low_level_inv; eassumption.
        - eapply ptInsertPTE_low_level_inv; try eassumption.
          eapply ptAllocPDE_low_level_inv; eassumption.
      Qed.

      Lemma ptInsert_kernel_mode:
        forall d d' n vadr padr p v,
          ptInsert_spec n vadr padr p d = Some (d', v) ->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        - eapply ptInsertPTE_kernel_mode; eassumption.
        - eapply ptAllocPDE_kernel_mode; eassumption.
        - eapply ptInsertPTE_kernel_mode; try eassumption.
          eapply ptAllocPDE_kernel_mode; eassumption.
      Qed.

      Global Instance ptInsert_inv: PreservesInvariants ptInsert_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply ptInsert_low_level_inv; eassumption.
        - eapply ptInsert_high_level_inv; eassumption.
        - eapply ptInsert_kernel_mode; eassumption.
      Qed.

    End PTINSERT.

    Global Instance ptRmv_inv: PreservesInvariants ptRmv_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto;
      try (rewrite ZMap.gso; eauto; fail).
      - intros; eapply AT_kern_norm; eauto. 
      - intros; eapply AT_usr_norm; eauto.
      - apply ptRmv_quota_bounded_AT in H2; auto.
      - eapply consistent_ppage_norm; eassumption.
    Qed.

    Global Instance pt_init_kern_inv: PreservesInvariants pt_init_kern_spec.
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
  Definition mptkern_fresh : compatlayer (cdata RData) :=
    pt_insert ↦ gensem ptInsert_spec
              ⊕ pt_rmv ↦ gensem ptRmv_spec
              ⊕ pt_init_kern ↦ gensem pt_init_kern_spec.

  (** ** Layer Definition passthrough  *)
  Definition mptkern_passthrough : compatlayer (cdata RData) :=
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

          ⊕ pt_read ↦ gensem ptRead_spec
          ⊕ pt_read_pde ↦ gensem ptReadPDE_spec
          ⊕ pt_free_pde ↦ gensem ptFreePDE_spec

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
  Definition mptkern : compatlayer (cdata RData) := mptkern_fresh ⊕ mptkern_passthrough.

  (*Definition semantics := LAsm.Lsemantics mptintro.*)

End WITHMEM.

Section WITHPARAM.

  Context `{real_params: RealParams}.

  Local Open Scope Z_scope.

  Section Impl.

  Function pt_init_spec (mbi_adr:Z) (adt: RData): option RData :=
    match (init adt, pg adt, ikern adt, ihost adt, ipt adt) with
      | (false, false, true, true, true) => 
        Some adt {vmxinfo: real_vmxinfo} {pg: true} {AT: real_AT (AT adt)} {nps: real_nps}
             {AC: real_AC} {init: true} {PT: 0} {ptpool: real_pt (ptpool adt)}
             {idpde: real_idpde (idpde adt)}
      | _ => None
    end.

  End Impl.

End WITHPARAM.
