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
(*              Layers of VMM: MPTOP                                   *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the abstract data and the primitives for the MPTOp layer, which will introduce high-level primitives to operate on page table*)
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

(*Require Import CalRealPTPool.*)

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import INVLemmaContainer.
Require Import INVLemmaMemory.
Require Import CalRealIDPDE.
Require Import CalRealInitPTE.
Require Import CalRealPTPool.

Require Export MPTIntro.
Require Import AbstractDataType.

Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.
  Context `{real_params: RealParams}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section INV.

    Global Instance ptInsertAux_inv: PreservesInvariants ptInsertAux_spec.
    Proof.
      unfold ptInsertAux_spec.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto;
      subdestruct; try (inv H8; rewrite ZMap.gso; auto).
    Qed.

    Global Instance ptInsertPDE_inv: PreservesInvariants ptInsertPDE_spec.
    Proof.
      unfold ptInsertPDE_spec.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto;
      try (rewrite ZMap.gso; eauto; fail).
      - apply consistent_ppage_alloc_hide; assumption. 
      - apply dirty_ppage_gss; assumption.        
    Qed.

    (** * Proofs that the primitives satisfies the invariants at this layer *)
    Global Instance ptRmvAux_inv: PreservesInvariants ptRmvAux_spec.
    Proof.
      unfold ptRmvAux_spec.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto;
      subdestruct; try (inv H7; rewrite ZMap.gso; auto).
    Qed.

    (** * Proofs that the primitives satisfies the invariants at this layer *)
    Global Instance ptRmvPDE_inv: PreservesInvariants ptRmvPDE_spec.
    Proof.
      unfold ptRmvPDE_spec.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto;
      try (rewrite ZMap.gso; eauto; fail).
      - eapply consistent_ppage_hide_alloc; eassumption.
      - eapply dirty_ppage_gso_alloc; eauto.
      - eapply consistent_ppage_hide_alloc; eassumption.
      - eapply dirty_ppage_gso_alloc; eauto.
    Qed.

    Global Instance idpde_init_inv: PreservesInvariants idpde_init_spec.
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
  Definition mptop_fresh : compatlayer (cdata RData) :=
    pt_read ↦ gensem ptRead_spec
            ⊕ pt_read_pde ↦ gensem ptReadPDE_spec
            ⊕ pt_insert_aux ↦ gensem ptInsertAux_spec
            ⊕ pt_insert_pde ↦ gensem ptInsertPDE_spec
            ⊕ pt_rmv_aux ↦ gensem ptRmvAux_spec
            ⊕ pt_rmv_pde ↦ gensem ptRmvPDE_spec
            ⊕ idpde_init ↦ gensem idpde_init_spec.

  (** ** Layer Definition passthrough  *)
  Definition mptop_passthrough : compatlayer (cdata RData) :=
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
          ⊕ rmv_PDE ↦ gensem rmvPDE_spec
          ⊕ rmv_PTE ↦ gensem rmvPTE_spec
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
  Definition mptop : compatlayer (cdata RData) := mptop_fresh ⊕ mptop_passthrough.

  (* Definition semantics := LAsm.Lsemantics mptintro.*)

End WITHMEM.
