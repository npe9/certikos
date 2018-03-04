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
(*              Layers of VM: PIPCIntro                                *)
(*                                                                     *)
(*          Provide the abstraction of ipc channel                     *)
(*                                                                     *)
(*          Haozhong Zhang <haozhong.zhang@yale.edu>                   *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the abstract data and the primitives for the PIPCIntro layer,
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
Require Import CalRealSMSPool.
Require Import CalRealProcModule.

Require Import INVLemmaMemory.
Require Import INVLemmaThread.

Require Import AbstractDataType.

Require Export PThread.
Require Export ObjSyncIPC.
Require Import ObjThread.


(** * Abstract Data and Primitives at this layer*)
Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section INV.

    Global Instance set_sync_chan_to_inv: PreservesInvariants set_sync_chan_to_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto 2.
    Qed.

    Global Instance set_sync_chan_count_inv: PreservesInvariants set_sync_chan_count_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto 2.
    Qed.

    Global Instance set_sync_chan_paddr_inv: PreservesInvariants set_sync_chan_paddr_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto 2.
    Qed.

    Global Instance init_sync_chan_inv: PreservesInvariants init_sync_chan_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto 2.
    Qed.

    Global Instance flatmem_copy_inv: PreservesInvariants flatmem_copy_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant;      
      try eapply dirty_ppage_gss_copy; eauto.
    Qed.

    (*Global Instance set_chan_info_inv: PreservesInvariants set_chan_info_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto 2.
    Qed.

    Global Instance set_chan_content_inv: PreservesInvariants set_chan_content_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto 2.
    Qed.

    Global Instance init_chan_inv: PreservesInvariants init_chan_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto 2.
    Qed.*)

  End INV.

  (** * Layer Definition *)
  Definition pipcintro_fresh : compatlayer (cdata RData) :=
    get_sync_chan_to ↦ gensem get_sync_chan_to_spec
                     ⊕ get_sync_chan_paddr ↦ gensem get_sync_chan_paddr_spec
                     ⊕ get_sync_chan_count ↦ gensem get_sync_chan_count_spec
                     ⊕ set_sync_chan_to ↦ gensem set_sync_chan_to_spec
                     ⊕ set_sync_chan_paddr ↦ gensem set_sync_chan_paddr_spec
                     ⊕ set_sync_chan_count ↦ gensem set_sync_chan_count_spec
                     ⊕ init_sync_chan ↦ gensem init_sync_chan_spec
                     ⊕ get_kernel_pa ↦ gensem get_kernel_pa_spec.

  (*get_chan_info ↦ gensem get_chan_info_spec
                  ⊕ get_chan_content ↦ gensem get_chan_content_spec
                  ⊕ set_chan_info ↦ gensem set_chan_info_spec
                  ⊕ set_chan_content ↦ gensem set_chan_content_spec
                  ⊕ init_chan ↦ gensem init_chan_spec.*)

  Definition pipcintro_passthrough : compatlayer (cdata RData) :=
    fload ↦ gensem fload_spec
          ⊕ fstore ↦ gensem fstore_spec
          ⊕ flatmem_copy ↦ gensem flatmem_copy_spec
          ⊕ vmxinfo_get ↦ gensem vmxinfo_get_spec
          ⊕ device_output ↦ gensem device_output_spec
          ⊕ pfree ↦ gensem pfree_spec
          ⊕ set_pt ↦ gensem setPT_spec
          ⊕ pt_read ↦ gensem ptRead_spec
          ⊕ pt_resv ↦ gensem ptResv_spec
          ⊕ shared_mem_status ↦ gensem shared_mem_status_spec
          ⊕ offer_shared_mem ↦ gensem offer_shared_mem_spec
          ⊕ get_state ↦ gensem get_state0_spec

          ⊕ get_curid ↦ gensem get_curid_spec
          ⊕ thread_spawn ↦ dnew_compatsem thread_spawn_spec
          ⊕ thread_wakeup ↦ gensem thread_wakeup_spec

          ⊕ sched_init ↦ gensem sched_init_spec

          ⊕ pt_in ↦ primcall_general_compatsem' ptin_spec (prim_ident:= pt_in)
          ⊕ pt_out ↦ primcall_general_compatsem' ptout_spec (prim_ident:= pt_out)
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

          ⊕ thread_yield ↦ primcall_thread_schedule_compatsem thread_yield_spec (prim_ident:= thread_yield)
          ⊕ thread_sleep ↦ primcall_thread_transfer_compatsem thread_sleep_spec

          ⊕ accessors ↦ {| exec_load := (@exec_loadex _ _ Hmwd); 
                           exec_store := (@exec_storeex _ _ Hmwd) |}.

  Definition pipcintro : compatlayer (cdata RData) := pipcintro_fresh ⊕ pipcintro_passthrough.

End WITHMEM.
