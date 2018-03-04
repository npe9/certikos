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
(*              Layers of VM: UCtxtIntro                               *)
(*                                                                     *)
(*          Provide the abstraction of user contex                     *)
(*                                                                     *)
(*          Haozhong Zhang <haozhong.zhang@yale.edu>                   *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the abstract data and the primitives for the UCtxtIntro layer,
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
Require Import INVLemmaProc.

Require Import AbstractDataType.
Require Export PIPC.
Require Export PUCtxtIntroDef.

(** * Abstract Data and Primitives at this layer*)
Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  (** **Definition of the raw data at MPTBit layer*)
  (*Record RData :=
    mkRData {
        HP: flatmem; (**r we model the memory from 1G to 3G as heap*)
        ti: trapinfo; (**r abstract of CR2, stores the address where page fault happens*)
        pe: bool; (**r abstract of CR0, indicates whether the paging is enabled or not*)
        ikern: bool; (**r pure logic flag, shows whether it's in kernel mode or not*)
        ihost: bool; (**r logic flag, shows whether it's in the host mode or not*)         
        AT: ATable; (**r allocation table*)
        nps: Z; (**r number of the pages*)

        PT: Z; (**r the current page table index*)
        ptpool: PTPool; (**r page table pool*)
        ipt: bool; (**r pure logic flag, shows whether it's using the kernel's page table*)
        pb : PTBitMap; (**r [page table bit map], indicating which page table has been used*)

        kctxt: KContextPool; (**r kernel context pool*)
        abtcb: AbTCBPool; (**r thread control blocks pool*)
        abq: AbQueuePool; (**r thread queue pool*)
        cid: Z; (**r current thread id*) 

        chpool : ChanPool; (**r the channel pool for IPC*)
        uctxt : UContextPool (**r user context pool*)
      }.*)

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section INV.
    
    Global Instance uctx_set_inv: PreservesInvariants uctx_set_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto 2.
      eapply uctxt_inject_neutral_gss; eauto.
      eapply uctxt_inject_neutral0_gss; eauto.
      eapply uctxt_inject_neutral0_Vint.
    Qed.

    Global Instance uctx_set_eip_inv: UCTXSetEIPInvariants uctx_set_eip_spec.
    Proof.
      constructor; intros. 
      - (* low level inv *)
        inv H1. functional inversion H; inv H.
        constructor; trivial.
        eapply uctxt_inject_neutral_gss; eauto.
        eapply uctxt_inject_neutral0_gss; eauto.
        eapply uctxt_inject_neutral0_Vptr_flat; eauto.
      - (* high level inv *)
        inv H0. functional inversion H; inv H.
        constructor; trivial.
      - (* kernel mode *)
        functional inversion H; inv H.
        constructor; trivial.
    Qed.

    Global Instance save_uctx_inv: SaveUCtxInvariants save_uctx_spec.
    Proof.
      constructor; intros. 
      - (* low level inv *)
        inv H0. functional inversion H; inv H.
        constructor; trivial.
        eapply uctxt_inject_neutral_gss; eauto.
        repeat eapply uctxt_inject_neutral0_gss; 
          try eapply uctxt_inject_neutral0_Vint.
        apply uctxt_inject_neutral0_init; eauto.
      - (* high level inv *)
        inv H0. functional inversion H; inv H.
        constructor; trivial.
      - (* kernel mode *)
        functional inversion H; inv H.
        constructor; trivial.
    Qed.

    Global Instance restore_uctx_inv: RestoreUCtxInvariants restore_uctx_spec.
    Proof.
      constructor; intros. 
      - (* low level inv *)
        inv H0. functional inversion H; inv H.
        constructor; trivial.
      - (* high level inv *)
        inv H0. functional inversion H; inv H.
        subst. constructor; auto; simpl in *; intros; try congruence.
    Qed.
    
  End INV.

  (** * Layer Definition *)
  Definition puctxtintro_fresh_c : compatlayer (cdata RData) :=
    uctx_get ↦ gensem uctx_get_spec
             ⊕ uctx_set ↦ gensem uctx_set_spec
             ⊕ uctx_set_eip ↦ uctx_set_eip_compatsem uctx_set_eip_spec
             ⊕ save_uctx ↦ save_uctx_compatsem save_uctx_spec.

  Definition puctxtintro_fresh_asm : compatlayer (cdata RData) :=
    restore_uctx ↦ primcall_restoreuctx_compatsem restore_uctx_spec cid
                 ⊕ elf_load ↦ elf_load_compatsem.

  Definition puctxtintro_passthrough : compatlayer (cdata RData) :=
    fload ↦ gensem fload_spec
          ⊕ fstore ↦ gensem fstore_spec
          ⊕ vmxinfo_get ↦ gensem vmxinfo_get_spec
          ⊕ device_output ↦ gensem device_output_spec
          ⊕ pfree ↦ gensem pfree_spec
          ⊕ set_pt ↦ gensem setPT_spec
          ⊕ pt_read ↦ gensem ptRead_spec
          ⊕ pt_resv ↦ gensem ptResv_spec
          ⊕ shared_mem_status ↦ gensem shared_mem_status_spec
          ⊕ offer_shared_mem ↦ gensem offer_shared_mem_spec

          ⊕ get_curid ↦ gensem get_curid_spec
          ⊕ thread_spawn ↦ dnew_compatsem thread_spawn_spec
          ⊕ thread_wakeup ↦ gensem thread_wakeup_spec
          (*⊕ is_chan_ready ↦ gensem is_chan_ready_spec
          ⊕ sendto_chan ↦ gensem sendto_chan_spec
          ⊕ receive_chan ↦ gensem receive_chan_spec*)
          ⊕ syncreceive_chan ↦ gensem syncreceive_chan_spec
          ⊕ syncsendto_chan_pre ↦ gensem syncsendto_chan_pre_spec
          ⊕ syncsendto_chan_post ↦ gensem syncsendto_chan_post_spec

          ⊕ proc_init ↦ gensem proc_init_spec

          ⊕ pt_in ↦ primcall_general_compatsem' ptin_spec (prim_ident:= pt_in)
          ⊕ pt_out ↦ primcall_general_compatsem' ptout_spec (prim_ident:= pt_out)
          ⊕ container_get_nchildren ↦ gensem container_get_nchildren_spec
          ⊕ container_get_quota ↦ gensem container_get_quota_spec
          ⊕ container_get_usage ↦ gensem container_get_usage_spec
          ⊕ container_can_consume ↦ gensem container_can_consume_spec
          ⊕ container_alloc ↦ gensem alloc_spec
          ⊕ trap_in ↦ primcall_general_compatsem trapin_spec
          ⊕ host_in ↦ primcall_general_compatsem hostin_spec
          ⊕ host_out ↦ primcall_general_compatsem hostout_spec
          ⊕ trap_get ↦ primcall_trap_info_get_compatsem trap_info_get_spec
          ⊕ trap_set ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec

          ⊕ thread_yield ↦ primcall_thread_schedule_compatsem thread_yield_spec (prim_ident:= thread_yield)
          ⊕ thread_sleep ↦ primcall_thread_transfer_compatsem thread_sleep_spec

          ⊕ accessors ↦ {| exec_load := (@exec_loadex _ _ Hmwd); 
                           exec_store := (@exec_storeex _ _ Hmwd) |}.

  Definition puctxtintro : compatlayer (cdata RData) :=
    (puctxtintro_fresh_c ⊕ puctxtintro_fresh_asm) ⊕ puctxtintro_passthrough.

(*Definition puctxtintro_impl : compatlayer (cdata RData) :=
    thread_spawn ↦ dnew_compatsem (dnew := thread_spawn_spec)
      ⊕ uctx_set ↦ gensem uctx_set_spec
      ⊕ uctx_set_eip ↦ uctx_set_eip_compatsem
      ⊕ elf_load ↦ elf_load_compatsem.
  Definition puctxtintro_rest : compatlayer (cdata RData) :=
    uctx_get ↦ gensem uctx_get_spec
      ⊕ save_uctx ↦ save_uctx_compatsem
      ⊕ restore_uctx ↦ primcall_restoreuctx_compatsem
      ⊕ palloc ↦ gensem palloc_spec
      ⊕ pfree ↦ gensem pfree_spec
      ⊕ set_pt ↦ gensem setPT_spec
      ⊕ pt_read ↦ gensem ptRead_spec
      ⊕ pt_resv ↦ gensem ptResv_spec
      ⊕ pt_in ↦ primcall_general_compatsem' (prim_generic:= ptin_spec) (prim_ident:= pt_in)
      ⊕ pt_out ↦ primcall_general_compatsem' (prim_generic:= ptout_spec) (prim_ident:= pt_out)
      ⊕ trap_in ↦ primcall_general_compatsem (prim_generic:= trapin_spec)
      ⊕ host_in ↦ primcall_general_compatsem (prim_generic:= hostin_spec)
      ⊕ host_out ↦ primcall_general_compatsem (prim_generic:= hostout_spec)
      ⊕ trap_get ↦ primcall_trap_info_get_compatsem (trap_info_get:= trap_info_get_spec)
      ⊕ trap_set ↦ primcall_trap_info_ret_compatsem (trap_info_ret:= trap_info_ret_spec)
      ⊕ get_curid ↦ gensem get_curid_spec
      ⊕ thread_kill ↦ gensem thread_kill_spec
      ⊕ thread_wakeup ↦ gensem thread_wakeup_spec
      ⊕ thread_yield ↦ primcall_thread_schedule_compatsem (thread_schedule:= thread_yield_spec) (prim_ident:= thread_yield)
      ⊕ thread_sleep ↦ primcall_thread_transfer_compatsem (thread_transfer:= thread_sleep_spec)
      ⊕ is_chan_ready ↦ gensem is_chan_ready_spec
      ⊕ sendto_chan ↦ gensem sendto_chan_spec
      ⊕ receive_chan ↦ gensem receive_chan_spec
      ⊕ proc_init ↦ gensem proc_init_spec
      ⊕ accessors ↦ {| exec_load := @exec_loadex; exec_store := @exec_storeex |}.

  Lemma puctxtintro_impl_eq : puctxtintro ≡ puctxtintro_impl ⊕ puctxtintro_rest.
  Proof. reflexivity. Qed.

  Definition semantics := LAsm.Lsemantics puctxtintro.*)

End WITHMEM.
