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
(*              Layers of PM: PThreadIntro                             *)
(*                                                                     *)
(*          Provide abstraction of Context                             *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*          Yu Guo <yu.guo@yale.edu>                                   *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the abstract data and the primitives for the PThreadIntro layer, 
which will introduce abstraction of kernel context*)
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

Require Export PKContextNew.
Require Export ObjQueue.

(** * Abstract Data and Primitives at PThreadIntro layer*)
Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  (** **Definition of the raw data at this layer*)
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
        tcb: TCBPool (*r thread control blocks poola*)                 
      }.*)

  (** * Specifications of Primitives*)
  (*Section Prim_Define.

    (** primitve: set n-th thread's prev to be s*)
    Function set_prev_spec (n s: Z) (adt: RData) : option RData :=
      match (ikern adt, pg adt, ihost adt, ipt adt) with
        | (true, true, true, true) =>
          if zle_lt 0 n num_proc then
            match (ZMap.get n (tcb adt)) with 
              | TCBValid ts _ next =>
                Some adt {tcb: ZMap.set n (TCBValid ts s next) (tcb adt)}
              | _ => None
            end
          else None
        | _ => None
      end.

    (** primitve: set n-th thread's next to be s*)
    Function set_next_spec (n s: Z) (adt: RData) : option RData :=
      match (ikern adt, pg adt, ihost adt, ipt adt) with
        | (true, true, true, true) =>
          if zle_lt 0 n num_proc then
            match (ZMap.get n (tcb adt)) with 
              | TCBValid ts prev _ =>
                Some adt {tcb: ZMap.set n (TCBValid ts prev s) (tcb adt)}
              | _ => None
            end
          else None
        | _ => None
      end.

  End Prim_Define.*)

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section INV.

    Global Instance set_state_inv: PreservesInvariants set_state_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto 2.
    Qed.

    Global Instance set_prev_inv: PreservesInvariants set_prev_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto 2.
    Qed.

    Global Instance set_next_inv: PreservesInvariants set_next_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto 2.
    Qed.

    Global Instance tcb_init_inv: PreservesInvariants tcb_init_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto 2.
    Qed.

  End INV.

  (** * Layer Definition *)
  Definition pthreadintro_fresh : compatlayer (cdata RData) :=
    get_state ↦ gensem get_state_spec
              ⊕ get_prev ↦ gensem get_prev_spec
              ⊕ get_next ↦ gensem get_next_spec
              ⊕ set_state ↦ gensem set_state_spec
              ⊕ set_prev ↦ gensem set_prev_spec
              ⊕ set_next ↦ gensem set_next_spec
              ⊕ tcb_init ↦ gensem tcb_init_spec.

  Definition pthreadintro_passthrough : compatlayer (cdata RData) :=
    fload ↦ gensem fload_spec
          ⊕ fstore ↦ gensem fstore_spec
          ⊕ flatmem_copy ↦ gensem flatmem_copy_spec
          ⊕ vmxinfo_get ↦ gensem vmxinfo_get_spec
          ⊕ device_output ↦ gensem device_output_spec
          ⊕ pfree ↦ gensem pfree_spec
          ⊕ set_pt ↦ gensem setPT_spec
          ⊕ pt_read ↦ gensem ptRead_spec
          ⊕ pt_resv ↦ gensem ptResv_spec
          (*⊕ pt_free ↦ gensem pt_free_spec*)
          ⊕ shared_mem_init ↦ gensem sharedmem_init_spec
          ⊕ shared_mem_status ↦ gensem ObjShareMem.shared_mem_status_spec
          ⊕ offer_shared_mem ↦ gensem ObjShareMem.offer_shared_mem_spec
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
          ⊕ kctxt_switch ↦ primcall_kctxt_switch_compatsem kctxt_switch_spec
          ⊕ accessors ↦ {| exec_load := (@exec_loadex _ _ Hmwd); 
                           exec_store := (@exec_storeex _ _ Hmwd) |}          
          ⊕ kctxt_new ↦ dnew_compatsem ObjThread.kctxt_new_spec.

  Definition pthreadintro : compatlayer (cdata RData) := pthreadintro_fresh ⊕ pthreadintro_passthrough.

End WITHMEM.

Section WITHPARAM.

  Context `{real_params: RealParams}.

  Local Open Scope Z_scope.

  Section Impl.

    (* TODO: currently, I remove all the things related to free things.
     I will try to fix the PT_free in the future *)

    (*Function thread_free_spec (adt: RData) (n:Z): option (RData):=
      match pt_free_spec adt n with
        | Some abd' => tcb_init_spec abd' n
        | _ => None
      end.*)
    
    Function thread_init_spec (mbi_adr:Z) (abd: RData) : option RData :=
      match sharedmem_init_spec mbi_adr abd with
        | Some adt =>
          Some adt {tcb: real_tcb (tcb adt)}
        | _ => None
      end.

  End Impl.

End WITHPARAM.
