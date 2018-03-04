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
(*              Layers of PM: PQueueIntro                              *)
(*                                                                     *)
(*          Provide abstraction of thread queue                        *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*          Yu Guo <yu.guo@yale.edu>                                   *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the abstract data and the primitives for the PQueueIntro layer, 
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

Require Export PThreadInit.

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
        tcb: TCBPool; (*r thread control blocks pool*)                 
        tdq: TDQueuePool (**r thread queue pool*)
      }.*)

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section INV.

    Global Instance set_head_inv: PreservesInvariants set_head_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto 2.
    Qed.

    Global Instance set_tail_inv: PreservesInvariants set_tail_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto 2.
    Qed.

    Global Instance tdq_init_inv: PreservesInvariants tdq_init_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto 2.
    Qed.

  End INV.

  (** * Layer Definition *)
  Definition pqueueintro_fresh : compatlayer (cdata RData) :=
    get_head ↦ gensem get_head_spec
             ⊕ get_tail ↦ gensem get_tail_spec
             ⊕ set_head ↦ gensem set_head_spec
             ⊕ set_tail ↦ gensem set_tail_spec
             ⊕ tdq_init ↦ gensem tdq_init_spec.

  Definition pqueueintro_passthrough : compatlayer (cdata RData) :=
    fload ↦ gensem fload_spec
          ⊕ fstore ↦ gensem fstore_spec
          ⊕ flatmem_copy ↦ gensem flatmem_copy_spec
          ⊕ vmxinfo_get ↦ gensem vmxinfo_get_spec
          ⊕ device_output ↦ gensem device_output_spec
          ⊕ pfree ↦ gensem pfree_spec
          ⊕ set_pt ↦ gensem setPT_spec
          ⊕ pt_read ↦ gensem ptRead_spec
          ⊕ pt_resv ↦ gensem ptResv_spec
          ⊕ kctxt_new ↦ dnew_compatsem ObjThread.kctxt_new_spec
          (*⊕ pt_free ↦ gensem pt_free_spec*)
          ⊕ shared_mem_status ↦ gensem shared_mem_status_spec
          ⊕ offer_shared_mem ↦ gensem offer_shared_mem_spec
          ⊕ get_state ↦ gensem get_state_spec
          ⊕ get_prev ↦ gensem get_prev_spec
          ⊕ get_next ↦ gensem get_next_spec
          ⊕ set_state ↦ gensem set_state_spec
          ⊕ set_prev ↦ gensem set_prev_spec
          ⊕ set_next ↦ gensem set_next_spec
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
          ⊕ thread_init ↦ gensem thread_init_spec.

  Definition pqueueintro : compatlayer (cdata RData) := pqueueintro_fresh ⊕ pqueueintro_passthrough.

  (*Definition pqueueintro_impl : compatlayer (cdata RData) :=
    thread_init ↦ gensem thread_init_spec
      ⊕ tdq_init ↦ gensem tdq_init_spec
      ⊕ set_prev ↦ gensem set_prev_spec
      ⊕ set_next ↦ gensem set_next_spec
      ⊕ get_head ↦ gensem get_head_spec
      ⊕ get_tail ↦ gensem get_tail_spec
      ⊕ get_prev ↦ gensem get_prev_spec
      ⊕ get_next ↦ gensem get_next_spec
      ⊕ set_head ↦ gensem set_head_spec
      ⊕ set_tail ↦ gensem set_tail_spec.
  
  Definition pqueueintro_rest : compatlayer (cdata RData) :=
    palloc ↦ gensem palloc_spec
      ⊕ pfree ↦ gensem pfree_spec
      ⊕ set_pt ↦ gensem setPT_spec
      ⊕ pt_read ↦ gensem ptRead_spec
      ⊕ pt_resv ↦ gensem ptResv_spec
      ⊕ pt_in ↦ primcall_general_compatsem' (prim_generic:= ptin_spec) (prim_ident:= pt_in)
      ⊕ pt_out ↦ primcall_general_compatsem' (prim_generic:= ptout_spec) (prim_ident:= pt_out)
      ⊕ trap_in ↦ primcall_general_compatsem (prim_generic:= trapin_spec)
      ⊕ trap_out ↦ primcall_general_compatsem (prim_generic:= trapout_spec)
      ⊕ host_in ↦ primcall_general_compatsem (prim_generic:= hostin_spec)
      ⊕ host_out ↦ primcall_general_compatsem (prim_generic:= hostout_spec)
      ⊕ trap_get ↦ primcall_trap_info_get_compatsem (trap_info_get:= trap_info_get_spec)
      ⊕ trap_set ↦ primcall_trap_info_ret_compatsem (trap_info_ret:= trap_info_ret_spec)
      ⊕ kctxt_switch ↦ primcall_kctxt_switch_compatsem (kctxt_switch:= kctxt_switch_spec)
      ⊕ kctxt_new ↦ dnew_compatsem (dnew := kctxt_new_spec)
      ⊕ get_state ↦ gensem get_state_spec
      ⊕ set_state ↦ gensem set_state_spec
      ⊕ thread_free ↦ gensem thread_free_spec
      ⊕ accessors ↦ {| exec_load := @exec_loadex; exec_store := @exec_storeex |}.

  Lemma pqueueintro_impl_eq : pqueueintro ≡ pqueueintro_impl ⊕ pqueueintro_rest.
  Proof. reflexivity. Qed.

  Definition semantics := LAsm.Lsemantics pqueueintro.*)

End WITHMEM.

Section WITHPARAM.

  Context `{real_params: RealParams}.

  Local Open Scope Z_scope.

  Section Impl.

    (** primitve: enqueue*)
    Function enqueue_spec (n i: Z) (adt: RData): option RData :=
      match (ikern adt, pg adt, ihost adt, ipt adt) with
        | (true, true, true, true) =>
          if Queue_arg n i then
            match (ZMap.get n (tdq adt), ZMap.get i (tcb adt))  with 
              | (TDQValid h t, TCBValid st _ _) =>
                if zeq t num_proc then
                  Some adt {tcb: ZMap.set i (TCBValid st num_proc num_proc) (tcb adt)}
                       {tdq: ZMap.set n (TDQValid i i) (tdq adt)}
                else
                  if zle_lt 0 t num_proc then
                    match (ZMap.get t (tcb adt)) with
                      | TCBValid st' prev' _ =>
                        let tcb':= ZMap.set t (TCBValid st' prev' i) (tcb adt) in
                        Some adt {tcb: ZMap.set i (TCBValid st t num_proc) tcb'}
                             {tdq: ZMap.set n (TDQValid h i) (tdq adt)}
                      | _ => None
                    end
                  else None
              | _ => None
            end
          else None
        | _ => None
      end.

    (** primitve: dequeue*)
    Function dequeue_spec (n: Z) (adt: RData): option (RData* Z) :=
      match (ikern adt, pg adt, ihost adt, ipt adt) with
        | (true, true, true, true) =>
          if zle_le 0 n num_chan then
              match (ZMap.get n (tdq adt)) with 
                | TDQValid h t =>
                  if zeq h num_proc then
                    Some (adt, num_proc)
                  else
                    if zle_lt 0 h num_proc then
                      match (ZMap.get h (tcb adt)) with
                        | TCBValid st _ next =>
                          if zeq next num_proc then
                            Some (adt {tdq: ZMap.set n (TDQValid num_proc num_proc) (tdq adt)}, h)
                            else
                              match (ZMap.get next (tcb adt)) with
                                | TCBValid st' _ next' =>
                                  Some (adt {tcb: ZMap.set next (TCBValid st' num_proc next') (tcb adt)}
                                            {tdq: ZMap.set n (TDQValid next t) (tdq adt)} , h)
                                | _ => None
                              end
                        | _ => None
                      end
                    else None
                | _ => None
              end
          else None
        | _ => None
      end.
        
    (** primitive: initialize the allocation table, set up the paging mechanism, and initialize the page table pool*)   
    Function tdqueue_init_spec (mbi_adr:Z) (abd: RData): option RData :=
      match thread_init_spec mbi_adr abd  with
        | Some adt =>
          Some adt {tdq: real_tdq (tdq adt)}
        | _ => None
      end.

  End Impl.

End WITHPARAM.
