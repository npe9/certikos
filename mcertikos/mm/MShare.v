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
(*              Layers of VMM: MShareIntro                             *)
(*                                                                     *)
(*          Introduce the shared-memory                                *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the abstract data and the primitives for the PIPC layer,
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

Require Import INVLemmaMemory.
(*Require Import CalRealFreePT.*)

Require Export MShareOp.
Require Import AbstractDataType.

(** * Abstract Data and Primitives at this layer*)
Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section INV.

    Global Instance shared_mem_status_inv: 
      PreservesInvariants ObjShareMem.shared_mem_status_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto 2.
    Qed.

    Global Instance offer_shared_mem_inv: 
      PreservesInvariants ObjShareMem.offer_shared_mem_spec.
    Proof.
        preserves_invariants_simpl';
        functional inversion H2; subst; eauto 2; try (inv H0; constructor; trivial; fail).
        - exploit ptResv2_low_level_inv; eauto.
          intros HP; inv HP. constructor; trivial.
        - exploit ptResv2_low_level_inv; eauto.
          intros HP; inv HP. constructor; trivial.
        - exploit ptResv2_high_level_inv; eauto.
          intros HP; inv HP. constructor; trivial.
        - exploit ptResv2_high_level_inv; eauto.
          intros HP; inv HP. constructor; trivial.
        - exploit ptResv2_kernel_mode; eauto.
        - exploit ptResv2_kernel_mode; eauto.
      Qed.

  End INV.

  (** * Layer Definition *)
  Definition mshare_fresh : compatlayer (cdata RData) :=
    shared_mem_status ↦ gensem ObjShareMem.shared_mem_status_spec
                      ⊕ offer_shared_mem ↦ gensem ObjShareMem.offer_shared_mem_spec.

  Definition mshare_passthrough : compatlayer (cdata RData) :=
    fload ↦ gensem fload_spec
          ⊕ fstore ↦ gensem fstore_spec
          ⊕ flatmem_copy ↦ gensem flatmem_copy_spec
          ⊕ vmxinfo_get ↦ gensem vmxinfo_get_spec
          ⊕ device_output ↦ gensem device_output_spec
          ⊕ pfree ↦ gensem pfree_spec
          ⊕ set_pt ↦ gensem setPT_spec
          ⊕ pt_read ↦ gensem ptRead_spec
          ⊕ pt_resv ↦ gensem ptResv_spec
          ⊕ pt_new ↦ gensem pt_new_spec
          ⊕ shared_mem_init ↦ gensem sharedmem_init_spec
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
          ⊕ accessors ↦ {| exec_load := (@exec_loadex _ _ Hmwd); 
                           exec_store := (@exec_storeex _ _ Hmwd) |}.

  Definition mshare : compatlayer (cdata RData) := mshare_fresh ⊕ mshare_passthrough.

End WITHMEM.

Section WITHPARAM.

  Context `{real_params: RealParams}.

  Local Open Scope Z_scope.

  (** Implementation of primtives in VMCBOps *)
  Section Impl.

    Function ll_offer_shared_mem_spec (pid1 pid2 vadr: Z) (adt: RData) : option (RData * Z) :=
      match (ikern adt, ihost adt, pg adt, ipt adt, shared_mem_arg pid1 pid2) with
        | (true, true, true, true, true) =>
          match ZMap.get pid2 (ZMap.get pid1 (smspool adt)) with
            | SHRDValid st _ _ => 
              if SharedMemInfo_dec st SHRDPEND then Some (adt, SHARED_MEM_PEND)
              else
                match ZMap.get pid1 (ZMap.get pid2 (smspool adt)) with
                  | SHRDValid st' _ vadr' => 
                    if zle_lt 0 vadr' adr_max then
                      if SharedMemInfo_dec st' SHRDPEND then
                        match shared_mem_to_ready_spec pid1 pid2 vadr adt with
                          | Some (adt', re) =>
                            if zeq re MagicNumber
                            then match shared_mem_to_dead_spec pid1 pid2 vadr adt' with
                                   | Some adt'' => Some (adt'', SHARED_MEM_DEAD)
                                   | _ => None
                                 end
                            else Some (adt', SHARED_MEM_READY)
                          | _ => None
                        end
                      else match shared_mem_to_pending_spec pid1 pid2 vadr adt with
                             | Some adt'' => Some (adt'', SHARED_MEM_PEND)
                             | _ => None
                           end
                    else None
                  | _ => None
                end
            | _ => None
          end
        | _ => None
      end.

  End Impl.

End WITHPARAM.
