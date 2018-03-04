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
(*              Layers of PM: PKContextNew                             *)
(*                                                                     *)
(*          Provide operations of Kernel Context                       *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*          Yu Guo <yu.guo@yale.edu>                                   *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the abstract data and the primitives for the PKContext layer, 
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

Require Import INVLemmaMemory.
Require Import INVLemmaThread.
Require Import INVLemmaContainer.

Require Export PKContext.
Require Import AbstractDataType.

(** * Abstract Data and Primitives at MPMap layer*)
(** The abstract data at MPMap layer is the same with MPTNew layer*)
Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section INV.

    Global Instance kctxt_new_inv: DNewInvariants ObjThread.kctxt_new_spec.
    Proof.
      constructor; intros; inv H0;
      unfold ObjThread.kctxt_new_spec in *;
      subdestruct; inv H; simpl; auto.
      - (* low level invariant *)
        constructor; trivial; intros; simpl in *.
        eapply kctxt_inject_neutral_gss_flatinj'; eauto.
        eapply kctxt_inject_neutral_gss_flatinj; eauto.

      - (* high_level_invariant *)
        constructor; simpl; eauto 2; try congruence; intros.
        + exploit split_container_valid; eauto.
          eapply container_split_some; eauto.
          auto.
        + unfold update_cusage, update_cchildren; zmap_solve.
    Qed.

  End INV.

  (** * Layer Definition *)
  Definition pkcontextnew_fresh : compatlayer (cdata RData) :=
    kctxt_new ↦ dnew_compatsem ObjThread.kctxt_new_spec.

  Definition pkcontextnew_passthrough : compatlayer (cdata RData) :=
    fload ↦ gensem fload_spec
          ⊕ fstore ↦ gensem fstore_spec
          ⊕ flatmem_copy ↦ gensem flatmem_copy_spec
          ⊕ vmxinfo_get ↦ gensem vmxinfo_get_spec
          ⊕ device_output ↦ gensem device_output_spec
          ⊕ pfree ↦ gensem pfree_spec
          ⊕ set_pt ↦ gensem setPT_spec
          ⊕ pt_read ↦ gensem ptRead_spec
          ⊕ pt_resv ↦ gensem ptResv_spec
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
                           exec_store := (@exec_storeex _ _ Hmwd) |}.

  Definition pkcontextnew : compatlayer (cdata RData) := pkcontextnew_fresh ⊕ pkcontextnew_passthrough.

End WITHMEM.
