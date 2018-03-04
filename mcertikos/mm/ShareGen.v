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
(*          Refinement proof for MPTComm layer                         *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MPTOp layer and MPTComm layer*)
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import Asm.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Values.
Require Import Memory.
Require Import Maps.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import FlatMemory.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import RealParams.
Require Import LoadStoreSem2.
Require Import AsmImplLemma.
Require Import LAsm.
Require Import RefinementTactic.
Require Import PrimSemantics.
Require Import XOmega.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import compcert.cfrontend.Ctypes.
Require Import LayerCalculusLemma.

Require Import MShare.

Require Import ShareOpGen.
Require Import ShareGenSpec.

Require Import AbstractDataType.

(** * Notation of the refinement relation*)
Section Refinement.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata HDATA).
  Notation LDATAOps := (cdata LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** * Proofs the one-step forward simulations for the low level specifications*)
    Section OneStep_Forward_Relation.

      Section FRESH_PRIM.

        Lemma shared_mem_status_kernel_mode:
          forall d2 d2' v1 v2,
            shared_mem_status_spec v1 v2 d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H; subst;
          simpl; auto.
        Qed.

        Lemma shared_mem_status_spec_ref:
          compatsim (crel HDATA LDATA) (gensem shared_mem_status_spec) shared_mem_status_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit shared_mem_status_exists; eauto 1.
          intros (labd' & HP & HM).
          refine_split; try econstructor; eauto. 
          - eapply shared_mem_status_kernel_mode; eauto.
          - constructor.
        Qed.

        Lemma offer_shared_mem_kernel_mode:
          forall d2 d2' v1 v2 v3,
            offer_shared_mem_spec v1 v2 v3 d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H; subst;
          simpl; auto.
        Qed.

        Lemma offer_shared_mem_spec_ref:
          compatsim (crel HDATA LDATA) (gensem offer_shared_mem_spec) offer_shared_mem_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit offer_shared_mem_exists; eauto 1.
          intros (labd' & HP & HM).
          refine_split; try econstructor; eauto. 
          - eapply offer_shared_mem_kernel_mode; eauto.
          - constructor.
        Qed.

      End FRESH_PRIM.
 
      Lemma passthrough_correct:
        sim (crel HDATA LDATA) mshare_passthrough mshareop.
      Proof.
        sim_oplus.
        - apply fload_sim.
        - apply fstore_sim.
        - apply flatmem_copy_sim.
        - apply vmxinfo_get_sim.
        - apply device_output_sim.
        - apply pfree_sim.
        - apply setPT_sim.
        - apply ptRead_sim. 
        - apply ptResv_sim.
        - apply pt_new_sim.
        - apply sharedmem_init_sim.
        - apply ptin_sim.
        - apply ptout_sim.
        - apply clearCR2_sim.
        - apply container_get_nchildren_sim.
        - apply container_get_quota_sim.
        - apply container_get_usage_sim.
        - apply container_can_consume_sim.
        - apply alloc_sim.
        - apply trapin_sim.
        - apply trapout_sim.
        - apply hostin_sim.
        - apply hostout_sim.
        - apply trap_info_get_sim.
        - apply trap_info_ret_sim.
        - layer_sim_simpl.
          + eapply load_correct2.
          + eapply store_correct2.
      Qed.

    End OneStep_Forward_Relation.

  End WITHMEM.

End Refinement.
