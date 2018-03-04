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
(*          Refinement proof for PTKern layer                          *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MPTComm layer and MPTKern layer*)
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

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import compcert.cfrontend.Ctypes.
Require Import PTKernGenSpec.
Require Import LayerCalculusLemma.

Require Import MPTKern.
Require Import AbstractDataType.

Require Import PTOpGen.
Require Import PTCommGen.

Require Import AbstractDataType.

(** * Definition of the refinement relation*)
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

      (** ** The low level specifications exist*)
      Section Exists.

        Lemma pt_init_kern_exist:
          forall habd habd' labd i f,
            pt_init_kern_spec i habd = ret habd'
            -> relate_RData f habd labd
            -> exists labd', pt_init_kern_spec i labd = Some labd' /\ relate_RData f habd' labd'
                             /\ kernel_mode labd.
        Proof.
          unfold pt_init_kern_spec. intros until f; exist_simpl.
        Qed.

        Lemma ptInsertPTE_exist:
          forall habd habd' labd n v pa pe f,
            ptInsertPTE_spec n v pa pe habd = Some habd'
            -> relate_RData f habd labd
            -> exists labd', ptInsertPTE_spec n v pa pe labd = Some labd'
                             /\ relate_RData f habd' labd'
                             /\ kernel_mode labd.
        Proof.
          unfold ptInsertPTE_spec; intros until f. exist_simpl.
        Qed.

        Lemma ptInsert_exist:
          forall habd habd' labd i n v pa pe f,
            ptInsert_spec n v pa pe habd = Some (habd', i)
            -> relate_RData f habd labd
            -> exists labd', ptInsert_spec n v pa pe labd = Some (labd', i)
                             /\ relate_RData f habd' labd'
                             /\ kernel_mode labd.
        Proof.
          unfold ptInsert_spec; intros. pose proof H0 as HR. inv H0. revert H.
          subrewrite. subdestruct.
          - inv HQ. exploit ptInsertPTE_exist; eauto. intros (labd' & HP & HR' & Hk).
            rewrite HP. refine_split'; trivial.
          - inv HQ. exploit ptAllocPDE_exist; eauto. intros (labd' & HP & HR' & Hk).
            rewrite HP. subst; simpl. refine_split'; trivial.
          - inv HQ. exploit ptAllocPDE_exist; eauto. intros (labd' & HP & HR' & Hk).
            rewrite HP. destruct (zeq i 0); contra_inv.  
            exploit ptInsertPTE_exist; eauto.
            intros (labd'' & HP' & HR'' & Hk').
            rewrite HP'. refine_split'; trivial.
        Qed.

        Lemma ptRmv_exist:
          forall n v habd habd' labd i f,
            ptRmv_spec n v habd = Some (habd', i)
            -> relate_RData f habd labd
            -> exists labd', ptRmv_spec n v labd = Some (labd', i)
                             /\ relate_RData f habd' labd'
                             /\ kernel_mode labd.
        Proof.
          unfold ptRmv_spec; intros until f. exist_simpl.
        Qed.

      End Exists.

      Section FRESH_PRIM.

        Lemma pt_init_kern_spec_ref:
          compatsim (crel HDATA LDATA) (gensem pt_init_kern_spec) pt_init_kern_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit pt_init_kern_exist; eauto 1.
          intros [labd' [HP [HM Hkern]]].
          refine_split; try econstructor; eauto. constructor.
        Qed.

        Lemma ptInsert_spec_ref:
          compatsim (crel HDATA LDATA) (gensem ptInsert_spec) ptInsert_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit ptInsert_exist; eauto 1.
          intros [labd' [HP [HM Hkern]]].
          refine_split; try econstructor; eauto. constructor.
        Qed.

        Lemma ptRmv_spec_ref:
          compatsim (crel HDATA LDATA) (gensem ptRmv_spec) ptRmv_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit ptRmv_exist; eauto 1.
          intros [labd' [HP [HM Hkern]]].
          refine_split; try econstructor; eauto. constructor.
        Qed.

      End FRESH_PRIM.

      Section PASSTHROUGH_RPIM.
        
        Lemma passthrough_correct:
          sim (crel HDATA LDATA) mptkern_passthrough mptcommon.
        Proof.
          sim_oplus.
          - apply fload_sim.
          - apply fstore_sim.
          - apply flatmem_copy_sim.
          - apply vmxinfo_get_sim.
          - apply device_output_sim.
          - apply setPG1_sim.
          - apply get_at_c_sim.
          - apply set_at_c0_sim.
          - apply pfree'_sim.
          - apply setPT'_sim. 
          - apply ptRead_sim.
          - apply ptReadPDE_sim.
          - apply ptFreePDE_sim.
          - apply ptin'_sim.
          - apply ptout_sim.
          - apply clearCR2_sim.
          - apply container_get_parent_sim.
          - apply container_get_nchildren_sim.
          - apply container_get_quota_sim.
          - apply container_get_usage_sim.
          - apply container_can_consume_sim.
          - apply container_split_sim.
          - apply container_alloc_sim.
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

      End PASSTHROUGH_RPIM.

    End OneStep_Forward_Relation.

  End WITHMEM.

End Refinement.
