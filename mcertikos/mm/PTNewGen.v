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
(*              Layers of VMM: Refinement Proof for MPTNew             *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MPTBit layer and MPTNew layer*)
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
Require Import GenSem.
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

Require Import MPTNew.
Require Import AbstractDataType.

Require Import PTNewGenSpec.
Require Import LayerCalculusLemma.

Require Import ObjFlatMem.
Require Import ObjLMM0.
Require Import ObjLMM1.
Require Import ObjContainer.
Require Import ObjCPU.
Require Import ObjVMMFun.
Require Import ObjVMMGetSet.

(** * Notation of the refinement relation*)
Section Refinement.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := mptinit_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := mptinit_data_ops) LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** Relation between raw data at two layers*)
    Record relate_RData (f: meminj) (hadt: LDATA) (ladt: LDATA) :=
      mkrelate_RData {
          flatmem_re: FlatMem.flatmem_inj (HP hadt) (HP ladt);
          vmxinfo_re: vmxinfo hadt = vmxinfo ladt;
          devout_re: devout hadt = devout ladt;
          ikern_re: ikern ladt = ikern hadt;
          pg_re: pg ladt = pg hadt;
          ihost_re: ihost ladt = ihost hadt;
          AC_re: AC ladt = AC hadt;
          ti_fst_re: (fst (ti ladt)) = (fst (ti hadt));
          ti_snd_re: val_inject f (snd (ti hadt)) (snd (ti ladt));
          LAT_re: LAT ladt = LAT hadt;
          nps_re: nps ladt = nps hadt;
          PT_re:  PT ladt = PT hadt;
          ptp_re: ptpool ladt = ptpool hadt;
          ipt_re: ipt ladt = ipt hadt;
          init_re: init ladt = init hadt;
          pperm_re: pperm ladt = pperm hadt;
          idpde_re: idpde ladt = idpde hadt

        }.

    Inductive match_RData: stencil -> HDATA -> mem -> meminj -> Prop :=
    | MATCH_RDATA: forall habd m f s, match_RData s habd m f.   

    Local Hint Resolve MATCH_RDATA.

    Global Instance rel_ops: CompatRelOps HDATAOps LDATAOps :=
      {
        relate_AbData s f d1 d2 := relate_RData f d1 d2;
        match_AbData s d1 m f := match_RData s d1 m f;
        new_glbl := nil
      }.    

    (** ** Properties of relations*)
    Section Rel_Property.

      (** Prove that after taking one step, the refinement relation still holds*)    
      Lemma relate_incr:  
        forall abd abd' f f',
          relate_RData f abd abd'
          -> inject_incr f f'
          -> relate_RData f' abd abd'.
      Proof.
        inversion 1; subst; intros; inv H; constructor; eauto.
      Qed.

      Lemma relate_kernel_mode:
        forall abd abd' f,
          relate_RData f abd abd' 
          -> (kernel_mode abd <-> kernel_mode abd').
      Proof.
        inversion 1; simpl; split; congruence.
      Qed.

      Lemma relate_observe:
        forall p abd abd' f,
          relate_RData f abd abd' ->
          observe p abd = observe p abd'.
      Proof.
        inversion 1; simpl; unfold ObservationImpl.observe; congruence.
      Qed.

      Global Instance rel_prf: CompatRel HDATAOps LDATAOps.
      Proof.
        constructor; intros; simpl; trivial.
        eapply relate_incr; eauto.
        eapply relate_kernel_mode; eauto.
        eapply relate_observe; eauto.
      Qed.

    End Rel_Property.

    (** * Proofs the one-step forward simulations for the low level specifications*)
    Section OneStep_Forward_Relation.

      Section FRESH_PRIM.

        Lemma pt_new_spec_kernel_mode:
          forall d d' id q z,
            pt_new_spec id q d = Some (d', z) ->
            kernel_mode d.
        Proof.
          intros. simpl; functional inversion H; eauto.
        Qed.

        Lemma pt_new_spec_ref:
          compatsim (crel HDATA LDATA) (gensem pt_new_spec) pt_new_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit pt_new_exist; eauto 1.
          intros (labd' & HP & HM).
          exploit pt_new_spec_kernel_mode; eauto. intros.
          refine_split; try econstructor; eauto. 
          constructor.
        Qed.

        Lemma ptResv_spec_kernel_mode:
          forall d d' i i0 i1 z,
            ptResv_spec i i0 i1 d = Some (d', z) ->
            kernel_mode d.
        Proof.
          intros. simpl; functional inversion H; eauto.
          - functional inversion H2; eauto.
          - functional inversion H1; eauto.
        Qed.

        Lemma ptResv_spec_ref:
          compatsim (crel HDATA LDATA) (gensem ptResv_spec) ptResv_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit ptResv_exist; eauto 1.
          intros (labd' & HP & HM).
          exploit ptResv_spec_kernel_mode; eauto. intros.
          refine_split; try econstructor; eauto. constructor.
        Qed.

        Lemma ptResv2_spec_kernel_mode:
          forall d d' i i0 i1 i2 i3 i4 z,
            ptResv2_spec i i0 i1 i2 i3 i4 d = Some (d', z) ->
            kernel_mode d.
        Proof.
          intros. simpl; functional inversion H; eauto.
          - functional inversion H2; eauto.
          - functional inversion H2; eauto.
          - functional inversion H1; eauto.
        Qed.

        Lemma ptResv2_spec_ref:
          compatsim (crel HDATA LDATA) (gensem ptResv2_spec) ptResv2_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit ptResv2_exist; eauto 1.
          intros (labd' & HP & HM).
          exploit ptResv2_spec_kernel_mode; eauto. intros.
          refine_split; try econstructor; eauto. constructor.
        Qed.

        Lemma pmap_init_spec_kernel_mode:
          forall d d' i,
            pmap_init_spec i d = Some d' ->
            kernel_mode d.
        Proof.
          intros. simpl; functional inversion H; eauto.
        Qed.

        Lemma pmap_init_spec_ref:
          compatsim (crel HDATA LDATA) (gensem pmap_init_spec) pmap_init_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit pmap_init_exist; eauto 1.
          intros (labd' & HP & HM).
          exploit pmap_init_spec_kernel_mode; eauto. intros.
          refine_split; try econstructor; eauto. constructor.
        Qed.

        (*Lemma pt_free_spec_ref:
        compatsim (crel HDATA LDATA) (gensem pt_free_spec) pt_free_spec_low.
      Proof. 
        compatsim_simpl (@match_AbData).
        exploit pt_free_exist; eauto 1.
        intros [labd' [HP [HM Hkern]]].
        refine_split; try econstructor; eauto. constructor.
      Qed.*)

      End FRESH_PRIM.
            
      Section PASSTHROUGH_PRIM.

        Global Instance: (LoadStoreProp (hflatmem_store:= flatmem_store) (lflatmem_store:= flatmem_store)).
        Proof.
          accessor_prop_tac.
          - eapply flatmem_store_exists; eauto.
        Qed.          

        Lemma passthrough_correct:
          sim (crel HDATA LDATA) mptnew_passthrough mptinit.
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
          - apply ptReadPDE_sim.
          - apply ptFreePDE0_sim.
          - apply ptRmv0_sim.
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

      End PASSTHROUGH_PRIM.

    End OneStep_Forward_Relation.

  End WITHMEM.

End Refinement.
