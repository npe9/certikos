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
(*          Refinement Proof for MPTOp                                 *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MPTIntro layer and MPTOp layer*)
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
Require Import PTOpGenSpec.
Require Import LayerCalculusLemma.

Require Import MPTOp.
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

    (** ** Definition the refinement relation: relate_RData + match_RData *)    
    Record relate_RData (f: meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
          flatmem_re: FlatMem.flatmem_inj (HP hadt) (HP ladt);
          vmxinfo_re: vmxinfo hadt = vmxinfo ladt;
          devout_re: devout hadt = devout ladt;
          ikern_re: ikern hadt = ikern ladt;
          pg_re: pg hadt = pg ladt;
          ihost_re: ihost hadt = ihost ladt;
          AC_re: AC hadt = AC ladt;
          ti_fst_re: (fst (ti hadt)) = (fst (ti ladt));
          ti_snd_re: val_inject f (snd (ti hadt)) (snd (ti ladt));
          AT_re: AT hadt = AT ladt;
          nps_re: nps hadt = nps ladt;
          init_re: init hadt = init ladt;
          pperm_re: pperm hadt = pperm ladt;

          PT_re:  PT hadt = PT ladt;
          ptp_re: ptpool hadt = ptpool ladt;
          idpde_re: idpde hadt = idpde ladt;
          ipt_re: ipt hadt = ipt ladt
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

      (** ** The low level specifications exist*)
      Section Exists.

        Lemma ptRmvPDE_exist:
          forall habd habd' labd n vadr f,
            ptRmvPDE_spec n vadr habd = Some habd'
            -> relate_RData f habd labd
            -> exists labd', ptRmvPDE_spec n vadr labd = Some labd' /\ relate_RData f habd' labd'
                             /\ kernel_mode labd.
        Proof.
          unfold ptRmvPDE_spec, rmvPDE_spec; intros until f; exist_simpl.
        Qed.

        Lemma ptInsertPDE_exist:
          forall habd habd' labd n vadr padr f,
            ptInsertPDE_spec n vadr padr habd = Some habd'
            -> relate_RData f habd labd
            -> exists labd', ptInsertPDE_spec n vadr padr labd = Some labd' /\ relate_RData f habd' labd'
                             /\ kernel_mode labd.
        Proof.
          unfold ptInsertPDE_spec, setPDEU_spec; intros until f. exist_simpl.
          eapply FlatMem.free_page_inj'. assumption.
        Qed.

        Lemma idpdeinit_exist:
          forall habd habd' labd i f,
            idpde_init_spec i habd = ret habd'
            -> relate_RData f habd labd
            -> exists labd', idpde_init_low_spec i labd = Some labd' /\ relate_RData f habd' labd'
                             /\ kernel_mode labd.
        Proof.
          unfold idpde_init_spec, idpde_init_low_spec; intros until f; exist_simpl.
        Qed.

        Lemma ptRead_kern_mode:
          forall i j v d,
            ptRead_spec i j d = Some v
            -> kernel_mode d.
        Proof.
          unfold ptRead_spec, getPTE_spec. simpl; intros.
          subdestruct; auto.
        Qed.

        Lemma ptReadPDE_kern_mode:
          forall i j v d,
            ptReadPDE_spec i j d = Some v
            -> kernel_mode d.
        Proof.
          unfold ptReadPDE_spec, getPDE_spec. simpl; intros.
          subdestruct; auto.
        Qed.

        Lemma ptRmvAux_kern_mode:
          forall i j d d',
            ptRmvAux_spec i j d = Some d'
            -> kernel_mode d.
        Proof.
          unfold ptRmvAux_spec, rmvPTE_spec. simpl; intros.
          subdestruct; auto.
        Qed.

        Lemma ptInsertAux_kern_mode:
          forall i j s t d d',
            ptInsertAux_spec i j s t d = Some d'
            -> kernel_mode d.
        Proof.
          unfold ptInsertAux_spec, setPTE_spec. simpl; intros.
          subdestruct; auto.
        Qed.
        
      End Exists.

      Section FRESH_PRIM.

        Lemma idpde_init_spec_ref:
          compatsim (crel HDATA LDATA) (gensem idpde_init_spec) idpde_init_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit idpdeinit_exist; eauto 1.
          intros [labd' [HP [HM Hkern]]].
          refine_split; try econstructor; eauto. constructor.
        Qed.
      
        Lemma ptRead_spec_ref:
          compatsim (crel HDATA LDATA) (gensem ptRead_spec) ptRead_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit ptRead_exist; eauto 1. intros HP.
          exploit ptRead_kern_mode; eauto. intros.
          refine_split; try econstructor; eauto.
        Qed.

        Lemma ptReadPDE_spec_ref:
          compatsim (crel HDATA LDATA) (gensem ptReadPDE_spec) ptReadPDE_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit ptReadPDE_exist; eauto 1. intros HP.
          exploit ptReadPDE_kern_mode; eauto. intros.
          refine_split; try econstructor; eauto.
        Qed.

        Lemma ptRmvAux_spec_ref:
          compatsim (crel HDATA LDATA) (gensem ptRmvAux_spec) ptRmvAux_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit ptRmvAux_exist; eauto 1.
          intros (labd' & HP & HM).
          exploit ptRmvAux_kern_mode; eauto. intros.
          refine_split; try econstructor; eauto. constructor.
        Qed.

        Lemma ptRmvPDE_spec_ref:
          compatsim (crel HDATA LDATA) (gensem ptRmvPDE_spec) ptRmvPDE_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit ptRmvPDE_exist; eauto 1.
          intros [labd' [HP [HM Hkern]]].
          refine_split; try econstructor; eauto. constructor.
        Qed.

        Lemma ptInsertAux_spec_ref:
          compatsim (crel HDATA LDATA) (gensem ptInsertAux_spec) ptInsertAux_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit ptInsertAux_exist; eauto 1.
          intros (labd' & HP & HM).
          exploit ptInsertAux_kern_mode; eauto. intros.
          refine_split; try econstructor; eauto. constructor.
        Qed.

        Lemma ptInsertPDE_spec_ref:
          compatsim (crel HDATA LDATA) (gensem ptInsertPDE_spec) ptInsertPDE_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit ptInsertPDE_exist; eauto 1.
          intros [labd' [HP [HM Hkern]]].
          refine_split; try econstructor; eauto. constructor.
        Qed.

      End FRESH_PRIM.

      Section PASSTHROUGH_RPIM.

        Global Instance: (LoadStoreProp (hflatmem_store:= flatmem_store) (lflatmem_store:= flatmem_store)).
        Proof.
          accessor_prop_tac.
          - eapply flatmem_store_exists; eauto.
        Qed.          

        Lemma passthrough_correct:
          sim (crel HDATA LDATA) mptop_passthrough mptintro.
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
          - apply setPDE_sim.
          - apply rmvPDE_sim.
          - apply rmvPTE_sim.
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
