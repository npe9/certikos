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

Require Import MShareOp.
Require Import AbstractDataType.
Require Import ShareOpGenSpec.

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
    Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
          flatmem_re: FlatMem.flatmem_inj (HP hadt) (HP ladt);
          vmxinfo_re: vmxinfo hadt = vmxinfo ladt;
          devout_re: devout hadt = devout ladt;
          CR3_re:  CR3 hadt = CR3 ladt;
          ikern_re: ikern hadt = ikern ladt;
          pg_re: pg hadt = pg ladt;
          ihost_re: ihost hadt = ihost ladt;
          AC_re: AC hadt = AC ladt;
          ti_fst_re: (fst (ti hadt)) = (fst (ti ladt));
          ti_snd_re: val_inject f (snd (ti hadt)) (snd (ti ladt));
          LAT_re: LAT hadt = LAT ladt;
          nps_re: nps hadt = nps ladt;
          init_re: init hadt = init ladt;

          pperm_re: pperm ladt = pperm hadt;
          PT_re:  PT ladt = PT hadt;
          ptp_re: ptpool ladt = ptpool hadt;
          idpde_re: idpde ladt = idpde hadt;
          ipt_re: ipt ladt = ipt hadt;
          smspool_re: smspool ladt = smspool hadt

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

        Lemma shared_mem_init_kernel_mode:
          forall d2 d2' mbi_adr,
            sharedmem_init_spec mbi_adr d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H; subst;
          simpl; auto.
        Qed.

        Lemma shared_mem_init_spec_ref:
          compatsim (crel HDATA LDATA) (gensem sharedmem_init_spec) shared_mem_init_spec_low.
        Proof.
          compatsim_simpl (@match_AbData).
          exploit sharedmem_init_exist; eauto 1.
          intros (labd' & HP & HM).
          refine_split; try econstructor; eauto.
	  - eapply shared_mem_init_kernel_mode; eauto.
	  - constructor.
        Qed.

        Lemma shared_mem_to_ready_kernel_mode:
          forall d2 d2' pid1 pid2 vadr rest,
            shared_mem_to_ready_spec pid1 pid2 vadr d2 = Some (d2', rest)
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H; subst;
          simpl; auto.
        Qed.

        Lemma shared_mem_to_ready_spec_ref:
          compatsim (crel HDATA LDATA) (gensem shared_mem_to_ready_spec) shared_mem_to_ready_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit shared_mem_to_ready_exist; eauto 1.
          intros (labd' & HP & HM).
          refine_split; try econstructor; eauto.
	  - eapply shared_mem_to_ready_kernel_mode; eauto.
	  - constructor.
        Qed.

        Lemma shared_mem_to_pending_kernel_mode:
          forall d2 d2' pid1 pid2 vadr,
            shared_mem_to_pending_spec pid1 pid2 vadr d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H; subst;
          simpl; auto.
        Qed.

        Lemma shared_mem_to_pending_spec_ref:
          compatsim (crel HDATA LDATA) (gensem shared_mem_to_pending_spec) shared_mem_to_pending_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit shared_mem_to_pending_exist; eauto 1.
          intros (labd' & HP & HM).
          refine_split; try econstructor; eauto.
	  - eapply shared_mem_to_pending_kernel_mode; eauto.
	  - constructor.
        Qed.

        Lemma shared_mem_to_dead_kernel_mode:
          forall d2 d2' pid1 pid2 vadr,
            shared_mem_to_dead_spec pid1 pid2 vadr d2 = Some d2'
            -> kernel_mode d2.
        Proof.
          intros. functional inversion H; subst;
          simpl; auto.
        Qed.

        Lemma shared_mem_to_dead_spec_ref:
          compatsim (crel HDATA LDATA) (gensem shared_mem_to_dead_spec) shared_mem_to_dead_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit shared_mem_to_dead_exist; eauto 1.
          intros (labd' & HP & HM).
          refine_split; try econstructor; eauto.
	  - eapply shared_mem_to_dead_kernel_mode; eauto.
	  - constructor.
        Qed.

        Lemma get_shared_mem_status_seen_spec_ref:
          compatsim (crel HDATA LDATA) (gensem get_shared_mem_status_seen_spec) get_shared_mem_status_seen_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          refine_split; try econstructor; eauto.
          - revert H2. unfold get_shared_mem_status_seen_spec.
            inv match_related.
            subrewrite.
	  - simpl. inv match_related.
            functional inversion H2; split; congruence.
        Qed.

      End FRESH_PRIM.

      Global Instance: (LoadStoreProp (hflatmem_store:= flatmem_store) (lflatmem_store:= flatmem_store)).
      Proof.
        accessor_prop_tac.
        - eapply flatmem_store_exists; eauto.
      Qed.          

      Lemma passthrough_correct:
        sim (crel HDATA LDATA) mshareop_passthrough mshareintro.
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
        - apply ptResv2_sim.
        - apply pt_new_sim.
        - apply get_shared_mem_state_sim.
        - apply get_shared_mem_seen_sim.
        - apply set_shared_mem_seen_sim.
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
