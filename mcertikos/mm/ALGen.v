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
(*              Layers of VMM: Refinement proof for MAL                *)
(*                                                                     *)
(*          Refinement proof for MAL layer                             *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MALOp layer and MAL layer*)
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
Require Import LoadStoreSem1.
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
Require Import LayerCalculusLemma.

Require Import MALT.
Require Import MALOp.
Require Import ALGenSpec.

Require Import AbstractDataType.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** * Definition of the refinement relation*)
Section Refinement.

  Context `{real_params: RealParams}.

  Notation HDATAOps := (cdata (cdata_ops := malt_data_ops) RData).
  Notation LDATAOps := (cdata (cdata_ops := malop_data_ops) RData).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** ** Definition the refinement relation: relate_RData + match_RData *)    
    Record relate_RData (f:meminj) (hadt: RData) (ladt: RData) :=
      mkrelate_RData {
          flatmem_re: FlatMem.flatmem_inj (HP hadt) (HP ladt);
          vmxinfo_re: vmxinfo hadt = vmxinfo ladt;
          devout_re: devout hadt = devout ladt;
          CR3_re:  CR3 hadt = CR3 ladt;
          ikern_re: ikern hadt = ikern ladt;
          pg_re: pg hadt = pg ladt;
          ihost_re: ihost hadt = ihost ladt;
          ti_fst_re: (fst (ti hadt)) = (fst (ti ladt));
          ti_snd_re: val_inject f (snd (ti hadt)) (snd (ti ladt));
          AT_re: AT hadt = AT ladt;
          nps_re: nps hadt = nps ladt;
          init_re: init hadt = init ladt
        }.

    Inductive match_RData: stencil -> RData -> mem -> meminj -> Prop :=
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

        Lemma pfree_exist:
          forall habd habd' labd i f,
            ObjPMM.pfree'_spec i habd = Some habd'
            -> relate_RData f habd labd
            -> exists labd', pfree_spec i labd = Some labd' /\ relate_RData f habd' labd'
                             /\ kernel_mode labd.
        Proof.
          unfold pfree_spec, ObjPMM.pfree'_spec; intros until f. exist_simpl.
        Qed.

        Lemma palloc_exist:
          forall habd habd' labd i f,
            ObjPMM.palloc'_spec habd = Some (habd', i)
            -> relate_RData f habd labd
            -> exists labd', palloc_spec labd = Some (labd', i) /\ relate_RData f habd' labd'
                             /\ kernel_mode labd.
        Proof.
          unfold palloc_spec, ObjPMM.palloc'_spec; intros until f; exist_simpl.
        Qed.

        Lemma flatmem_store_exists:
          forall hadt ladt hadt' t addr v v' f,
            flatmem_store hadt t addr v = Some hadt'
            -> relate_RData f hadt ladt
            -> val_inject f v v'
            -> exists ladt',
                 flatmem_store' ladt t addr v' = Some ladt'
                 /\ relate_RData f hadt' ladt'.
        Proof.
          unfold flatmem_store', flatmem_store. intros.
          revert H. inv H0. subrewrite. subdestruct.
          inv HQ; simpl. refine_split'; eauto.
          constructor; trivial; simpl. 
          eapply (FlatMem.store_mapped_inj f); trivial;
          assumption.
        Qed.

        Lemma fstore_exist:
          forall habd habd' labd i v f,
            fstore0_spec i v habd = Some habd'
            -> relate_RData f habd labd
            -> exists labd', fstore'_spec i v labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold fstore0_spec, fstore'_spec; intros.
          revert H. pose proof H0 as HR.
          inv H0. subrewrite. subdestruct. 
          eapply flatmem_store_exists; eauto.
        Qed.

        Lemma flatmem_copy_exist:
          forall habd habd' labd i from to f,
            flatmem_copy0_spec i from to habd = Some habd'
            -> relate_RData f habd labd
            -> exists labd', flatmem_copy'_spec i from to labd = Some labd' 
                             /\ relate_RData f habd' labd'.
        Proof.
          unfold flatmem_copy0_spec, flatmem_copy'_spec; intros.
          revert H. pose proof H0 as HR.
          inv H0. subrewrite. subdestruct. 
          exploit flatmem_copy_aux_exists; eauto.
          intros (lh' & HCopy & Hinj).
          rewrite HCopy. refine_split'; trivial.
          inv HR.
          inv HQ; constructor; trivial; simpl. 
        Qed.

        Lemma set_at_c_exist:
          forall habd habd' labd i z f,
            set_at_c0_spec i z habd = Some habd'
            -> relate_RData f habd labd
            -> exists labd', set_at_c_spec i z labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold set_at_c0_spec, set_at_c_spec; intros until f; exist_simpl; inv HR'.
        Qed.

      End Exists.

      Section FRESH_PRIM.

        Lemma pfree_spec_ref:
          compatsim (crel RData RData) (gensem ObjPMM.pfree'_spec) pfree_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit pfree_exist; eauto 1.
          intros [labd' [HP [HM Hkern]]].
          refine_split; try econstructor; eauto. constructor.
        Qed.

        Lemma palloc_spec_ref:
          compatsim (crel RData RData) (gensem ObjPMM.palloc'_spec) palloc_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          exploit palloc_exist; eauto 1.
          intros [labd' [HP [HM Hkern]]].
          refine_split; try econstructor; eauto. constructor.
        Qed.

      End FRESH_PRIM.

      Section PASSTHROUGH_PRIM.

        Global Instance: (LoadStoreProp (hflatmem_store:= flatmem_store) (lflatmem_store:= flatmem_store')).
        Proof.
          accessor_prop_tac.
          - eapply flatmem_store_exists; eauto.
        Qed.          

        Lemma passthrough_correct:
          sim (crel RData RData) malt_passthrough malop.
        Proof.
          sim_oplus.
          - apply fload'_sim.
          - (* fstore *)
            layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
            exploit fstore_exist; eauto 1; intros [labd' [HP HM]].
            match_external_states_simpl. 
          - (* flatmem_copy *)
            layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
            exploit flatmem_copy_exist; eauto 1; intros [labd' [HP HM]].
            match_external_states_simpl. 
          - apply vmxinfo_get_sim.
          - apply device_output_sim.
          - apply setPG0_sim.
          - apply clearCR2_sim.
          - apply setCR30_sim.
          - apply get_nps_sim.
          - apply is_at_norm_sim.
          - apply get_at_u_sim.
          - apply get_at_c_sim.
          - (* set_a_c *)
            layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
            exploit set_at_c_exist; eauto 1. intros [labd' [HP HM]].
            match_external_states_simpl. 
          - apply mem_init_sim.
          - apply trapin_sim.
          - apply trapout0_sim.
          - apply hostin_sim.
          - apply hostout_sim.
          - apply trap_info_get_sim.
          - apply trap_info_ret_sim.
          - layer_sim_simpl.
            + eapply load_correct1.
            + eapply store_correct1.
        Qed.

      End PASSTHROUGH_PRIM.

    End OneStep_Forward_Relation.

  End WITHMEM.

End Refinement.  
