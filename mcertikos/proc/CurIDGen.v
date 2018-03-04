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
(*           Layers of PM: Refinement Proof for PCurID                 *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between PThreadInit layer and PQueueIntro layer*)
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
Require Import LayerCalculusLemma.
Require Import AbstractDataType.

Require Import PCurID.
Require Import PAbQueue.
Require Import CurIDGenSpec.

(** * Definition of the refinement relation*)
Section Refinement.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.
  
  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := pcurid_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := pabqueue_data_ops) LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** ** Definition the refinement relation: relate_RData + match_RData *)    
    Section REFINEMENT_REL.
        
        Inductive match_CurID: stencil -> Z -> mem -> meminj -> Prop :=
        | MATCH_CURID: 
            forall v m b f cid s,
              Mem.load Mint32 m b 0 = Some (Vint v)
              -> Mem.valid_access m Mint32 b 0 Writable
              -> find_symbol s CURID_LOC = Some b
              -> cid = (Int.unsigned v)
              -> match_CurID s cid m f.

        (** Relation between the new raw data at the higher layer with the mememory at lower layer*)
        Inductive match_RData: stencil -> HDATA -> mem -> meminj -> Prop :=
        | MATCH_RDATA: 
            forall hadt m f s,
              match_CurID s (cid hadt) m f
              -> match_RData s hadt m f. 

        (** Relation between raw data at two layers*)
        Record relate_RData (f: meminj) (hadt: HDATA) (ladt: LDATA) :=
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

              pperm_re: pperm hadt = pperm ladt;
              PT_re:  PT hadt = PT ladt;
              ptp_re: ptpool hadt = ptpool ladt;
              idpde_re: idpde hadt = idpde ladt;
              ipt_re: ipt hadt = ipt ladt;
              smspool_re: smspool hadt = smspool ladt;

              kctxt_re: kctxt_inj f num_proc (kctxt hadt) (kctxt ladt);
              abtcb_re:  abtcb hadt = abtcb ladt;
              abq_re:  abq hadt = abq ladt
            }.

        Global Instance rel_ops: CompatRelOps HDATAOps LDATAOps :=
          {
            relate_AbData s f d1 d2 := relate_RData f d1 d2;
            match_AbData s d1 m f := match_RData s d1 m f;
            new_glbl := CURID_LOC :: nil
          }.

    End REFINEMENT_REL.

    (** ** Properties of relations*)
    Section Rel_Property.

      Lemma inject_match_correct:
        forall s d1 m2 f m2' j,
          match_RData s d1 m2 f ->
          Mem.inject j m2 m2' ->
          inject_incr (Mem.flat_inj (genv_next s)) j ->
          match_RData s d1 m2' (compose_meminj f j).
      Proof.
        inversion 1; subst; intros.
        inv H0.
        assert (HFB0: j b = Some (b, 0)).
        {
          eapply stencil_find_symbol_inject'; eauto.
        }
        econstructor; eauto; intros.
        econstructor; eauto; intros.
        specialize (Mem.load_inject _ _  _ _ _ _ _ _ _ H1 H3 HFB0).
        repeat rewrite Z.add_0_r. 
        intros [v1'[HLD1' HV1']].
        inv HV1'. assumption.
        specialize(Mem.valid_access_inject _ _  _ _ _ _ _ _ _ HFB0 H1 H4).
        rewrite Z.add_0_r; trivial.
      Qed.

      Lemma store_match_correct:
        forall s abd m0 m0' f b2 v v' chunk,
          match_RData s abd m0 f ->
          (forall i b,
             In i new_glbl ->
             find_symbol s i = Some b -> b <> b2) ->
          Mem.store chunk m0 b2 v v' = Some m0' ->
          match_RData s abd m0' f.
      Proof.
        intros. inv H. inv H2.
        econstructor; eauto.
        econstructor; eauto.
        eapply H0 in H4; simpl; eauto.
        repeat rewrite (Mem.load_store_other  _ _ _ _ _ _ H1); auto.
        eapply Mem.store_valid_access_1; eauto.
      Qed.

      Lemma storebytes_match_correct:
        forall s abd m0 m0' f b2 v v',
          match_RData s abd m0 f ->
          (forall i b,
             In i new_glbl ->
             find_symbol s i = Some b -> b <> b2) ->
          Mem.storebytes m0 b2 v v' = Some m0' ->
          match_RData s abd m0' f.
      Proof.
        intros. inv H. inv H2.
        econstructor; eauto.
        econstructor; eauto. 
        eapply H0 in H4; simpl; eauto.
        repeat rewrite (Mem.load_storebytes_other _ _ _ _ _ H1); eauto.
        eapply Mem.storebytes_valid_access_1; eauto.
      Qed.

      Lemma free_match_correct:
        forall s abd m0 m0' f ofs sz b2,
          match_RData s abd m0 f->
          (forall i b,
             In i new_glbl ->
             find_symbol s i = Some b -> b <> b2) ->
          Mem.free m0 b2 ofs sz = Some m0' ->
          match_RData s abd m0' f.
      Proof.
        intros; inv H; inv H2.
        econstructor; eauto.
        econstructor; eauto. 
        eapply H0 in H4; simpl; eauto.
        repeat rewrite (Mem.load_free _ _ _ _ _ H1); auto.
        eapply H0 in H4; simpl; eauto.
        eapply Mem.valid_access_free_1; eauto.
      Qed.
      
      Lemma alloc_match_correct:
        forall s abd m'0  m'1 f f' ofs sz b0 b'1,
          match_RData s abd m'0 f->
          Mem.alloc m'0 ofs sz = (m'1, b'1) ->
          f' b0 = Some (b'1, 0%Z) ->
          (forall b : block, b <> b0 -> f' b = f b) ->
          inject_incr f f' ->
          (forall i b,
             In i new_glbl ->
             find_symbol s i = Some b -> b <> b0) ->
          match_RData s abd m'1 f'.
      Proof.
        intros. rename H1 into HF1, H2 into HB. inv H; inv H1.
        econstructor; eauto.
        econstructor; eauto; 
        try (apply (Mem.load_alloc_other _ _ _ _ _ H0));          
        try (eapply Mem.valid_access_alloc_other); eauto.
      Qed.

      (** Prove that after taking one step, the refinement relation still holds*)    
      Lemma relate_incr:  
        forall abd abd' f f',
          relate_RData f abd abd'
          -> inject_incr f f'
          -> relate_RData f' abd abd'.
      Proof.
        inversion 1; subst; intros; inv H; constructor; eauto.
        - eapply kctxt_inj_incr; eauto.
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
        constructor.
        - apply inject_match_correct.
        - apply store_match_correct.
        - apply alloc_match_correct.
        - apply free_match_correct.
        - apply storebytes_match_correct.
        - intros. eapply relate_incr; eauto.
        - intros; eapply relate_kernel_mode; eauto.
        - intros; eapply relate_observe; eauto.
      Qed.

    End Rel_Property.

    (** * Proofs the one-step forward simulations for the low level specifications*)
    Section OneStep_Forward_Relation.

      (** ** The low level specifications exist*)
      Section Exists.

        Lemma get_state_exist:
          forall habd labd n z f,
            get_state0_spec n habd = Some z
            -> relate_RData f habd labd
            -> get_state0_spec n labd = Some z.
        Proof.
          unfold get_state0_spec; intros until f; exist_simpl.
        Qed.

        Lemma set_state_exist:
          forall habd habd' labd n i f,
            set_state0_spec n i habd = Some habd'
            -> relate_RData f habd labd
            -> exists labd', set_state0_spec n i labd = Some labd' /\ relate_RData f habd' labd'
                             /\ cid habd' = cid habd.
        Proof.
          unfold set_state0_spec; intros until f; exist_simpl.
        Qed.

        Lemma tdqueue_init_exist:
          forall habd habd' labd i f,
            tdqueue_init0_spec i habd = Some habd'
            -> relate_RData f habd labd
            -> exists labd', tdqueue_init0_spec i labd = Some labd' /\ relate_RData f habd' labd'
                             /\ cid habd' = cid habd.
        Proof.
          unfold tdqueue_init0_spec. intros until f. exist_simpl.
        Qed.

        Lemma dequeue_exist:
          forall habd habd' labd n i f,
            dequeue0_spec n habd = Some (habd', i)
            -> relate_RData f habd labd
            -> exists labd', dequeue0_spec n labd = Some (labd', i) /\ relate_RData f habd' labd'
                             /\ cid habd' = cid habd.
        Proof.
          unfold dequeue0_spec, Queue_arg. intros until f. exist_simpl.
        Qed.

        Lemma queue_rmv_exist:
          forall habd habd' labd n i f,
            queue_rmv0_spec n i habd = Some habd'
            -> relate_RData f habd labd
            -> exists labd', queue_rmv0_spec n i labd = Some labd' /\ relate_RData f habd' labd'
                             /\ cid habd' = cid habd.
        Proof.
          unfold queue_rmv0_spec, Queue_arg. intros until f. exist_simpl.
        Qed.

      End Exists.

      Ltac pattern2_refinement_simpl:=  
        pattern2_refinement_simpl' (@relate_AbData).

      Section FRESH_PRIM.

        Lemma get_curid_spec_ref:
          compatsim (crel HDATA LDATA) (gensem get_curid_spec) get_curid_spec_low.
        Proof.
          compatsim_simpl (@match_AbData). inv H.
          assert(HOS: kernel_mode d2).
          {
            simpl; inv match_related.
            functional inversion H2; repeat split; trivial; congruence.
          }
          assert (HP: v = z).
          {
            functional inversion H2; subst. rewrite H4 in H. 
            rewrite <- Int.repr_unsigned with z.
            rewrite <- H. rewrite Int.repr_unsigned. trivial.
          }          
          refine_split; eauto; econstructor; eauto.
        Qed.

        Lemma set_curid_spec_ref:
          compatsim (crel HDATA LDATA) (gensem set_curid_spec) set_curid_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          assert (Hkern: kernel_mode d2).
          {
            inv match_related. functional inversion H1; subst.
            repeat split; try congruence; eauto.
          }
          inv H. 
          specialize (Mem.valid_access_store _ _ _ _ (Vint i) H2); intros [m' HST].
          refine_split.
          - econstructor; eauto.
            instantiate (2:= m').
            instantiate (1:= d2).
            simpl; lift_trivial. subrewrite'.
          - constructor.
          - pose proof H1 as Hspec.
            functional inversion Hspec; subst.
            split; eauto; pattern2_refinement_simpl. 
            econstructor; simpl; eauto.
            econstructor; eauto; intros.          
            eapply Mem.load_store_same in HST; eauto.
            eapply Mem.store_valid_access_1; eauto.
          - apply inject_incr_refl.
        Qed.

      End FRESH_PRIM.

      Section PASSTHROUGH_PRIM.

        Global Instance: (LoadStoreProp (hflatmem_store:= flatmem_store) (lflatmem_store:= flatmem_store)).
        Proof.
          accessor_prop_tac.
          - eapply flatmem_store_exists; eauto.
          - eapply flatmem_store_match; eauto.
        Qed.

        Lemma passthrough_correct:
          sim (crel HDATA LDATA) pcurid_passthrough pabqueue.
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
          - apply kctxt_new_sim.
          - apply shared_mem_status_sim.
          - apply offer_shared_mem_sim.
          - (* get_state0*)
            layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
            match_external_states_simpl.
            erewrite get_state_exist; simpl; eauto 1; reflexivity.
          - (* set_state0 *)
            layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
            exploit set_state_exist; eauto 1; intros (labd' & HP & HM & CID).
            match_external_states_simpl.
          - (* tdqueue_init0 *)
            layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
            exploit tdqueue_init_exist; eauto 1; intros (labd' & HP & HM & CID).
            match_external_states_simpl.
          - apply enqueue0_sim.
          - (* dequeue0 *)
            layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
            exploit dequeue_exist; eauto 1; intros (labd' & HP & HM & CID).
            match_external_states_simpl.
          - (* queue_rmv0 *)
            layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
            exploit queue_rmv_exist; eauto 1; intros (labd' & HP & HM & CID).
            match_external_states_simpl.
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
          - apply kctxt_switch_sim.
          - layer_sim_simpl.
            + eapply load_correct2.
            + eapply store_correct2.
        Qed.

      End PASSTHROUGH_PRIM.

    End OneStep_Forward_Relation.

  End WITHMEM.

End Refinement.
