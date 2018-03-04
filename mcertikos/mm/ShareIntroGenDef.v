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
(*           Layers of PM: Refinement Proof for PThreadIntro           *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between PKContextNew layer and PThreadIntro layer*)
Require Export Coqlib.
Require Export Errors.
Require Export AST.
Require Export Integers.
Require Export Floats.
Require Export Op.
Require Export Asm.
Require Export Events.
Require Export Globalenvs.
Require Export Smallstep.
Require Export Values.
Require Export Memory.
Require Export Maps.
Require Export CommonTactic.
Require Export AuxLemma.
Require Export FlatMemory.
Require Export AuxStateDataType.
Require Export Constant.
Require Export GlobIdent.
Require Export RealParams.
Require Export LoadStoreSem2.
Require Export AsmImplLemma.
Require Export GenSem.
Require Export RefinementTactic.
Require Export PrimSemantics.
Require Export XOmega.

Require Export liblayers.logic.PTreeModules.
Require Export liblayers.logic.LayerLogicImpl.
Require Export liblayers.compcertx.Stencil.
Require Export liblayers.compcertx.MakeProgram.
Require Export liblayers.compat.CompatLayers.
Require Export liblayers.compat.CompatGenSem.
Require Export compcert.cfrontend.Ctypes.

Require Export AbstractDataType.
Require Export LayerCalculusLemma.

Require Export MShareIntro.
Require Export MPTNew.

Open Scope string_scope.
Open Scope error_monad_scope.
Open Scope Z_scope.

Notation HDATA := RData.
Notation LDATA := RData.

Notation HDATAOps := (cdata (cdata_ops := mshareintro_data_ops) HDATA).
Notation LDATAOps := (cdata (cdata_ops := mptinit_data_ops) LDATA).

(** * Definition of the refinement relation*)
Section Refinement.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** ** Definition the refinement relation: relate_RData + match_RData *)    
    Section REFINEMENT_REL.
        
      Inductive match_SharedMem: SharedMemState -> val -> val -> val-> Prop :=
      | MATCH_SharedMemUNDEF:
          forall v1 v2 v3, match_SharedMem SHRDUndef v1 v2 v3
      | MATCH_SharedMemVALID: 
          forall v1 v2 v3 si b,
            Z2SharedMemInfo (Int.unsigned v1) = Some si ->
            ZtoBool (Int.unsigned v2) = Some b ->
            match_SharedMem (SHRDValid si b (Int.unsigned v3)) (Vint v3) (Vint v1) (Vint v2).

      Inductive match_SharedMemSTPool: stencil -> SharedMemSTPool -> mem -> meminj -> Prop :=
      | MATCH_SharedMemSTPool: 
          forall sharedmemp m b f s,
            (forall pid1 pid2, 
               0 <= pid1 < num_proc ->
               0 <= pid2 < num_proc ->
               (exists v1 v2 v3, 
                  Mem.load Mint32 m b (pid1 * 768 + pid2 * 12) = Some v1 /\
                  Mem.valid_access m Mint32 b (pid1 * 768 + pid2 * 12) Writable /\
                  Mem.load Mint32 m b (pid1 * 768 + pid2 * 12 + 4) = Some v2 /\
                  Mem.valid_access m Mint32 b (pid1 * 768 + pid2 * 12 + 4) Writable /\
                  Mem.load Mint32 m b (pid1 * 768 + pid2 * 12 + 8) = Some v3 /\
                  Mem.valid_access m Mint32 b (pid1 * 768 + pid2 * 12 + 8) Writable /\
                  match_SharedMem (ZMap.get pid2 (ZMap.get pid1 sharedmemp)) v1 v2 v3))
            -> find_symbol s SHRDMEMPOOL_LOC = Some b
            -> match_SharedMemSTPool s sharedmemp m f.

        (** Relation between the new raw data at the higher layer with the mememory at lower layer*)
        Inductive match_RData: stencil -> HDATA -> mem -> meminj -> Prop :=
        | MATCH_RDATA: 
            forall hadt m f s,
              match_SharedMemSTPool s (smspool hadt) m f
              -> match_RData s hadt m f. 

        (** Relation between raw data at two layers*)
        Record relate_RData (f: meminj) (hadt: HDATA) (ladt: LDATA) :=
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

        Global Instance rel_ops: CompatRelOps HDATAOps LDATAOps :=
          {
            relate_AbData s f d1 d2 := relate_RData f d1 d2;
            match_AbData s d1 m f := match_RData s d1 m f;
            new_glbl := SHRDMEMPOOL_LOC :: nil
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
        specialize (H3 _ _ H0 H5).
        destruct H3 as [v1[v2[v3[HL1[HV1[HL2[HV2[HL3[HV3 HM]]]]]]]]]. 
        specialize (Mem.load_inject _ _  _ _ _ _ _ _ _ H1 HL1 HFB0).
        specialize (Mem.load_inject _ _  _ _ _ _ _ _ _ H1 HL2 HFB0).
        specialize (Mem.load_inject _ _  _ _ _ _ _ _ _ H1 HL3 HFB0).
        repeat rewrite Z.add_0_r. 
        intros [v1'[HLD1' HV1']].
        intros [v2'[HLD2' HV2']].
        intros [v3'[HLD3' HV3']].
        refine_split'; eauto.
        specialize(Mem.valid_access_inject _ _  _ _ _ _ _ _ _ HFB0 H1 HV1).
        rewrite Z.add_0_r; trivial.
        specialize(Mem.valid_access_inject _ _  _ _ _ _ _ _ _ HFB0 H1 HV2).
        rewrite Z.add_0_r; trivial.
        specialize(Mem.valid_access_inject _ _  _ _ _ _ _ _ _ HFB0 H1 HV3).
        rewrite Z.add_0_r; trivial.
        inv HM. constructor.
        inv HV1'. inv HV2'. inv HV3'. constructor; auto.
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
        intros. specialize (H _ _ H2 H4).
        destruct H as [v1[v2[v3[HL1[HV1[HL2[HV2[HL3[HV3 HM]]]]]]]]]. 
        eapply H0 in H3; simpl; eauto.
        repeat rewrite (Mem.load_store_other  _ _ _ _ _ _ H1); auto.
        refine_split'; eauto;
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
        intros. specialize (H _ _ H2 H4).
        destruct H as [v1[v2[v3[HL1[HV1[HL2[HV2[HL3[HV3 HM]]]]]]]]]. 
        eapply H0 in H3; simpl; eauto.
        repeat rewrite (Mem.load_storebytes_other _ _ _ _ _ H1); eauto.
        refine_split'; eauto;
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
        intros. specialize (H _ _ H2 H4).
        destruct H as [v1[v2[v3[HL1[HV1[HL2[HV2[HL3[HV3 HM]]]]]]]]]. 
        eapply H0 in H3; simpl; eauto.
        repeat rewrite (Mem.load_free _ _ _ _ _ H1); auto.
        refine_split'; eauto;
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
        econstructor; eauto. 
        intros. specialize (H _ _ H1 H5).
        destruct H as [v1[v2[v3[HL1[HV1[HL2[HV2[HL3[HV3 HM]]]]]]]]]. 
        refine_split'; eauto;
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

  End WITHMEM.

End Refinement.
