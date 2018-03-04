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
(*           Layers of PM: Refinement Proof for PKContext              *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MPTInit layer and MPTBit layer*)
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
(*Require Import AsmImplTactic.*)
Require Import LayerCalculusLemma.
Require Import AbstractDataType.

Require Import PKContext.
Require Import KContextGenSpec.
          
(** * Definition of the refinement relation*)
Section Refinement.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.
  
  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := mshareintro_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := mshareintro_data_ops) LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** ** Definition the refinement relation: relate_RData + match_RData *)    
    Section REFINEMENT_REL.
        
        (** Relation between the kernel context pool and the underline memory*)
        Inductive match_KCtxtPool: stencil -> KContextPool -> mem -> meminj -> Prop :=
        | MATCH_KCTXTPOOL: 
            forall kcp m b s f,
              (forall ofs, 
                 0<= ofs < num_proc ->
                 forall n r,
                   ZtoPreg n = Some r
                   -> (exists v, 
                         Mem.load Mint32 m b (ofs * 24 + n * 4) = Some v /\
                         Mem.valid_access m Mint32 b (ofs * 24 + n * 4) Writable /\
                         val_inject f (Val.load_result Mint32 (Pregmap.get r (ZMap.get ofs kcp))) v))
              -> find_symbol s KCtxtPool_LOC = Some b
              -> match_KCtxtPool s kcp m f.

        (** Relation between the new raw data at the higher layer with the mememory at lower layer*)
        Inductive match_RData: stencil -> HDATA -> mem -> meminj -> Prop :=
        | MATCH_RDATA: 
            forall hadt m s f,
              match_KCtxtPool s (kctxt hadt) m f
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

              pperm_re: pperm ladt = pperm hadt;
              PT_re:  PT ladt = PT hadt;
              ptp_re: ptpool ladt = ptpool hadt;
              idpde_re: idpde ladt = idpde hadt;
              ipt_re: ipt ladt = ipt hadt;
              smspool_re: smspool ladt = smspool hadt
            }.

        Global Instance rel_ops: CompatRelOps HDATAOps LDATAOps :=
          {
            relate_AbData s f d1 d2 := relate_RData f d1 d2;
            match_AbData s d1 m f := match_RData s d1 m f;
            new_glbl := KCtxtPool_LOC :: nil
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
        specialize (H3 _ H0 _ _ H5).
        destruct H3 as [v1[HL1[HV1 HM]]]. 
        specialize (Mem.load_inject _ _  _ _ _ _ _ _ _ H1 HL1 HFB0).
        repeat rewrite Z.add_0_r. 
        intros [v1'[HLD1' HV1']].
        refine_split'; eauto.
        specialize(Mem.valid_access_inject _ _  _ _ _ _ _ _ _ HFB0 H1 HV1).
        rewrite Z.add_0_r; trivial.
        eapply val_inject_compose; eauto.
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
        intros. specialize (H _ H2 _ _ H4).
        destruct H as [v1[HL1[HV1 HM]]]. 
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
        intros. specialize (H _ H2 _ _ H4).
        destruct H as [v1[HL1[HV1 HM]]]. 
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
        intros. specialize (H _ H2 _ _ H4).
        destruct H as [v1[HL1[HV1 HM]]]. 
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
        intros. specialize (H _ H1 _ _ H5).
        destruct H as [v1[HL1[HV1 HM]]]. 
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

    (** * Proofs the one-step forward simulations for the low level specifications*)
    Section OneStep_Forward_Relation.

      Ltac pattern2_refinement_simpl:=  
        pattern2_refinement_simpl' (@relate_AbData).

      Section FRESH_PRIM.

        Lemma kctxt_ra_spec_ref:
          compatsim (crel HDATA LDATA) PKContext.kctxt_ra_compatsem
                    kctxt_ra_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          assert(HOS: kernel_mode d2 /\ 0 <= Int.unsigned n < num_proc).
          {
            simpl; inv match_related.
            unfold kctxt_ra_spec in *.
            subdestruct. inv H7.
            refine_split'; trivial; try congruence. omega.
          }
          destruct HOS as [Hkern HOS]. 
          inv H. rename H0 into HMem. 
          assert (HOS': ZtoPreg 5 = Some RA) by reflexivity.
          destruct (HMem _ HOS _ _ HOS') as [v1[HL1[HV1 HM]]].
          specialize (Mem.valid_access_store _ _ _ _ (Vptr b ofs) HV1); intros [m' HST].
          assert(HFB: ι b = Some (b, 0)).
          {
            destruct H5 as [fun_id Hsymbol].
            eapply stencil_find_symbol_inject'; eauto.
          }          
          refine_split.
          - econstructor; eauto.
            instantiate (2:= m').
            instantiate (1:= d2).
            simpl in HST; simpl; lift_trivial. subrewrite'.
          - constructor.
          - rename H7 into Hspec.
            unfold kctxt_ra_spec in Hspec.
            pose proof match_related as match_relate'.
            inv match_related.
            subdestruct. inv Hspec. 
            split; eauto; pattern2_refinement_simpl. 
            econstructor; simpl; eauto.
            econstructor; eauto; intros.
            destruct (zeq ofs0 (Int.unsigned n)); subst.          
            + (* ofs0 = Int.unsigned n *)
              destruct (zeq n0 5); subst.
              * (* n0 = 5  *)
                refine_split'; eauto;
                try eapply Mem.store_valid_access_1; eauto.
                eapply Mem.load_store_same; eauto.
                repeat rewrite ZMap.gss. inv H0.
                rewrite Pregmap.gsspec. simpl.
                econstructor; eauto. 
                rewrite Int.add_zero; trivial.
              * (* n0 <> 5 *)
                specialize (HMem _ H _ _ H0).
                destruct HMem as [v1'[HL1'[HV1' HM']]].
                refine_split'; eauto;
                try eapply Mem.store_valid_access_1; eauto.
                rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
                simpl; right. destruct (zlt n0 5); [left; omega|right; omega].
                rewrite ZMap.gss. 
                rewrite Pregmap.gsspec.
                destruct (Pregmap.elt_eq r RA); subst; auto.
                apply ZtoPreg_correct in H0. 
                inv H0. omega.
            + (* ofs0 <> Int.unsigned n *)
              specialize (HMem _ H _ _ H0).
              destruct HMem as [v1'[HL1'[HV1' HM']]].
              refine_split'; eauto;
              try eapply Mem.store_valid_access_1; eauto.
              rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
              simpl; right. apply ZtoPreg_range in H0.
              destruct (zlt ofs0 (Int.unsigned n)); [left; omega|right; omega].
              rewrite ZMap.gso; trivial.
          - apply inject_incr_refl.
        Qed.

        Lemma kctxt_sp_spec_ref:
          compatsim (crel HDATA LDATA) PKContext.kctxt_sp_compatsem
                    kctxt_sp_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          assert(HOS: kernel_mode d2 /\ 0 <= Int.unsigned n < num_proc).
          {
            simpl; inv match_related.
            unfold kctxt_sp_spec in *.
            subdestruct. inv H8.
            refine_split'; trivial; try congruence. omega.
          }
          destruct HOS as [Hkern HOS]. 
          inv H. rename H0 into HMem. 
          assert (HOS': ZtoPreg 0 = Some (IR ESP)) by reflexivity.
          destruct (HMem _ HOS _ _ HOS') as [v1[HL1[HV1 HM]]].
          specialize (Mem.valid_access_store _ _ _ _ (Vptr b ofs) HV1); intros [m' HST].
          assert(HFB: ι b = Some (b, 0)).
          {
            destruct H6 as [fun_id Hsymbol].
            eapply stencil_find_symbol_inject'; eauto.
          }          
          refine_split.
          - econstructor; eauto.
            instantiate (2:= m').
            instantiate (1:= d2).
            simpl in HST; simpl; lift_trivial.
            replace (Int.unsigned n * 24) with (Int.unsigned n * 24 + 0) by omega.
            subrewrite'.
          - constructor.
          - rename H8 into Hspec.
            unfold kctxt_sp_spec in Hspec.
            pose proof match_related as match_relate'.
            inv match_related.
            subdestruct. inv Hspec. 
            split; eauto; pattern2_refinement_simpl. 
            econstructor; simpl; eauto.
            econstructor; eauto; intros.
            destruct (zeq ofs0 (Int.unsigned n)); subst.          
            + (* ofs0 = Int.unsigned n *)
              destruct (zeq n0 0); subst.
              * (* n0 = 0 *)
                refine_split'; eauto;
                try eapply Mem.store_valid_access_1; eauto.
                eapply Mem.load_store_same; eauto.
                repeat rewrite ZMap.gss. inv H0.
                rewrite Pregmap.gsspec. simpl.
                econstructor; eauto. 
                rewrite Int.add_zero; trivial.
              * (* n0 <> 0 *)
                specialize (HMem _ H _ _ H0).
                destruct HMem as [v1'[HL1'[HV1' HM']]].
                refine_split'; eauto;
                try eapply Mem.store_valid_access_1; eauto.
                rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
                simpl; right. destruct (zlt n0 0); [left; omega|right; omega].
                rewrite ZMap.gss. 
                rewrite Pregmap.gsspec.
                destruct (Pregmap.elt_eq r ESP); subst; auto.
                apply ZtoPreg_correct in H0. 
                inv H0. omega.
            + (* ofs0 <> Int.unsigned n *)
              specialize (HMem _ H _ _ H0).
              destruct HMem as [v1'[HL1'[HV1' HM']]].
              refine_split'; eauto;
              try eapply Mem.store_valid_access_1; eauto.
              rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
              simpl; right. apply ZtoPreg_range in H0.
              destruct (zlt ofs0 (Int.unsigned n)); [left; omega|right; omega].
              rewrite ZMap.gso; trivial.
          - apply inject_incr_refl.
        Qed.

        Lemma kctxt_switch_spec_ref:
          compatsim (crel HDATA LDATA)
                    (primcall_kctxt_switch_compatsem kctxt_switch_spec)
                    kctxt_switch_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData). intros.
          inv match_extcall_states.
          unfold kctxt_switch_spec in *.
          subdestruct. 
          inv match_match. inv H.
          rename H0 into HMAT. 
          assert (HV0: forall ofs : Z,
                         0 <= ofs < num_proc ->
                         forall n0, 0<= n0 <= 5 -> Mem.valid_access m2 Mint32 b0 (ofs * 24 + n0 * 4) Writable).
          {
            intros. destruct (ZtoPreg_range_correct _ H0) as [r HEX].
            destruct (HMAT _ H _ _ HEX) as [_[_[HV _]]]; trivial.
          }
          assert (HP: exists m0, Mem.store Mint32 m2 b0 (Int.unsigned n * 24) (rs2#ESP) = Some m0).
          {
            assert(HOS0: 0 <= 0 <=5) by omega.
            specialize (HV0 _ a _ HOS0).
            replace (Int.unsigned n * 24 + 0 * 4) with (Int.unsigned n * 24) in HV0 by omega.
            apply (Mem.valid_access_store); auto.
          }
          destruct HP as [m0 HST0].
          assert (HV1: forall ofs : Z,
                         0 <= ofs < num_proc ->
                         forall n0, 0<= n0 <= 5 -> Mem.valid_access m0 Mint32 b0 (ofs * 24 + n0 * 4) Writable).
          {
            intros; eapply Mem.store_valid_access_1; eauto.
          }
          clear HV0.
          assert (HP: exists m1, Mem.store Mint32 m0 b0 (Int.unsigned n * 24 + 1 * 4) (rs2#EDI) = Some m1).
          {
            assert(HOS0: 0 <= 1 <=5) by omega.
            apply (Mem.valid_access_store); auto.
          }
          destruct HP as [m1 HST1].
          assert (HV2: forall ofs : Z,
                         0 <= ofs < num_proc ->
                         forall n0, 0<= n0 <= 5 -> Mem.valid_access m1 Mint32 b0 (ofs * 24 + n0 * 4) Writable).
          {
            intros; eapply Mem.store_valid_access_1; eauto.
          }
          clear HV1.
          assert (HP: exists m2', Mem.store Mint32 m1 b0 (Int.unsigned n * 24 + 2 * 4) (rs2#ESI) = Some m2').
          {
            assert(HOS0: 0 <= 2 <=5) by omega.
            apply (Mem.valid_access_store); auto.
          }
          destruct HP as [m2' HST2].
          assert (HV3: forall ofs : Z,
                         0 <= ofs < num_proc ->
                         forall n0, 0<= n0 <= 5 -> Mem.valid_access m2' Mint32 b0 (ofs * 24 + n0 * 4) Writable).
          {
            intros; eapply Mem.store_valid_access_1; eauto.
          }
          clear HV2.
          assert (HP: exists m3, Mem.store Mint32 m2' b0 (Int.unsigned n * 24 + 3 * 4) (rs2#EBX) = Some m3).
          {
            assert(HOS0: 0 <= 3 <=5) by omega.
            apply (Mem.valid_access_store); auto.
          }
          destruct HP as [m3 HST3].
          assert (HV4: forall ofs : Z,
                         0 <= ofs < num_proc ->
                         forall n0, 0<= n0 <= 5 -> Mem.valid_access m3 Mint32 b0 (ofs * 24 + n0 * 4) Writable).
          {
            intros; eapply Mem.store_valid_access_1; eauto.
          }
          clear HV3.
          assert (HP: exists m4, Mem.store Mint32 m3 b0 (Int.unsigned n * 24 + 4 * 4) (rs2#EBP) = Some m4).
          {
            assert(HOS0: 0 <= 4 <=5) by omega.
            apply (Mem.valid_access_store); auto.
          }
          destruct HP as [m4 HST4].
          assert (HV5: forall ofs : Z,
                         0 <= ofs < num_proc ->
                         forall n0, 0<= n0 <= 5 -> Mem.valid_access m4 Mint32 b0 (ofs * 24 + n0 * 4) Writable).
          {
            intros; eapply Mem.store_valid_access_1; eauto.
          }
          clear HV4.
          assert (HP: exists m5, Mem.store Mint32 m4 b0 (Int.unsigned n * 24 + 5 * 4) (rs2#RA) = Some m5).
          {
            assert(HOS0: 0 <= 5 <=5) by omega.
            apply (Mem.valid_access_store); auto.
          }
          destruct HP as [m5 HST5].
          assert (HV: forall ofs : Z,
                        0 <= ofs < num_proc ->
                        forall n0, 0<= n0 <= 5 -> Mem.valid_access m5 Mint32 b0 (ofs * 24 + n0 * 4) Writable).
          {
            intros; eapply Mem.store_valid_access_1; eauto.
          }
          clear HV5.          
          assert (HMAT':  
                    forall ofs : Z,
                      0 <= ofs < num_proc ->
                      ofs <> Int.unsigned n ->
                      forall (n : Z) (r : preg),
                        ZtoPreg n = Some r ->
                        exists v : val,
                          Mem.load Mint32 m5 b0 (ofs * 24 + n * 4) = Some v /\
                          Mem.valid_access m5 Mint32 b0 (ofs * 24 + n * 4) Writable /\
                          val_inject ι ((Val.load_result 
                                           Mint32 (Pregmap.get 
                                                     r (ZMap.get ofs (kctxt d1))))) v).
          {
            intros.
            destruct (HMAT _ H _ _ H2) as [v[HLD[_ HM]]].
            exists v.
            specialize (ZtoPreg_range _ _ H2); intros Hn1.
            split; eauto.
            Ltac simpl_other ofs n:= 
              right; simpl; destruct (zlt ofs (Int.unsigned n));
              [left; omega|right; omega].       
            rewrite (Mem.load_store_other  _ _ _ _ _ _ HST5); [|simpl_other ofs n].
            rewrite (Mem.load_store_other  _ _ _ _ _ _ HST4); [|simpl_other ofs n].
            rewrite (Mem.load_store_other  _ _ _ _ _ _ HST3); [|simpl_other ofs n].
            rewrite (Mem.load_store_other  _ _ _ _ _ _ HST2); [|simpl_other ofs n].
            rewrite (Mem.load_store_other  _ _ _ _ _ _ HST1); [|simpl_other ofs n].
            rewrite (Mem.load_store_other  _ _ _ _ _ _ HST0); [|simpl_other ofs n].
            trivial. 
          }
          clear HMAT.
          assert (forall n0 : Z, 0 <= n0 <= 5 -> Mem.valid_access m5 Mint32 b0 (Int.unsigned n' * 24 + n0 * 4) Readable).
          {
            specialize (HV _ a0).
            intros. specialize (HV _ H).
            eapply Mem.valid_access_implies; eauto.
            constructor.
          }
          clear HV.
          assert (HP: exists v0, Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 0 * 4) = Some v0).
          {
            assert (0<= 0 <= 5) by omega.
            eapply Mem.valid_access_load; eauto.
          }
          destruct HP as [v0 HLD0].
          assert (HP: exists v1, Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 1 * 4) = Some v1).
          {
            assert (0<= 1 <= 5) by omega.
            eapply Mem.valid_access_load; eauto.
          }          
          destruct HP as [v1 HLD1].
          assert (HP: exists v2, Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 2 * 4) = Some v2).
          {
            assert (0<= 2 <= 5) by omega.
            eapply Mem.valid_access_load; eauto.
          }
          destruct HP as [v2 HLD2].
          assert (HP: exists v3, Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 3 * 4) = Some v3).
          {
            assert (0<= 3 <= 5) by omega.
            eapply Mem.valid_access_load; eauto.
          }
          destruct HP as [v3 HLD3].
          assert (HP: exists v4, Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 4 * 4) = Some v4).
          {
            assert (0<= 4 <= 5) by omega.
            eapply Mem.valid_access_load; eauto.
          }
          destruct HP as [v4 HLD4].
          assert (HP: exists v5, Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + 5 * 4) = Some v5).
          {
            assert (0<= 5 <= 5) by omega.
            eapply Mem.valid_access_load; eauto.
          }
          destruct HP as [v5 HLD5].
          simpl in *.
          assert(N_ARU': rs2 EAX = Vint n /\ rs2 EDX = Vint n').
          {
            unfold Pregmap.get in *.
            split.
            specialize (match_reg EAX).
            rewrite N_ARU1 in match_reg.
            inv match_reg; trivial.
            unfold Pregmap.get in *.
            specialize (match_reg EDX).
            rewrite N_ARU2 in match_reg.
            inv match_reg; trivial.
          }
          destruct N_ARU' as [N_ARU1' N_ARU2'].
          assert(HMCTXT: match_KCtxtPool s (kctxt d1') m5 ι).
          {
            econstructor; eauto. clear HLD0 HLD1 HLD2 HLD3 HLD4 HLD5.
            intros.
            destruct (zeq ofs (Int.unsigned n)).
            * (* ofs = Int.unsigned n*)
              clear HMAT'. subst.
              specialize (ZtoPreg_range _ _ H2).
              intros Hn1.
              destruct (zeq n1 5); subst; inv H2.
              eexists (Val.load_result Mint32 (rs2 RA)).
              split.
              eapply Mem.load_store_same; eauto. 
              split.
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_3; eauto. 
              inv H4. simpl in *.
              rewrite ZMap.gss.
              unfold Pregmap.get in *.
              specialize (match_reg RA).
              inv match_reg; try constructor.
              econstructor; eauto.
              assert (HW0: Mem.load Mint32 m5 b0 (Int.unsigned n * 24 + n1 * 4) = 
                           Mem.load Mint32 m4 b0 (Int.unsigned n * 24 + n1 * 4)).
              {
                rewrite (Mem.load_store_other  _ _ _ _ _ _ HST5).
                trivial.
                right. left. simpl. omega.
              }
              destruct (zeq n1 4); subst. inv H4.
              eexists (Val.load_result Mint32 (rs2 EBP)).
              split. rewrite HW0.
              eapply Mem.load_store_same; eauto. 
              split.
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_3; eauto. 
              inv H5. simpl in *. rewrite ZMap.gss.
              unfold Pregmap.get in *.
              specialize (match_reg EBP).
              inv match_reg; try constructor.
              econstructor; eauto.
              assert (HW1: Mem.load Mint32 m5 b0 (Int.unsigned n * 24 + n1 * 4)
                           = Mem.load Mint32 m3 b0 (Int.unsigned n * 24 + n1 * 4)).
              {
                rewrite HW0.
                rewrite (Mem.load_store_other  _ _ _ _ _ _ HST4).
                trivial.
                right. left. simpl. omega.
              }
              clear HW0.
              destruct (zeq n1 3); subst. inv H4.
              eexists (Val.load_result Mint32 (rs2 EBX)).
              split. rewrite HW1.
              eapply Mem.load_store_same; eauto. 
              split.
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_3; eauto. 
              inv H5. simpl in *.
              rewrite ZMap.gss.
              unfold Pregmap.get in *.
              specialize (match_reg EBX).
              inv match_reg; try constructor.
              econstructor; eauto.
              assert (HW2: Mem.load Mint32 m5 b0 (Int.unsigned n * 24 + n1 * 4)
                           = Mem.load Mint32 m2' b0 (Int.unsigned n * 24 + n1 * 4)).
              {
                rewrite HW1.
                rewrite (Mem.load_store_other  _ _ _ _ _ _ HST3).
                trivial.
                right. left. simpl. omega.
              }
              clear HW1.
              destruct (zeq n1 2); subst. inv H4.
              eexists (Val.load_result Mint32 (rs2 ESI)).
              split. rewrite HW2.
              eapply Mem.load_store_same; eauto. 
              split.
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_3; eauto. 
              inv H5. simpl in *.
              rewrite ZMap.gss.
              unfold Pregmap.get in *.
              specialize (match_reg ESI).
              inv match_reg; try constructor.
              econstructor; eauto.
              assert (HW1: Mem.load Mint32 m5 b0 (Int.unsigned n * 24 + n1 * 4)
                           = Mem.load Mint32 m1 b0 (Int.unsigned n * 24 + n1 * 4)).
              {
                rewrite HW2.
                rewrite (Mem.load_store_other  _ _ _ _ _ _ HST2).
                trivial.
                right. left. simpl. omega.
              }
              clear HW2.
              destruct (zeq n1 1); subst; inv H4.
              eexists (Val.load_result Mint32 (rs2 EDI)).
              split. rewrite HW1.
              eapply Mem.load_store_same; eauto. 
              split.
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_3; eauto. 
              inv H5. simpl in *.
              rewrite ZMap.gss.
              unfold Pregmap.get in *.
              specialize (match_reg EDI).
              inv match_reg; try constructor.
              econstructor; eauto.
              assert (HW0: Mem.load Mint32 m5 b0 (Int.unsigned n * 24 + n1 * 4)
                           = Mem.load Mint32 m0 b0 (Int.unsigned n * 24 + n1 * 4)).
              {
                rewrite HW1.
                rewrite (Mem.load_store_other  _ _ _ _ _ _ HST1).
                trivial.
                right. left. simpl. omega.
              }
              clear HW1.
              destruct (zeq n1 0). subst. inv H5.
              eexists (Val.load_result Mint32 (rs2 ESP)).
              replace (Int.unsigned n * 24 + 0 * 4) with (Int.unsigned n * 24) in * by omega.
              split. rewrite HW0.
              eapply Mem.load_store_same; eauto. 
              split.
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_1; eauto. 
              eapply Mem.store_valid_access_3; eauto. 
              simpl in *.
              rewrite ZMap.gss.
              unfold Pregmap.get in *.
              specialize (match_reg ESP).
              inv match_reg; try constructor.
              econstructor; eauto.          
              omega.
            *  (** ofs <> Int.unsigned n**)
              specialize (HMAT' _ H0 n2 _ _ H2).
              inv H4. simpl.      
              rewrite ZMap.gso; trivial.
          }
          refine_split; eauto 2.
          - econstructor; eauto; simpl; lift_trivial;
            try eassumption; unfold set; simpl.
            eapply reg_symbol_inject; eassumption.
            rewrite HST0. reflexivity.
            simpl; rewrite HST1. reflexivity.
            simpl; rewrite HST2. reflexivity.
            simpl; rewrite HST3. reflexivity.
            simpl; rewrite HST4. reflexivity.
            simpl; rewrite HST5. reflexivity.

            simpl. inv match_related.
            split; congruence.
          - pose proof match_related as match_relate'.
            inv match_related. inv H4.
            econstructor; eauto.
            split; eauto; pattern2_refinement_simpl.           
            econstructor; eauto 2.
            econstructor; simpl; eauto 2.
            assert (HINJ: forall n1 r,
                            ZtoPreg n1 = Some r ->
                            forall v ,
                              Mem.load Mint32 m5 b0 (Int.unsigned n' * 24 + n1 * 4) = Some v ->
                              val_inject ι ((ZMap.get (Int.unsigned n') (kctxt d1)) r) v).
            {
              assert (Hn: Int.unsigned n' <> Int.unsigned n) by auto.
              intros. specialize (HMAT' _ a0 Hn _ _ H0).
              destruct HMAT' as [v'[HL'[_ HV']]].
              rewrite H2 in HL'. inv HL'.
              refine_split'; eauto 2.
              unfold Pregmap.get in *.
              specialize (N_TYPE _ _ H0).
              caseEq (ZMap.get (Int.unsigned n') (kctxt d1) r); intros;
              rewrite H3 in *; try assumption; inv N_TYPE.
            }
            clear HMAT'. subst rs3.
            val_inject_simpl;
              try (eapply HINJ; [apply PregToZ_correct; reflexivity| trivial]).
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
          sim (crel HDATA LDATA) pkcontext_passthrough mshare.
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
          - apply shared_mem_status_sim.
          - apply offer_shared_mem_sim.
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
