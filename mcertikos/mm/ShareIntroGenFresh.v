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
(*           Layers of PM: Refinement Proof for PShareIntro           *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between PKContextNew layer and PShareIntro layer*)
Require Import ShareIntroGenSpec.
Require Import ShareIntroGenDef.

(** * Definition of the refinement relation*)
Section Refinement.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Ltac pattern2_refinement_simpl:=  
      pattern2_refinement_simpl' (@relate_AbData).


    Lemma clear_shared_mem_spec_ref:
      compatsim (crel HDATA LDATA) (gensem clear_shared_mem_spec) clear_shared_mem_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      assert(HOS: kernel_mode d2 
                  /\ 0 <= Int.unsigned i < num_proc
                  /\ 0 <= Int.unsigned i0 < num_proc).
      {
        simpl; inv match_related.
        functional inversion H1; functional inversion H2; 
        repeat (split; trivial); try congruence.
      }
      destruct HOS as (Hkern & HOS & HOS1).
      inv H. rename H0 into HMem; destruct (HMem _ _ HOS HOS1) as [v1[v2[v3[HL1[HV1[HL2[HV2[HL3[HV3 HM]]]]]]]]].
      specialize (Mem.valid_access_store _ _ _ _ (Vint Int.zero) HV1); intros [m'1 HST1].
      apply (Mem.store_valid_access_1 _ _ _ _ _ _ HST1) in HV2.
      specialize (Mem.valid_access_store _ _ _ _ (Vint (Int.repr SHARED_MEM_DEAD)) HV2); intros [m'2 HST2].
      apply (Mem.store_valid_access_1 _ _ _ _ _ _ HST1) in HV3.
      apply (Mem.store_valid_access_1 _ _ _ _ _ _ HST2) in HV3.
      specialize (Mem.valid_access_store _ _ _ _ (Vint Int.one) HV3); intros [m'3 HST3].
      refine_split.
      - econstructor; eauto.
        instantiate (1:= (m'1, d2)).
        replace (Int.unsigned (Int.repr (768 * Int.unsigned i + 12 * Int.unsigned i0 + 0))) with
        (Int.unsigned i * 768 + Int.unsigned i0 * 12) by (rewrite Int.unsigned_repr; trivial; rewrite_omega).
        simpl; lift_trivial.
        subrewrite'.
        instantiate (1:= (m'2, d2)).
        replace (Int.unsigned (Int.repr (768 * Int.unsigned i + 12 * Int.unsigned i0 + 4))) with
        (Int.unsigned i * 768 + Int.unsigned i0 * 12 + 4) by (rewrite Int.unsigned_repr; trivial; rewrite_omega).
        simpl; lift_trivial. 
        subrewrite'.
        instantiate (1:= d2).
        instantiate (1:= m'3).
        replace (Int.unsigned (Int.repr (768 * Int.unsigned i + 12 * Int.unsigned i0 + 8))) with
        (Int.unsigned i * 768 + Int.unsigned i0 * 12 + 8) by (rewrite Int.unsigned_repr; trivial; rewrite_omega).
        simpl; lift_trivial. 
        subrewrite'.
      - constructor.
      - pose proof H1 as Hspec.
        functional inversion Hspec; subst.
        split; eauto; pattern2_refinement_simpl.
        econstructor; simpl; eauto.
        econstructor; eauto; intros.
        destruct (zeq pid1 (Int.unsigned i)); subst.
        + (* pid1 = Int.unsigned i *)
          destruct (zeq pid2 (Int.unsigned i0)); subst.      
          * refine_split'; eauto;
            repeat  (eapply Mem.store_valid_access_1; eauto).
            erewrite (Mem.load_store_other _ _ _ _ _ _ HST3); eauto; [|right; left; simpl; omega].
            erewrite (Mem.load_store_other _ _ _ _ _ _ HST2); eauto; [|right; left; simpl; omega].
            eapply Mem.load_store_same; eauto.
            erewrite (Mem.load_store_other _ _ _ _ _ _ HST3); eauto; [|right; left; simpl; omega].
            eapply Mem.load_store_same; eauto.
            eapply Mem.load_store_same; eauto.
            repeat rewrite ZMap.gss. simpl.
            replace 0 with (Int.unsigned (Int.repr 0)).
            constructor; trivial.
            apply Int.unsigned_repr. rewrite_omega.
          * (* pid2 <> Int.unsigned i0 *)
            specialize (HMem _ _ H H7).
            destruct HMem as [v1'[v2'[v3'[HL1'[HV1'[HL2'[HV2'[HL3'[HV3' HM']]]]]]]]].
            repeat (erewrite (Mem.load_store_other _ _ _ _ _ _ HST3); [|load_other_simpl pid2 i0]).
            repeat (erewrite (Mem.load_store_other _ _ _ _ _ _ HST2); [|load_other_simpl pid2 i0]).
            repeat (erewrite (Mem.load_store_other _ _ _ _ _ _ HST1); [|load_other_simpl pid2 i0]).
            refine_split'; eauto;
            repeat (eapply Mem.store_valid_access_1; eauto).
            rewrite ZMap.gss.
            rewrite ZMap.gso; auto.
        + (* pid1 <> Int.unsigned i *)
          specialize (HMem _ _ H H7).
          destruct HMem as [v1'[v2'[v3'[HL1'[HV1'[HL2'[HV2'[HL3'[HV3' HM']]]]]]]]].
          repeat (erewrite (Mem.load_store_other _ _ _ _ _ _ HST3); [|load_other_simpl pid1 i]).
          repeat (erewrite (Mem.load_store_other _ _ _ _ _ _ HST2); [|load_other_simpl pid1 i]).
          repeat (erewrite (Mem.load_store_other _ _ _ _ _ _ HST1); [|load_other_simpl pid1 i]).
          refine_split'; eauto;
          repeat (eapply Mem.store_valid_access_1; eauto).
          rewrite ZMap.gso; auto.
      - apply inject_incr_refl.
    Qed.

    Lemma get_shared_mem_loc_spec_ref:
      compatsim (crel HDATAOps LDATAOps) (gensem get_shared_mem_loc_spec) get_shared_mem_loc_spec_low.
    Proof.
      compatsim_simpl (@match_AbData). inv H.
      assert(HOS: kernel_mode d2 
                  /\ 0 <= Int.unsigned i < num_proc
                  /\ 0 <= Int.unsigned i0 < num_proc).
      {
        simpl; inv match_related.
        functional inversion H2; functional inversion H3; 
        repeat (split; trivial); try congruence.
      }
      destruct HOS as (Hkern & HOS & HOS1).
      pose proof H0 as HMem.
      specialize (H0 _ _ HOS HOS1). destruct H0 as [v1[v2[v3[HL1[_[HL2[_[HL3[_ HM]]]]]]]]].
      refine_split; eauto. econstructor; eauto.
      assert (HP: v1 = Vint z).
      {
        functional inversion H2; subst. rewrite H7 in HM. inv HM.
        rewrite <- Int.repr_unsigned with z. rewrite <- H10.
        rewrite Int.repr_unsigned. trivial.
      }        
      replace (768 * Int.unsigned i + 12 * Int.unsigned i0 + 0) with
      (Int.unsigned i * 768 + Int.unsigned i0 * 12) by omega.
      subst; assumption.
    Qed.

    Lemma get_shared_mem_state_spec_ref:
      compatsim (crel HDATAOps LDATAOps) (gensem get_shared_mem_state_spec) get_shared_mem_state_spec_low.
    Proof.
      compatsim_simpl (@match_AbData). inv H.
      assert(HOS: kernel_mode d2 
                  /\ 0 <= Int.unsigned i < num_proc
                  /\ 0 <= Int.unsigned i0 < num_proc).
      {
        simpl; inv match_related.
        functional inversion H2; functional inversion H3; 
        repeat (split; trivial); try congruence.
      }
      destruct HOS as (Hkern & HOS & HOS1).
      pose proof H0 as HMem.
      specialize (H0 _ _ HOS HOS1). destruct H0 as [v1[v2[v3[HL1[_[HL2[_[HL3[_ HM]]]]]]]]].
      refine_split; eauto. econstructor; eauto.
      assert (HP: v2 = Vint z).
      {
        functional inversion H2; subst. rewrite H7 in HM. inv HM.
        apply Z2SharedMemInfo_correct in H14.
        rewrite H14 in H.
        rewrite <- Int.repr_unsigned with z. rewrite <- H.
        rewrite Int.repr_unsigned. trivial.
      }          
      replace (768 * Int.unsigned i + 12 * Int.unsigned i0 + 4) with
      (Int.unsigned i * 768 + Int.unsigned i0 * 12 + 4) by omega.
      subst; assumption.
    Qed.

    Lemma ZtoBool_correct:
      forall b i,
        ZtoBool i = Some b -> BooltoZ b = i.
    Proof.
      intros. functional inversion H; trivial.
    Qed.

    Lemma get_shared_mem_seen_spec_ref:
      compatsim (crel HDATAOps LDATAOps) (gensem get_shared_mem_seen_spec) get_shared_mem_seen_spec_low.
    Proof.
      compatsim_simpl (@match_AbData). inv H.
      assert(HOS: kernel_mode d2 
                  /\ 0 <= Int.unsigned i < num_proc
                  /\ 0 <= Int.unsigned i0 < num_proc).
      {
        simpl; inv match_related.
        functional inversion H2; functional inversion H3; 
        repeat (split; trivial); try congruence.
      }
      destruct HOS as (Hkern & HOS & HOS1).
      pose proof H0 as HMem.
      specialize (H0 _ _ HOS HOS1). destruct H0 as [v1[v2[v3[HL1[_[HL2[_[HL3[_ HM]]]]]]]]].
      refine_split; eauto. econstructor; eauto.
      assert (HP: v3 = Vint z).
      {
        functional inversion H2; subst. rewrite H7 in HM. inv HM.
        apply ZtoBool_correct in H15.
        rewrite H15 in H.
        rewrite <- Int.repr_unsigned with z. rewrite <- H.
        rewrite Int.repr_unsigned. trivial.
      }          
      replace (768 * Int.unsigned i + 12 * Int.unsigned i0 + 8)
      with (Int.unsigned i * 768 + Int.unsigned i0 * 12 + 8) by omega.
      subst; assumption.
    Qed.

    Lemma set_shared_mem_loc_spec_ref:
      compatsim (crel HDATA LDATA) (gensem set_shared_mem_loc_spec) set_shared_mem_loc_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      assert(HOS: kernel_mode d2 
                  /\ 0 <= Int.unsigned i < num_proc
                  /\ 0 <= Int.unsigned i0 < num_proc).
      {
        simpl; inv match_related.
        functional inversion H1; functional inversion H2; 
        repeat (split; trivial); try congruence.
      }
      destruct HOS as (Hkern & HOS & HOS1).
      inv H. rename H0 into HMem; destruct (HMem _ _ HOS HOS1) as [v1[v2[v3[HL1[HV1[HL2[HV2[HL3[HV3 HM]]]]]]]]].
      specialize (Mem.valid_access_store _ _ _ _ (Vint i1) HV1); intros [m' HST].
      refine_split.
      - econstructor; eauto.
        instantiate (2:= m').
        instantiate (1:= d2).
        replace (768 * Int.unsigned i + 12 * Int.unsigned i0 + 0) with
        (Int.unsigned i * 768 + Int.unsigned i0 * 12) by omega.
        simpl; lift_trivial.
        subrewrite'.
      - constructor.
      - pose proof H1 as Hspec.
        functional inversion Hspec; subst.
        split; eauto; pattern2_refinement_simpl.
        rewrite H7 in HM. inv HM.
        econstructor; simpl; eauto.
        econstructor; eauto; intros.
        destruct (zeq pid1 (Int.unsigned i)); subst.
        + (* pid1 = Int.unsigned i *)
          destruct (zeq pid2 (Int.unsigned i0)); subst.      
          * refine_split'; eauto;
            try eapply Mem.store_valid_access_1; eauto.
            eapply Mem.load_store_same; eauto.
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL2; eauto.
            simpl; right; right. reflexivity.
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL3; eauto.
            simpl; right; right. omega.
            repeat rewrite ZMap.gss. simpl.
            constructor; assumption.
          * (* pid2 <> Int.unsigned i0 *)
            specialize (HMem _ _ H H8).
            destruct HMem as [v1'[v2'[v3'[HL1'[HV1'[HL2'[HV2'[HL3'[HV3' HM']]]]]]]]].
            refine_split'; eauto;
            try eapply Mem.store_valid_access_1; eauto.
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
            simpl; right. destruct (zlt pid2 (Int.unsigned i0)); [left; omega|right; omega].
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL2'; eauto.
            simpl; right. destruct (zlt pid2 (Int.unsigned i0)); [left; omega|right; omega].
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL3'; eauto.
            simpl; right. destruct (zlt pid2 (Int.unsigned i0)); [left; omega|right; omega].
            rewrite ZMap.gss.
            rewrite ZMap.gso; trivial.
        + (* pid1 <> Int.unsigned i *)
          specialize (HMem _ _ H H8).
          destruct HMem as [v1'[v2'[v3'[HL1'[HV1'[HL2'[HV2'[HL3'[HV3' HM']]]]]]]]].
          refine_split'; eauto;
          try eapply Mem.store_valid_access_1; eauto.
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
          simpl; right. destruct (zlt pid1 (Int.unsigned i)); [left; omega|right; omega].
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL2'; eauto.
          simpl; right. destruct (zlt pid1 (Int.unsigned i)); [left; omega|right; omega].
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL3'; eauto.
          simpl; right. destruct (zlt pid1 (Int.unsigned i)); [left; omega|right; omega].          
          rewrite ZMap.gso; trivial.
      - apply inject_incr_refl.
    Qed.

    Lemma set_shared_mem_state_spec_ref:
      compatsim (crel HDATA LDATA) (gensem set_shared_mem_state_spec) set_shared_mem_state_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      assert(HOS: kernel_mode d2 
                  /\ 0 <= Int.unsigned i < num_proc
                  /\ 0 <= Int.unsigned i0 < num_proc).
      {
        simpl; inv match_related.
        functional inversion H1; functional inversion H2; 
        repeat (split; trivial); try congruence.
      }
      destruct HOS as (Hkern & HOS & HOS1).
      inv H. rename H0 into HMem; destruct (HMem _ _ HOS HOS1) as [v1[v2[v3[HL1[HV1[HL2[HV2[HL3[HV3 HM]]]]]]]]].
      specialize (Mem.valid_access_store _ _ _ _ (Vint i1) HV2); intros [m' HST].
      refine_split.
      - econstructor; eauto.
        instantiate (2:= m').
        instantiate (1:= d2).
        replace (768 * Int.unsigned i + 12 * Int.unsigned i0 + 4) with
        (Int.unsigned i * 768 + Int.unsigned i0 * 12 + 4) by omega.
        simpl; lift_trivial.
        subrewrite'.
      - constructor.
      - pose proof H1 as Hspec.
        functional inversion Hspec; subst.
        split; eauto; pattern2_refinement_simpl.
        rewrite H8 in HM. inv HM.
        econstructor; simpl; eauto.
        econstructor; eauto; intros.
        destruct (zeq pid1 (Int.unsigned i)); subst.
        + (* pid1 = Int.unsigned i *)
          destruct (zeq pid2 (Int.unsigned i0)); subst.      
          * refine_split'; eauto;
            try eapply Mem.store_valid_access_1; eauto.
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1; eauto.
            simpl; right; left. reflexivity.
            eapply Mem.load_store_same; eauto.
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL3; eauto.
            simpl; right; right. omega.
            repeat rewrite ZMap.gss. simpl.
            constructor; assumption.
          * (* pid2 <> Int.unsigned i0 *)
            specialize (HMem _ _ H H9).
            destruct HMem as [v1'[v2'[v3'[HL1'[HV1'[HL2'[HV2'[HL3'[HV3' HM']]]]]]]]].
            refine_split'; eauto;
            try eapply Mem.store_valid_access_1; eauto.
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
            simpl; right. destruct (zlt pid2 (Int.unsigned i0)); [left; omega|right; omega].
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL2'; eauto.
            simpl; right. destruct (zlt pid2 (Int.unsigned i0)); [left; omega|right; omega].
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL3'; eauto.
            simpl; right. destruct (zlt pid2 (Int.unsigned i0)); [left; omega|right; omega].
            rewrite ZMap.gss.
            rewrite ZMap.gso; trivial.
        + (* pid1 <> Int.unsigned i *)
          specialize (HMem _ _ H H9).
          destruct HMem as [v1'[v2'[v3'[HL1'[HV1'[HL2'[HV2'[HL3'[HV3' HM']]]]]]]]].
          refine_split'; eauto;
          try eapply Mem.store_valid_access_1; eauto.
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
          simpl; right. destruct (zlt pid1 (Int.unsigned i)); [left; omega|right; omega].
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL2'; eauto.
          simpl; right. destruct (zlt pid1 (Int.unsigned i)); [left; omega|right; omega].
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL3'; eauto.
          simpl; right. destruct (zlt pid1 (Int.unsigned i)); [left; omega|right; omega].          
          rewrite ZMap.gso; trivial.
      - apply inject_incr_refl.
    Qed.

    Lemma set_shared_mem_seen_spec_ref:
      compatsim (crel HDATA LDATA) (gensem set_shared_mem_seen_spec) set_shared_mem_seen_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      assert(HOS: kernel_mode d2 
                  /\ 0 <= Int.unsigned i < num_proc
                  /\ 0 <= Int.unsigned i0 < num_proc).
      {
        simpl; inv match_related.
        functional inversion H1; functional inversion H2; 
        repeat (split; trivial); try congruence.
      }
      destruct HOS as (Hkern & HOS & HOS1).
      inv H. rename H0 into HMem; destruct (HMem _ _ HOS HOS1) as [v1[v2[v3[HL1[HV1[HL2[HV2[HL3[HV3 HM]]]]]]]]].
      specialize (Mem.valid_access_store _ _ _ _ (Vint i1) HV3); intros [m' HST].
      refine_split.
      - econstructor; eauto.
        instantiate (2:= m').
        instantiate (1:= d2).
        replace (768 * Int.unsigned i + 12 * Int.unsigned i0 + 8) with
        (Int.unsigned i * 768 + Int.unsigned i0 * 12 + 8) by omega.
        simpl; lift_trivial.
        subrewrite'.
      - constructor.
      - pose proof H1 as Hspec.
        functional inversion Hspec; subst.
        split; eauto; pattern2_refinement_simpl.
        rewrite H8 in HM. inv HM.
        econstructor; simpl; eauto.
        econstructor; eauto; intros.
        destruct (zeq pid1 (Int.unsigned i)); subst.
        + (* pid1 = Int.unsigned i *)
          destruct (zeq pid2 (Int.unsigned i0)); subst.      
          * refine_split'; eauto;
            try eapply Mem.store_valid_access_1; eauto.
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1; eauto.
            simpl; right; left. omega.
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL2; eauto.
            simpl; right; left. omega.
            eapply Mem.load_store_same; eauto.
            repeat rewrite ZMap.gss. simpl.
            constructor; assumption.
          * (* pid2 <> Int.unsigned i0 *)
            specialize (HMem _ _ H H9).
            destruct HMem as [v1'[v2'[v3'[HL1'[HV1'[HL2'[HV2'[HL3'[HV3' HM']]]]]]]]].
            refine_split'; eauto;
            try eapply Mem.store_valid_access_1; eauto.
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
            simpl; right. destruct (zlt pid2 (Int.unsigned i0)); [left; omega|right; omega].
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL2'; eauto.
            simpl; right. destruct (zlt pid2 (Int.unsigned i0)); [left; omega|right; omega].
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL3'; eauto.
            simpl; right. destruct (zlt pid2 (Int.unsigned i0)); [left; omega|right; omega].
            rewrite ZMap.gss.
            rewrite ZMap.gso; trivial.
        + (* pid1 <> Int.unsigned i *)
          specialize (HMem _ _ H H9).
          destruct HMem as [v1'[v2'[v3'[HL1'[HV1'[HL2'[HV2'[HL3'[HV3' HM']]]]]]]]].
          refine_split'; eauto;
          try eapply Mem.store_valid_access_1; eauto.
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
          simpl; right. destruct (zlt pid1 (Int.unsigned i)); [left; omega|right; omega].
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL2'; eauto.
          simpl; right. destruct (zlt pid1 (Int.unsigned i)); [left; omega|right; omega].
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL3'; eauto.
          simpl; right. destruct (zlt pid1 (Int.unsigned i)); [left; omega|right; omega].          
          rewrite ZMap.gso; trivial.
      - apply inject_incr_refl.
    Qed.

  End WITHMEM.

End Refinement.
