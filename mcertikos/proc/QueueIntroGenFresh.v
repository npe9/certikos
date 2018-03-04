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
(*           Layers of PM: Refinement Proof for PQueueIntro            *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between PThreadInit layer and PQueueIntro layer*)
Require Import QueueIntroGenDef.
Require Import QueueIntroGenSpec.

(** * Definition of the refinement relation*)
Section Refinement.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Ltac pattern2_refinement_simpl:=  
      pattern2_refinement_simpl' (@relate_AbData).

    Lemma get_head_spec_ref:
      compatsim (crel HDATA LDATA) (gensem get_head_spec) get_head_spec_low.
    Proof.
      compatsim_simpl (@match_AbData). inv H.
      assert(HOS: kernel_mode d2 /\ 0 <= Int.unsigned i <= num_chan).
      {
        simpl; inv match_related.
        functional inversion H2; repeat (split; trivial); congruence.
      }
      destruct HOS as [Hkern HOS].
      pose proof H0 as HMem.
      specialize (H0 _ HOS). destruct H0 as [v1[v2[HL1[_[HL2[_ HM]]]]]].
      assert (HP: v1 = Vint z).
      {
        functional inversion H2; subst. rewrite H7 in HM; inv HM.
        rewrite <- Int.repr_unsigned with z; rewrite <- H8.
        rewrite Int.repr_unsigned. trivial.
      }          
      refine_split; eauto; econstructor; eauto.
    Qed.

    Lemma get_tail_spec_ref:
      compatsim (crel HDATA LDATA) (gensem get_tail_spec) get_tail_spec_low.
    Proof.
      compatsim_simpl (@match_AbData). inv H.
      assert(HOS: kernel_mode d2 /\ 0 <= Int.unsigned i <= num_chan).
      {
        simpl; inv match_related.
        functional inversion H2; repeat (split; trivial); congruence.
      }
      destruct HOS as [Hkern HOS].
      pose proof H0 as HMem.
      specialize (H0 _ HOS). destruct H0 as [v1[v2[HL1[_[HL2[_ HM]]]]]].
      assert (HP: v2 = Vint z).
      {
        functional inversion H2; subst. rewrite H7 in HM; inv HM.
        rewrite <- Int.repr_unsigned with z; rewrite <- H9.
        rewrite Int.repr_unsigned. trivial.
      }          
      refine_split; eauto; econstructor; eauto.
    Qed.

    Lemma set_head_spec_ref:
      compatsim (crel HDATA LDATA) (gensem set_head_spec) set_head_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      assert (Hkern: kernel_mode d2 /\ 0<= Int.unsigned i <= num_chan).
      {
        inv match_related. functional inversion H1; subst.
        repeat (split; trivial); try congruence; eauto.
      }
      destruct Hkern as [Hkern HOS].
      inv H. rename H0 into HMem; destruct (HMem _ HOS) as [v1[v2[HL1[HV1[HL2[HV2 HM]]]]]].
      specialize (Mem.valid_access_store _ _ _ _ (Vint i0) HV1); intros [m' HST].
      refine_split.
      - econstructor; eauto.
        simpl; lift_trivial. 
        rewrite HST. reflexivity.
      - constructor.
      - pose proof H1 as Hspec.
        functional inversion Hspec; subst.
        split; eauto; pattern2_refinement_simpl. 
        rewrite H7 in HM. inv HM.
        econstructor; simpl; eauto.
        econstructor; eauto; intros.
        destruct (zeq ofs (Int.unsigned i)); subst.
        + (* ofs = Int.unsigned i *)
          refine_split'; eauto;
          try eapply Mem.store_valid_access_1; eauto.
          eapply Mem.load_store_same; eauto.
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL2; eauto.
          simpl; right; right. reflexivity.
          rewrite ZMap.gss. simpl.
          constructor. 
          
        + (* ofs <> Int.unsigned i *)
          specialize (HMem _ H).
          destruct HMem as [v1'[v2'[HL1'[HV1'[HL2'[HV2' HM']]]]]].
          refine_split'; eauto;
          try eapply Mem.store_valid_access_1; eauto.
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
          simpl; right. destruct (zlt ofs (Int.unsigned i)); [left; omega|right; omega].
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL2'; eauto.
          simpl; right. destruct (zlt ofs (Int.unsigned i)); [left; omega|right; omega].
          rewrite ZMap.gso; trivial.
      - apply inject_incr_refl.
    Qed.

    Lemma set_tail_spec_ref:
      compatsim (crel HDATA LDATA) (gensem set_tail_spec) set_tail_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      assert (Hkern: kernel_mode d2 /\ 0<= Int.unsigned i <= num_chan).
      {
        inv match_related. functional inversion H1; subst.
        repeat (split; trivial); try congruence; eauto.
      }
      destruct Hkern as [Hkern HOS].
      inv H. rename H0 into HMem; destruct (HMem _ HOS) as [v1[v2[HL1[HV1[HL2[HV2 HM]]]]]].
      specialize (Mem.valid_access_store _ _ _ _ (Vint i0) HV2); intros [m' HST].
      refine_split.
      - econstructor; eauto.
        simpl; lift_trivial. rewrite HST. reflexivity.
      - constructor.
      - pose proof H1 as Hspec.
        functional inversion Hspec; subst.
        split; eauto; pattern2_refinement_simpl. 
        rewrite H7 in HM. inv HM.
        econstructor; simpl; eauto.
        econstructor; eauto; intros.
        destruct (zeq ofs (Int.unsigned i)); subst.
        + (* ofs = Int.unsigned i *)
          refine_split'; eauto;
          try eapply Mem.store_valid_access_1; eauto.
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1; eauto.
          simpl; right; left. reflexivity.
          eapply Mem.load_store_same; eauto.
          rewrite ZMap.gss. simpl.
          constructor. 
          
        + (* ofs <> Int.unsigned i *)
          specialize (HMem _ H).
          destruct HMem as [v1'[v2'[HL1'[HV1'[HL2'[HV2' HM']]]]]].
          refine_split'; eauto;
          try eapply Mem.store_valid_access_1; eauto.
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
          simpl; right. destruct (zlt ofs (Int.unsigned i)); [left; omega|right; omega].
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL2'; eauto.
          simpl; right. destruct (zlt ofs (Int.unsigned i)); [left; omega|right; omega].
          rewrite ZMap.gso; trivial.
      - apply inject_incr_refl.
    Qed.

    Lemma tdq_init_spec_ref:
      compatsim (crel HDATA LDATA) (gensem tdq_init_spec) tdq_init_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      assert (Hkern: kernel_mode d2 /\ 0<= Int.unsigned i <= num_chan).
      {
        inv match_related. functional inversion H1; subst.
        repeat (split; trivial); try congruence; eauto.
      }
      destruct Hkern as [Hkern HOS].
      inv H. rename H0 into HMem; destruct (HMem _ HOS) as [v1[v2[HL1[HV1[HL2[HV2 HM]]]]]].
      specialize (Mem.valid_access_store _ _ _ _ (Vint (Int.repr num_chan)) HV1); intros [m'1 HST1].
      apply (Mem.store_valid_access_1 _ _ _ _ _ _ HST1) in HV2.
      specialize (Mem.valid_access_store _ _ _ _ (Vint (Int.repr num_chan)) HV2); intros [m'2 HST2].
      refine_split.
      - econstructor; eauto.
        instantiate (1:= (m'1, d2)).
        simpl. lift_trivial. rewrite HST1.
        reflexivity.
        simpl. lift_trivial. rewrite HST2.
        reflexivity.
      - constructor.
      - pose proof H1 as Hspec.
        functional inversion Hspec; subst.
        split; eauto; pattern2_refinement_simpl.
        econstructor; simpl; eauto.
        econstructor; eauto; intros.
        destruct (zeq ofs (Int.unsigned i)); subst.
        + (* ofs = Int.unsigned i *)
          refine_split'; eauto;
          repeat (eapply Mem.store_valid_access_1; eauto).
          erewrite (Mem.load_store_other _ _ _ _ _ _ HST2); eauto; [|right; left; simpl; omega].
          eapply Mem.load_store_same; eauto.
          eapply Mem.load_store_same; eauto.
          rewrite ZMap.gss.
          replace 64 with (Int.unsigned (Int.repr 64)).
          constructor; trivial.
          apply Int.unsigned_repr. rewrite int_max; omega.

        + (* ofs <> Int.unsigned i *)
          specialize (HMem _ H).
          destruct HMem as [v1'[v2'[HL1'[HV1'[HL2'[HV2' HM']]]]]].
          repeat (erewrite (Mem.load_store_other _ _ _ _ _ _ HST2); [|load_other_simpl ofs i]).
          repeat (erewrite (Mem.load_store_other _ _ _ _ _ _ HST1); [|load_other_simpl ofs i]).
          refine_split'; eauto;
          repeat (eapply Mem.store_valid_access_1; eauto).
          rewrite ZMap.gso; auto.
      - apply inject_incr_refl.
    Qed.

  End WITHMEM.

End Refinement.