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
Require Import IPCIntroGenDef.
Require Import IPCIntroGenSpec.

(** * Definition of the refinement relation*)
Section Refinement.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Ltac pattern2_refinement_simpl:=  
      pattern2_refinement_simpl' (@relate_AbData).

    Lemma get_kernel_pa_kern_mode:
      forall i1 i2 v d,
        get_kernel_pa_spec i1 i2 d = Some v
        -> kernel_mode d
           /\ 0 <= i1 < num_proc.
    Proof.
      unfold get_kernel_pa_spec, ptRead_spec, getPTE_spec, PTE_Arg, PDE_Arg. 
      simpl; intros.
      subdestruct; auto.
    Qed.

    Lemma get_kernel_pa_spec_ref:
      compatsim (crel HDATA LDATA) (gensem get_kernel_pa_spec) 
                get_kernel_pa_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      exploit get_kernel_pa_exist; eauto 1. intros.
      exploit get_kernel_pa_kern_mode; eauto. intros (Hkern & Hrange).
      refine_split; try econstructor; eauto. 
    Qed.

    Lemma get_sync_chan_to_spec_ref:
      compatsim (crel HDATA LDATA) (gensem get_sync_chan_to_spec) get_sync_chan_to_spec_low.
    Proof.
      compatsim_simpl (@match_AbData). inv H.
      assert(HOS: kernel_mode d2 /\ 0 <= Int.unsigned i < num_chan).
      {
        simpl; inv match_related.
        functional inversion H2; repeat (split; trivial); congruence.
      }
      destruct HOS as [Hkern HOS].
      pose proof H0 as HMem.
      specialize (H0 _ HOS). 
      destruct H0 as (v1 & v2 & v3 & HL1 & HV1 & HL2 & HV2 & HL3 & HV3 & HM).
      assert (HP: v1 = Vint z).
      {
        functional inversion H2; subst. rewrite H7 in HM; inv HM.
        rewrite <- Int.repr_unsigned with z; rewrite <- H.
        rewrite Int.repr_unsigned. trivial.
      }          
      refine_split; eauto; econstructor; eauto.
    Qed.

    Lemma get_sync_chan_paddr_spec_ref:
      compatsim (crel HDATA LDATA) (gensem get_sync_chan_paddr_spec) get_sync_chan_paddr_spec_low.
    Proof.
      compatsim_simpl (@match_AbData). inv H.
      assert(HOS: kernel_mode d2 /\ 0 <= Int.unsigned i < num_chan).
      {
        simpl; inv match_related.
        functional inversion H2; repeat (split; trivial); congruence.
      }
      destruct HOS as [Hkern HOS].
      pose proof H0 as HMem.
      specialize (H0 _ HOS). 
      destruct H0 as (v1 & v2 & v3 & HL1 & HV1 & HL2 & HV2 & HL3 & HV3 & HM).
      assert (HP: v2 = Vint z).
      {
        functional inversion H2; subst. rewrite H7 in HM; inv HM.
        rewrite <- Int.repr_unsigned with z; rewrite <- H.
        rewrite Int.repr_unsigned. trivial.
      }          
      refine_split; eauto; econstructor; eauto.
    Qed.

    Lemma get_sync_chan_count_spec_ref:
      compatsim (crel HDATA LDATA) (gensem get_sync_chan_count_spec) get_sync_chan_count_spec_low.
    Proof.
      compatsim_simpl (@match_AbData). inv H.
      assert(HOS: kernel_mode d2 /\ 0 <= Int.unsigned i < num_chan).
      {
        simpl; inv match_related.
        functional inversion H2; repeat (split; trivial); congruence.
      }
      destruct HOS as [Hkern HOS].
      pose proof H0 as HMem.
      specialize (H0 _ HOS). 
      destruct H0 as (v1 & v2 & v3 & HL1 & HV1 & HL2 & HV2 & HL3 & HV3 & HM).
      assert (HP: v3 = Vint z).
      {
        functional inversion H2; subst. rewrite H7 in HM; inv HM.
        rewrite <- Int.repr_unsigned with z; rewrite <- H.
        rewrite Int.repr_unsigned. trivial.
      }          
      refine_split; eauto; econstructor; eauto.
    Qed.

    Lemma set_sync_chan_to_spec_ref:
      compatsim (crel HDATA LDATA) (gensem set_sync_chan_to_spec) set_sync_chan_to_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      assert (Hkern: kernel_mode d2 /\ 0<= Int.unsigned i < num_chan).
      {
        inv match_related. functional inversion H1; subst.
        repeat (split; trivial); try congruence; eauto.
      }
      destruct Hkern as [Hkern HOS].
      inv H. rename H0 into HMem; 
             destruct (HMem _ HOS) as (v1 & v2 & v3 & HL1 & HV1 & HL2 & HV2 & HL3 & HV3 & HM).
      specialize (Mem.valid_access_store _ _ _ _ (Vint i0) HV1); intros [m' HST].
      refine_split.
      - econstructor; eauto.
        lift_unfold. split; eauto.
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
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL3; eauto.
          simpl; right; right. omega.

          rewrite ZMap.gss. simpl.
          rewrite Int.repr_unsigned.
          constructor. 
          
        + (* ofs <> Int.unsigned i *)
          specialize (HMem _ H).
          destruct HMem as (v1' & v2' & v3' & HL1' & HV1' & HL2' & HV2' & HL3' & HV3' & HM').
          refine_split'; eauto;
          try eapply Mem.store_valid_access_1; eauto.
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
          simpl; right. destruct (zlt ofs (Int.unsigned i)); [left; omega|right; omega].
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL2'; eauto.
          simpl; right. destruct (zlt ofs (Int.unsigned i)); [left; omega|right; omega].
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL3'; eauto.
          simpl; right. destruct (zlt ofs (Int.unsigned i)); [left; omega|right; omega].
          rewrite ZMap.gso; trivial.
      - apply inject_incr_refl.
    Qed.

    Lemma set_sync_chan_paddr_spec_ref:
      compatsim (crel HDATA LDATA) (gensem set_sync_chan_paddr_spec) set_sync_chan_paddr_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      assert (Hkern: kernel_mode d2 /\ 0<= Int.unsigned i < num_chan).
      {
        inv match_related. functional inversion H1; subst.
        repeat (split; trivial); try congruence; eauto.
      }
      destruct Hkern as [Hkern HOS].
      inv H. rename H0 into HMem; 
             destruct (HMem _ HOS) as (v1 & v2 & v3 & HL1 & HV1 & HL2 & HV2 & HL3 & HV3 & HM).
      specialize (Mem.valid_access_store _ _ _ _ (Vint i0) HV2); intros [m' HST].
      refine_split.
      - econstructor; eauto.
        lift_unfold. split; eauto.
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
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL3; eauto.
          simpl; right; right. omega.
          rewrite ZMap.gss. simpl.
          rewrite Int.repr_unsigned.
          constructor. 
          
        + (* ofs <> Int.unsigned i *)
          specialize (HMem _ H).
          destruct HMem as (v1' & v2' & v3' & HL1' & HV1' & HL2' & HV2' & HL3' & HV3' & HM').
          refine_split'; eauto;
          try eapply Mem.store_valid_access_1; eauto.
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
          simpl; right. destruct (zlt ofs (Int.unsigned i)); [left; omega|right; omega].
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL2'; eauto.
          simpl; right. destruct (zlt ofs (Int.unsigned i)); [left; omega|right; omega].
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL3'; eauto.
          simpl; right. destruct (zlt ofs (Int.unsigned i)); [left; omega|right; omega].
          rewrite ZMap.gso; trivial.
      - apply inject_incr_refl.
    Qed.

    Lemma set_sync_chan_count_spec_ref:
      compatsim (crel HDATA LDATA) (gensem set_sync_chan_count_spec) set_sync_chan_count_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      assert (Hkern: kernel_mode d2 /\ 0<= Int.unsigned i < num_chan).
      {
        inv match_related. functional inversion H1; subst.
        repeat (split; trivial); try congruence; eauto.
      }
      destruct Hkern as [Hkern HOS].
      inv H. rename H0 into HMem; 
             destruct (HMem _ HOS) as (v1 & v2 & v3 & HL1 & HV1 & HL2 & HV2 & HL3 & HV3 & HM).
      specialize (Mem.valid_access_store _ _ _ _ (Vint i0) HV3); intros [m' HST].
      refine_split.
      - econstructor; eauto.
        lift_unfold. split; eauto.
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
          simpl; right; left. omega.
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL2; eauto.
          simpl; right; left. omega.
          eapply Mem.load_store_same; eauto.
          rewrite ZMap.gss. simpl.
          rewrite Int.repr_unsigned.
          constructor. 
          
        + (* ofs <> Int.unsigned i *)
          specialize (HMem _ H).
          destruct HMem as (v1' & v2' & v3' & HL1' & HV1' & HL2' & HV2' & HL3' & HV3' & HM').
          refine_split'; eauto;
          try eapply Mem.store_valid_access_1; eauto.
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
          simpl; right. destruct (zlt ofs (Int.unsigned i)); [left; omega|right; omega].
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL2'; eauto.
          simpl; right. destruct (zlt ofs (Int.unsigned i)); [left; omega|right; omega].
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL3'; eauto.
          simpl; right. destruct (zlt ofs (Int.unsigned i)); [left; omega|right; omega].
          rewrite ZMap.gso; trivial.
      - apply inject_incr_refl.
    Qed.

    Lemma init_sync_chan_spec_ref:
      compatsim (crel HDATA LDATA) (gensem init_sync_chan_spec) init_sync_chan_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      assert (Hkern: kernel_mode d2 /\ 0<= Int.unsigned i < num_chan).
      {
        inv match_related. functional inversion H1; subst.
        repeat (split; trivial); try congruence; eauto.
      }
      destruct Hkern as [Hkern HOS].
      inv H. rename H0 into HMem; 
             destruct (HMem _ HOS) as (v1 & v2 & v3 & HL1 & HV1 & HL2 & HV2 & HL3 & HV3 & HM).
      specialize (Mem.valid_access_store _ _ _ _ (Vint (Int.repr num_chan)) HV1); intros [m'1 HST1].
      apply (Mem.store_valid_access_1 _ _ _ _ _ _ HST1) in HV2.
      apply (Mem.store_valid_access_1 _ _ _ _ _ _ HST1) in HV3.
      specialize (Mem.valid_access_store _ _ _ _ Vzero HV2); intros [m'2 HST2].
      apply (Mem.store_valid_access_1 _ _ _ _ _ _ HST2) in HV3.
      specialize (Mem.valid_access_store _ _ _ _ Vzero HV3); intros [m'3 HST3].
      refine_split.
      - econstructor; eauto.
        instantiate (1:= (m'1, d2)).
        lift_unfold; split; eauto.
        instantiate (1:= (m'2, d2)).
        lift_unfold; split; eauto.
        instantiate (1:= d2).
        instantiate (1:= m'3).
        lift_unfold; split; eauto.
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
          erewrite (Mem.load_store_other _ _ _ _ _ _ HST3); eauto; [|right; left; simpl; omega].
          erewrite (Mem.load_store_other _ _ _ _ _ _ HST2); eauto; [|right; left; simpl; omega].
          eapply Mem.load_store_same; eauto.
          erewrite (Mem.load_store_other _ _ _ _ _ _ HST3); eauto; [|right; left; simpl; omega].
          eapply Mem.load_store_same; eauto.
          eapply Mem.load_store_same; eauto.
          rewrite ZMap.gss.
          repeat rewrite Int.repr_unsigned.
          constructor; trivial.

        + (* ofs <> Int.unsigned i *)
          specialize (HMem _ H).
          destruct HMem as (v1' & v2' & v3' & HL1' & HV1' & HL2' & HV2' & HL3' & HV3' & HM').
          repeat (erewrite (Mem.load_store_other _ _ _ _ _ _ HST3); [|load_other_simpl ofs i]).
          repeat (erewrite (Mem.load_store_other _ _ _ _ _ _ HST2); [|load_other_simpl ofs i]).
          repeat (erewrite (Mem.load_store_other _ _ _ _ _ _ HST1); [|load_other_simpl ofs i]).
          refine_split'; eauto;
          repeat (eapply Mem.store_valid_access_1; eauto).
          rewrite ZMap.gso; auto.
      - apply inject_incr_refl.
    Qed.

  End WITHMEM.

End Refinement.