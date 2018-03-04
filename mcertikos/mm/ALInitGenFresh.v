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
(*          Refinement proof for MALInit layer                         *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MBoot layer and MALInit layer*)
Require Import ALInitGenSpec.
Require Import ALInitGenDef.

(** * Definition of the refinement relation*)
Section Refinement.  

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

      Ltac pattern2_refinement_simpl:=  
        pattern2_refinement_simpl' (@relate_AbData).

      Section getnps_ref.
        
        Lemma getnps_spec_ref:
          compatsim (crel HDATA LDATA) (gensem get_nps_spec) get_nps_spec_low.
        Proof.
          compatsim_simpl (@match_AbData).
          destruct H0 as [HL HV].
          refine_split; try (econstructor; eauto).
          - simpl. inv match_related.
            functional inversion H2; subst. split; congruence.
          - functional inversion H2; subst; simpl in *.
            rewrite <- Int.repr_unsigned with z.
            rewrite <- Int.repr_unsigned with n. rewrite <- H0, <- H1.
            constructor.
          - apply inject_incr_refl.
        Qed.

      End getnps_ref.

      Section setnps_ref.

        Lemma setnps_spec_ref:
          compatsim (crel HDATA LDATA) (gensem set_nps_spec) set_nps_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          destruct H0 as [HL HV].
          specialize (Mem.valid_access_store _ _ _ _ (Vint i) HV); intros [m2' Hm2'].
          refine_split.
          - econstructor; eauto.
            simpl; lift_trivial. subrewrite'. reflexivity.
            simpl. inv match_related.
            functional inversion H1; subst. split; congruence.
          - constructor.
          - pose proof H1 as Hspec.
            functional inversion Hspec; subst.
            split; eauto; pattern2_refinement_simpl.
            inv H.
            assert (HNB: b <> b0).
            {
              red; intros; subst.
              specialize (genv_vars_inj  _ _ _ _ H3 H6).
              discriminate. 
            }
            econstructor; eauto.
            * econstructor; eauto.
              intros. specialize (H0 _ H).
              rewrite <- (Mem.load_store_other _ _ _ _ _ _ Hm2') in H0; eauto. 
              rewrite <- (Mem.load_store_other _ _ _ _ _ _ Hm2') in H0; eauto. 
              rewrite <- (Mem.load_store_other _ _ _ _ _ _ Hm2') in H0; eauto. 
              destruct H0 as [v1[v2[v3[HL1[HL2[HL3[HV1[HV2[HV3 HAT]]]]]]]]].      
              exists v1, v2, v3.
              refine_split'; trivial;
              try apply (Mem.store_valid_access_1 _ _ _ _ _ _ Hm2'); trivial.
            * split.
              exploit Mem.load_store_same; eauto.
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ Hm2'); trivial.
            * reflexivity.
          - apply inject_incr_refl.
        Qed.

      End setnps_ref.

      Section getatu_ref.

        Lemma getatu_spec_ref:
          compatsim (crel HDATA LDATA) (gensem get_at_u_spec) at_get_spec_low.
        Proof.
          compatsim_simpl (@match_AbData).
          destruct H0 as [HL HV]. inv H.
          assert(HOS: kernel_mode d2 /\ 0 <= Int.unsigned i < maxpage).
          {
            simpl; inv match_related.
            functional inversion H2; repeat (split; trivial); congruence.
          }
          destruct HOS as [Hkern HOS].
          pose proof H0 as HAT.
          specialize (H0 _ HOS); destruct H0 as [v1[v2[v3[HL1[HL2[HL3[_[_[_ HM]]]]]]]]].
          assert (HP: exists v, Int.unsigned z = IntToBoolZ v /\ v2 = Vint v).
          {
            unfold get_at_u_spec in *; subdestruct;
            inv HM; esplit; split; eauto; inv H2; functional inversion H10; trivial.
          }
          destruct HP as [v[HEQ HEV]]; subst.
          refine_split; eauto; econstructor; eauto.
        Qed.

      End getatu_ref.

      Section getatc_ref.

        Lemma getatc_spec_ref:
          compatsim (crel HDATA LDATA) (gensem get_at_c_spec) at_get_c_spec_low.
        Proof.
          compatsim_simpl (@match_AbData).
          destruct H0 as [HL HV]. inv H.
          assert(HOS: kernel_mode d2 /\ 0<= Int.unsigned i < maxpage).
          {
            simpl; inv match_related.
            functional inversion H2; repeat (split; trivial); congruence.
          }
          destruct HOS as [Hkern HOS].
          pose proof H0 as HAT.
          specialize (H0 _ HOS); destruct H0 as [v1[v2[v3[HL1[HL2[HL3[_[_[_ HM]]]]]]]]].
          assert (HP: v3 = Vint z).
          {
            unfold get_at_c_spec in *; subdestruct.
            inv HM; eauto.
            rewrite <- (Int.repr_unsigned z).
            rewrite <- (Int.repr_unsigned v). inv H2.
            reflexivity.
          }
          subst. refine_split; eauto; econstructor; eauto.
        Qed.

      End getatc_ref.

      Section setatu_ref.

        Lemma setatu_spec_ref:
          compatsim (crel HDATA LDATA) (gensem set_at_u_spec) at_set_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          assert (Hkern: kernel_mode d2 /\ 0<= Int.unsigned i < maxpage
                         /\ (exists atype, ZtoBool (Int.unsigned i0) = Some atype)).
          {
            inv match_related.
            unfold set_at_u_spec in *; subdestruct;
            repeat (split; congruence); eauto.
          }
          destruct Hkern as [Hkern[HOS [attype HZ2AT]]].
          inv H. rename H4 into HMAT; destruct (HMAT _ HOS) as [v1 [v2[v3[HL1 [HL2[HL3[HV1[HV2[HV3 HM]]]]]]]]].
          specialize (Mem.valid_access_store _ _ _ _ (Vint i0) HV2); intros [m2' HST].
          refine_split.
          - econstructor; eauto.
            simpl; lift_trivial. subrewrite'. reflexivity.
          - constructor.
          - pose proof H1 as Hspec.
            functional inversion Hspec; subst.
            split; eauto; pattern2_refinement_simpl.
            econstructor; simpl; eauto.
            * econstructor; eauto; intros.
              destruct (zeq ofs (Int.unsigned i)); subst.
              (* ofs = Int.unsigned i *)
              {
                exists v1, (Vint i0), v3.
                refine_split'; try eapply Mem.store_valid_access_1; eauto.
                rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1; auto.
                right; left; simpl; omega.
                apply Mem.load_store_same in HST; trivial.
                rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL3; auto.
                right; right; simpl; omega.
                rewrite ZMap.gss.
                rewrite <- Int.repr_unsigned with i0.
                rewrite H9 in HM. inv HM; try econstructor; eauto.
              }
              (* ofs <> Int.unsigned i *)
              {
                specialize (HMAT _ H).
                destruct HMAT as [v1'[v2'[v3'[HL1'[HL2'[HL3'[HV1'[HV2'[HV3' HM2]]]]]]]]]. 
                exists v1', v2', v3'.
                rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1', HL2', HL3';
                  try (simpl; right; destruct (zle ofs (Int.unsigned i)); [left; omega|right; omega]).
                refine_split'; trivial;
                try eapply Mem.store_valid_access_1; eauto.
                simpl; rewrite ZMap.gso; trivial.
              }
            * assert (HNB: b <> b0).
              {
                red; intros; subst.
                specialize (genv_vars_inj  _ _ _ _ H3 H5).
                discriminate. 
              }
              destruct H0 as [HL0 HV0].
              split. rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL0; auto.
              eapply Mem.store_valid_access_1; eauto.
          - apply inject_incr_refl.
        Qed.

      End setatu_ref.

      Section setatc_ref.

        Lemma setatc_spec_ref:
          compatsim (crel HDATA LDATA) (gensem set_at_c_spec) at_set_c_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          assert (Hkern: kernel_mode d2 /\ 0<= Int.unsigned i < maxpage).
          {
            inv match_related.
            unfold set_at_c_spec in *; subdestruct;
            repeat (split; congruence); eauto.
          }
          destruct Hkern as [Hkern HOS].
          inv H. rename H4 into HMAT; destruct (HMAT _ HOS) as [v1 [v2[v3[HL1 [HL2[HL3[HV1[HV2[HV3 HM]]]]]]]]].
          specialize (Mem.valid_access_store _ _ _ _ (Vint i0) HV3); intros [m3' HST].
          refine_split.
          - econstructor; eauto.
            simpl. lift_trivial. subrewrite'. reflexivity.
          - constructor.
          - pose proof H1 as Hspec.
            functional inversion Hspec; subst.
            split; eauto; pattern2_refinement_simpl.
            econstructor; simpl; eauto.
            * econstructor; eauto; intros.
              destruct (zeq ofs (Int.unsigned i)); subst.
              (* ofs = Int.unsigned i *)
              {
                exists v1, v2, (Vint i0).
                refine_split'; try eapply Mem.store_valid_access_1; eauto.
                rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1; auto.
                right; left; simpl; omega.
                rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL2; auto.
                right; left; simpl; omega.
                apply Mem.load_store_same in HST; trivial.
                rewrite ZMap.gss.
                rewrite H8 in HM. inv HM; try econstructor; eauto.
              }
              (* ofs <> Int.unsigned i *)
              {
                specialize (HMAT _ H).
                destruct HMAT as [v1'[v2'[v3'[HL1'[HL2'[HL3'[HV1'[HV2'[HV3' HM2]]]]]]]]]. 
                exists v1', v2', v3'.
                rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1', HL2', HL3';
                  try (simpl; right; destruct (zle ofs (Int.unsigned i)); [left; omega|right; omega]).
                refine_split'; trivial;
                try eapply Mem.store_valid_access_1; eauto.
                simpl; rewrite ZMap.gso; trivial.
              }
            * assert (HNB: b <> b0).
              {
                red; intros; subst.
                specialize (genv_vars_inj  _ _ _ _ H3 H5).
                discriminate. 
              }
              destruct H0 as [HL0 HV0].
              split. rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL0; auto.
              eapply Mem.store_valid_access_1; eauto.
          - apply inject_incr_refl.
        Qed.

      End setatc_ref.

      Section getatnorm_ref.

        Lemma getatnorm_spec_ref:
          compatsim (crel HDATA LDATA) (gensem is_at_norm_spec) is_norm_spec_low.
        Proof.
          compatsim_simpl (@match_AbData).
          destruct H0 as [HL HV]. inv H.
          assert(HOS: kernel_mode d2 /\ 0<= Int.unsigned i < maxpage).
          {
            simpl; inv match_related.
            functional inversion H2; repeat (split; trivial); congruence.
          }
          destruct HOS as [Hkern HOS].
          pose proof H0 as HAT.
          specialize (H0 _ HOS); destruct H0 as [v1 [v2[v3[HL1 [HL2[HL3[_[_[_ HM]]]]]]]]].
          assert (HP: exists v, Int.unsigned z = ZToATTypeZ (Int.unsigned v) /\ v1 = Vint v).
          {
            unfold is_at_norm_spec in *; subdestruct;
            inv HM; refine_split'; eauto; inv H2. 
            - functional inversion H9; trivial.
            - destruct t; functional inversion H9; trivial. congruence.
          }
          destruct HP as [v[HEQ HEV]]; subst.
          refine_split; eauto; econstructor; eauto.
        Qed.

      End getatnorm_ref.

      Section setatnorm_ref.

        Lemma setatnorm_spec_ref:
          compatsim (crel HDATA LDATA) (gensem set_at_norm_spec) set_norm_spec_low.
        Proof. 
          compatsim_simpl (@match_AbData).
          assert (Hkern: kernel_mode d2 /\ 0<= Int.unsigned i < maxpage
                         /\ (exists atype, ZtoATType (Int.unsigned i0) = Some atype)).
          {
            simpl; inv match_related.
            unfold set_at_norm_spec in *; subdestruct;
            repeat (split; congruence); eauto.
          }
          destruct Hkern as [Hkern[HOS [attype HZ2AT]]].
          inv H. rename H4 into HMAT; destruct (HMAT _ HOS) as [v1[v2[v3[HL1[HL2[HL3[HV1[HV2[HV3 HM]]]]]]]]].
          specialize (Mem.valid_access_store _ _ _ _ (Vint i0) HV1); intros [m0 HST].
          assert (HP: exists m1, Mem.store Mint32 m0 b0 (Int.unsigned i * 12 + 4) (Vzero) = Some m1).
          {
            apply (Mem.valid_access_store); auto.
            eapply Mem.store_valid_access_1; eauto.
          }
          destruct HP as [m1 HST1].
          assert (HP: exists m2, Mem.store Mint32 m1 b0 (Int.unsigned i * 12 + 8) (Vzero) = Some m2).
          {
            apply (Mem.valid_access_store); auto.
            repeat (eapply Mem.store_valid_access_1; eauto).
          }
          destruct HP as [m22 HST2].
          refine_split.
          - econstructor; eauto; simpl; lift_trivial.
            simpl. subrewrite'.
            simpl. subrewrite'.
            simpl. subrewrite'. unfold set; simpl. reflexivity.
          - constructor.
          - pose proof H1 as Hspec.
            functional inversion Hspec; subst.
            split; eauto; pattern2_refinement_simpl.
            econstructor; simpl; eauto.
            * econstructor; eauto; intros.
              destruct (zeq ofs (Int.unsigned i)); subst.
              (* ofs = Int.unsigned i *)
              {
                exists (Vint i0), (Vint (Int.repr 0)), (Vint Int.zero).
                refine_split';
                  repeat (eapply Mem.store_valid_access_1; eauto).
                apply Mem.load_store_same in HST.
                rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST1) in HST; trivial.
                rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST2) in HST; trivial.
                right; left; simpl; omega.
                right; left; simpl; omega.
                apply Mem.load_store_same in HST1; trivial.
                rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST2) in HST1; trivial.
                right; left; simpl; omega.
                apply Mem.load_store_same in HST2; trivial.
                rewrite ZMap.gss. 
                change 0 with (Int.unsigned (Int.repr 0)).
                econstructor; eauto.
              }
              (* ofs <> Int.unsigned i *)
              {
                specialize (HMAT _ H).
                destruct HMAT as [v1'[v2'[v3'[HL1'[HL2'[HL3'[HV1'[HV2'[HV3' HM2]]]]]]]]]. 
                exists v1', v2', v3'.
                rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1', HL2', HL3';
                  try (simpl; right; destruct (zle ofs (Int.unsigned i)); [left; omega|right; omega]).
                rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST1) in HL1', HL2', HL3';
                  try (simpl; right; destruct (zle ofs (Int.unsigned i)); [left; omega|right; omega]).
                rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST2) in HL1', HL2', HL3';
                  try (simpl; right; destruct (zle ofs (Int.unsigned i)); [left; omega|right; omega]).
                refine_split'; trivial;
                repeat (eapply Mem.store_valid_access_1; eauto).
                simpl; rewrite ZMap.gso; trivial.
              }
            * assert (HNB: b <> b0).
              {
                red; intros; subst.
                specialize (genv_vars_inj  _ _ _ _ H3 H5).
                discriminate. 
              }
              destruct H0 as [HL0 HV0]. split.
              rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL0; auto.
              rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST1) in HL0; auto.
              rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST2) in HL0; auto.
              repeat (eapply Mem.store_valid_access_1; eauto).
          - apply inject_incr_refl.
        Qed.

      End setatnorm_ref.

  End WITHMEM.

End Refinement.