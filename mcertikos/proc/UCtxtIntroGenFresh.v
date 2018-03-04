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
(*           Layers of PM: Refinement Proof for PUctxtIntro            *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between PIPC layer and PUCtxtIntro layer*)

Require Import UCtxtIntroGenDef.
Require Import UCtxtIntroGenSpec.

(** * Definition of the refinement relation*)
Section Refinement.

  Ltac pattern2_refinement_simpl:=  
    pattern2_refinement_simpl' (@relate_AbData).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Lemma elf_load_spec_ref:
      compatsim (crel HDATA LDATA) elf_load_compatsem elf_load_spec_low.
    Proof.
      compatsim_simpl (@match_AbData). intros.
      inv H.
      assert (HFB: ι be = Some (be, 0)).
      {
        destruct H5 as [fun_id Hsymbol].
        eapply stencil_find_symbol_inject'; eauto.
      }
      exists ι, (rs2#RA<- Vundef#Asm.PC <- (rs2#RA)).
      refine_split'; repeat val_inject_inv; eauto;
      try econstructor; eauto.
      - inv_val_inject.
        inv H0. inv H.
        rewrite H8 in HFB. inv HFB.
        rewrite Int.add_zero in EXTCALL_ARG.
        unfold sextcall_sig in *.
        unfold csig_sig in *.
        simpl in EXTCALL_ARG.
        unfold signature_of_type in *.
        simpl in EXTCALL_ARG.
        inv EXTCALL_ARG.
        econstructor. eassumption. inv H11. inv H4.
        econstructor. eassumption.
        constructor.
      - intros. inv ASM_INV.
        inv inv_inject_neutral.
        destruct r; simpl;
        repeat simpl_Pregmap; eauto.
    Qed.

    Lemma uctx_get_spec_ref:
      compatsim (crel HDATA LDATA) (gensem uctx_get_spec)
                uctx_get_spec_low.
    Proof.
      compatsim_simpl (@match_AbData). inv H.
      assert(HOS: kernel_mode d2 /\ 0 <= Int.unsigned i < num_proc
                  /\ 0<= Int.unsigned i0 < UCTXT_SIZE
                  /\ is_UCTXT_ptr (Int.unsigned i0) = false).
      {
        simpl; inv match_related.
        functional inversion H2.
        pose proof H8 as Hfalse.
        apply is_UCTXT_ptr_range in H8.
        refine_split'; trivial; try congruence.
      }
      destruct HOS as [Hkern [HOS [HOS' Hfalse]]].
      pose proof H0 as HMem.
      specialize (H0 _ _ HOS HOS'). destruct H0 as [v1[HL1[_[_ HM]]]].
      assert (HP: v1 = Vint z).
      {
        functional inversion H2; subst. 
        unfold UContext in H8.
        rewrite H8 in HM. inv HM.
        rewrite <- Int.repr_unsigned with z; rewrite <- H.
        rewrite Int.repr_unsigned. trivial.
      }          
      refine_split'; repeat val_inject_inv; eauto;
      try econstructor; eauto.
    Qed.

    Lemma uctx_set_spec_ref:
      compatsim (crel HDATA LDATA) (gensem uctx_set_spec)
                uctx_set_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      assert(HOS: kernel_mode d2 /\ 0 <= Int.unsigned i < num_proc
                  /\ 0<= Int.unsigned i0 < UCTXT_SIZE
                  /\ is_UCTXT_ptr (Int.unsigned i0) = false).
      {
        simpl; inv match_related.
        functional inversion H1.
        pose proof H7 as Hfalse.
        apply is_UCTXT_ptr_range in H7. 
        refine_split'; trivial; try congruence.
      }
      destruct HOS as [Hkern [HOS [HOS' Hfalse]]].
      inv H. rename H0 into HMem. 
      destruct (HMem _ _ HOS HOS') as [v1[HL1[HV1[_ HM]]]].
      specialize (Mem.valid_access_store _ _ _ _ (Vint i1) HV1); intros [m' HST].
      refine_split.
      - econstructor; eauto.
        lift_unfold. split; eauto.
      - constructor.
      - pose proof H1 as Hspec.
        functional inversion Hspec; subst.
        split; eauto; pattern2_refinement_simpl. 
        subst uctx.
        (*rewrite H8 in HM. inv HM.*)
        econstructor; simpl; eauto.
        econstructor; eauto; intros.
        destruct (zeq i2 (Int.unsigned i)); subst.          
        + (* i2 = Int.unsigned i *)
          destruct (zeq n (Int.unsigned i0)); subst.
          * (* n = Int.unsigned i0 *)
            refine_split'; eauto;
            try eapply Mem.store_valid_access_1; eauto.
            eapply Mem.load_store_same; eauto.
            subst uctx'.
            repeat rewrite ZMap.gss. 
            rewrite Int.repr_unsigned.
            constructor. 
          * (* n <> Int.unsigned i0 *)
            specialize (HMem _ _ H H8).
            destruct HMem as [v1'[HL1'[HV1'[_ HM']]]].
            refine_split'; eauto;
            try eapply Mem.store_valid_access_1; eauto.
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
            simpl; right. destruct (zlt n (Int.unsigned i0)); [left; omega|right; omega].
            rewrite ZMap.gss. subst uctx'.
            rewrite ZMap.gso; trivial.
        + (* i2 <> Int.unsigned i *)
          specialize (HMem _ _ H H8).
          destruct HMem as [v1'[HL1'[HV1'[_ HM']]]].
          refine_split'; eauto;
          try eapply Mem.store_valid_access_1; eauto.
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
          simpl; right. destruct (zlt i2 (Int.unsigned i)); [left; omega|right; omega].
          rewrite ZMap.gso; trivial.
      - apply inject_incr_refl.
    Qed.

    Lemma uctx_set_eip_spec_ref:
      compatsim (crel HDATA LDATA) (uctx_set_eip_compatsem uctx_set_eip_spec)
                uctx_set_eip_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData).
      assert(HOS: kernel_mode d2 /\ 0 <= Int.unsigned i < num_proc).
      {
        simpl; inv match_related.
        functional inversion H5.
        refine_split'; trivial; try congruence.
      }
      destruct HOS as [Hkern HOS].
      inv H. rename H0 into HMem. 
      assert (HOS': 0<= U_EIP < UCTXT_SIZE) by omega.
      destruct (HMem _ _ HOS HOS') as [v1[HL1[HV1[_ HM]]]].
      specialize (Mem.valid_access_store _ _ _ _ (Vptr b ofs) HV1); intros [m' HST].
      assert(HFB: ι b = Some (b, 0)).
      {
        destruct H7 as [fun_id Hsymbol].
        eapply stencil_find_symbol_inject'; eauto.
      }          
      refine_split.
      - econstructor; eauto.
        lift_unfold. split; eauto.
      - constructor.
      - pose proof H5 as Hspec.
        functional inversion Hspec; subst.
        split; eauto; pattern2_refinement_simpl. 
        subst uctx.
        econstructor; simpl; eauto.
        econstructor; eauto; intros.
        destruct (zeq i0 (Int.unsigned i)); subst.          
        + (* i0 = Int.unsigned i *)
          destruct (zeq n U_EIP); subst.
          * (* n = U_EIP  *)
            refine_split'; eauto;
            try eapply Mem.store_valid_access_1; eauto.
            eapply Mem.load_store_same; eauto.
            subst uctx'.
            repeat rewrite ZMap.gss. 
            econstructor; eauto. 
            rewrite Int.add_zero; trivial.
          * (* n <> U_EIP *)
            specialize (HMem _ _ H H8).
            destruct HMem as [v1'[HL1'[HV1'[_ HM']]]].
            refine_split'; eauto;
            try eapply Mem.store_valid_access_1; eauto.
            rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
            simpl; right. destruct (zlt n U_EIP); [left; omega|right; omega].
            rewrite ZMap.gss. subst uctx'.
            rewrite ZMap.gso; trivial.
        + (* i0 <> Int.unsigned i *)
          specialize (HMem _ _ H H8).
          destruct HMem as [v1'[HL1'[HV1'[_ HM']]]].
          refine_split'; eauto;
          try eapply Mem.store_valid_access_1; eauto.
          rewrite <- (Mem.load_store_other  _ _ _ _ _ _ HST) in HL1'; eauto.
          simpl; right. destruct (zlt i0 (Int.unsigned i)); [left; omega|right; omega].
          rewrite ZMap.gso; trivial.
      - apply inject_incr_refl.
    Qed.

    Lemma restore_uctx_spec_ref:
      compatsim (crel HDATA LDATA) 
                (primcall_restoreuctx_compatsem restore_uctx_spec cid)
                restore_uctx_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData). intros.
      inv match_extcall_states.
      assert(HP: exists d', trapout_spec d2 = Some d' 
                            /\ relate_RData ι d1' d'
                            /\ uctxt d1' = uctxt d1
                            /\ cid d1 = cid d2
                            /\ 0<= cid d2 < num_proc
                            /\ kernel_mode d2
                            /\ rs' = ZMap.get (cid d1) (uctxt d1)).
      {
        simpl; inv match_related.
        unfold trapout_spec. 
        inv Hlow.
        pose proof (valid_curid _ Hhigh) as Hcid.
        subrewrite'.
        functional inversion H7; subst; simpl.
        rewrite <- ikern_re, <- init_re, <- pg_re, <- ihost_re, <- ipt_re.
        subrewrite'.
        refine_split'; trivial; try congruence.
        econstructor; eauto. 
      }
      destruct HP as [d'[Htrapout[HR[HUctx[HCid [HOS [Hkern Hrs']]]]]]].
      inv match_match. inv H.
      set (vcid := cid d1) in *.
      assert (HV0: forall n0, 0<= n0 < UCTXT_SIZE -> 
                              Mem.valid_access m2 Mint32 b0 (vcid * UCTXT_SIZE * 4 + n0 * 4) Readable).
      {
        intros. specialize (H0 _ _ HOS H).
        destruct H0 as [_[_ [HV _]]]. subst vcid.
        rewrite HCid. eapply Mem.valid_access_implies; eauto.
        constructor.
      }
      assert (HP: exists v0, Mem.load Mint32 m2 b0 (vcid * UCTXT_SIZE * 4 + U_EDI * 4) = Some v0).
      {
        eapply Mem.valid_access_load; eauto.
        eapply HV0. omega.
      }
      destruct HP as [v0 HLD0].
      assert (HP: exists v1, Mem.load Mint32 m2 b0 (vcid * UCTXT_SIZE * 4 + U_ESI * 4) = Some v1).
      {
        eapply Mem.valid_access_load; eauto.
        eapply HV0. omega.
      }
      destruct HP as [v1 HLD1].
      assert (HP: exists v2, Mem.load Mint32 m2 b0 (vcid * UCTXT_SIZE * 4 + U_EBP * 4) = Some v2).
      {
        eapply Mem.valid_access_load; eauto.
        eapply HV0. omega.
      }
      destruct HP as [v3 HLD3].
      assert (HP: exists v4, Mem.load Mint32 m2 b0 (vcid * UCTXT_SIZE * 4 + U_EBX * 4) = Some v4).
      {
        eapply Mem.valid_access_load; eauto.
        eapply HV0. omega.
      }
      destruct HP as [v4 HLD4].
      assert (HP: exists v5, Mem.load Mint32 m2 b0 (vcid * UCTXT_SIZE * 4 + U_EDX * 4) = Some v5).
      {
        eapply Mem.valid_access_load; eauto.
        eapply HV0. omega.
      }
      destruct HP as [v5 HLD5].
      assert (HP: exists v6, Mem.load Mint32 m2 b0 (vcid * UCTXT_SIZE * 4 + U_ECX * 4) = Some v6).
      {
        eapply Mem.valid_access_load; eauto.
        eapply HV0. omega.
      }
      destruct HP as [v6 HLD6].
      assert (HP: exists v7, Mem.load Mint32 m2 b0 (vcid * UCTXT_SIZE * 4 + U_EAX * 4) = Some v7).
      {
        eapply Mem.valid_access_load; eauto.
        eapply HV0. omega.
      }
      destruct HP as [v7 HLD7].
      assert (HP: exists v8, Mem.load Mint32 m2 b0 (vcid * UCTXT_SIZE * 4 + U_ESP * 4) = Some v8).
      {
        eapply Mem.valid_access_load; eauto.
        eapply HV0. omega.
      }
      destruct HP as [v8 HLD8].
      assert (HP: exists v9, Mem.load Mint32 m2 b0 (vcid * UCTXT_SIZE * 4 + U_EIP * 4) = Some v9).
      {
        eapply Mem.valid_access_load; eauto.
        eapply HV0. omega.
      }
      destruct HP as [v9 HLD9].
      refine_split; eauto 2.
      - subst vcid. rewrite HCid in *.
        replace (cid d2 * 17 * 4 + 0 * 4) with (cid d2 * 17 * 4) by omega.
        rewrite H11 in *.
        econstructor; eauto 2.
        eapply reg_symbol_inject; eassumption. 
        exploit (extcall_args_inject (D1:= HDATAOps) (D2:= LDATAOps)); eauto.
        instantiate (3:= d1').
        apply extcall_args_with_data; eauto.
        instantiate (1:= d2).
        intros [?[? Hinv]]. inv_val_inject.
        apply extcall_args_without_data in H; eauto.
      - econstructor; eauto.
        + econstructor; eauto.
          econstructor; eauto.
          rewrite HUctx.
          econstructor; eauto.
        + assert (Hinj: forall n v, 0<= n < UCTXT_SIZE ->
                                    Mem.load Mint32 m2 b0 (vcid * 17 * 4 + n * 4) = Some v ->
                                    val_inject ι (ZMap.get n (ZMap.get vcid (uctxt d1))) v).
          {
            intros. rewrite <- HCid in HOS.
            specialize (H0 _ _ HOS H).
            specialize (N_TYPE _ H).
            destruct H0 as [v'[HL[_[_ Hinj]]]].
            rewrite HL in H2. inv H2.
            Transparent Val.load_result.
            caseEq (ZMap.get n0 (ZMap.get (cid d1) (uctxt d1))); intros;
            unfold UContext in *; rewrite H0 in *; simpl in Hinj; try assumption;
            inv N_TYPE.
          }
          val_inject_simpl; eapply Hinj; eauto 2; omega.
    Qed.

  End WITHMEM.

End Refinement.
