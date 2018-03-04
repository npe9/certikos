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

    Lemma save_uctx_spec_ref:
      compatsim (crel HDATA LDATA) (save_uctx_compatsem save_uctx_spec)
                save_uctx_spec_low.
    Proof. 
      compatsim_simpl (@match_AbData). 
      assert(HOS: kernel_mode d2 /\ 0 <= cid d2 < num_proc
                  /\ cid d1' = cid d2
                  /\ uctxt d1' = ZMap.set (cid d1') uctx4 (uctxt d1)
                  /\ pg d2 = true).
      {
        simpl; inv match_related.
        functional inversion H6; subst; simpl. inv Hhigh.
        refine_split'; trivial; try congruence.
      }
      destruct HOS as [Hkern [HOS[Hcid [Heq Hpe]]]].
      inv H. rename H0 into HMem. 
      set (vcid := cid d2) in *. 
      assert (HV0: forall n0, 0<= n0 < UCTXT_SIZE -> 
                              Mem.valid_access m2 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros n0 HR. specialize (HMem _ _ HOS HR).
        destruct HMem as [_[_[HV _]]].
        replace (17 * 4 * vcid + 4 * n0) with (vcid * 17 * 4 + n0 * 4) by omega. trivial.
      }
      assert (HP: exists m0, Mem.store Mint32 m2 b (UCTXT_SIZE * 4 * vcid + 4 * U_EDI) (Vint v0) = Some m0).
      {
        apply (Mem.valid_access_store); auto.
        apply HV0. omega.
      }
      destruct HP as [m0 HST0].
      assert (HV1: forall n0, 0<= n0 < UCTXT_SIZE -> Mem.valid_access m0 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros. eapply Mem.store_valid_access_1; eauto.
      }
      clear HV0.        
      assert (HP: exists m1, Mem.store Mint32 m0 b (UCTXT_SIZE * 4 * vcid + 4 * U_ESI) (Vint v1) = Some m1).
      {
        apply (Mem.valid_access_store); auto.
        apply HV1. omega.
      }
      destruct HP as [m1 HST1].
      assert (HV2: forall n0, 0<= n0 < UCTXT_SIZE -> Mem.valid_access m1 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros; eapply Mem.store_valid_access_1; eauto.
      }
      clear HV1.
      assert (HP: exists m2, Mem.store Mint32 m1 b (UCTXT_SIZE * 4 * vcid + 4 * U_EBP) (Vint v2) = Some m2).
      {
        apply (Mem.valid_access_store); auto.
        apply HV2. omega.
      }
      destruct HP as [m2' HST2].
      assert (HV3: forall n0, 0<= n0 < UCTXT_SIZE -> Mem.valid_access m2' Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros; eapply Mem.store_valid_access_1; eauto.
      }
      clear HV2.
      assert (HP: exists m3, Mem.store Mint32 m2' b (UCTXT_SIZE * 4 * vcid + 4 * U_OESP) (Vint v3) = Some m3).
      {
        apply (Mem.valid_access_store); auto.
        apply HV3. omega.
      }
      destruct HP as [m3 HST3].
      assert (HV4: forall n0, 0<= n0 < UCTXT_SIZE ->  Mem.valid_access m3 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros; eapply Mem.store_valid_access_1; eauto.
      }
      clear HV3.
      assert (HP: exists m4, Mem.store Mint32 m3 b (UCTXT_SIZE * 4 * vcid + 4 * U_EBX) (Vint v4) = Some m4).
      {
        apply (Mem.valid_access_store); auto.
        apply HV4. omega.
      }
      destruct HP as [m4 HST4].
      assert (HV5: forall n0, 0<= n0 < UCTXT_SIZE -> Mem.valid_access m4 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros; eapply Mem.store_valid_access_1; eauto.
      }
      clear HV4.
      assert (HP: exists m5, Mem.store Mint32 m4 b (UCTXT_SIZE * 4 * vcid + 4 * U_EDX) (Vint v5) = Some m5).
      {
        apply (Mem.valid_access_store); auto.
        apply HV5. omega.
      }
      destruct HP as [m5 HST5].
      assert (HV6: forall n0, 0<= n0 < UCTXT_SIZE -> Mem.valid_access m5 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros; eapply Mem.store_valid_access_1; eauto.
      }
      clear HV5.
      assert (HP: exists m6, Mem.store Mint32 m5 b (UCTXT_SIZE * 4 * vcid + 4 * U_ECX) (Vint v6) = Some m6).
      {
        apply (Mem.valid_access_store); auto.
        apply HV6. omega.
      }
      destruct HP as [m6 HST6].
      assert (HV7: forall n0, 0<= n0 < UCTXT_SIZE ->  Mem.valid_access m6 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros; eapply Mem.store_valid_access_1; eauto.
      }
      clear HV6.
      assert (HP: exists m7, Mem.store Mint32 m6 b (UCTXT_SIZE * 4 * vcid + 4 * U_EAX) (Vint v7) = Some m7).
      {
        apply (Mem.valid_access_store); auto.
        apply HV7. omega.
      }
      destruct HP as [m7 HST7].
      assert (HV8: forall n0, 0<= n0 < UCTXT_SIZE ->  Mem.valid_access m7 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros; eapply Mem.store_valid_access_1; eauto.
      }
      clear HV7.
      assert (HP: exists m8, Mem.store Mint32 m7 b (UCTXT_SIZE * 4 * vcid + 4 * U_ES) (Vint v8) = Some m8).
      {
        apply (Mem.valid_access_store); auto.
        apply HV8. omega.
      }
      destruct HP as [m8 HST8].
      assert (HV9: forall n0, 0<= n0 < UCTXT_SIZE -> Mem.valid_access m8 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros; eapply Mem.store_valid_access_1; eauto.
      }
      clear HV8.
      assert (HP: exists m9, Mem.store Mint32 m8 b (UCTXT_SIZE * 4 * vcid + 4 * U_DS) (Vint v9) = Some m9).
      {
        apply (Mem.valid_access_store); auto.
        apply HV9. omega.
      }
      destruct HP as [m9 HST9].
      assert (HV10: forall n0, 0<= n0 < UCTXT_SIZE -> Mem.valid_access m9 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros; eapply Mem.store_valid_access_1; eauto.
      }
      clear HV9.
      assert (HP: exists m10, Mem.store Mint32 m9 b (UCTXT_SIZE * 4 * vcid + 4 * U_TRAPNO) (Vint v10) = Some m10).
      {
        apply (Mem.valid_access_store); auto.
        apply HV10. omega.
      }
      destruct HP as [m10 HST10].
      assert (HV11: forall n0, 0<= n0 < UCTXT_SIZE -> Mem.valid_access m10 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros; eapply Mem.store_valid_access_1; eauto.
      }
      clear HV10.
      assert (HP: exists m11, Mem.store Mint32 m10 b (UCTXT_SIZE * 4 * vcid + 4 * U_ERR) (Vint v11) = Some m11).
      {
        apply (Mem.valid_access_store); auto.
        apply HV11. omega.
      }
      destruct HP as [m11 HST11].
      assert (HV12: forall n0, 0<= n0 < UCTXT_SIZE -> Mem.valid_access m11 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros; eapply Mem.store_valid_access_1; eauto.
      }
      clear HV11.
      assert (HP: exists m12, Mem.store Mint32 m11 b (UCTXT_SIZE * 4 * vcid + 4 * U_EIP) (Vint v12) = Some m12).
      {
        apply (Mem.valid_access_store); auto.
        apply HV12. omega.
      }
      destruct HP as [m12 HST12].
      assert (HV13: forall n0, 0<= n0 < UCTXT_SIZE -> Mem.valid_access m12 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros; eapply Mem.store_valid_access_1; eauto.
      }
      clear HV12.
      assert (HP: exists m13, Mem.store Mint32 m12 b (UCTXT_SIZE * 4 * vcid + 4 * U_CS) (Vint v13) = Some m13).
      {
        apply (Mem.valid_access_store); auto.
        apply HV13. omega.
      }
      destruct HP as [m13 HST13].
      assert (HV14: forall n0, 0<= n0 < UCTXT_SIZE -> Mem.valid_access m13 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros; eapply Mem.store_valid_access_1; eauto.
      }
      clear HV13.
      assert (HP: exists m14, Mem.store Mint32 m13 b (UCTXT_SIZE * 4 * vcid + 4 * U_EFLAGS) (Vint v14) = Some m14).
      {
        apply (Mem.valid_access_store); auto.
        apply HV14. omega.
      }
      destruct HP as [m14 HST14].
      assert (HV15: forall n0, 0<= n0 < UCTXT_SIZE -> Mem.valid_access m14 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros; eapply Mem.store_valid_access_1; eauto.
      }
      clear HV14.
      assert (HP: exists m15, Mem.store Mint32 m14 b (UCTXT_SIZE * 4 * vcid + 4 * U_ESP) (Vint v15) = Some m15).
      {          
        apply (Mem.valid_access_store); auto.
        apply HV15. omega.
      }
      destruct HP as [m15 HST15].
      assert (HV16: forall n0, 0<= n0 < UCTXT_SIZE -> Mem.valid_access m15 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros; eapply Mem.store_valid_access_1; eauto.
      }
      clear HV15.
      assert (HP: exists m16, Mem.store Mint32 m15 b (UCTXT_SIZE * 4 * vcid + 4 * U_SS) (Vint v16) = Some m16).
      {
        apply (Mem.valid_access_store); auto.
        apply HV16. omega.
      }
      destruct HP as [m16 HST16].
      assert (HV: forall n0, 0<= n0 < UCTXT_SIZE -> Mem.valid_access m16 Mint32 b (UCTXT_SIZE * 4 * vcid + 4 * n0) Writable).
      {
        intros; eapply Mem.store_valid_access_1; eauto.
      }
      clear HV16.
      
      assert(HMCTXT: match_UCtxt s (uctxt d1') m16 ι).  
      {
        econstructor; eauto.
        intros n r HZ HO.
        replace (n * 17 * 4 + r * 4) with (17 * 4 * n + 4 * r) by omega.
        unfold UContext in Heq. rewrite Heq.
        rewrite Hcid.             
        destruct (zeq n vcid); subst.
        - rewrite ZMap.gss.
          destruct (zeq r U_SS); subst.
          refine_split'; trivial.
          erewrite Mem.load_store_same; eauto.      
          Ltac simpl_valid_access m :=
            repeat match goal with
                     | [ |- Mem.valid_access m _ _ _ _] 
                       => eapply Mem.store_valid_access_3; eauto
                     | _ => eapply Mem.store_valid_access_1; eauto
                   end.
          simpl_valid_access m15.
          subst uctx3 uctx2 uctx1.
          Ltac simpl_zmap_get :=
            repeat match goal with
                     | [ |- context[ZMap.get ?a (ZMap.set ?a _ _ )]] 
                       => rewrite ZMap.gss
                     | [ H0: ?a <> ?b |- context[ZMap.get ?a (ZMap.set ?b _ _ )]]
                       => rewrite (ZMap.gso _ _ H0); auto
                     | _ => constructor
                   end.
          simpl_zmap_get.          
          assert (HW0: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r) 
                       = Mem.load Mint32 m15 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite (Mem.load_store_other  _ _ _ _ _ _ HST16); trivial.
            right. destruct (zlt r U_SS).
            left. unfold size_chunk. omega.
            right. unfold size_chunk. omega.
          }
          destruct (zeq r U_ESP); subst.
          refine_split'; trivial.
          rewrite HW0.
          erewrite Mem.load_store_same; eauto.
          simpl_valid_access m14.
          subst uctx3 uctx2 uctx1.
          simpl_zmap_get.

          assert (HW1: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)
                       = Mem.load Mint32 m14 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite HW0.
            rewrite (Mem.load_store_other  _ _ _ _ _ _ HST15); trivial.
            right. destruct (zlt r U_ESP).
            left. unfold size_chunk. omega.
            right. unfold size_chunk. omega.
          }
          destruct (zeq r U_EFLAGS); subst.
          refine_split'; trivial.
          rewrite HW1.
          erewrite Mem.load_store_same; eauto.
          simpl_valid_access m13.

          subst uctx3 uctx2 uctx1.
          simpl_zmap_get.

          assert (HW2: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r) 
                       = Mem.load Mint32 m13 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite HW1.
            rewrite (Mem.load_store_other  _ _ _ _ _ _ HST14); trivial.
            right. destruct (zlt r U_EFLAGS).
            left. unfold size_chunk. omega.
            right. unfold size_chunk. omega.
          }
          clear HW0 HW1.
          destruct (zeq r U_CS); subst.
          refine_split'; trivial.
          rewrite HW2.
          erewrite Mem.load_store_same; eauto.
          simpl_valid_access m12.

          subst uctx3 uctx2 uctx1.
          simpl_zmap_get.

          assert (HW3: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r) 
                       = Mem.load Mint32 m12 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite HW2. rewrite (Mem.load_store_other  _ _ _ _ _ _ HST13).
            trivial. right. destruct (zlt r U_CS).
            left. unfold size_chunk. omega.
            right. unfold size_chunk. omega.
          }
          clear HW2.
          destruct (zeq r U_EIP); subst.
          refine_split'; trivial.
          rewrite HW3.
          erewrite Mem.load_store_same; eauto.
          simpl_valid_access m11.

          subst uctx3 uctx2 uctx1.
          simpl_zmap_get.

          assert (HW4: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r) 
                       = Mem.load Mint32 m11 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite HW3. rewrite (Mem.load_store_other  _ _ _ _ _ _ HST12).
            trivial. right. destruct (zlt r U_EIP).
            left. unfold size_chunk. omega.
            right. unfold size_chunk. omega.
          }
          clear HW3.
          destruct (zeq r U_ERR); subst.
          refine_split'; trivial.
          rewrite HW4.
          erewrite Mem.load_store_same; eauto.
          simpl_valid_access m10.

          subst uctx3 uctx2 uctx1.
          simpl_zmap_get.

          assert (HW5: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r) 
                       = Mem.load Mint32 m10 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite HW4. rewrite (Mem.load_store_other  _ _ _ _ _ _ HST11).
            trivial. right. destruct (zlt r U_ERR).
            left. unfold size_chunk. omega.
            right. unfold size_chunk. omega.
          }
          clear HW4.
          destruct (zeq r U_TRAPNO); subst.
          refine_split'; trivial.
          rewrite HW5.
          erewrite Mem.load_store_same; eauto.
          simpl_valid_access m9.

          subst uctx3 uctx2 uctx1.
          simpl_zmap_get.

          assert (HW6: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r) 
                       = Mem.load Mint32 m9 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite HW5. rewrite (Mem.load_store_other  _ _ _ _ _ _ HST10).
            trivial. right. destruct (zlt r U_TRAPNO).
            left. unfold size_chunk. omega.
            right. unfold size_chunk. omega.
          }
          clear HW5.
          destruct (zeq r U_DS); subst.
          refine_split'; trivial.
          rewrite HW6.
          erewrite Mem.load_store_same; eauto.
          simpl_valid_access m8.

          subst uctx3 uctx2 uctx1.
          simpl_zmap_get.

          assert (HW7: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r) 
                       = Mem.load Mint32 m8 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite HW6. rewrite (Mem.load_store_other  _ _ _ _ _ _ HST9).
            trivial. right. destruct (zlt r U_DS).
            left. unfold size_chunk. omega.
            right. unfold size_chunk. omega.
          }
          clear HW6.
          destruct (zeq r U_ES); subst.
          refine_split'; trivial.
          rewrite HW7.
          erewrite Mem.load_store_same; eauto.
          simpl_valid_access m7.

          subst uctx3 uctx2 uctx1.
          simpl_zmap_get.

          assert (HW8: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r) 
                       = Mem.load Mint32 m7 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite HW7. rewrite (Mem.load_store_other  _ _ _ _ _ _ HST8).
            trivial. right. 
            destruct (zlt r U_ES).
            left. unfold size_chunk. omega.
            right. unfold size_chunk. omega.
          }
          clear HW7.
          destruct (zeq r U_EAX); subst.
          refine_split'; trivial.
          rewrite HW8.
          erewrite Mem.load_store_same; eauto.
          simpl_valid_access m6.

          subst uctx3 uctx2 uctx1.
          simpl_zmap_get.

          assert (HW9: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r) 
                       = Mem.load Mint32 m6 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite HW8.
            rewrite (Mem.load_store_other  _ _ _ _ _ _ HST7).
            trivial. right. 
            destruct (zlt r U_EAX).
            left. unfold size_chunk. omega.
            right. unfold size_chunk. omega.
          }
          clear HW8.
          destruct (zeq r U_ECX); subst.
          refine_split'; trivial.
          rewrite HW9.
          erewrite Mem.load_store_same; eauto.
          simpl_valid_access m5.

          subst uctx3 uctx2 uctx1.
          simpl_zmap_get.

          assert (HW10: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r) 
                        = Mem.load Mint32 m5 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite HW9. rewrite (Mem.load_store_other  _ _ _ _ _ _ HST6).
            trivial. right. destruct (zlt r U_ECX).
            left. unfold size_chunk. omega.
            right. unfold size_chunk. omega.
          }
          clear HW9.
          destruct (zeq r U_EDX); subst.
          refine_split'; trivial.
          rewrite HW10.
          erewrite Mem.load_store_same; eauto.
          simpl_valid_access m4.

          subst uctx3 uctx2 uctx1.
          simpl_zmap_get.

          assert (HW11: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r) 
                        = Mem.load Mint32 m4 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite HW10. rewrite (Mem.load_store_other  _ _ _ _ _ _ HST5).
            trivial. right. destruct (zlt r U_EDX).
            left. unfold size_chunk. omega.
            right. unfold size_chunk. omega.
          }
          clear HW10.
          destruct (zeq r U_EBX); subst.
          refine_split'; trivial.
          rewrite HW11.
          erewrite Mem.load_store_same; eauto.
          simpl_valid_access m3.

          subst uctx3 uctx2 uctx1.
          simpl_zmap_get.

          assert (HW12: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r) 
                        = Mem.load Mint32 m3 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite HW11. rewrite (Mem.load_store_other  _ _ _ _ _ _ HST4).
            trivial. right. 
            destruct (zlt r U_EBX); subst.
            left. unfold size_chunk. omega.
            right. unfold size_chunk. omega.
          }
          clear HW11.
          destruct (zeq r U_OESP); subst.
          refine_split'; trivial.
          rewrite HW12.
          erewrite Mem.load_store_same; eauto.
          simpl_valid_access m2'.

          subst uctx3 uctx2 uctx1.
          simpl_zmap_get.

          assert (HW13: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r) 
                        = Mem.load Mint32 m2' b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite HW12. rewrite (Mem.load_store_other  _ _ _ _ _ _ HST3).
            trivial. right. destruct (zlt r U_OESP).
            left. unfold size_chunk. omega.
            right. unfold size_chunk. omega.
          }
          clear HW12.
          destruct (zeq r U_EBP); subst.
          refine_split'; trivial.
          rewrite HW13.
          erewrite Mem.load_store_same; eauto.
          simpl_valid_access m1.

          subst uctx3 uctx2 uctx1.
          simpl_zmap_get.

          assert (HW14: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r) 
                        = Mem.load Mint32 m1 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite HW13. rewrite (Mem.load_store_other  _ _ _ _ _ _ HST2).
            trivial. right. destruct (zlt r U_EBP).
            left. unfold size_chunk. omega.
            right. unfold size_chunk. omega.
          }
          clear HW13.
          destruct (zeq r U_ESI); subst.
          refine_split'; trivial.
          rewrite HW14.
          erewrite Mem.load_store_same; eauto.
          simpl_valid_access m0.

          subst uctx3 uctx2 uctx1.
          simpl_zmap_get.

          assert (HW15: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r) 
                        = Mem.load Mint32 m0 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite HW14. rewrite (Mem.load_store_other  _ _ _ _ _ _ HST1).
            trivial. right. destruct (zlt r U_ESI).
            left. unfold size_chunk. omega.
            right. unfold size_chunk. omega.
          }
          clear HW14.
          destruct (zeq r U_EDI); subst.
          refine_split'; trivial.
          rewrite HW15.
          erewrite Mem.load_store_same; eauto.
          simpl_valid_access m2.

          subst uctx3 uctx2 uctx1.
          simpl_zmap_get.

          assert (HW: Mem.load Mint32 m16 b (UCTXT_SIZE * 4 * cid d2 + 4 * r) 
                      = Mem.load Mint32 m2 b (UCTXT_SIZE * 4 * cid d2 + 4 * r)).
          {
            rewrite HW15. rewrite (Mem.load_store_other  _ _ _ _ _ _ HST0).
            trivial. right. 
            right. unfold size_chunk. omega.
          } 
          clear HW15. omega.
          
        - Opaque Z.add Z.mul Val.load_result.
          rewrite ZMap.gso; auto.
          simpl in *.
          specialize (HMem _ _ HZ HO).
          destruct HMem as [v[HL[HVa HM]]].
          eexists v. split.
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST16); 
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST15); 
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST14); 
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST13); 
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST12); 
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST11); 
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST10); 
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST9); 
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST8); 
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST7); 
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST6); 
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST5);
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST4); 
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST3); 
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST2);
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST1); 
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          rewrite (Mem.load_store_other  _ _ _ _ _ _ HST0); 
            [ |destruct (zle n (cid d2)); right;[left; simpl; omega|right; simpl; omega]].
          replace (17 * 4 * n + 4 * r) with (n * 17 * 4 + r * 4) by omega. 
          apply HL.

          split; trivial.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          eapply Mem.store_valid_access_1; eauto.
          replace (17 * 4 * n + 4 * r) with (n * 17 * 4 + r * 4) by omega. 
          apply HVa.
      }

      refine_split; eauto 2.
      - econstructor; eauto.
        instantiate (1:= (m0, d2)).         
        lift_simpl. split; eauto.
        instantiate (1:= (m1, d2)).
        lift_simpl. split; eauto.
        instantiate (1:= (m2', d2)).
        lift_simpl. split; eauto.
        instantiate (1:= (m3, d2)).
        lift_simpl. split; eauto.
        instantiate (1:= (m4, d2)).
        lift_simpl. split; eauto.
        instantiate (1:= (m5, d2)).
        lift_simpl. split; eauto.
        instantiate (1:= (m6, d2)).
        lift_simpl. split; eauto.
        instantiate (1:= (m7, d2)).
        lift_simpl. split; eauto.
        instantiate (1:= (m8, d2)).
        lift_simpl. split; eauto.
        instantiate (1:= (m9, d2)).
        lift_simpl. split; eauto.
        instantiate (1:= (m10, d2)).
        lift_simpl. split; eauto.
        instantiate (1:= (m11, d2)).
        lift_simpl. split; eauto.
        instantiate (1:= (m12, d2)).
        lift_simpl. split; eauto.
        instantiate (1:= (m13, d2)).
        lift_simpl. split; eauto.
        instantiate (1:= (m14, d2)).
        lift_simpl. split; eauto.
        instantiate (1:= (m15, d2)).
        lift_simpl. split; eauto.
        instantiate (2:= m16).
        lift_simpl. split; eauto.

      - pose proof H6 as Hspec.
        functional inversion Hspec; subst.
        split; eauto; pattern2_refinement_simpl. 
        econstructor; simpl; eauto.
    Qed.

  End WITHMEM.

End Refinement.