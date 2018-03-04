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
Require Import BootGenDef.
Require Import BootGenLemma.

(** * Definition of the refinement relation*)
Section Refinement.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    Global Instance: LoadStoreProp' (HD:= mboot_data_prf).
    Proof.
      accessor_prop_tac.
    Qed.          

    Lemma flatmem_load_correct0:
      forall (s: stencil) ι (m1 m2: mem) (d1: HDATAOps) (d2: LDATAOps) chunk n v b,
        FlatMem.load chunk (HP d1) n = v ->
        MatchExtcallStates (one_crel (CompatRelOps0:= rel_ops) HDATAOps LDATAOps) s ι m1 d1 m2 d2 ->
        0 <= n <= adr_max - size_chunk chunk ->
        (align_chunk chunk | n) ->
        find_symbol s FlatMem_LOC = Some b ->
        exists v',
          Mem.load (mem:= mwd LDATAOps) chunk (m2, d2) b n = Some v' /\
          val_inject ι v v'.
    Proof.
      intros. inv H0.
      inv match_match. inv H.
      rewrite H3 in H4; inv H4.
      assert (HOS1: n + size_chunk chunk <= adr_max).
      {
        revert H1; clear; intros.
        omega.
      }
      assert (HOS2: n >= 0) by omega.
      pose proof (size_chunk_pos chunk) as HOS3.
      destruct H0 as [v1[v2[HL1[HV1[HL2 HM]]]]].
      assert (HW1: adr_max = n + (adr_max - n)) by omega.
      rewrite HW1 in HL1, HL2. clear HW1. 
      eapply Mem.loadbytes_split in HL1; try omega.
      eapply FlatMem.loadbytes_split in HL2; try omega.
      rewrite Z.add_0_l in HL1, HL2.
      destruct HL1 as (bs11 & bs12 & HL11 & HL12 & Hca1).
      destruct HL2 as (bs21 & bs22 & HL21 & HL22 & Hca2).
      assert (Heq1: length bs11 = length bs21).
      {
        erewrite Mem.loadbytes_length; eauto 1.
        erewrite FlatMem.loadbytes_length; eauto 1.
      }
      assert (Heq2: length bs12 = length bs22).
      {
        erewrite Mem.loadbytes_length; eauto 1.
        erewrite FlatMem.loadbytes_length; eauto 1.
      }
      clear HL21.
      assert (HW2: adr_max - n = size_chunk chunk + (adr_max - n - size_chunk chunk)) by omega.
      rewrite HW2 in HL12, HL22. clear HW2.
      eapply Mem.loadbytes_split in HL12; try omega.
      eapply FlatMem.loadbytes_split in HL22; try omega.
      destruct HL12 as (bs121 & bs122 & HL121 & HL122 & Hca11).
      destruct HL22 as (bs221 & bs222 & HL221 & HL222 & Hca21).
      assert (Heq3: length bs121 = length bs221).
      {
        erewrite Mem.loadbytes_length; eauto 1.
        erewrite FlatMem.loadbytes_length; eauto 1.
      }
      assert (Heq4: length bs122 = length bs222).
      {
        erewrite Mem.loadbytes_length; eauto 1.
        erewrite FlatMem.loadbytes_length; eauto 1.
      }
      clear HL222.
      exploit Mem.loadbytes_load; eauto.
      intros HL1'.
      erewrite FlatMem.loadbytes_load; eauto.
      simpl. lift_trivial.
      rewrite HL1'. 
      refine_split'; eauto 1.
      eapply decode_val_inject; eauto.
      clear HL221.
      subst.
      eapply list_forall2_sep in HM; auto.
      destruct HM as [_ HM].
      eapply list_forall2_sep in HM; auto.
      apply HM.
    Qed.        

    Ltac pattern2_refinement_simpl:=  
      pattern2_refinement_simpl' (@relate_AbData).

    Lemma flatmem_store_correct0:
      forall v v' (s: stencil) ι (m1 m2: mem) (d1 d1': HDATAOps) d2 chunk n b,
        flatmem_store' d1 chunk n v = Some d1' ->
        MatchExtcallStates (one_crel (CompatRelOps0:= rel_ops) HDATAOps LDATAOps) s ι m1 d1 m2 d2 ->
        0 <= n <= adr_max - size_chunk chunk ->
        (align_chunk chunk | n) ->
        val_inject ι v v' ->
        find_symbol s FlatMem_LOC = Some b ->
        exists m2',
          Mem.store chunk m2 b n v' = Some m2' /\
          MatchExtcallStates (one_crel (CompatRelOps0:= rel_ops) HDATAOps LDATAOps) s ι m1 d1' m2' d2.
    Proof.
      intros. inv H0.
      inv match_match. inv H0.
      rewrite H6 in H4; inv H4.
      destruct H5 as [v1[v2[HL1[HV1[HL2 HM]]]]].
      assert (HV: Mem.valid_access m2 chunk b n Writable).
      {
        unfold Mem.valid_access.
        split; try assumption.
        unfold Mem.range_perm in *. intros.
        Transparent Z.sub.
        eapply HV1. omega.
      }
      Opaque Z.sub.
      pose proof (Mem.valid_access_store _ _ _ _ v' HV) as HST.
      destruct HST as [m2' HST].
      rewrite HST.
      refine_split'; eauto 1. functional inversion H. 
      econstructor; eauto 1; pattern2_refinement_simpl.
      constructor. econstructor; try eassumption.
      Transparent Z.sub.
      assert (HW1: adr_max = n + (adr_max - n)) by omega.
      rewrite HW1 in HL1, HL2 |- *.
      pose proof (size_chunk_pos chunk) as HOS3.
      eapply Mem.loadbytes_split in HL1; try omega.
      eapply FlatMem.loadbytes_split in HL2; try omega.
      rewrite Z.add_0_l in HL1, HL2.
      destruct HL1 as (bs11 & bs12 & HL11 & HL12 & Hca1).
      destruct HL2 as (bs21 & bs22 & HL21 & HL22 & Hca2).
      assert (Heq1: length bs11 = length bs21).
      {
        erewrite Mem.loadbytes_length; eauto 1.
        erewrite FlatMem.loadbytes_length; eauto 1.
      }
      assert (Heq2: length bs12 = length bs22).
      {
        erewrite Mem.loadbytes_length; eauto 1.
        erewrite FlatMem.loadbytes_length; eauto 1.
      }
      assert (HW2: adr_max - n = size_chunk chunk + (adr_max - n - size_chunk chunk)) by omega.
      rewrite HW2 in HL12, HL22 |- *. 
      eapply Mem.loadbytes_split in HL12; try omega.
      eapply FlatMem.loadbytes_split in HL22; try omega.
      destruct HL12 as (bs121 & bs122 & HL121 & HL122 & Hca11).
      destruct HL22 as (bs221 & bs222 & HL221 & HL222 & Hca21).
      assert (Heq3: length bs121 = length bs221).
      {
        erewrite Mem.loadbytes_length; eauto 1.
        erewrite FlatMem.loadbytes_length; eauto 1.
      }
      assert (Heq4: length bs122 = length bs222).
      {
        erewrite Mem.loadbytes_length; eauto 1.
        erewrite FlatMem.loadbytes_length; eauto 1.
      }
      exploit Mem.loadbytes_store_same; eauto.
      intros HL1'.
      refine_split'; eauto 1. 
      + eapply Mem.loadbytes_concat; try omega.
        * erewrite Mem.loadbytes_store_other; eauto 1.
          right; right; left. reflexivity. 
        * rewrite Z.add_0_l.
          eapply Mem.loadbytes_concat; try omega.
          {
            erewrite Mem.loadbytes_store_same; eauto 1.
          }                                  
          {
            erewrite Mem.loadbytes_store_other; eauto 1.
            right; right; right. reflexivity. 
          }                              
      + rewrite <- HW2. rewrite <- HW1.
        unfold Mem.range_perm in *. intros.
        eapply Mem.perm_store_1; eauto.
      + assert (HF1: FlatMem.store chunk (HP d1) n v = HP d1 {HP : FlatMem.store chunk (HP d1) n v}) by reflexivity.
        rewrite <- HF1. clear HF1.
        pose proof (FlatMem.loadbytes_store_same chunk (HP d1) n v _ refl_equal) as HL2'.
        destruct HL2' as [HL2'|HL2']. 
        * assert (HF: FlatMem.loadbytes (FlatMem.store chunk (HP d1) n v) 0
                                        (n + (size_chunk chunk + (4294967296 - n - size_chunk chunk)))
                      = bs21 ++ encode_val chunk v ++ bs222).
          {
            eapply FlatMem.loadbytes_concat; try omega.
            - erewrite FlatMem.loadbytes_store_other; eauto 1.
              right; left. reflexivity. 
            - rewrite Z.add_0_l.
              eapply FlatMem.loadbytes_concat; try omega.
              + unfold flatmem_store. simpl. assumption.
              + erewrite FlatMem.loadbytes_store_other; eauto 1.
                right; right. reflexivity. 
          }                                
          rewrite HF.
          clear HF HL2' HL222 HL221 HL21. subst.
          eapply list_forall2_sep in HM; auto.
          destruct HM as [HM1 HM].
          eapply list_forall2_sep in HM; auto.
          destruct HM as [_ HM2].
          apply list_forall2_app; eauto 1.
          apply list_forall2_app; eauto 1.
          eapply encode_val_inject; eauto.
        * assert (HF: FlatMem.loadbytes (FlatMem.store chunk (HP d1) n v) 0
                                        (n + (size_chunk chunk + (4294967296 - n - size_chunk chunk)))
                      = bs21 ++ (list_repeat (length (encode_val chunk v)) Undef) ++ bs222).
          {
            eapply FlatMem.loadbytes_concat; try omega.
            - erewrite FlatMem.loadbytes_store_other; eauto 1.
              right; left. reflexivity. 
            - rewrite Z.add_0_l.
              eapply FlatMem.loadbytes_concat; try omega.
              + unfold flatmem_store. simpl. assumption.
              + erewrite FlatMem.loadbytes_store_other; eauto 1.
                right; right. reflexivity. 
          }                                
          rewrite HF.
          clear HF HL2' HL222 HL221 HL21. subst.
          eapply list_forall2_sep in HM; auto.
          destruct HM as [HM1 HM].
          eapply list_forall2_sep in HM; auto.
          destruct HM as [_ HM2].
          apply list_forall2_app; eauto 1.
          apply list_forall2_app; eauto 1.
          apply list_forall2_memval_undef_chunk.
    Qed.

  End WITHMEM.

End Refinement.