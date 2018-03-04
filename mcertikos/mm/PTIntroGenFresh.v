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
(*          Refinement proof for PTIntro layer                         *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MAL layer and MPTIntro layer*)
Require Import PTIntroGenDef.
Require Import PTIntroGenSpec.

(** * Definition of the refinement relation*)
Section Refinement.

  Context `{real_params: RealParams}.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** ** The low level specifications exist*)
    Section Exists.

      Lemma setCR3_exist:
        forall habd habd' labd m n s f,
          setPT'_spec n habd = Some habd'
          -> high_level_invariant habd
          -> relate_RData f habd labd
          -> match_RData s habd m f
          -> exists labd', setCR30_spec labd (GLOBP PTPool_LOC (Int.repr (n * PgSize)))
                           = Some labd' /\ relate_RData f habd' labd'
                           /\ PT habd' = n
                           /\ ptpool habd' = ptpool habd
                           /\ pperm habd' = pperm habd
                           /\ idpde habd' = idpde habd
                           /\ CR3 labd' = (GLOBP PTPool_LOC (Int.repr (n * PgSize)))
                           /\ 0 <= n < num_proc.
      Proof.
        unfold setPT'_spec, setCR30_spec; intros until f.
        intros HP HINV HR HM; pose proof HR as HR'; inv HR; revert HP;
        subrewrite'; intros HQ; inv HINV; subdestruct;
        destruct (CR3_valid_dec
                    (GLOBP PTPool_LOC (Int.repr (n * 4096)))).
        - (* ipt = true /\ valid CR3*)
          inv HQ; refine_split'; eauto.
          inv HR'. econstructor; eauto; simpl.
          econstructor; eauto.
          rewrite Int.unsigned_repr. omega.
          rewrite int_max. omega.
        - elim n0; unfold CR3_valid; eauto.
        - (* ipt = false /\ valid CR3 *)
          inv HQ; refine_split'; eauto.
          inv HR'. econstructor; eauto; simpl.
          econstructor; eauto.
          rewrite Int.unsigned_repr. omega.
          rewrite int_max. omega.
        - elim n0; unfold CR3_valid; eauto.
      Qed.

    End Exists.

    Ltac pattern2_refinement_simpl:=  
      pattern2_refinement_simpl' (@relate_AbData).

    Section FRESH_PRIM.

      Lemma setPT_spec_ref:
        compatsim (crel HDATA LDATA) (gensem setPT'_spec) setPT_spec_low.
      Proof. 
        compatsim_simpl (@match_AbData).
        assert(HOS: kernel_mode d2).
        {
          simpl; inv match_related.
          functional inversion H1; subst;
          refine_split'; trivial; congruence.
        }
        exploit setCR3_exist; eauto; intros (labd' & HP & HM & HN1 & HN2 & HN3 & Hide & HCR3 & Hrange).
        refine_split; eauto.
        econstructor; eauto.
        pose proof match_related as match_relate'.
        inv match_related.          
        split; eauto; pattern2_refinement_simpl. 
        econstructor; eauto; subrewrite'.
      Qed.

      Lemma getPDE_spec_ref:
        compatsim (crel HDATA LDATA) (gensem getPDE_spec) getPDE_spec_low.
      Proof.
        compatsim_simpl (@match_AbData). 
        assert(HOS: kernel_mode d2 
                    /\ 0 <= Int.unsigned i < num_proc
                    /\ 0 <= Int.unsigned i0 <= PDX Int.max_unsigned).
        {
          simpl; inv match_related.
          unfold getPDE_spec in *.
          unfold PDE_Arg in *.
          subdestruct; refine_split'; trivial; congruence.
        }
        destruct HOS as [Hkern [Hrange Hrange']].
        generalize H; intros HMAT. inv H. specialize (H1 _ Hrange).
        inv H1. specialize (H _ Hrange').
        destruct H as (v & HLD & _ & HM).
        assert (HVint: exists v', Vint v' = v /\ Int.unsigned z = Int.unsigned v' / PgSize).
        {
          functional inversion H2.
          - subst pt. rewrite H8 in HM. inv HM.
            refine_split'; trivial. subrewrite'.
            rewrite Zplus_comm.
            rewrite Z_div_plus. reflexivity.
            omega.
          - subst pt. rewrite H8 in HM. inv HM.
            refine_split'; trivial. 
        }
        destruct HVint as (v' & Heq & Heq'); subst.
        refine_split; eauto.
        econstructor; eauto.
      Qed.

      Lemma getPTE_spec_ref:
        compatsim (crel HDATA LDATA) (gensem getPTE_spec) getPTE_spec_low.
      Proof.
        compatsim_simpl (@match_AbData). 
        assert(HOS: kernel_mode d2 
                    /\ 0 <= Int.unsigned i < num_proc
                    /\ 0 <= Int.unsigned i0 <= PDX Int.max_unsigned
                    /\ 0 <= Int.unsigned i1 <= PTX Int.max_unsigned).
        {
          simpl; inv match_related.
          unfold getPTE_spec in *. 
          unfold PTE_Arg in *. unfold PDE_Arg in *.
          subdestruct; refine_split'; trivial; congruence.
        }
        destruct HOS as (Hkern & Hrange & Hrange' & Hrange'').
        generalize H; intros HMAT. inv H. specialize (H1 _ Hrange).
        inv H1. specialize (H _ Hrange').
        destruct H as (v & HLD & _ & HM).
        assert (HVint: exists v1 v2, Vint v1 = v /\ Int.unsigned v1 = v2 * PgSize + PT_PERM_PTU /\
                                     fload'_spec (v2 * one_k + Int.unsigned i1) d2 = Some (Int.unsigned z)).
        { 
          unfold getPTE_spec in *.
          destruct (ikern d1') eqn: Hik; contra_inv.
          destruct (ihost d1') eqn: Hih; contra_inv.
          destruct (init d1') eqn: Hii; contra_inv.
          destruct (ipt d1') eqn: Hit; contra_inv.
          destruct (PTE_Arg (Int.unsigned i) (Int.unsigned i0) (Int.unsigned i1)); contra_inv.
          destruct (ZMap.get (Int.unsigned i0) (ZMap.get (Int.unsigned i) (ptpool d1'))) eqn: HT; contra_inv.
          inv HM. exploit relate_PMap_re; eauto 1. intros HPMap.
          inv HPMap. specialize (H _ Hrange _ Hrange' _ _ HT _ Hrange'').
          destruct H as (v' & HLD' & HM).
          assert (HLD'': fload'_spec (pi * one_k + Int.unsigned i1) d2 = Some (Int.unsigned z)).
          {
            unfold fload'_spec. inv match_related. rewrite <- ikern_re, <- ihost_re.
            rewrite Hik, Hih.
            assert (HOS: 0 <= pi * 4096 + 7 <= Int.max_unsigned).
            {
              specialize (Int.unsigned_range_2 v0). subrewrite'.
            }
            rewrite zle_lt_true.
            - replace ((pi * 1024 + Int.unsigned i1) * 4) with (pi * 4096 + Int.unsigned i1 * 4) by omega.
              destruct (ZMap.get (Int.unsigned i1) pte); contra_inv; inv HM; inv H2.
              + refine_split'; trivial. 
                rewrite H7. apply PermZ_eq in H6. rewrite H6. trivial.
              + refine_split'; trivial.
            - revert HOS Hrange''. clear.
              intros. rewrite_omega.
          }
          refine_split'; eauto 1. 
        }
        destruct HVint as (v1 & v2 & Heq1 & Heq2 & Heq4).
        refine_split; eauto 1.
        econstructor; eauto.
      Qed.

      Lemma setPTE_spec_ref:
        compatsim (crel HDATA LDATA) (gensem setPTE_spec) setPTE_spec_low.
      Proof.
        compatsim_simpl (@match_AbData).
        assert (Hkern: exists p0,
                         kernel_mode d2
                         /\ 0 <= Int.unsigned i < num_proc
                         /\ 0 <= Int.unsigned i0 <= PDX Int.max_unsigned
                         /\ 0 <= Int.unsigned i1 <= PTX Int.max_unsigned
                         /\ 0 < Int.unsigned i2 < nps d2
                         /\ ZtoPerm (Int.unsigned i3) = Some p0
                         /\ PT d1' = PT d1).
        {
          inv match_related. functional inversion H1; subst.
          unfold PTE_Arg, PDE_Arg in *. subdestruct.
          refine_split'; try congruence; eauto.
        }
        destruct Hkern as (perm & Hkern & Hrange & Hrange' & Hrange'' & Hrange''' & HPerm & HPT).
        inv H. generalize H2; intros HMAT; specialize (H2 _ Hrange); inv H2.
        specialize (H _ Hrange'); destruct H as [v[HLD [HV HM]]].
        assert (HVint: exists v1 v2, Vint v1 = v /\ Int.unsigned v1 = v2 * PgSize + PT_PERM_PTU
                                     /\ match_RData s d1' m2 ι
                                     /\ init d2 = true
                                     /\ exists d2', fstore0_spec  (v2 * one_k + Int.unsigned i1) 
                                                                  (Int.unsigned i2 * PgSize + Int.unsigned i3) d2
                                                    = Some d2'
                                                    /\ relate_RData ι d1' d2').
        { 
          unfold setPTE_spec in *. subdestruct.
          inv HM. esplit; esplit. split; [reflexivity|]. split; [eassumption|]. split; [|split].
          - (* match_RData *)
            constructor; inv H1; simpl; trivial. 
            econstructor; eauto 1; intros.
            destruct (zeq n0 (Int.unsigned i)); subst.
            + (* n = Int.unsigned i *)           
              rewrite ZMap.gss. constructor; intros.
              destruct (zeq i4 (Int.unsigned i0)); subst.
              * (* i4 = Int.unsigned i0 *)   
                rewrite ZMap.gss. refine_split'; eauto 1.
                constructor; eauto; intros.
              * (* i4 <> Int.unsigned i0 *)   
                rewrite ZMap.gso; eauto 2.
                specialize (HMAT _ Hrange). inv HMAT.
                eapply H2; eauto 2.
            + (* n <> int.unsigned i*)
              rewrite ZMap.gso; eauto 2.
          - inv match_related. congruence.                
          - (* fstore /\ relate RData *)
            unfold fstore0_spec. inv match_related.
            rewrite <- ikern_re, <- ihost_re. rewrite Hdestruct, Hdestruct0.
            assert (HOS: 0<= pi * 4096 + 7 <= Int.max_unsigned).
            {
              specialize (Int.unsigned_range_2 v0). subrewrite'. 
            }
            rewrite zle_lt_true.
            + replace ((pi * 1024 + Int.unsigned i1) * 4) with (pi * 4096 + Int.unsigned i1 * 4) by omega.
              unfold flatmem_store. unfold PageI.                 
              replace ((pi * 4096 + Int.unsigned i1 * 4) / 4096) with pi.
              * pose proof (pperm_re pi) as HPP.
                rewrite H10 in HPP. inv HPP. trivial.
                refine_split'; eauto 1.
                inv H1. constructor; trivial; simpl; try congruence.
                { (* FlatMem *)
                  unfold FlatMem.flatmem_inj in *.
                  intros; rewrite valid_dirty; [| assumption| eassumption]. 
                  eapply FlatMem.store_unmapped_inj; eauto 1.
                  simpl. rewrite_omega.
                }
                { (* PMap *) 
                  constructor; intros. inv relate_PMap_re. 
                  destruct (zeq n0 (Int.unsigned i)); subst.
                  - (* n = Int.unsigned i *)           
                    rewrite ZMap.gss in H4. 
                    destruct (zeq i4 (Int.unsigned i0)); subst.
                    + (* i4 = Int.unsigned i0 *)   
                      rewrite ZMap.gss in H4. inv H4. 
                      destruct (zeq vadr (Int.unsigned i1)); subst.
                      * (* vadr = Int.unsigned i1 *)
                        rewrite ZMap.gss. rewrite FlatMem.load_store_same.
                        refine_split'; trivial.
                        econstructor; eauto. apply Int.unsigned_repr.
                        apply ZtoPerm_range in Hdestruct6.
                        exploit valid_nps; eauto. rewrite nps_re.
                        rewrite_omega.
                      * (* vadr <> Int.unsigned i1 *)              
                        rewrite ZMap.gso; auto. erewrite FlatMem.load_store_other; eauto 2.
                        simpl. destruct (zle (vadr + 1) (Int.unsigned i1)).
                        left; omega. right; omega.
                    + (* i4 <> Int.unsigned i0 *)
                      rewrite ZMap.gso in H4; auto. 
                      assert (Hneq: pi <> pi0).
                      {
                        red; intros; subst.
                        specialize (HMAT _ Hrange). inv HMAT.
                        specialize (H8 _ H2). destruct H8 as (v & _ & _ & HMAT).
                        rewrite H4 in HMAT. inv HMAT. congruence.
                      }
                      erewrite FlatMem.load_store_other; eauto 2. simpl.
                      destruct (zle (pi0 + 1) pi); rewrite_omega. 
                  - (* n <> int.unsigned i*)              
                    rewrite ZMap.gso in H4; auto. 
                    assert (Hneq: pi <> pi0).
                    {
                      red; intros; subst.
                      specialize (HMAT _ H1). inv HMAT.
                      specialize (H8 _ H2). destruct H8 as (v & _ & _ & HMAT).
                      unfold PMap, ZMap.t, PMap.t in HMAT.
                      rewrite H4 in HMAT. inv HMAT. congruence.
                    }
                    erewrite FlatMem.load_store_other; eauto 2. simpl. 
                    destruct (zle (pi0 + 1) pi); rewrite_omega.
                }

              * rewrite Zplus_comm.
                rewrite Z_div_plus. rewrite Zdiv_small. reflexivity.
                revert Hrange''. clear; intros. rewrite_omega. omega.
            + rewrite_omega.
        }
        destruct HVint as (v1 & v2 & Heq1 & Heq2 & Hma & Hinit &  d2' & HST & Hre); subst.
        exists ι, Vundef, (fst (m2, d2)), d2'.
        refine_split; eauto 1.
        - econstructor; eauto 1.
        - split; eauto; pattern2_refinement_simpl. 
      Qed.

      Lemma rmvPTE_spec_ref:
        compatsim (crel HDATA LDATA) (gensem rmvPTE_spec) rmvPTE_spec_low.
      Proof.
        compatsim_simpl (@match_AbData).
        assert (Hkern: kernel_mode d2
                       /\ 0 <= Int.unsigned i < num_proc
                       /\ 0 <= Int.unsigned i0 <= PDX Int.max_unsigned
                       /\ 0 <= Int.unsigned i1 <= PTX Int.max_unsigned
                       /\ PT d1' = PT d1).
        {
          inv match_related. functional inversion H1; subst.
          unfold PTE_Arg, PDE_Arg in *. subdestruct.
          refine_split'; try congruence; eauto.
        }
        destruct Hkern as [Hkern [Hrange [Hrange' [Hrange'' HPT]]]].
        inv H. generalize H2; intros HMAT; specialize (H2 _ Hrange); inv H2.
        specialize (H _ Hrange'); destruct H as [v[HLD [HV HM]]].
        assert (HVint: exists v1 v2, Vint v1 = v /\ Int.unsigned v1 = v2 * PgSize + PT_PERM_PTU
                                     /\ match_RData s d1' m2 ι
                                     /\ exists d2', fstore0_spec (v2 * one_k + Int.unsigned i1) 0 d2 = Some d2'
                                                    /\ relate_RData ι d1' d2').
        { 
          unfold rmvPTE_spec in *. subdestruct.
          inv HM. esplit; esplit. split; [reflexivity|]. split; [eassumption|]. split.
          - (* match_RData *)
            constructor; inv H1; simpl; trivial. econstructor; eauto 1; intros.
            destruct (zeq n0 (Int.unsigned i)); subst.
            + (* n = Int.unsigned i *)           
              rewrite ZMap.gss. constructor; intros.
              destruct (zeq i2 (Int.unsigned i0)); subst.
              * (* i2 = Int.unsigned i0 *)   
                rewrite ZMap.gss. refine_split'; eauto 1.
                constructor; eauto; intros.
              * (* i2 <> Int.unsigned i0 *)   
                rewrite ZMap.gso; eauto 2.
                specialize (HMAT _ Hrange). inv HMAT.
                eauto 2.
            + (* n <> int.unsigned i*)
              rewrite ZMap.gso; eauto 2.
              
          - (* fstore /\ relate RData *)
            unfold fstore0_spec. inv match_related.
            rewrite <- ikern_re, <- ihost_re. rewrite Hdestruct, Hdestruct0.
            assert (HOS: 0<= pi * 4096 + 7 <= Int.max_unsigned).
            {
              specialize (Int.unsigned_range_2 v0). subrewrite'.
            }
            rewrite zle_lt_true.
            + replace ((pi * 1024 + Int.unsigned i1) * 4) with (pi * 4096 + Int.unsigned i1 * 4) by omega.
              unfold flatmem_store. unfold PageI.                 
              replace ((pi * 4096 + Int.unsigned i1 * 4) / 4096) with pi.
              * pose proof (pperm_re pi) as HPP.
                rewrite H10 in HPP. inv HPP.
                refine_split'; eauto 1.
                inv H1. constructor; trivial; simpl; try congruence.
                { (* FlatMem *)
                  unfold FlatMem.flatmem_inj in *.
                  intros; rewrite valid_dirty; [| assumption| eassumption]. 
                  eapply FlatMem.store_unmapped_inj; eauto 1.
                  simpl. rewrite_omega.
                }
                { (* PMap *) 
                  constructor; intros. inv relate_PMap_re. 
                  destruct (zeq n0 (Int.unsigned i)); subst.
                  - (* n = Int.unsigned i *)           
                    rewrite ZMap.gss in H4. 
                    destruct (zeq i2 (Int.unsigned i0)); subst.
                    + (* i2 = Int.unsigned i0 *)   
                      rewrite ZMap.gss in H4. inv H4. 
                      destruct (zeq vadr (Int.unsigned i1)); subst.
                      * (* vadr = Int.unsigned i1 *)
                        rewrite ZMap.gss. rewrite FlatMem.load_store_same.
                        refine_split'; trivial.
                        econstructor; eauto. 
                      * (* vadr <> Int.unsigned i1 *)              
                        rewrite ZMap.gso; auto. erewrite FlatMem.load_store_other; eauto 2.
                        simpl. destruct (zle (vadr + 1) (Int.unsigned i1)).
                        left; omega. right; omega.
                    + (* i2 <> Int.unsigned i0 *)
                      rewrite ZMap.gso in H4; auto. 
                      assert (Hneq: pi <> pi0).
                      {
                        red; intros; subst.
                        specialize (HMAT _ Hrange). inv HMAT.
                        specialize (H8 _ H2). destruct H8 as (v & _ & _ & HMAT).
                        rewrite H4 in HMAT. inv HMAT. congruence.
                      }
                      erewrite FlatMem.load_store_other; eauto 2.
                      simpl. destruct (zle (pi0 + 1) pi); rewrite_omega.
                  - (* n <> int.unsigned i*)              
                    rewrite ZMap.gso in H4; auto. 
                    assert (Hneq: pi <> pi0).
                    {
                      red; intros; subst.
                      specialize (HMAT _ H1). inv HMAT.
                      specialize (H8 _ H2). destruct H8 as (v & _ & _ & HMAT).
                      unfold PMap, ZMap.t, PMap.t in HMAT.
                      rewrite H4 in HMAT. inv HMAT. congruence.
                    }
                    erewrite FlatMem.load_store_other; eauto 2.
                    simpl. destruct (zle (pi0 + 1) pi); rewrite_omega.
                }

              * rewrite Zplus_comm.
                rewrite Z_div_plus. rewrite Zdiv_small. reflexivity.
                revert Hrange''. clear; intros. rewrite_omega. omega.
            + rewrite_omega.
        }
        destruct HVint as (v1 & v2 & Heq1 & Heq2 & Hma & d2' & HST & Hre); subst.
        exists ι, Vundef, (fst (m2, d2)), d2'.
        refine_split; eauto 1.
        - econstructor; eauto 1.
        - split; eauto; pattern2_refinement_simpl.
      Qed.

      Lemma setPDEU_spec_ref:
        compatsim (crel HDATA LDATA) (gensem setPDEU_spec) setPDEU_spec_low.
      Proof.
        compatsim_simpl (@match_AbData).
        assert (Hkern: kernel_mode d2
                       /\ 0 <= Int.unsigned i < num_proc
                       /\ 0 <= Int.unsigned i0 <= PDX Int.max_unsigned
                       /\ 0 < Int.unsigned i1 < nps d2
                       /\ PT d1' = PT d1
                       /\ init d2 = true).
        {
          inv match_related. 
          unfold setPDEU_spec in *.
          unfold PDE_Arg in *.
          subdestruct; refine_split'; trivial; try congruence.
          inv H1. reflexivity.
        }
        destruct Hkern as (Hkern & Hrange & Hrange' & Hrange'' & HPT & Hinit).
        inv H. generalize H2; intros HMAT; specialize (H2 _ Hrange); inv H2.
        specialize (H _ Hrange'); destruct H as [_[_ [HV _]]].
        specialize (Mem.valid_access_store _ _ _ _ 
                                           (Vint (Int.repr (Int.unsigned i1 * PgSize + PT_PERM_PTU)))
                                           HV); intros [m0 HST].
        refine_split; eauto.
        - econstructor; eauto.
          simpl; lift_trivial. rewrite HST. reflexivity.
        - pose proof H1 as Hspec.
          functional inversion Hspec; subst; simpl in *.
          split; eauto 1; pattern2_refinement_simpl.           
          + inv match_related; simpl in *; split; simpl; try eassumption.
            { (* Flatmem *)
              apply FlatMem.free_page_inj. assumption.
            }
            { (* PPermT_les *)
              intros j. specialize (pperm_re j).
              destruct (zeq j (Int.unsigned i1)); subst.
              - rewrite ZMap.gss. rewrite H10 in pperm_re.
                inv pperm_re. constructor.
              - rewrite ZMap.gso; eauto 2.
            }
            { (* PMapPool *)
              subst pt'. constructor; intros.
              destruct (zeq n (Int.unsigned i)); subst.             
              { (* n = int.unsigned i*)
                rewrite ZMap.gss in H12.
                destruct (zeq i2 (Int.unsigned i0)); subst.
                { (* i2 = Int.unsigned i0 *)
                  rewrite ZMap.gss in H12.                  
                  inv H12. rewrite ZMap.gi. 
                  refine_split'; eauto 2. constructor.
                }
                { (* i2 <> Int.unsigned i0 *)                    
                  rewrite ZMap.gso in H12; eauto 1.
                  inv relate_PMap_re. eauto.
                }
              }
              { (* n <> int.unsigned i*)              
                rewrite ZMap.gso in H12; eauto 1.
                inv relate_PMap_re. eauto.
              }
            }
            
          + econstructor; eauto 1; simpl in *.
            {
              econstructor; eauto 1; intros.
              * destruct (zeq n (Int.unsigned i)); subst.
                { (* n = int.unsigned i*)
                  rewrite ZMap.gss.
                  specialize (HMAT _ H). inv HMAT.
                  constructor; intros.
                  specialize (H11 _ H12).
                  destruct (zeq i2 (Int.unsigned i0)); subst.
                  { (* i2 = Int.unsigned i0 *)
                    refine_split'.
                    - eapply Mem.load_store_same; eauto.
                    - eapply Mem.store_valid_access_1; eauto.
                    - subst pt'; repeat rewrite ZMap.gss.
                      constructor; intros.
                      + rewrite Int.unsigned_repr. reflexivity.
                        exploit valid_nps; eauto 1.
                        intros. rewrite_omega.
                      + rewrite ZMap.gss. reflexivity.
                  }
                  { (* i1 <> Int.unsigned i0 *)                    
                    destruct H11 as [v1[HL1[HV1 HM1]]].
                    refine_split'.
                    - erewrite Mem.load_store_other; eauto.
                      right; simpl.
                      destruct (zle (i2 + 1) (Int.unsigned i0)).
                      + left. revert n l. clear. intros. omega.
                      + right. revert n g. clear. intros. omega. 
                    - eapply Mem.store_valid_access_1; eauto.
                    - subst pt'. rewrite ZMap.gso; auto.
                      inv HM1; constructor; intros; eauto 1.
                      + destruct (zeq pi (Int.unsigned i1)); subst.
                        * congruence.
                        * rewrite ZMap.gso; eauto 1.
                  }
                }
                { (* n <> int.unsigned i*)              
                  constructor; intros. rewrite ZMap.gso; auto.
                  specialize (HMAT _ H). inv HMAT.
                  specialize (H12 _ H11); destruct H12 as [v1[HL1[HV1 HM1]]].
                  refine_split'.
                  - erewrite Mem.load_store_other; eauto.
                    right; simpl.
                    destruct (zle (n + 1) (Int.unsigned i)).
                    + left. rewrite_omega.
                    + right. rewrite_omega.
                  - eapply Mem.store_valid_access_1; eauto.
                  - unfold PMap, ZMap.t, PMap.t in HM1. 
                    inv HM1; econstructor; intros; eauto 1.    
                    + destruct (zeq pi (Int.unsigned i1)); subst.
                      * congruence. 
                      * rewrite ZMap.gso; eauto 1.
                }
            }
            {
              inv H0. esplit; eauto. intros.
              specialize (H _ H0 _ H12).
              destruct H as (v & HLD & HV' & HM).
              erewrite Mem.load_store_other; eauto.
              - refine_split'; eauto.
                eapply Mem.store_valid_access_1; eauto.
              - left. red; intros; subst.
                specialize (genv_vars_inj _ _ _ _ H3 H11).
                intros. inv H.
            }
      Qed.

      Lemma rmvPDE_spec_ref:
        compatsim (crel HDATA LDATA) (gensem rmvPDE_spec) rmvPDE_spec_low.
      Proof.
        compatsim_simpl (@match_AbData).
        assert (Hkern: kernel_mode d2
                       /\ 0 <= Int.unsigned i < num_proc
                       /\ 0 <= Int.unsigned i0 <= PDX Int.max_unsigned
                       /\ PT d1' = PT d1
                       /\ idpde d1' = idpde d1).
        {
          inv match_related. 
          unfold rmvPDE_spec in *.
          unfold PDE_Arg in *.
          subdestruct; refine_split'; trivial; try congruence;
          inv H1; reflexivity.
        }
        destruct Hkern as (Hkern & Hrange & Hrange' & HPT & Hipde).
        inv H. generalize H2; intros HMAT; specialize (H2 _ Hrange); inv H2.
        specialize (H _ Hrange'); destruct H as [_[_ [HV _]]].
        specialize (Mem.valid_access_store _ _ _ _ 
                                           (Vint (Int.repr PT_PERM_UP))
                                           HV); intros [m0 HST].
        refine_split; eauto.
        - econstructor; eauto.
          simpl; lift_trivial. rewrite HST. reflexivity.
        - pose proof H1 as Hspec.
          assert (Hre_ab: relate_AbData s ι d1' d2).
          {
            inv match_related. 
            assert (HP: relate_PMapPool
                          (ZMap.set (Int.unsigned i)
                                    (ZMap.set (Int.unsigned i0) PDEUnPresent
                                              (ZMap.get (Int.unsigned i) (ptpool d1))) 
                                    (ptpool d1)) (HP d2)).
            {
              constructor; intros.
              destruct (zeq n (Int.unsigned i)); subst.             
              { (* n = int.unsigned i*)
                rewrite ZMap.gss in H4.
                destruct (zeq i1 (Int.unsigned i0)); subst.
                { (* i1 = Int.unsigned i0 *)
                  rewrite ZMap.gss in H4. inv H4.
                }
                { (* i2 <> Int.unsigned i0 *)                    
                  rewrite ZMap.gso in H4; eauto 1.
                  inv relate_PMap_re. eauto.
                }
              }
              { (* n <> int.unsigned i*)              
                rewrite ZMap.gso in H4; eauto 1.
                inv relate_PMap_re. eauto.
              }
            }
            functional inversion Hspec; subst;
            split; trivial; simpl in *; contra_inv.
            { (* PPermT_les *)
              intros j. specialize (pperm_re j).
              destruct (zeq j pi); subst.
              - rewrite ZMap.gss. rewrite H12 in pperm_re.
                inv pperm_re. constructor.
              - rewrite ZMap.gso; eauto 2.
            }
            { (* PPermT_les *)
              intros j. specialize (pperm_re j).
              destruct (zeq j pi); subst.
              - rewrite ZMap.gss. rewrite H11 in pperm_re.
                inv pperm_re. constructor.
              - rewrite ZMap.gso; eauto 2.
            }
          }
          assert (Hma_ab:  match_AbData s d1' m0 ι).
          {
            econstructor; eauto 1; simpl in *.
            {
              econstructor; eauto 1; intros. pose proof HMAT as HMAT'.
              specialize (HMAT _ H). 
              assert(HP: forall pp,
                           (forall pi0 a1 a2, ZMap.get pi0 (pperm d1) = PGHide (PGPMap a1 a2) ->
                                              (a1 <> Int.unsigned i \/ a2 <> Int.unsigned i0) ->
                                              ZMap.get pi0 pp = PGHide (PGPMap a1 a2)) ->
                           match_PMap s (ZMap.get n (ZMap.set (Int.unsigned i)
                                                              (ZMap.set (Int.unsigned i0) PDEUnPresent
                                                                        (ZMap.get (Int.unsigned i) (ptpool d1))) 
                                                              (ptpool d1))) pp m0 b n).
              { 
                intros.
                * destruct (zeq n (Int.unsigned i)); subst.
                  { (* n = int.unsigned i*)
                    rewrite ZMap.gss. inv HMAT.
                    constructor; intros.
                    specialize (H4 _ H5).
                    destruct (zeq i1 (Int.unsigned i0)); subst.
                    { (* i1 = Int.unsigned i0 *)
                      refine_split'.
                      - eapply Mem.load_store_same; eauto.
                      - eapply Mem.store_valid_access_1; eauto.
                      - repeat rewrite ZMap.gss.
                        constructor.
                    }
                    { (* i1 <> Int.unsigned i0 *)                    
                      destruct H4 as [v1[HL1[HV1 HM1]]].
                      refine_split'.
                      - erewrite Mem.load_store_other; eauto.
                        right; simpl.
                        destruct (zle (i1 + 1) (Int.unsigned i0)).
                        + left. omega.
                        + right. omega. 
                      - eapply Mem.store_valid_access_1; eauto.
                      - rewrite ZMap.gso; auto.
                        inv HM1; constructor; intros; eauto.
                    }
                  }
                  { (* n <> int.unsigned i*)              
                    constructor; intros. rewrite ZMap.gso; auto.
                    inv HMAT. specialize (H5 _ H4); destruct H5 as [v1[HL1[HV1 HM1]]].
                    refine_split'.
                    - erewrite Mem.load_store_other; eauto.
                      right; simpl.
                      destruct (zle (n + 1) (Int.unsigned i)).
                      + left. rewrite_omega.
                      + right. rewrite_omega.
                    - eapply Mem.store_valid_access_1; eauto.
                    - unfold PMap, ZMap.t, PMap.t in HM1. 
                      inv HM1; econstructor; intros; eauto.    
                  }
              } 
              functional inversion Hspec; subst; simpl in *;          
              subst pt'; eapply HP; eauto 1; contra_inv.
              {
                intros. destruct (zeq pi0 pi); subst.
                - specialize (HMAT' _ Hrange). inv HMAT'.
                  specialize (H15 _ Hrange').
                  destruct H15 as (? & _ & _ & HM).
                  rewrite H12 in HM. inv HM.
                  destruct H14; congruence. 
                - rewrite ZMap.gso; eauto 1.
              }
              {
                intros. destruct (zeq pi0 pi); subst.
                - specialize (HMAT' _ Hrange). inv HMAT'.
                  specialize (H14 _ Hrange').
                  destruct H14 as (? & _ & _ & HM).
                  rewrite H11 in HM. inv HM.
                  destruct H13; congruence. 
                - rewrite ZMap.gso; eauto 1.
              }
            }
            {
              inv H0. rewrite Hipde. esplit; eauto. intros.
              specialize (H _ H0 _ H4).
              destruct H as (v & HLD & HV' & HM).
              erewrite Mem.load_store_other; eauto.
              - refine_split'; eauto.
                eapply Mem.store_valid_access_1; eauto.
              - left. red; intros; subst.
                specialize (genv_vars_inj _ _ _ _ H3 H2).
                intros. inv H.
            }
          }
          split; eauto 1; pattern2_refinement_simpl.
      Qed.

      Lemma setPDE_spec_ref:
        compatsim (crel HDATA LDATA) (gensem setPDE_spec) setPDE_spec_low.
      Proof.
        compatsim_simpl (@match_AbData).
        assert (Hkern: kernel_mode d2
                       /\ 0 <= Int.unsigned i < num_proc
                       /\ 0 <= Int.unsigned i0 <= PDX Int.max_unsigned
                       /\ PT d1' = PT d1).
        {
          inv match_related. 
          unfold setPDE_spec in *.
          unfold PDE_Arg in *.
          subdestruct; refine_split'; trivial; try congruence.
          inv H1. reflexivity.
        }
        destruct Hkern as (Hkern & Hrange & Hrange' & HPT).
        inv H. generalize H2; intros HMAT; specialize (H2 _ Hrange); inv H2.
        specialize (H _ Hrange'); destruct H as [_[_ [HV _]]]. inv H0.
        specialize (Mem.valid_access_store _ _ _ _ 
                                           (Vptr b0 (Int.repr (Int.unsigned i0 * PgSize + PT_PERM_PTU)))
                                           HV); intros [m0 HST].
        refine_split; eauto.
        - econstructor; eauto.
          simpl; lift_trivial. rewrite HST. reflexivity.
        - pose proof H1 as Hspec.
          functional inversion Hspec; subst; simpl in *.
          split; eauto 1; pattern2_refinement_simpl.           
          + inv match_related; simpl in *; split; simpl; try eassumption.
            { (* PMapPool *)
              subst pt'. constructor; intros.
              destruct (zeq n (Int.unsigned i)); subst.             
              { (* n = int.unsigned i*)
                rewrite ZMap.gss in H11.
                destruct (zeq i1 (Int.unsigned i0)); subst.
                { (* i1 = Int.unsigned i0 *)
                  rewrite ZMap.gss in H11.                  
                  inv H11.
                }
                { (* i1 <> Int.unsigned i0 *)                    
                  rewrite ZMap.gso in H11; eauto 1.
                  inv relate_PMap_re. eauto.
                }
              }
              { (* n <> int.unsigned i*)              
                rewrite ZMap.gso in H11; eauto 1.
                inv relate_PMap_re. eauto.
              }
            }
            
          + econstructor; eauto 1; simpl in *.
            {
              econstructor; eauto 1; intros.
              * destruct (zeq n (Int.unsigned i)); subst.
                { (* n = int.unsigned i*)
                  rewrite ZMap.gss.
                  specialize (HMAT _ H0). inv HMAT.
                  constructor; intros.
                  specialize (H10 _ H11).
                  destruct (zeq i1 (Int.unsigned i0)); subst.
                  { (* i1 = Int.unsigned i0 *)
                    refine_split'.
                    - eapply Mem.load_store_same; eauto.
                    - eapply Mem.store_valid_access_1; eauto.
                    - subst pt'; repeat rewrite ZMap.gss.
                      constructor; intros; eauto.
                      rewrite Int.unsigned_repr. reflexivity.
                      rewrite_omega.
                  }
                  { (* i1 <> Int.unsigned i0 *)                    
                    destruct H10 as [v1[HL1[HV1 HM1]]].
                    refine_split'.
                    - erewrite Mem.load_store_other; eauto.
                      right; simpl.
                      destruct (zle (i1 + 1) (Int.unsigned i0)).
                      + left. omega.
                      + right. omega. 
                    - eapply Mem.store_valid_access_1; eauto.
                    - subst pt'. rewrite ZMap.gso; auto.
                  }
                }
                { (* n <> int.unsigned i*)              
                  constructor; intros. rewrite ZMap.gso; auto.
                  specialize (HMAT _ H0). inv HMAT.
                  specialize (H11 _ H10); destruct H11 as [v1[HL1[HV1 HM1]]].
                  refine_split'.
                  - erewrite Mem.load_store_other; eauto.
                    right; simpl.
                    destruct (zle (n + 1) (Int.unsigned i)).
                    + left. rewrite_omega.
                    + right. rewrite_omega.
                  - eapply Mem.store_valid_access_1; eauto.
                  - unfold PMap, ZMap.t, PMap.t in HM1. 
                    inv HM1; econstructor; intros; eauto 1.    
                }
            }
            {
              esplit; eauto. intros.
              specialize (H _ H0 _ H10).
              destruct H as (v & HLD & HV' & HM).
              erewrite Mem.load_store_other; eauto.
              - refine_split'; eauto.
                eapply Mem.store_valid_access_1; eauto.
              - left. red; intros; subst.
                specialize (genv_vars_inj _ _ _ _ H3 H2).
                intros. inv H.
            }
      Qed.

      Lemma pt_in_spec_ref:
        compatsim (crel HDATA LDATA) (primcall_general_compatsem' 
                                        ptin'_spec (prim_ident:= pt_in)) pt_in_spec_low.
      Proof.
        compatsim_simpl (@match_AbData); intros.
        inv match_extcall_states.
        assert(HOS: kernel_mode d2).
        {
          simpl; inv match_related.
          functional inversion H8; subst;
          refine_split'; trivial; try congruence.
        }
        refine_split'; eauto.
        econstructor; eauto.
        - specialize (match_reg PC). unfold Pregmap.get in *.
          rewrite H7 in match_reg.
          inv match_reg.
          exploit inject_forward_equal'; eauto.
          intros HW; inv HW.
          rewrite Int.add_zero. reflexivity.
        - functional inversion H8; subst.
          pose proof match_related as match_relate'.
          inv match_related.
          split; eauto; pattern2_refinement_simpl. 
          + econstructor; eauto.
            econstructor; eauto.
            inv match_match.
            econstructor; eauto.
          + val_inject_simpl.
      Qed.

      Lemma pt_out_spec_ref:
        compatsim (crel HDATA LDATA) (primcall_general_compatsem' 
                                        ptout_spec (prim_ident:= pt_out)) pt_out_spec_low.
      Proof.
        compatsim_simpl (@match_AbData); intros.
        inv match_extcall_states.
        assert(HOS: kernel_mode d2).
        {
          simpl; inv match_related.
          functional inversion H8; subst;
          refine_split'; trivial; try congruence.
        }
        refine_split'; eauto.
        econstructor; eauto.
        - eapply reg_symbol_inject; eassumption.
        - functional inversion H8; subst.
          pose proof match_related as match_relate'.
          inv match_related.          
          split; eauto; pattern2_refinement_simpl. 
          + econstructor; eauto.
            econstructor; eauto.
            inv match_match.
            econstructor; eauto.
          + val_inject_simpl.
      Qed.

      Lemma setIDPTE_spec_ref:
        compatsim (crel HDATA LDATA) (gensem setIDPTE_spec) setIDPTE_spec_low.
      Proof.
        compatsim_simpl (@match_AbData).
        assert (Hkern: kernel_mode d2
                       /\ 0 <= Int.unsigned i <= PDX Int.max_unsigned
                       /\ 0 <= Int.unsigned i0 <= PTX Int.max_unsigned
                       /\ PT d1' = PT d1
                       /\ exists p0, ZtoPerm (Int.unsigned i1) = Some p0).
        {
          inv match_related. 
          unfold setIDPTE_spec in *.
          unfold IDPTE_Arg in *.
          subdestruct; refine_split'; trivial; try congruence. 
          inv H1. reflexivity.
        }
        destruct Hkern as (Hkern & Hrange & Hrange' & HPT & p0 & Hipde).
        inv H0. generalize H2; intros HMAT. specialize (H2 _ Hrange _ Hrange').
        destruct H2 as [_[_ [HV _]]].
        specialize (Mem.valid_access_store _ _ _ _ 
                                           (Vint (Int.repr ((Int.unsigned i * 1024 + Int.unsigned i0) * 4096 +
                                                            Int.unsigned i1)))
                                           HV); intros [m0 HST].
        refine_split; eauto.
        - econstructor; eauto.
          simpl; lift_trivial. rewrite HST. reflexivity.
        - pose proof H1 as Hspec.
          functional inversion Hspec; subst; simpl in *.
          split; eauto 1; pattern2_refinement_simpl.           
          + inv match_related; simpl in *; split; simpl; try eassumption.            
          + econstructor; eauto 1; simpl in *.
            {
              inv H. esplit; eauto. intros.
              specialize (H0 _ H). inv H0.
              split; intros. specialize (H11 _ H0).
              destruct H11 as (v & HLD & HV' & HM).
              erewrite Mem.load_store_other; eauto.
              - refine_split'; eauto.
                eapply Mem.store_valid_access_1; eauto.
              - left. red; intros; subst.
                specialize (genv_vars_inj _ _ _ _ H3 H10).
                intros. contra_inv.
            }
            {
              econstructor; eauto 1; intros. subst pde'.
              * destruct (zeq i2 (Int.unsigned i)); subst. 
                { (* i2 = int.unsigned i*)
                  rewrite ZMap.gss.
                  specialize (HMAT _ H0). 
                  destruct (zeq j (Int.unsigned i0)); subst.
                  { (* j = Int.unsigned i0 *)
                    rewrite ZMap.gss. refine_split'.
                    - eapply Mem.load_store_same; eauto.
                    - eapply Mem.store_valid_access_1; eauto.
                    - simpl. econstructor; eauto.
                      rewrite Int.unsigned_repr. reflexivity.
                      exploit ZtoPerm_range; eauto. intros.
                      rewrite_omega.
                  }
                  { (* j <> Int.unsigned i0 *)                    
                    specialize (HMAT _ H10).
                    destruct HMAT as [v1[HL1[HV1 HM1]]].
                    refine_split'.
                    - erewrite Mem.load_store_other; eauto.
                      right; simpl.
                      destruct (zle (j + 1) (Int.unsigned i0)).
                      + left. omega.
                      + right. omega. 
                    - eapply Mem.store_valid_access_1; eauto.
                    - rewrite ZMap.gso; auto.
                  }
                }
                { (* i2 <> int.unsigned i*)              
                  rewrite ZMap.gso; auto.
                  specialize (HMAT _ H0 _ H10). 
                  destruct HMAT as [v1[HL1[HV1 HM1]]].
                  refine_split'; eauto.
                  - erewrite Mem.load_store_other; eauto.
                    right; simpl.
                    destruct (zle (i2 + 1) (Int.unsigned i)).
                    + left. rewrite_omega.
                    + right. rewrite_omega.
                  - eapply Mem.store_valid_access_1; eauto.
                }
            }
      Qed.

    End FRESH_PRIM.

  End WITHMEM.

End Refinement.
