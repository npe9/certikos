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
Require Export PTIntroGenDef.
Require Import PTIntroGenAccessor0.
Require Import PTIntroGenAccessor.

(** * Definition of the refinement relation*)
Section Refinement.

  Context `{real_params: RealParams}.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** ** The low level specifications exist*)
    Section Exists.

      Lemma container_init0_exist:
        forall habd habd' labd i f,
          container_init0_spec i habd = Some habd'
          -> relate_RData f habd labd
          -> exists labd', container_init_spec i labd = Some labd' /\ relate_RData f habd' labd'
                           /\ PT habd' = PT habd
                           /\ ptpool habd' = ptpool habd
                           /\ CR3 labd' = CR3 labd
                           /\ pperm habd' = pperm habd
                           /\ idpde habd' = idpde habd.
      Proof.
        unfold container_init0_spec, container_init_spec; intros until f; exist_simpl.
      Qed.

      Lemma trapout_exist:
        forall habd habd' labd f,
          trapout_spec habd = Some habd'
          -> relate_RData f habd labd
          -> exists labd', trapout0_spec labd = Some labd' /\ relate_RData f habd' labd'
                           /\ PT habd' = PT habd
                           /\ ptpool habd' = ptpool habd
                           /\ CR3 labd' = CR3 labd
                           /\ pperm habd' = pperm habd
                           /\ idpde habd' = idpde habd.
      Proof.
        unfold trapout_spec, trapout0_spec; intros until f; exist_simpl.
      Qed.

      Lemma setPG_exist:
        forall habd habd' labd f,
          setPG1_spec habd = Some habd'
          -> high_level_invariant habd
          -> relate_RData f habd labd
          -> exists labd', setPG0_spec labd = Some labd' /\ relate_RData f habd' labd'
                           /\ PT habd' = PT habd
                           /\ ptpool habd' = ptpool habd
                           /\ CR3 labd' = CR3 labd
                           /\ pperm habd' = pperm habd
                           /\ idpde habd' = idpde habd.
      Proof.
        unfold setPG0_spec, setPG1_spec; intros until f.
        intros HP HINV HR; pose proof HR as HR'; inv HR; revert HP;
        subrewrite'; intros HQ; inv HINV. subdestruct.
        pose proof relate_PT_re as HPT.
        inv HPT. omega.
        destruct (CR3_valid_dec (GLOBP PTPool_LOC ofs)).
        + inv HQ; refine_split'; eauto 1. 
          inv HR'; constructor; trivial. 
        + elim n. unfold CR3_valid; eauto.
      Qed.
      
      Lemma match_PMapPool_Hide:
        forall s p p' ptp m f,
          (forall i v1 v2, ZMap.get i p = PGHide (PGPMap v1 v2) -> ZMap.get i p' = PGHide (PGPMap v1 v2)) ->
          match_PMapPool s ptp p m f ->
          match_PMapPool s ptp p' m f.
      Proof.
        intros. inv H0. econstructor; eauto.
        intros. specialize (H1 _ H0). inv H1.
        constructor. intros. specialize (H3 _ H1).
        destruct H3 as (v & HLD & HV & HM).
        refine_split'; eauto.
        inv HM; econstructor; eauto 2.
      Qed.

      Lemma pfree_exist:
        forall habd habd' labd i f,
          pfree'_spec i habd = Some habd'
          -> relate_RData f habd labd
          -> exists labd', pfree'_spec i labd = Some labd' /\ relate_RData f habd' labd'
                           /\ PT habd' = PT habd
                           /\ ptpool habd' = ptpool habd
                           /\ CR3 labd' = CR3 labd
                           /\ idpde habd' = idpde habd
                           /\ (forall i v1 v2, ZMap.get i (pperm habd) = PGHide (PGPMap v1 v2)->
                                               ZMap.get i (pperm habd') = PGHide (PGPMap v1 v2)).
      Proof.
        unfold pfree'_spec; intros until f.
        intros HP HR; pose proof HR as HR'; inv HR; revert HP;
        subrewrite'; intros HQ. pose proof pperm_re as Hp. subdestruct.
        assert (Hp': ZMap.get i (pperm labd) = PGAlloc).
        {
          specialize (pperm_re i). rewrite Hdestruct7 in pperm_re.
          inv pperm_re; reflexivity.
        }
        rewrite Hp'. inv HQ; refine_split'; eauto. 
        - inv HR'. constructor; trivial; simpl.
          intros i'. destruct (zeq i i'); subst.
          + repeat rewrite ZMap.gss. constructor.
          + repeat rewrite ZMap.gso; eauto.
        - simpl. intros.
          destruct (zeq i0 i); subst.
          + congruence.
          + rewrite ZMap.gso; eauto.
      Qed.

      Lemma container_alloc_exist:
        forall habd habd' labd i n f,
          container_alloc_spec n habd = Some (habd', i)
          -> relate_RData f habd labd
          -> high_level_invariant habd
          -> exists labd', container_alloc_spec n labd = Some (labd', i) /\ relate_RData f habd' labd'
                           /\ PT habd' = PT habd
                           /\ ptpool habd' = ptpool habd
                           /\ CR3 labd' = CR3 labd
                           /\ idpde habd' = idpde habd
                           /\ (forall i o, ZMap.get i (pperm habd) = PGHide o ->
                                           ZMap.get i (pperm habd') = PGHide o).
      Proof.
        unfold container_alloc_spec; intros until f; exist_simpl.
        - intros i'.
          destruct (zeq i i'); subst.
          + repeat rewrite ZMap.gss. constructor.
          + repeat rewrite ZMap.gso; eauto.
        - intros. destruct (zeq i0 i); subst.
          + specialize (valid_pperm_ppage _ H).
            destruct a as (Hrange & HNorm & ?).
            intros Hc. specialize (Hc i). inv HR'. exploit Hc.
            * subrewrite'. omega.
            * subrewrite'. intros [HF _].
              exploit HF. red; intros HF'; inv HF'.
              intros HF'. destruct HF' as [? HF'].
              destruct HNorm as (? & HNorm). congruence. 
          + rewrite ZMap.gso; eauto.
      Qed.

      Lemma PageI_4:
        forall i ofs,
          i * 4 <= ofs < i * 4 + size_chunk Mint32 ->
          PageI ofs = PageI (i * 4).
      Proof.
        simpl; intros.
        assert (HP: exists a, ofs = i * 4 + a
                              /\ 0<= a <= 3).
        {
          exists (ofs - i * 4). split; omega.
        }
        destruct HP as (a & Heq & Hrange). clear H.
        rewrite Heq. unfold PageI. clear Heq.
        assert (HP: exists b c, i = 1024 * b + c
                                /\ 0<= c < 1024).
        {
          exists (i/1024), (i mod 1024). split.
          apply Z_div_mod_eq. omega.
          apply Z_mod_lt. omega.
        }
        destruct HP as (b & c & Heq & Hrange').
        rewrite Heq. clear Heq.
        replace ((1024 * b + c) * 4) with (b * 4096 + c * 4) by omega.
        replace (b * 4096 + c * 4 + a) with (b * 4096 + (c * 4 + a)) by omega.
        assert (HT: 4096 <> 0) by omega.
        repeat rewrite Z_div_plus_full_l; try assumption.
        clear HT.
        repeat rewrite Zdiv_small. reflexivity.
        omega. omega.
      Qed.

      Lemma fload_exist:
        forall habd labd i z f,
          fload_spec i habd = Some z
          -> relate_RData f habd labd
          -> fload'_spec i labd = Some z.
      Proof.
        unfold fload_spec, fload'_spec; intros.
        revert H. inv H0. subrewrite.
        assert (HG: forall ofs',
                      i * 4 <= ofs' < i * 4 + size_chunk Mint32 ->
                      forall o, ZMap.get (PageI ofs') (pperm habd) <> PGHide o).
        {
          intros. erewrite PageI_4; eauto 1.
          subdestruct. 
        }
        specialize (FlatMem.load_inj _ _ Mint32 (i * 4) _ f flatmem_re refl_equal).
        subdestruct. intros (v2 & HLD & HVAL).
        rewrite HLD. inv HVAL. assumption.
      Qed.

      Lemma flatmem_copy_aux_load_other_plus:
        forall n h h' pp from to vadr o,
          ZMap.get (PageI to) pp = PGAlloc ->
          ZMap.get (PageI vadr) pp = PGHide o ->
          (4 | to) ->
          PageI to = PageI (to + (Z.of_nat (n + 1)) * 4 - 4) ->
          PageI (vadr) = PageI (vadr + 3) ->
          (4 | vadr) ->
          flatmem_copy_aux (n + 1) from to h = Some h' ->
          FlatMem.load Mint32 h vadr = FlatMem.load Mint32 h' vadr.
      Proof.
        intros until n.
        induction n.
        - simpl; intros. 
          subdestruct. inv H5.
          erewrite (FlatMem.load_store_other Mint32 h (FlatMem.store Mint32 h to (Vint i))); eauto 2.
          simpl.
          assert (~ ( vadr - 4 < to < vadr + 4)).
          {
            red; intros.
            assert (vadr <= to).
            {
              destruct H1 as (m & He).
              destruct H4 as (m' & He').
              subst.
              destruct (zle (m' -1) m).
              - omega.
              - omega.
            }
            assert (vadr <= to <= vadr + 3) by omega.
            exploit PageI_range; eauto.
            intros.
            assert (vadr <= vadr <= vadr + 3) by omega.            
            exploit PageI_range; eauto.
            intros. congruence.
          }
          omega.
        - simpl; intros. subdestruct.
          exploit (IHn (FlatMem.store Mint32 h to (Vint i))); try eapply H5; try eassumption.
          + erewrite PageI_range; eauto.
            eapply to_range.
          + apply to_add_divide; eauto.
          + eapply PageI_eq; eauto.
          + intros. erewrite <- H6.
            erewrite (FlatMem.load_store_other Mint32 h (FlatMem.store Mint32 h to (Vint i))); eauto 2.
            simpl.
          assert (~ ( vadr - 4 < to < vadr + 4)).
          {
            red; intros.
            assert (vadr <= to).
            {
              destruct H1 as (m & He).
              destruct H4 as (m' & He').
              subst.
              destruct (zle (m' -1) m).
              - omega.
              - omega.
            }
            assert (vadr <= to <= vadr + 3) by omega.
            exploit PageI_range; eauto.
            intros.
            assert (vadr <= vadr <= vadr + 3) by omega.            
            exploit PageI_range; eauto.
            intros. congruence.
          }
          omega.
      Qed.

      Lemma flatmem_copy_aux_load_other':
        forall n h h' pp from to o vadr,
          ZMap.get (PageI to) pp = PGAlloc ->
          ZMap.get (PageI vadr) pp = PGHide o ->
          (PgSize | to)  ->
          Z.of_nat n <= one_k ->
          PageI (vadr) = PageI (vadr + 3) ->
          (4 | vadr) ->
          flatmem_copy_aux n from to h = Some h' ->
          FlatMem.load Mint32 h vadr = FlatMem.load Mint32 h' vadr.
      Proof.
        destruct n; intros.
        - simpl in *. inv H5. trivial.
        - replace (S n) with ((n + 1)%nat) in * by omega.
          eapply flatmem_copy_aux_load_other_plus; eauto.
          + destruct H1 as (i & He).
            exists (i * 1024).
            subst. omega.
          + eapply PageI_divide; eauto.
      Qed.

      Lemma flatmem_copy_aux_load_other:
        forall vadr n h h' pp from to o,
          flatmem_copy_aux (Z.to_nat n) from to h = Some h' ->
          ZMap.get (PageI vadr) pp = PGHide o ->
          ZMap.get (PageI to) pp = PGAlloc ->
          (PgSize | to)  ->
          0 <= n <= one_k ->
          PageI (vadr) = PageI (vadr + 3) ->
          (4 | vadr) ->
          FlatMem.load Mint32 h vadr = FlatMem.load Mint32 h' vadr.
      Proof.
        intros.
        eapply flatmem_copy_aux_load_other'; eauto.
        rewrite Z2Nat.id; try omega.
      Qed.

      Lemma flatmem_copy_exist:
        forall habd habd' labd i from to s m f,
          flatmem_copy_spec i from to habd = Some habd'
          -> relate_RData f habd labd
          -> match_RData s habd m f
          -> exists labd', flatmem_copy0_spec i from to labd = Some labd' 
                           /\ relate_RData f habd' labd'
                           /\ PT habd' = PT habd
                           /\ ptpool habd' = ptpool habd
                           /\ CR3 labd' = CR3 labd
                           /\ pperm habd' = pperm habd
                           /\ idpde habd' = idpde habd.
      Proof.
        unfold flatmem_copy0_spec, flatmem_copy_spec; intros.
        revert H. pose proof H0 as HR.
        inv H0. subrewrite. subdestruct.
        assert (HW: ZMap.get (PageI from) (pperm labd) = PGAlloc).
        {
          specialize (pperm_re (PageI from)). 
          rewrite Hdestruct7 in pperm_re.
          inv pperm_re; reflexivity.
        }
        assert (HW': ZMap.get (PageI to) (pperm labd) = PGAlloc).
        {
          specialize (pperm_re (PageI to)). 
          rewrite Hdestruct8 in pperm_re.
          inv pperm_re; reflexivity.
        }
        rewrite HW, HW'.
        exploit flatmem_copy_aux_exists; eauto.
        intros (lh' & HCopy & Hinj).
        inv HQ.
        rewrite HCopy. refine_split'; trivial.
        inv HR.
        constructor; trivial; simpl. 
        - (* PMap *)
          constructor; intros. inv relate_PMap_re.
          (*erewrite FlatMem.load_store_other; eauto 2. simpl.
          assert (~ pi * PgSize + vadr * 4 - size_chunk t < ofs < pi * PgSize + vadr * 4 + 4).
          {
            red; intros.
            assert (PageI ofs = pi).
            {
              revert H7 H5 H3. clear; intros.
              exploit  (Z_mod_lt ofs PgSize). omega.
              intros Hofs.
              rewrite (Z_div_mod_eq ofs PgSize) in H7 |-*; try omega.
              assert (HW: (ofs / 4096) = pi).
              {
                destruct (zeq pi (ofs / 4096)); subst; trivial.
                destruct (zle (pi + 1) (ofs / 4096)); rewrite_omega.
              }
              subst. unfold PageI.
              replace (PgSize * (ofs / PgSize)) with ((ofs / PgSize) * PgSize) by omega.
              rewrite Z_div_plus_full_l; [| omega].
              rewrite (Zdiv_small (ofs mod PgSize) PgSize); omega.
            }
            subst.*)
          specialize (H4 _ H _ H0 _ _ H2 _ H3).
          inv H1. inv H5. specialize (H1 _ H).
          inv H1. specialize (H5 _ H0).
          destruct H5 as (v0 & _ & _ & HMAT).
          unfold PMap, ZMap.t, PMap.t in H2, HMAT. rewrite H2 in HMAT.
          inv HMAT. 
          assert (HPA: PageI (pi * 4096 + vadr * 4) = pi).
          {
            revert H3. clear; intros.
            unfold PageI.
            rewrite Z_div_plus_full_l; [| omega].
            rewrite (Zdiv_small (vadr * 4) PgSize); rewrite_omega.
          }
          clear HW HW'.
          exploit (flatmem_copy_aux_load_other (pi * 4096 + vadr * 4)); eauto.
          + rewrite HPA. eassumption.
          + revert H3. clear; intros.
            unfold PageI.
            replace (pi * 4096 + vadr * 4 + 3)
            with (pi * 4096 + (vadr * 4 + 3)) by omega.
            repeat (rewrite Z_div_plus_full_l; [| omega]).
            rewrite (Zdiv_small (vadr * 4) PgSize); rewrite_omega.
            rewrite (Zdiv_small (vadr * 4 + 3) PgSize); rewrite_omega.
          + exists (pi * 1024 + vadr); omega.
                   + intros.
                     rewrite <- H1. eauto.
      Qed.

    End Exists.

    Ltac pattern2_refinement_simpl:=  
      pattern2_refinement_simpl' (@relate_AbData).

    Lemma passthrough_correct:
      sim (crel HDATA LDATA) mptintro_passthrough mcontainer.
    Proof.
      sim_oplus.
      - (* fload *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        match_external_states_simpl. 
        erewrite fload_exist; eauto 1. reflexivity.
      - (* fstore *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        exploit fstore_exist; eauto 1. intros (labd' & HP & HM & HN1 & HN2 & HN3 & HN4 & HN5).
        match_external_states_simpl.
      - (* flatmem_copy *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        exploit flatmem_copy_exist; eauto 1.
        intros (labd' & HP & HM & HN1 & HN2 & HN3 & HN4 & HN5).
        match_external_states_simpl.
      - apply vmxinfo_get_sim.
      - apply device_output_sim.
      - (* set PG *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        exploit setPG_exist; eauto 1; intros (labd' & HP & HM & HN1 & HN2 & HN3 & HN4 & HN5).
        match_external_states_simpl.
      - apply get_at_c_sim.
      - apply set_at_c0_sim.
      - (* pfree *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        exploit pfree_exist; eauto 1; intros (labd' & HP & HM & HN1 & HN2 & HN3 & HN4 & HN5).
        refine_split; try econstructor; eauto. repeat (econstructor; eauto).
        constructor; subrewrite'.
        eapply match_PMapPool_Hide; eassumption.
      - apply clearCR2_sim.
      - (* container_init *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        exploit container_init0_exist; eauto 1; intros (labd' & HP & HM & HN1 & HN2 & HN3 & HN4 & HN5).
        match_external_states_simpl.
      - apply container_get_parent_sim.
      - apply container_get_nchildren_sim.
      - apply container_get_quota_sim.
      - apply container_get_usage_sim.
      - apply container_can_consume_sim.
      - apply container_split_sim.
      - (* container_alloc *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        exploit container_alloc_exist; eauto 1. intros (labd' & HP & HM & HN1 & HN2 & HN3 & HN4 & HN5).
        refine_split; try econstructor; eauto. econstructor; eauto.
        constructor; eauto.
        constructor; subrewrite'.
        eapply match_PMapPool_Hide; try eassumption.
        intros; eapply HN5. assumption.
      - apply trapin_sim.
      - (* trapout *)
        layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
        inv match_extcall_states.
        exploit trapout_exist; eauto 1; intros (labd' & HP & HM & HN1 & HN2 & HN3 & HN4 & HN5).
        inv match_match. match_external_states_simpl.
      - apply hostin_sim.
      - apply hostout_sim.
      - apply trap_info_get_sim.
      - apply trap_info_ret_sim.
      - layer_sim_simpl.
        + eapply load_correct.
        + eapply store_correct.
    Qed.

  End WITHMEM.

End Refinement.
