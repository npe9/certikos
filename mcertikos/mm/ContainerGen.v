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
(*          Refinement proof for MALInitMContainer layer               *)
(*                                                                     *)
(*          David Costanzo <david.costanzo@yale.edu>                   *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MBoot layer and MALInit layer*)
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
Require Import LoadStoreSem1.
Require Import AsmImplLemma.
Require Import GenSem.
Require Import RefinementTactic.
Require Import PrimSemantics.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import compcert.cfrontend.Ctypes.
Require Import LayerCalculusLemma.

Require Import AbstractDataType.

Require Import MContainer.
Require Import MALT.

Require Import ProofIrrelevance.
Require Import ContainerGenSpec.

(** * Definition of the refinement relation*)
Section Refinement.  

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := mcontainer_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := malt_data_ops) LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** ** Definition the refinement relation: relate_RData + match_RData *)    
    Section REFINEMENT_REL.
      
      (** Relation between Z and int *)
      Inductive match_int: Z -> int -> Prop :=
      | MATCH_INT: forall v, 0 <= v <= Int.max_unsigned -> match_int v (Int.repr v).

      (** Relation between a single container and the underlying memory *)
      Inductive match_container: Container -> val -> val -> val -> val -> val -> Prop :=
      | MATCH_CONTAINER_UNUSED: 
          forall q u p c v1 v2 v3 v4, 
            match_container (mkContainer q u p c false) v1 v2 v3 v4 (Vint Int.zero)
      | MATCH_CONTAINER_USED: 
          forall q u p c, 
            match_int q (Int.repr q) -> match_int u (Int.repr u) -> match_int p (Int.repr p) ->
            match_int (Z_of_nat (length c)) (Int.repr (Z_of_nat (length c))) ->
            match_container (mkContainer q u p c true)
              (Vint (Int.repr q)) (Vint (Int.repr u)) (Vint (Int.repr p)) 
              (Vint (Int.repr (Z_of_nat (length c)))) (Vint Int.one).
      
      (** Relation between the container pool and the underlying memory *)
      Inductive match_RData: stencil -> HDATA -> mem -> meminj -> Prop :=
      | MATCH_CP: forall m b s hadt f,
                    (forall i, 0 <= i < num_id -> 
                       (exists v1 v2 v3 v4 v5, 
                          Mem.load Mint32 m b (i*CSIZE+QUOTA) = Some (Vint v1) /\
                          Mem.load Mint32 m b (i*CSIZE+USAGE) = Some (Vint v2) /\
                          Mem.load Mint32 m b (i*CSIZE+PARENT) = Some (Vint v3) /\
                          Mem.load Mint32 m b (i*CSIZE+NCHILDREN) = Some (Vint v4) /\
                          Mem.load Mint32 m b (i*CSIZE+USED) = Some (Vint v5) /\
                          Mem.valid_access m Mint32 b (i*CSIZE+QUOTA) Writable /\
                          Mem.valid_access m Mint32 b (i*CSIZE+USAGE) Writable /\
                          Mem.valid_access m Mint32 b (i*CSIZE+PARENT) Writable /\
                          Mem.valid_access m Mint32 b (i*CSIZE+NCHILDREN) Writable /\
                          Mem.valid_access m Mint32 b (i*CSIZE+USED) Writable /\
                          match_container (ZMap.get i (AC hadt)) (Vint v1) (Vint v2) 
                                             (Vint v3) (Vint v4) (Vint v5)))
                    -> find_symbol s AC_LOC = Some b
                    -> match_RData s hadt m f.
      
      (** Relation between the shared raw data at two layers*)
      Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
        mkrelate_RData {
            flatmem_re: FlatMem.flatmem_inj (HP hadt) (HP ladt);
            vmxinfo_re: vmxinfo hadt = vmxinfo ladt;
            devout_re: devout hadt = devout ladt;
            CR3_re:  CR3 hadt = CR3 ladt;
            ikern_re: ikern hadt = ikern ladt;
            pg_re: pg hadt = pg ladt;
            ihost_re: ihost hadt = ihost ladt;
            ti_fst_re: (fst (ti hadt)) = (fst (ti ladt));
            ti_snd_re: val_inject f (snd (ti hadt)) (snd (ti ladt));
            AT_re: AT hadt = AT ladt;
            nps_re: nps hadt = nps ladt;
            init_re: init hadt = init ladt;
            pperm_re: pperm hadt = pperm ladt
          }.

      Global Instance rel_ops: CompatRelOps HDATAOps LDATAOps :=
        {
          relate_AbData s f d1 d2 := relate_RData f d1 d2;
          match_AbData s d1 m f := match_RData s d1 m f;
          new_glbl := AC_LOC :: nil
        }.

      Definition AC_glbl : In AC_LOC new_glbl.
      Proof.
        simpl; auto.
      Defined.

    End REFINEMENT_REL.

    Lemma fields_sep :
      forall m k1 k2 a b : Z, 
        a <> b -> 0 <= m ->
        0 <= k1 -> k1 + size_chunk Mint32 <= m -> 0 <= k2 -> k2 + size_chunk Mint32 <= m -> 
        a * m + k1 + size_chunk Mint32 <= b * m + k2 \/ b * m + k2 + size_chunk Mint32 <= a * m + k1.
    Proof.
      intros m k1 k2 a1 a2 Ha_neq Hm_0 Hk1_0 Hle1 Hk2_0 Hle2.
      assert (a1 < a2 \/ a2 < a1) as Ha; try omega.
      destruct Ha; [left | right].
      apply Z.le_trans with (m := a1 * m + m); try omega.
      replace (a1 * m + m) with ((a1 + 1) * m).
      assert (a1 + 1 <= a2) as Hle_a; try omega.
      apply Z.mul_le_mono_nonneg_r with (p := m) in Hle_a; auto; omega.
      rewrite Z.mul_add_distr_r; omega.
      apply Z.le_trans with (m := a2 * m + m); try omega.
      replace (a2 * m + m) with ((a2 + 1) * m).
      assert (a2 + 1 <= a1) as Hle_a; try omega.
      apply Z.mul_le_mono_nonneg_r with (p := m) in Hle_a; auto; omega.
      rewrite Z.mul_add_distr_r; omega.
    Qed.

    Ltac sep' := apply fields_sep; simpl; auto; omega.
    Ltac sep := try solve [left; sep' | right; sep'].

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
        assert (HFB: j b = Some (b, 0)).
        {
          eapply stencil_find_symbol_inject'; eauto.
        }
        econstructor; eauto; intros i Hi.
        destruct (H0 i Hi) as [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
        exists v1, v2, v3, v4, v5.
        refine_split; auto.
        specialize (Mem.load_inject _ _  _ _ _ _ _ _ _ H2 HL1 HFB).
        rewrite Z.add_0_r; intros [v1' [HL1' Hv1']]; inv Hv1'; auto.
        specialize (Mem.load_inject _ _  _ _ _ _ _ _ _ H2 HL2 HFB).
        rewrite Z.add_0_r; intros [v1' [HL2' Hv2']]; inv Hv2'; auto.
        specialize (Mem.load_inject _ _  _ _ _ _ _ _ _ H2 HL3 HFB).
        rewrite Z.add_0_r; intros [v1' [HL3' Hv3']]; inv Hv3'; auto.
        specialize (Mem.load_inject _ _  _ _ _ _ _ _ _ H2 HL4 HFB).
        rewrite Z.add_0_r; intros [v1' [HL4' Hv4']]; inv Hv4'; auto.
        specialize (Mem.load_inject _ _  _ _ _ _ _ _ _ H2 HL5 HFB).
        rewrite Z.add_0_r; intros [v1' [HL5' Hv5']]; inv Hv5'; auto.
        specialize(Mem.valid_access_inject _ _  _ _ _ _ _ _ _ HFB H2 HA1).
        rewrite Z.add_0_r; auto.
        specialize(Mem.valid_access_inject _ _  _ _ _ _ _ _ _ HFB H2 HA2).
        rewrite Z.add_0_r; auto.
        specialize(Mem.valid_access_inject _ _  _ _ _ _ _ _ _ HFB H2 HA3).
        rewrite Z.add_0_r; auto.
        specialize(Mem.valid_access_inject _ _  _ _ _ _ _ _ _ HFB H2 HA4).
        rewrite Z.add_0_r; auto.
        specialize(Mem.valid_access_inject _ _  _ _ _ _ _ _ _ HFB H2 HA5).
        rewrite Z.add_0_r; auto.
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
        intros; inv H.
        econstructor; eauto; intros i Hi.
        specialize (H0 _ _ AC_glbl H3).
        destruct (H2 i Hi) as [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
        exists v1, v2, v3, v4, v5.
        refine_split; auto; try solve [rewrite (Mem.load_store_other _ _ _ _ _ _ H1); auto]; 
                            try solve [eapply Mem.store_valid_access_1; eauto].
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
        intros; inv H.
        econstructor; eauto; intros i Hi.
        specialize (H0 _ _ AC_glbl H3).
        destruct (H2 i Hi) as [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
        exists v1, v2, v3, v4, v5.
        refine_split; auto; try solve [rewrite (Mem.load_storebytes_other _ _ _ _ _ H1); auto]; 
                            try solve [eapply Mem.storebytes_valid_access_1; eauto].
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
        intros; inv H.
        econstructor; eauto; intros i Hi.
        specialize (H0 _ _ AC_glbl H3).
        destruct (H2 i Hi) as [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
        exists v1, v2, v3, v4, v5.
        refine_split; auto; try solve [rewrite (Mem.load_free _ _ _ _ _ H1); auto]; 
                            try solve [eapply Mem.valid_access_free_1; eauto].
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
        intros; inv H.
        econstructor; eauto; intros i Hi.
        specialize (H4 _ _ AC_glbl H6).
        destruct (H5 i Hi) as [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
        exists v1, v2, v3, v4, v5.
        refine_split; auto; try solve [apply (Mem.load_alloc_other _ _ _ _ _ H0); auto]; 
                            try solve [eapply Mem.valid_access_alloc_other; eauto].
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

    (** * Proofs of the one-step forward simulations for the low level specifications *)
    Section OneStep_Forward_Relation.

      Section container_init_ref.

        Lemma container_init_spec_ref:
          compatsim (crel HDATA LDATA) (gensem container_init_spec) container_init_spec_low.
        Proof.
          compatsim_simpl (@match_AbData).
          assert (Hi0: 0 <= 0 < 64) by omega.
          assert (Hrq_range:= real_quota_range).
          destruct (H 0 Hi0) as [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
          simpl in *.
          assert (HA1old:= HA1).
          assert (HA2old:= HA2).
          assert (HA3old:= HA3).
          assert (HA4old:= HA4).
          assert (HA5old:= HA5).
          apply Mem.valid_access_store with (v := Vint (Int.repr real_quota)) in HA1.
          destruct HA1 as [m3 HA1].
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA1) in HA2.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA1) in HA3.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA1) in HA4.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA1) in HA5.
          apply Mem.valid_access_store with (v := Vint Int.zero) in HA2.
          destruct HA2 as [m4 HA2].
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2) in HA3.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2) in HA4.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2) in HA5.
          apply Mem.valid_access_store with (v := Vint Int.zero) in HA3.
          destruct HA3 as [m5 HA3].
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA3) in HA4.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA3) in HA5.
          apply Mem.valid_access_store with (v := Vint Int.zero) in HA4.
          destruct HA4 as [m6 HA4].
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA4) in HA5.
          apply Mem.valid_access_store with (v := Vint Int.one) in HA5.
          destruct HA5 as [m7 HA5].
          inv Hι.
          inv H4; inv H6.
          exists ι, Vundef, m7, (d2 {MM : real_mm} {MMSize : real_size} {vmxinfo : real_vmxinfo}
                                    {AT : real_AT (AT d2)} {nps : real_nps} {init : true}).
          repeat (apply conj).
          - apply (container_init_low_intro _ _ _ m7 m3 m4 m5 m6 d2 _ b); auto.
            functional inversion H1; inv match_related; unfold mem_init_spec; rewrites; auto.
            functional inversion H1; inv match_related; split; congruence.
          - constructor.
          - functional inversion H1; inv match_related.
            split; eauto; pattern2_refinement_simpl' (@relate_AbData).
            constructor; auto; simpl; congruence.
            econstructor; eauto.
            intros i' Hi'. unfold real_AC in *.
            destruct (zeq i' 0); subst; simpl.
            (* i' is 0 *)
            rewrite ZMap.gss.
            exists (Int.repr real_quota), Int.zero, Int.zero, Int.zero, Int.one.
            split.
              (* quota value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA3).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2).
              apply (Mem.load_store_same _ _ _ _ _ _ HA1).
              simpl; unfold USAGE; right; left; omega.
              simpl; unfold PARENT; right; left; omega.
              simpl; unfold NCHILDREN; right; left; omega.
              simpl; unfold USED; right; left; omega.
            split.
              (* usage value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA3).
              apply (Mem.load_store_same _ _ _ _ _ _ HA2).
              simpl; unfold PARENT; right; left; omega.
              simpl; unfold NCHILDREN; right; left; omega.
              simpl; unfold USED; right; left; omega.
            split.
              (* parent value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              apply (Mem.load_store_same _ _ _ _ _ _ HA3).
              simpl; unfold NCHILDREN; right; left; omega.
              simpl; unfold USED; right; left; omega.
            split.
              (* nchildren value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              apply (Mem.load_store_same _ _ _ _ _ _ HA4).
              simpl; unfold USED; right; left; omega.
            split.
              (* used value *)
              apply (Mem.load_store_same _ _ _ _ _ _ HA5).
            repeat (split; try solve [
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA5);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA4);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA3);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA1); auto]).
            constructor; constructor; unfold Int.max_unsigned; simpl; omega.
            (* i' is not 0 *)
            rewrite ZMap.gso; auto.
            destruct (H i' Hi') as 
                [v1'[v2'[v3'[v4'[v5'[HL1'[HL2'[HL3'[HL4'[HL5'[HA1'[HA2'[HA3'[HA4'[HA5' Hm']]]]]]]]]]]]]]].
            exists v1', v2', v3', v4', v5'.
            split.
              (* quota value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA3).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA1); auto.
              simpl; unfold QUOTA; unfold CSIZE; right; right; omega.
              simpl; unfold QUOTA; unfold USAGE; unfold CSIZE; right; right; omega.
              simpl; unfold QUOTA; unfold PARENT; unfold CSIZE; right; right; omega.
              simpl; unfold QUOTA; unfold NCHILDREN; unfold CSIZE; right; right; omega.
              simpl; unfold QUOTA; unfold USED; unfold CSIZE; right; right; omega.
            split.
              (* usage value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA3).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA1); auto.
              simpl; unfold USAGE; unfold QUOTA; unfold CSIZE; right; right; omega.
              simpl; unfold USAGE; unfold CSIZE; right; right; omega.
              simpl; unfold USAGE; unfold PARENT; unfold CSIZE; right; right; omega.
              simpl; unfold USAGE; unfold NCHILDREN; unfold CSIZE; right; right; omega.
              simpl; unfold USAGE; unfold USED; unfold CSIZE; right; right; omega.
            split.
              (* parent value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA3).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA1); auto.
              simpl; unfold PARENT; unfold QUOTA; unfold CSIZE; right; right; omega.
              simpl; unfold PARENT; unfold USAGE; unfold CSIZE; right; right; omega.
              simpl; unfold PARENT; unfold CSIZE; right; right; omega.
              simpl; unfold PARENT; unfold NCHILDREN; unfold CSIZE; right; right; omega.
              simpl; unfold PARENT; unfold USED; unfold CSIZE; right; right; omega.
            split.
              (* nchildren value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA3).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA1); auto.
              simpl; unfold NCHILDREN; unfold QUOTA; unfold CSIZE; right; right; omega.
              simpl; unfold NCHILDREN; unfold USAGE; unfold CSIZE; right; right; omega.
              simpl; unfold NCHILDREN; unfold PARENT; unfold CSIZE; right; right; omega.
              simpl; unfold NCHILDREN; unfold CSIZE; right; right; omega.
              simpl; unfold NCHILDREN; unfold USED; unfold CSIZE; right; right; omega.
            split.
              (* used value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA3).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA1); auto.
              simpl; unfold USED; unfold QUOTA; unfold CSIZE; right; right; omega.
              simpl; unfold USED; unfold USAGE; unfold CSIZE; right; right; omega.
              simpl; unfold USED; unfold PARENT; unfold CSIZE; right; right; omega.
              simpl; unfold USED; unfold NCHILDREN; unfold CSIZE; right; right; omega.
              simpl; unfold USED; unfold CSIZE; right; right; omega.
            repeat (split; try solve [
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA5);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA4);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA3);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA1); auto]).
            rewrite ZMap.gi.
            inv Hm'.
            constructor.
            pose proof (valid_preinit_container _ Hhigh' H6 _ Hi') as _x.
            rewrite <- H2 in _x; contradict _x; auto.
          - auto.
        Qed.

      End container_init_ref.

      Section container_get_parent_ref.

        Lemma container_get_parent_spec_ref:
          compatsim (crel HDATA LDATA) (gensem container_get_parent_spec) 
                    container_get_parent_spec_low.
        Proof.
          compatsim_simpl (@match_AbData).
          functional inversion H2; subst c.
          inv Hι.
          inv H8; inv H10.
          inv Hhigh'.
          destruct valid_container.
          specialize (cvalid_id _ H3).
          exists ι, (Vint z), m2, d2; repeat (apply conj).
          - econstructor; eauto.
            destruct (H (Int.unsigned i) cvalid_id) as 
                [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
            inv Hm.
            rewrite <- H7 in H3; inv H3.
            rewrite <- H6 in H1.
            simpl in H1; subst.
            rewrite Int.repr_unsigned in HL3; auto.
            simpl; inv match_related; split; congruence.
          - constructor.
          - assumption.
          - auto.
        Qed.

      End container_get_parent_ref.

      Section container_get_nchildren_ref.

        Lemma container_get_nchildren_spec_ref:
          compatsim (crel HDATA LDATA) (gensem container_get_nchildren_spec) 
                    container_get_nchildren_spec_low.
        Proof.
          compatsim_simpl (@match_AbData).
          functional inversion H2; subst c.
          inv Hι.
          inv H8; inv H10.
          inv Hhigh'.
          destruct valid_container.
          specialize (cvalid_id _ H3).
          exists ι, (Vint z), m2, d2; repeat (apply conj).
          - econstructor; eauto.
            destruct (H (Int.unsigned i) cvalid_id) as 
                [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
            inv Hm.
            rewrite <- H7 in H3; inv H3.
            rewrite <- H6 in H1.
            simpl in H1; rewrite H1 in HL4.
            rewrite Int.repr_unsigned in HL4; auto.
            simpl; inv match_related; split; congruence.
          - constructor.
          - assumption.
          - auto.
        Qed.

      End container_get_nchildren_ref.

      Section container_get_quota_ref.

        Lemma container_get_quota_spec_ref:
          compatsim (crel HDATA LDATA) (gensem container_get_quota_spec) 
                    container_get_quota_spec_low.
        Proof.
          compatsim_simpl (@match_AbData).
          functional inversion H2; subst c.
          inv Hι.
          inv H8; inv H10.
          inv Hhigh'.
          destruct valid_container.
          specialize (cvalid_id _ H3).
          exists ι, (Vint z), m2, d2; repeat (apply conj).
          - econstructor; eauto.
            destruct (H (Int.unsigned i) cvalid_id) as 
                [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
            inv Hm.
            rewrite <- H7 in H3; inv H3.
            rewrite <- H6 in H1.
            simpl in H1; subst.
            rewrite Int.repr_unsigned in HL1; auto.
            simpl; inv match_related; split; congruence.
          - constructor.
          - assumption.
          - auto.
        Qed.

      End container_get_quota_ref.

      Section container_get_usage_ref.

        Lemma container_get_usage_spec_ref:
          compatsim (crel HDATA LDATA) (gensem container_get_usage_spec) 
                    container_get_usage_spec_low.
        Proof.
          compatsim_simpl (@match_AbData).
          functional inversion H2; subst c.
          inv Hι.
          inv H8; inv H10.
          inv Hhigh'.
          destruct valid_container.
          specialize (cvalid_id _ H3).
          exists ι, (Vint z), m2, d2; repeat (apply conj).
          - econstructor; eauto.
            destruct (H (Int.unsigned i) cvalid_id) as 
                [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
            inv Hm.
            rewrite <- H7 in H3; inv H3.
            rewrite <- H6 in H1.
            simpl in H1; subst.
            rewrite Int.repr_unsigned in HL2; auto.
            simpl; inv match_related; split; congruence.
          - constructor.
          - assumption.
          - auto.
        Qed.

      End container_get_usage_ref.

      Section container_can_consume_ref.

        Lemma container_can_consume_spec_ref:
          compatsim (crel HDATA LDATA) (gensem container_can_consume_spec) 
                    container_can_consume_spec_low.
        Proof.
          compatsim_simpl (@match_AbData).          
          inv Hι.
          inv H4; inv H6.
          inv H4; inv H7.
          rename i0 into n.
          exists ι, (Vint z), m2, d2; repeat (apply conj).
          - functional inversion H2.
            * inv Hhigh'.
              destruct valid_container.
              specialize (cvalid_id _ H3).
              destruct (H (Int.unsigned i) cvalid_id) as 
                  [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
              inv Hm.
              rewrite <- H8 in H3; inv H3.
              replace z with 
                (match (Int.unsigned n <=? Int.unsigned (Int.repr (cquota (ZMap.get (Int.unsigned i) (AC d1')))), 
                        Int.unsigned (Int.repr (cusage (ZMap.get (Int.unsigned i) (AC d1')))) <=? 
                        Int.unsigned (Int.repr (cquota (ZMap.get (Int.unsigned i) (AC d1')))) - Int.unsigned n) with
                 | (true, true) => Int.one 
                 | _ => Int.zero end).
              econstructor; eauto.
              rewrite <- H7; auto.
              rewrite <- H7; auto.
              simpl; inv match_related; split; congruence.
              specialize (cvalid_quota _ H3); specialize (cvalid_usage _ H3).
              rewrite 2 Int.unsigned_repr; try omega.              
              assert (Hle1: Int.unsigned n <= cquota (ZMap.get (Int.unsigned i) (AC d1'))) by omega.
              assert (Hle2: cusage (ZMap.get (Int.unsigned i) (AC d1')) <=
                            cquota (ZMap.get (Int.unsigned i) (AC d1')) - Int.unsigned n) by omega.
              rewrite <- Z.leb_le in Hle1, Hle2; rewrite Hle1, Hle2.
              apply f_equal with (f := Int.repr) in H1.
              rewrite Int.repr_unsigned in H1; auto.
            * inv Hhigh'.
              destruct valid_container.
              specialize (cvalid_id _ H3).
              destruct (H (Int.unsigned i) cvalid_id) as 
                  [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
              inv Hm.
              rewrite <- H8 in H3; inv H3.
              replace z with 
                (match (Int.unsigned n <=? Int.unsigned (Int.repr (cquota (ZMap.get (Int.unsigned i) (AC d1')))), 
                        Int.unsigned (Int.repr (cusage (ZMap.get (Int.unsigned i) (AC d1')))) <=? 
                        Int.unsigned (Int.repr (cquota (ZMap.get (Int.unsigned i) (AC d1')))) - Int.unsigned n) with
                 | (true, true) => Int.one 
                 | _ => Int.zero end).
              econstructor; eauto.
              rewrite <- H7; auto.
              rewrite <- H7; auto.
              simpl; inv match_related; split; congruence.
              specialize (cvalid_quota _ H3); specialize (cvalid_usage _ H3).
              rewrite 2 Int.unsigned_repr; try omega.              
              assert (Hrange:= Int.unsigned_range n).
              assert (Hle: ~ Int.unsigned n <= cquota (ZMap.get (Int.unsigned i) (AC d1')) \/
                           ~ cusage (ZMap.get (Int.unsigned i) (AC d1')) <=
                               cquota (ZMap.get (Int.unsigned i) (AC d1')) - Int.unsigned n) by omega.
              rewrite <- Z.leb_le in Hle; rewrite <- Z.leb_le in Hle; destruct Hle as [Hle|Hle].
              destruct (Int.unsigned n <=? cquota (ZMap.get (Int.unsigned i) (AC d1'))).
              contradict Hle; auto.
              apply f_equal with (f := Int.repr) in H1.
              rewrite Int.repr_unsigned in H1; auto.
              destruct (cusage (ZMap.get (Int.unsigned i) (AC d1')) <=?
                        cquota (ZMap.get (Int.unsigned i) (AC d1')) - Int.unsigned n).
              contradict Hle; auto.
              apply f_equal with (f := Int.repr) in H1.
              rewrite Int.repr_unsigned in H1.
              destruct (Int.unsigned n <=? cquota (ZMap.get (Int.unsigned i) (AC d1'))); auto.
          - constructor.
          - assumption.
          - auto.
        Qed.

      End container_can_consume_ref.

      Section container_split_ref.        

        Lemma container_split_spec_ref:
          compatsim (crel HDATA LDATA) (gensem container_split_spec) 
                    container_split_spec_low.
        Proof.
          compatsim_simpl (@match_AbData).
          functional inversion H1; subst c child.
          replace z with (Int.repr (Int.unsigned z)); try apply Int.repr_unsigned.
          rewrite <- H3 in *; clear H3 z.
          rename i0 into n, i1 into j, H0 into Hfind, _x into Hj, _x0 into Hnc, 
            _x1 into Hn, H7 into Hused; clear H4 H5 H6.
          inv Hhigh'.
          destruct valid_container.
          assert (cvalid_id':= cvalid_id); specialize (cvalid_id _ Hused).
          destruct (H (Int.unsigned i) cvalid_id) as 
              [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
          destruct (H _ Hj) as 
              [v1z[v2z[v3z[v4z[v5z[HL1z[HL2z[HL3z[HL4z[HL5z[HA1z[HA2z[HA3z[HA4z[HA5z Hmz]]]]]]]]]]]]]]].
          inv Hm.
          rewrite <- H2 in Hused; inv Hused.
          inv Hι.
          inv H4; inv H6.
          inv H4; inv H13.
          simpl in *.
          assert (HA1old := HA1).
          assert (HA2old := HA2).
          assert (HA3old := HA3).
          assert (HA4old := HA4).
          assert (HA5old := HA5).
          assert (HA1zold := HA1z).
          assert (HA2zold := HA2z).
          assert (HA3zold := HA3z).
          assert (HA4zold := HA4z).
          assert (HA5zold := HA5z).
          apply Mem.valid_access_store with (v := Vint Int.one) in HA5z.
          destruct HA5z as [m3 HA5z].
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA5z) in HA1z.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA5z) in HA2z.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA5z) in HA3z.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA5z) in HA4z.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA5z) in HA2.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA5z) in HA4.
          apply Mem.valid_access_store with (v := Vint n) in HA1z.
          destruct HA1z as [m4 HA1z].
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA1z) in HA2z.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA1z) in HA3z.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA1z) in HA4z.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA1z) in HA2.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA1z) in HA4.
          apply Mem.valid_access_store with (v := Vint Int.zero) in HA2z.
          destruct HA2z as [m5 HA2z].
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2z) in HA3z.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2z) in HA4z.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2z) in HA2.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2z) in HA4.
          apply Mem.valid_access_store with (v := Vint i) in HA3z.
          destruct HA3z as [m6 HA3z].
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA3z) in HA4z.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA3z) in HA2.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA3z) in HA4.
          apply Mem.valid_access_store with (v := Vint Int.zero) in HA4z.
          destruct HA4z as [m7 HA4z].
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA4z) in HA2.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA4z) in HA4.
          apply Mem.valid_access_store with (v := Vint (Int.add (Int.repr u) n)) in HA2.
          destruct HA2 as [m8 HA2].
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2) in HA4.
          apply Mem.valid_access_store with (v := Vint (Int.add (Int.repr (Z.of_nat (length c))) Int.one)) in HA4.
          destruct HA4 as [m9 HA4].
          rename H7 into Hmq, H10 into Hmu, H11 into Hmp, H12 into Hmc.
          assert (Hmax:= max_unsigned_val).
          exists ι, (Vint (Int.repr j)), m9, d2; repeat (apply conj).
          - apply (container_split_low_step_intro _ _ _ _ 
                     (m3,d2) (m4,d2) (m5,d2) (m6,d2) (m7,d2) (m8,d2) 
                     b _ _ _ (Int.repr u) (Int.repr (Z.of_nat (length c)))); 
              try (rewrite Int.unsigned_repr by omega); auto;
              try solve [simpl; unfold lift; simpl;
                first [rewrite HA5z | rewrite HA1z | rewrite HA2z | rewrite HA3z | rewrite HA4z |
                       rewrite HA2 | rewrite HA4 | rewrite HL2 | rewrite HL4]; auto].
            rewrite Int.unsigned_repr.
            apply f_equal with (f:= cchildren) in H0; simpl in H0; subst; auto.
            inv Hmc; auto.
            simpl; inv match_related; split; congruence.
          - constructor.
          - split; eauto; pattern2_refinement_simpl' (@relate_AbData).
            inv match_related; constructor; auto.
            econstructor; eauto.
            assert (j <> Int.unsigned i) by (intro; subst; omega).
            assert (j < Int.unsigned i \/ j > Int.unsigned i) as Hzi by omega.
            intros i' Hi'.
            destruct (zeq i' j); subst; simpl.
            (** CASE 1: i' is the newly-added child **)
            rewrite ZMap.gss.
            exists (Int.repr (Int.unsigned n)), (Int.repr 0), (Int.repr (Int.unsigned i)), (Int.repr 0), Int.one.
            split.
              (* quota value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA3z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2z).
              rewrite Int.repr_unsigned; apply (Mem.load_store_same _ _ _ _ _ _ HA1z).
              simpl; unfold CSIZE; unfold QUOTA; unfold USAGE; right; left; omega.
              simpl; unfold CSIZE; unfold QUOTA; unfold PARENT; right; left; omega.
              simpl; unfold CSIZE; unfold QUOTA; unfold NCHILDREN; right; left; omega.
              simpl; unfold CSIZE; unfold QUOTA; unfold USAGE; destruct Hzi; 
                [right; left; omega | right; right; omega].
              simpl; unfold CSIZE; unfold QUOTA; unfold NCHILDREN; destruct Hzi; 
                [right; left; omega | right; right; omega].
            split.
              (* usage value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA3z).
              apply (Mem.load_store_same _ _ _ _ _ _ HA2z).
              simpl; unfold CSIZE; unfold USAGE; unfold PARENT; right; left; omega.
              simpl; unfold CSIZE; unfold USAGE; unfold NCHILDREN; right; left; omega.
              simpl; unfold CSIZE; unfold USAGE; unfold USAGE; destruct Hzi; 
                [right; left; omega | right; right; omega].
              simpl; unfold CSIZE; unfold USAGE; unfold NCHILDREN; destruct Hzi; 
                [right; left; omega | right; right; omega].
            split.
              (* parent value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4z).
              rewrite Int.repr_unsigned; apply (Mem.load_store_same _ _ _ _ _ _ HA3z).
              simpl; unfold CSIZE; unfold PARENT; unfold NCHILDREN; right; left; omega.
              simpl; unfold CSIZE; unfold PARENT; unfold USAGE; destruct Hzi; 
                [right; left; omega | right; right; omega].
              simpl; unfold CSIZE; unfold PARENT; unfold NCHILDREN; destruct Hzi; 
                [right; left; omega | right; right; omega].
            split.
              (* nchildren value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2).
              apply (Mem.load_store_same _ _ _ _ _ _ HA4z).
              simpl; unfold CSIZE; unfold NCHILDREN; unfold USAGE; destruct Hzi; 
                [right; left; omega | right; right; omega].
              simpl; unfold CSIZE; unfold NCHILDREN; unfold NCHILDREN; destruct Hzi; 
                [right; left; omega | right; right; omega].
            split.
              (* used value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA3z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA1z).
              apply (Mem.load_store_same _ _ _ _ _ _ HA5z).
              simpl; unfold CSIZE; unfold USED; unfold QUOTA; right; right; omega.
              simpl; unfold CSIZE; unfold USED; unfold USAGE; right; right; omega.
              simpl; unfold CSIZE; unfold USED; unfold PARENT; right; right; omega.
              simpl; unfold CSIZE; unfold USED; unfold NCHILDREN; right; right; omega.
              simpl; unfold CSIZE; unfold USED; unfold USAGE; destruct Hzi; 
                [right; left; omega | right; right; omega].
              simpl; unfold CSIZE; unfold USED; unfold NCHILDREN; destruct Hzi; 
                [right; left; omega | right; right; omega].
            repeat (split; try solve [
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA4);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA4z);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA3z);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2z);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA1z);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA5z); auto]).
            constructor; constructor; 
              try solve [apply Int.unsigned_range_2];
              try solve [unfold Int.max_unsigned; simpl; omega].
            rewrite ZMap.gso; auto.
            destruct (zeq i' (Int.unsigned i)); subst.
            (** CASE 2: i' is the parent that we split **)
            unfold update_cusage, update_cchildren; rewrite 2 ZMap.gss; simpl.
            exists (Int.repr q), (Int.repr (u + Int.unsigned n)), (Int.repr p), 
                   (Int.repr (Z.of_nat (length (j :: c)))), Int.one.
            split.
              (* quota value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA3z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA1z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5z); auto.
              simpl; unfold CSIZE; unfold QUOTA; unfold USED; destruct Hzi; 
                [right; right; omega | right; left; omega].
              simpl; unfold CSIZE; unfold QUOTA; unfold QUOTA; destruct Hzi; 
                [right; right; omega | right; left; omega].
              simpl; unfold CSIZE; unfold QUOTA; unfold USAGE; destruct Hzi; 
                [right; right; omega | right; left; omega].
              simpl; unfold CSIZE; unfold QUOTA; unfold PARENT; destruct Hzi; 
                [right; right; omega | right; left; omega].
              simpl; unfold CSIZE; unfold QUOTA; unfold NCHILDREN; destruct Hzi; 
                [right; right; omega | right; left; omega].
              simpl; unfold CSIZE; unfold QUOTA; unfold USAGE; right; left; omega.
              simpl; unfold CSIZE; unfold QUOTA; unfold NCHILDREN; right; left; omega.
            split.
              (* usage value *)
              rewrite Int.add_unsigned in HA2; rewrite Int.unsigned_repr in HA2.
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              apply (Mem.load_store_same _ _ _ _ _ _ HA2).
              simpl; unfold CSIZE; unfold USAGE; unfold NCHILDREN; right; left; omega.
              inv Hmu; auto.
            split.
              (* parent value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA3z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA1z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5z); auto.
              simpl; unfold CSIZE; unfold PARENT; unfold USED; destruct Hzi; 
                [right; right; omega | right; left; omega].
              simpl; unfold CSIZE; unfold PARENT; unfold QUOTA; destruct Hzi; 
                [right; right; omega | right; left; omega].
              simpl; unfold CSIZE; unfold PARENT; unfold USAGE; destruct Hzi; 
                [right; right; omega | right; left; omega].
              simpl; unfold CSIZE; unfold PARENT; unfold PARENT; destruct Hzi; 
                [right; right; omega | right; left; omega].
              simpl; unfold CSIZE; unfold PARENT; unfold NCHILDREN; destruct Hzi; 
                [right; right; omega | right; left; omega].
              simpl; unfold CSIZE; unfold PARENT; unfold USAGE; right; right; omega.
              simpl; unfold CSIZE; unfold PARENT; unfold NCHILDREN; right; left; omega.
            split.
              (* nchildren value *)
              rewrite Int.add_unsigned in HA4; rewrite Int.unsigned_repr in HA4.
              replace (Z.of_nat (length (j :: c))) with (Z.of_nat (length c) + 1).
              apply (Mem.load_store_same _ _ _ _ _ _ HA4).
              replace 1 with (Z.of_nat 1); try solve [simpl; auto].
              rewrite <- Nat2Z.inj_add; rewrite plus_comm; simpl; auto.
              inv Hmc; auto.
            split.
              (* used value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA3z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA1z).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5z); auto.
              simpl; unfold CSIZE; unfold USED; unfold USED; destruct Hzi; 
                [right; right; omega | right; left; omega].
              simpl; unfold CSIZE; unfold USED; unfold QUOTA; destruct Hzi; 
                [right; right; omega | right; left; omega].
              simpl; unfold CSIZE; unfold USED; unfold USAGE; destruct Hzi; 
                [right; right; omega | right; left; omega].
              simpl; unfold CSIZE; unfold USED; unfold PARENT; destruct Hzi; 
                [right; right; omega | right; left; omega].
              simpl; unfold CSIZE; unfold USED; unfold NCHILDREN; destruct Hzi; 
                [right; right; omega | right; left; omega].
              simpl; unfold CSIZE; unfold USED; unfold USAGE; right; right; omega.
              simpl; unfold CSIZE; unfold USED; unfold NCHILDREN; right; right; omega.
            repeat (split; try solve [
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA4);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA4z);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA3z);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2z);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA1z);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA5z); auto]).
            rewrite <- H0 in *; simpl in *.
            constructor; auto.
            constructor; split.
            apply Z.add_nonneg_nonneg.
            inv Hmu; omega.
            apply Int.unsigned_range_2.
            transitivity q; inv Hmq; omega.
            constructor; split.
            apply Zle_0_nat.
            change (length (j::c)) with (S (length c)); rewrite Nat2Z.inj_succ; omega.
            (* CASE 3: i' is an uninvolved container *)
            unfold update_cusage, update_cchildren; rewrite 2 ZMap.gso; auto.
            destruct (H _ Hi') as 
              [v1'[v2'[v3'[v4'[v5'[HL1'[HL2'[HL3'[HL4'[HL5'[HA1'[HA2'[HA3'[HA4'[HA5' Hm']]]]]]]]]]]]]]].
            exists v1', v2', v3', v4', v5'.            
            unfold CSIZE, QUOTA, USAGE, PARENT, NCHILDREN, USED in *.
            repeat (
              split; [rewrite (Mem.load_store_other _ _ _ _ _ _ HA4); sep;
                      rewrite (Mem.load_store_other _ _ _ _ _ _ HA2); sep;
                      rewrite (Mem.load_store_other _ _ _ _ _ _ HA4z); sep;
                      rewrite (Mem.load_store_other _ _ _ _ _ _ HA3z); sep;
                      rewrite (Mem.load_store_other _ _ _ _ _ _ HA2z); sep;
                      rewrite (Mem.load_store_other _ _ _ _ _ _ HA1z); sep;
                      rewrite (Mem.load_store_other _ _ _ _ _ _ HA5z); sep; auto|]).
            repeat (
                split; [apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA4);
                        apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2);
                        apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA4z);
                        apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA3z);
                        apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2z);
                        apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA1z);
                        apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA5z); auto|]); assumption.
          - auto.
        Qed.

      End container_split_ref.

(*
      Section container_revoke_ref.

        Lemma container_revoke_spec_ref:
          compatsim (crel HDATA LDATA) (gensem container_revoke_spec) 
                    container_revoke_spec_low.
        Proof.
          compatsim_simpl (@match_AbData).
          functional inversion H1; subst c p.
          inv Hι.
          inv H12; inv H14.
          inv Hhigh'.
          assert (cvalid_id' := cvalid_id).
          specialize (cvalid_id' _ H7).
          destruct (H (Int.unsigned i) cvalid_id') as 
              [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
          assert (Hp_used := H6); apply cvalid_id in Hp_used.
          destruct (H (cparent (ZMap.get (Int.unsigned i) (AC d1))) Hp_used) as 
              [v1p[v2p[v3p[v4p[v5p[HL1p[HL2p[HL3p[HL4p[HL5p[HA1p[HA2p[HA3p[HA4p[HA5p Hmp]]]]]]]]]]]]]]].
          assert (HA2pold := HA2p); assert (HA4pold := HA4p); assert (HA5old := HA5).
          apply Mem.valid_access_store with (v := Vint (Int.sub v2p v1)) in HA2p.
          destruct HA2p as [m3 HA2p].
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2p) in HA4p.
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2p) in HA5.
          apply Mem.valid_access_store with (v := Vint (Int.sub v4p Int.one)) in HA4p.
          destruct HA4p as [m4 HA4p].
          apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA4p) in HA5.
          apply Mem.valid_access_store with (v := Vint Int.zero) in HA5.
          destruct HA5 as [m5 HA5].
          exists ι, Vundef, m5, d2; repeat (apply conj).
          - inv Hm.
            rewrite <- H10 in H7; inv H7.
            rewrite <- H2 in *; simpl in *; subst c; simpl in *.
            inv Hmp.
            rewrite <- H10 in H6; inv H6.
            inv H17.
            rewrite <- (Int.unsigned_repr p) in HL2p; auto.
            rewrite <- (Int.unsigned_repr p) in HL4p; auto.
            rewrite <- (Int.unsigned_repr p) in HA2p; auto.
            rewrite <- (Int.unsigned_repr p) in HA4p; auto.
            apply (container_revoke_low_step_intro _ _ (m2,d2) (m5,d2) (m3,d2) (m4,d2) _ _ _ _ _ _ H0 HL1 HL3 HL2p HL4p).
            simpl; unfold lift; unfold lens_lift; simpl; rewrite HA2p; auto.
            simpl; unfold lift; unfold lens_lift; simpl; rewrite HA4p; auto.
            simpl; unfold lift; unfold lens_lift; simpl; rewrite HA5; auto.
            simpl; inv match_related; split; congruence.
          - constructor.
          - split; eauto; pattern2_refinement_simpl' (@relate_AbData).
            inv match_related; econstructor; eauto.            
            intros i' Hi'.
            destruct (zeq i' (Int.unsigned i)); subst.
            (* Case 1: i' is the container being revoked *)
            exists v1, v2, v3, v4, Int.zero.
            unfold CSIZE in *; unfold QUOTA in *; unfold USAGE in *; unfold PARENT in *; 
              unfold NCHILDREN in *; unfold USED in *.
            split.
              (* quota value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4p).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2p); auto.              
              right; apply Hsep; simpl; try omega; rewrite <- Z.eqb_neq; auto.
              right; apply Hsep; simpl; try omega; rewrite <- Z.eqb_neq; auto.
              simpl; right; left; omega.
            split.
              (* usage value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4p).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2p); auto.
              right; apply Hsep; simpl; try omega; rewrite <- Z.eqb_neq; auto.
              right; apply Hsep; simpl; try omega; rewrite <- Z.eqb_neq; auto.
              simpl; right; left; omega.
            split.
              (* parent value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4p).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2p); auto.
              right; apply Hsep; simpl; try omega; rewrite <- Z.eqb_neq; auto.
              right; apply Hsep; simpl; try omega; rewrite <- Z.eqb_neq; auto.
              simpl; right; left; omega.
            split.
              (* nchildren value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4p).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2p); auto.
              right; apply Hsep; simpl; try omega; rewrite <- Z.eqb_neq; auto.
              right; apply Hsep; simpl; try omega; rewrite <- Z.eqb_neq; auto.
              simpl; right; left; omega.
            split.
              (* used value *)
              apply (Mem.load_store_same _ _ _ _ _ _ HA5).
            repeat (split; try solve [
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA5);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA4p);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2p); auto]).
            simpl.
            rewrite ZMap.gso.
            rewrite ZMap.gss; constructor.
            rewrite <- Z.eqb_neq; auto.
            destruct (zeq i' (cparent (ZMap.get (Int.unsigned i) (AC d1)))); subst.
            (* Case 2: i' is the parent of the container being revoked *)
            exists v1p, (Int.sub v2p v1), v3p, (Int.sub v4p Int.one), v5p.
            unfold CSIZE in *; unfold QUOTA in *; unfold USAGE in *; unfold PARENT in *; 
              unfold NCHILDREN in *; unfold USED in *.
            split.
              (* quota value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4p).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2p); auto.
              simpl; right; left; omega.
              simpl; right; left; omega.
              right; apply Hsep; simpl; try omega; rewrite <- Z.eqb_neq; auto.
            split.
              (* usage value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4p).
              apply (Mem.load_store_same _ _ _ _ _ _ HA2p).
              simpl; right; left; omega.
              right; apply Hsep; simpl; try omega; rewrite <- Z.eqb_neq; auto.
            split.
              (* parent value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4p).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2p); auto.
              simpl; right; right; omega.
              simpl; right; left; omega.
              right; apply Hsep; simpl; try omega; rewrite <- Z.eqb_neq; auto.
            split.
              (* nchildren value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              apply (Mem.load_store_same _ _ _ _ _ _ HA4p).
              right; apply Hsep; simpl; try omega; rewrite <- Z.eqb_neq; auto.
            split.
              (* used value *)
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA5).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA4p).
              rewrite (Mem.load_store_other _ _ _ _ _ _ HA2p); auto.
              simpl; right; right; omega.
              simpl; right; right; omega.
              right; apply Hsep; simpl; try omega; rewrite <- Z.eqb_neq; auto.
            repeat (split; try solve [
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA5);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA4p);
              apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2p); auto]).
            simpl; rewrite ZMap.gss.
            inv Hmp.
            rewrite <- H10 in H6; inv H6.
            Print match_container.
            SearchAbout Int.repr Int.sub.
            rewrite 2 Int.sub_signed.
            Print match_container.
            replace (Int.signed (Int.repr (Z.of_nat (length c))) - Int.signed Int.one) with 
                    (Z.of_nat (length (remove zeq (Int.unsigned i) c))).
            Print match_container.
            subst p'.
            rewrite <- H2; simpl.
            replace (Int.signed (Int.repr u) - Int.signed v1) with (u - cquota (ZMap.get (Int.unsigned i) (AC d1))).
            constructor; auto.
            apply MATCH_CONTAINER_USED.
            constructor.
            (* Case 3: i' is an uninvoved container *)
          - auto.
        Qed.

      End container_revoke_ref.
*)

      Section container_alloc_ref.

        Lemma container_alloc_spec_ref:
          compatsim (crel HDATA LDATA) (gensem container_alloc_spec) 
                    container_alloc_spec_low.
        Proof.
          constructor; split; simpl in *; try reflexivity; [|apply res_le_error].
          intros s WB1 WB2 ι vargs1 m1 d1 vres1 m1' d1' vargs2 m2 d2
                  HWB _ Hlow Hhigh Hhigh' H Hι Hmd.
          compatsim_simpl_inv_match H Hmd @match_AbData.          
          inv Hι.
          inv H4; inv H6.
          inv Hhigh'.
          destruct valid_container.
          functional inversion H1; subst c.
          {
            (* usage < quota *)
            specialize (cvalid_id _ H4).
            destruct (H _ cvalid_id) as 
                [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
            assert (HA2old := HA2).
            apply Mem.valid_access_store with (v := Vint (Int.add v2 Int.one)) in HA2.
            destruct HA2 as [m2' HA2].
            exists ι, (Vint (Int.repr (Int.unsigned z))), m2', 
              (d2 {AT : ZMap.set i0 (ATValid true ATNorm 0) (AT d2)}
                  {pperm : ZMap.set i0 PGAlloc (pperm d2)}); repeat (apply conj).
            - econstructor; eauto.
              + unfold palloc'_spec; inv match_related; rewrites.
                rewrite <- AT_re0, <- nps_re0; rewrites; auto.
              + inv Hm.
                rewrite <- H11 in *; discriminate.
                rewrite <- H10, Z.ltb_lt in *.
                inv H16; inv H17; rewrite 2 Int.unsigned_repr; auto.
              + apply Int.unsigned_range_2.
              + simpl; inv match_related; split; congruence.
            - rewrite Int.repr_unsigned; constructor.
            - split; eauto; pattern2_refinement_simpl' (@relate_AbData); try congruence.
              econstructor; eauto.
              intros i' Hi'; unfold QUOTA, USAGE, PARENT, NCHILDREN, USED, CSIZE in *.
              simpl; zmap_solve; subst.
              (* Case 1: i' is the container being updated *)
              exists v1, (Int.add v2 Int.one), v3, v4, v5.
              repeat (split; try solve 
                        [rewrite (Mem.load_store_other _ _ _ _ _ _ HA2); auto; right; left; simpl; omega | 
                         rewrite (Mem.load_store_other _ _ _ _ _ _ HA2); auto; right; right; simpl; omega | 
                         apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2); auto]).
              rewrite (Mem.load_store_same _ _ _ _ _ _ HA2); auto.
              subst cur; inv Hm.
              rewrite <- H3 in *; discriminate.
              rewrite <- H2, Z.ltb_lt in *; simpl in *.
              inv H15; replace (Int.add (Int.repr u) Int.one) with (Int.repr (u+1)).
              constructor; auto.
              inv H14; constructor; omega.
              rewrite <- (Int.unsigned_repr _ H3) at 1; auto.
              (* Case 2: i' is an uninvolved container *)
              destruct (H _ Hi') as 
                  [v1'[v2'[v3'[v4'[v5'[HL1'[HL2'[HL3'[HL4'[HL5'[HA1'[HA2'[HA3'[HA4'[HA5' Hm']]]]]]]]]]]]]]].
              exists v1', v2', v3', v4', v5'.
              repeat (split; try solve 
                        [rewrite (Mem.load_store_other _ _ _ _ _ _ HA2); auto; sep | 
                         apply (Mem.store_valid_access_1 _ _ _ _ _ _ HA2); auto]); assumption.
            - auto.
          }
          {
            (* usage = quota *)
            subst; specialize (cvalid_id _ H4).
            destruct (H _ cvalid_id) as 
                [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
            exists ι, Vzero, m2, d2; repeat (apply conj). 
            - econstructor; eauto.
              inv Hm.
              rewrite <- H9 in *; discriminate.
              specialize (cvalid_usage _ H4).
              rewrite <- H2, Z.ltb_nlt in *; simpl in *.
              assert (u = q) by omega; subst; auto.
              simpl; inv match_related; split; congruence.
            - apply f_equal with (f:= Int.repr) in H3.
              rewrite Int.repr_unsigned in H3; subst; constructor.
            - split; eauto; pattern2_refinement_simpl' (@relate_AbData).
            - auto.
          }
        Qed.

      End container_alloc_ref.

(*
      Section container_free_ref.

        Lemma container_free_spec_ref:
          compatsim (crel HDATA LDATA) (gensem container_free_spec) 
                    container_free_spec_low.
        Proof.
          compatsim_simpl (@match_AbData).
          functional inversion H1; subst c cur.
          inv Hι.
          inv H8; inv H10.
          inv Hhigh'.
          specialize (cvalid_id _ H3).
          exists ι, Vundef, , d2; repeat (apply conj).
          - econstructor; eauto.
            destruct (H (Int.unsigned i) cvalid_id) as 
                [v1[v2[v3[v4[v5[HL1[HL2[HL3[HL4[HL5[HA1[HA2[HA3[HA4[HA5 Hm]]]]]]]]]]]]]]].
            inv Hm.
            rewrite <- H7 in H3; inv H3.
            rewrite <- H6 in H1.
            simpl in H1; subst.
            rewrite Int.repr_unsigned in HL2; auto.
            simpl; inv match_related; split; congruence.
          - constructor.
          - assumption.
          - auto.
        Qed.

      End container_free_ref.
*)

    Ltac pattern2_refinement_simpl:=  
      pattern2_refinement_simpl' (@relate_AbData).

    Global Instance: (LoadStoreProp (hflatmem_store:= flatmem_store) (lflatmem_store:= flatmem_store)).
    Proof.
      accessor_prop_tac.
      - eapply flatmem_store_exists; eauto.
      - functional inversion H6; simpl; econstructor; eauto.
    Qed.          

    Lemma passthrough_correct:
      sim (crel HDATA LDATA) mcontainer_passthrough malt.
    Proof.
      sim_oplus.
      - apply fload'_sim.
      - apply fstore0_sim.
      - apply flatmem_copy0_sim.
      - apply vmxinfo_get_sim.
      - apply device_output_sim.
      - apply setPG0_sim.
      - apply pfree'_sim.
      - apply clearCR2_sim.
      - apply setCR30_sim.
      - apply get_at_c_sim.
      - apply set_at_c0_sim.
      - apply trapin_sim.
      - apply trapout0_sim.
      - apply hostin_sim.
      - apply hostout_sim.
      - apply trap_info_get_sim.
      - apply trap_info_ret_sim.
      - layer_sim_simpl.
        + eapply load_correct1.
        + eapply store_correct1.
    Qed.

    End OneStep_Forward_Relation.

  End WITHMEM.

End Refinement.
