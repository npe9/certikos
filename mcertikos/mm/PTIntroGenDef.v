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
Require Export Coqlib.
Require Export Errors.
Require Export AST.
Require Export Integers.
Require Export Floats.
Require Export Op.
Require Export Asm.
Require Export Events.
Require Export Globalenvs.
Require Export Smallstep.
Require Export Values.
Require Export Memory.
Require Export Maps.
Require Export CommonTactic.
Require Export AuxLemma.
Require Export FlatMemory.
Require Export AuxStateDataType.
Require Export Constant.
Require Export GlobIdent.
Require Export RealParams.
Require Export AsmImplLemma.
Require Export LAsm.
Require Export RefinementTactic.
Require Export PrimSemantics.
Require Export LoadStoreSem2.

Require Export liblayers.logic.PTreeModules.
Require Export liblayers.logic.LayerLogicImpl.
Require Export liblayers.compcertx.ClightModules.
Require Export liblayers.compat.CompatLayers.
Require Export liblayers.compat.CompatGenSem.
Require Export liblayers.compat.CompatClightSem.
Require Export LayerCalculusLemma.
Require Export GenSem.

Require Export AbstractDataType.
Require Export MContainer.
Require Export MPTIntro.
(*Require Export PTIntroGenSpec.*)

Open Scope string_scope.
Open Scope error_monad_scope.
Open Scope Z_scope.

Notation HDATA := RData.
Notation LDATA := RData.

Notation HDATAOps := (cdata (cdata_ops := mptintro_data_ops) HDATA).
Notation LDATAOps := (cdata (cdata_ops := mcontainer_data_ops) LDATA).

(** * Definition of the refinement relation*)
Section Refinement.

  Context `{real_params: RealParams}.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** ** Definition the refinement relation: relate_RData + match_RData *)    
    Section REFINEMENT_REL.
      
      Inductive match_PDE: stencil -> PDE -> val -> PPermT -> Z -> Z -> Prop :=
      | MATCH_PDE_UNDEF: forall v p n i s, 
                           match_PDE s PDEUndef v p n i
      | MATCH_PDE_UNP: forall p n i s, 
                         match_PDE s PDEUnPresent (Vint Int.zero) p n i
      | MATCH_PDE_KERN: forall p n i b v s, 
                          find_symbol s IDPMap_LOC = Some b ->
                          Int.unsigned v = i * PgSize + PT_PERM_PTU ->
                          match_PDE s PDEID (Vptr b v) p n i
      | MATCH_PDE_VALID: forall pdx v pi p n i s,
                           Int.unsigned v = pi * PgSize + PT_PERM_PTU ->
                           ZMap.get pi p = PGHide (PGPMap n i) ->
                           match_PDE s (PDEValid pi pdx) (Vint v) p n i.

      (** Relation between each page table and the underline memory*)
      Inductive match_PMap: stencil -> PMap -> PPermT -> mem -> block -> Z -> Prop :=
      | MATCH_PMAP: forall pt m n b p s,
                      (forall i, 
                         0 <= i <= PDX (Int.max_unsigned) -> 
                         exists v,
                           Mem.load Mint32 m b (n * PgSize + i * 4) = Some v /\
                           Mem.valid_access m Mint32 b (n * PgSize + i * 4) Writable /\
                           match_PDE s (ZMap.get i pt) v p n i)
                      -> match_PMap s pt p m b n.

      (** Relation between page table pool and the underline memory*)
      Inductive match_PMapPool: stencil -> PMapPool -> PPermT -> mem -> meminj -> Prop :=
      | MATCH_PMAPPOOL: forall ptp m b f p s,
                          (forall n, 
                             0<= n < num_proc -> 
                             match_PMap s (ZMap.get n ptp) p m b n)
                          -> find_symbol s PTPool_LOC = Some b
                          -> match_PMapPool s ptp p m f.

      Inductive match_IDPDE: IDPTEInfo -> val -> Z -> Z -> Prop :=
      | MATCH_IDPDE_UNDEF: forall v n i, 
                             match_IDPDE IDPTEUndef v n i
      | MATCH_IDPDE_VALID: forall v p n i j,
                             ZtoPerm v = Some p ->
                             Int.unsigned n = (i * one_k + j) * PgSize + v ->
                             match_IDPDE (IDPTEValid p) (Vint n) i j.

      Inductive match_IDPMap: stencil -> IDPDE -> mem -> meminj -> Prop :=
      | MATCH_IDPMAP: forall idpde m b f s,
                        (forall i, 
                           0 <= i <= PDX (Int.max_unsigned) -> 
                           forall j,
                             0 <= j <= PTX (Int.max_unsigned) ->
                             exists v,
                               Mem.load Mint32 m b (i * PgSize + j * 4) = Some v /\
                               Mem.valid_access m Mint32 b (i * PgSize + j * 4) Writable /\
                               match_IDPDE (ZMap.get j (ZMap.get i idpde)) v i j)
                        -> find_symbol s IDPMap_LOC = Some b
                        -> match_IDPMap s idpde m f.
      
      (** Relation between the new raw data at the higher layer with the mememory at lower layer*)
      Inductive match_RData: stencil -> HDATA -> mem -> meminj -> Prop :=
      | MATCH_RDATA: forall hadt m s f,
                       match_PMapPool s (ptpool hadt) (pperm hadt) m f
                       -> match_IDPMap s (idpde hadt) m f
                       -> match_RData s hadt m f.

      (** Relation between page table index and the undeline page table pointer*)
      Inductive relate_PT: Z -> globalpointer -> Prop :=
      | RELATE_PT_INT: relate_PT (-1) GLOBUndef
      | RELATE_PT_VALID: forall n ofs,
                           Int.unsigned ofs = n * PgSize ->
                           relate_PT n (GLOBP PTPool_LOC ofs).

      (** Relation between each entry of the second level page table and the underline memory*)
      Inductive relate_PTE: PTEInfo -> val -> Prop :=
      | RELATE_PTE_UNDEF: forall v, relate_PTE PTEUndef v
      | RELATE_PTE_UNP: relate_PTE PTEUnPresent (Vint Int.zero)
      | RELATE_PTE_VALID: forall n v p padr,
                            ZtoPerm v = Some p ->
                            Int.unsigned n = padr * PgSize + v ->
                            relate_PTE (PTEValid padr p) (Vint n).

      (** Relation between page table pool and the underline memory*)
      Inductive relate_PMapPool: PMapPool -> flatmem -> Prop :=
      | RELATE_PMAPPOOL: forall ptp hp,
                           (forall n, 
                              0<= n < num_proc ->
                              forall i, 
                                0 <= i <= PDX (Int.max_unsigned) -> 
                                forall pi pdx,
                                  ZMap.get i (ZMap.get n ptp) = PDEValid pi pdx ->
                                  forall vadr, 
                                    0 <= vadr <= PTX Int.max_unsigned -> 
                                    exists v',
                                      FlatMem.load Mint32 hp (pi * PgSize + vadr * 4) = v' /\
                                      relate_PTE (ZMap.get vadr pdx) v')
                           -> relate_PMapPool ptp hp.

      Inductive PPgInfo_leq': PPgInfo -> PPgInfo -> Prop :=
      | PGLE_REFL_FREE: PPgInfo_leq' (PGAlloc (*PGFreeable*)) (PGAlloc (*PGFreeable*))
      | PGLE_REFL_UNDEF: PPgInfo_leq' PGUndef PGUndef
      | PGLE_ALLOC_BUSY: forall o, PPgInfo_leq' (PGHide o) (PGAlloc (*PGFreeable*))
      (*| PGLE_ALLOC_FREE: PPgInfo_leq' (PGAlloc PGLoadable) (PGAlloc PGFreeable)*).
      
      Definition PPermT_les' (c1 c2: PPermT) :=
        forall i, PPgInfo_leq' (ZMap.get i c1) (ZMap.get i c2).
      
      (** Relation between the shared raw data at two layers*)
      Record relate_RData (f:meminj) (hadt: HDATA) (ladt: LDATA) :=
        mkrelate_RData {
            flatmem_re: FlatMem.flatmem_inj (HP hadt) (HP ladt);
            vmxinfo_re: vmxinfo hadt = vmxinfo ladt;
            devout_re: devout hadt = devout ladt;
            ikern_re: ikern hadt = ikern ladt;
            pg_re: pg hadt = pg ladt;
            ihost_re: ihost hadt = ihost ladt;
            AC_re: AC hadt = AC ladt;
            ti_fst_re: (fst (ti hadt)) = (fst (ti ladt));
            ti_snd_re: val_inject f (snd (ti hadt)) (snd (ti ladt));
            AT_re: AT hadt = AT ladt;
            nps_re: nps hadt = nps ladt;
            init_re: init hadt = init ladt;
            pperm_re: PPermT_les' (pperm hadt) (pperm ladt);
            relate_PT_re: relate_PT (PT hadt) (CR3 ladt);
            relate_PMap_re: relate_PMapPool (ptpool hadt) (HP ladt)
          }.

      Global Instance rel_ops: CompatRelOps HDATAOps LDATAOps :=
        {
          relate_AbData s f d1 d2 := relate_RData f d1 d2;
          match_AbData s d1 m f := match_RData s d1 m f;
          new_glbl := PTPool_LOC :: IDPMap_LOC :: nil
        }.    

    End REFINEMENT_REL.

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
        constructor.
        - inv H0. 
          assert (HFB0: j b = Some (b, 0)).
          {
            eapply stencil_find_symbol_inject'; eauto.
          }
          econstructor; eauto; intros.
          econstructor; eauto; intros.
          specialize (H4 _ H0). inv H4.
          specialize (H7 _ H6).
          destruct H7 as [v1[HL1[HV1 HM]]]. 
          specialize (Mem.load_inject _ _  _ _ _ _ _ _ _ H2 HL1 HFB0).
          repeat rewrite Z.add_0_r. 
          intros [v1'[HLD1' HV1']].
          refine_split'; eauto. 
          specialize(Mem.valid_access_inject _ _  _ _ _ _ _ _ _ HFB0 H2 HV1).
          rewrite Z.add_0_r; trivial. inv HM. 
          + econstructor; intros.
          + inv HV1'. constructor.
          + assert (HFB1: j b0 = Some (b0, 0)).
            {
              eapply stencil_find_symbol_inject'; eauto.
            }
            inv HV1'. rewrite H11 in HFB1. inv HFB1.
            rewrite Int.add_zero.
            constructor; eauto.
          + inv HV1'. constructor; assumption.
        - inv H1. 
          assert (HFB0: j b = Some (b, 0)).
          {
            eapply stencil_find_symbol_inject'; eauto.
          }
          econstructor; eauto; intros.
          specialize (H4 _ H1 _ H6). 
          destruct H4 as [v1[HL1[HV1 HM]]]. 
          specialize (Mem.load_inject _ _  _ _ _ _ _ _ _ H2 HL1 HFB0).
          repeat rewrite Z.add_0_r. 
          intros [v1'[HLD1' HV1']].
          refine_split'; eauto. 
          specialize(Mem.valid_access_inject _ _  _ _ _ _ _ _ _ HFB0 H2 HV1).
          rewrite Z.add_0_r; trivial. inv HM. 
          + constructor.
          + inv HV1'. econstructor; eauto.
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
        intros. inv H. constructor. 
        - inv H2.
          econstructor; eauto.
          intros. specialize (H _ H2).
          inv H. econstructor; intros.
          specialize (H5 _ H).
          destruct H5 as [v1[HL1[HV1 HM]]]. 
          eapply H0 in H4; simpl; eauto.
          repeat rewrite (Mem.load_store_other  _ _ _ _ _ _ H1); auto.
          refine_split'; eauto;
          try eapply Mem.store_valid_access_1; eauto.
        - inv H3.
          econstructor; eauto.
          intros. specialize (H _ H3 _ H5).
          destruct H as [v1[HL1[HV1 HM]]]. 
          eapply H0 in H4; simpl; eauto.
          repeat rewrite (Mem.load_store_other  _ _ _ _ _ _ H1); auto.
          refine_split'; eauto;
          try eapply Mem.store_valid_access_1; eauto.
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
        intros. inv H. constructor. 
        - inv H2.
          econstructor; eauto.
          intros. specialize (H _ H2).
          inv H. econstructor; intros.
          specialize (H5 _ H).
          destruct H5 as [v1[HL1[HV1 HM]]]. 
          eapply H0 in H4; simpl; eauto.
          repeat rewrite (Mem.load_storebytes_other _ _ _ _ _ H1); eauto.
          refine_split'; eauto;
          try eapply Mem.storebytes_valid_access_1; eauto.
        - inv H3.
          econstructor; eauto.
          intros. specialize (H _ H3 _ H5).
          destruct H as [v1[HL1[HV1 HM]]]. 
          eapply H0 in H4; simpl; eauto.
          repeat rewrite (Mem.load_storebytes_other _ _ _ _ _ H1); eauto.
          refine_split'; eauto;
          try eapply Mem.storebytes_valid_access_1; eauto.
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
        intros; inv H. constructor.
        - inv H2.
          econstructor; eauto.
          intros. specialize (H _ H2).
          inv H. econstructor; intros.
          specialize (H5 _ H).
          destruct H5 as [v1[HL1[HV1 HM]]]. 
          eapply H0 in H4; simpl; eauto.
          repeat rewrite (Mem.load_free _ _ _ _ _ H1); auto.
          refine_split'; eauto;
          try eapply Mem.valid_access_free_1; eauto.
        - inv H3.
          econstructor; eauto.
          intros. specialize (H _ H3 _ H5).
          destruct H as [v1[HL1[HV1 HM]]]. 
          eapply H0 in H4; simpl; eauto.
          repeat rewrite (Mem.load_free _ _ _ _ _ H1); auto.
          refine_split'; eauto;
          try eapply Mem.valid_access_free_1; eauto.
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
        intros. rename H1 into HF1, H2 into HB. 
        inv H. constructor.
        - inv H1.
          econstructor; eauto.
          intros. specialize (H _ H1).
          inv H. econstructor; intros.
          specialize (H6 _ H).
          destruct H6 as [v1[HL1[HV1 HM]]]. 
          refine_split'; eauto;
          try (apply (Mem.load_alloc_other _ _ _ _ _ H0));          
          try (eapply Mem.valid_access_alloc_other); eauto.
        - inv H2.
          econstructor; eauto.
          intros. specialize (H _ H2 _ H6).
          destruct H as [v1[HL1[HV1 HM]]]. 
          refine_split'; eauto;
          try (apply (Mem.load_alloc_other _ _ _ _ _ H0));          
          try (eapply Mem.valid_access_alloc_other); eauto.
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


  End WITHMEM.

End Refinement.
