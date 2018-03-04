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

Require Export liblayers.logic.PTreeModules.
Require Export liblayers.logic.LayerLogicImpl.
Require Export liblayers.compcertx.ClightModules.
Require Export liblayers.compat.CompatLayers.
Require Export liblayers.compat.CompatGenSem.
Require Export liblayers.compat.CompatClightSem.
Require Export LayerCalculusLemma.
Require Export GenSem.
Require Export AbstractDataType.

Require Export LoadStoreSem1.
Require Export LoadStoreSem0.

Require Export MBoot.
Require Export PreInit.

Open Scope string_scope.
Open Scope error_monad_scope.
Open Scope Z_scope.

Notation HDATAOps := (@cdata _ _ RData mboot_data_ops mboot_data_prf).
Notation LDATAOps := (@cdata _ _ RData preinit_data_ops preinit_data_prf).

(** * Definition of the refinement relation*)
Section Refinement.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** ** Definition the refinement relation: relate_RData + match_RData *)    
    Section REFINEMENT_REL.
       
      (** Relation between the allocation table and the underline memory*)
      Inductive match_flatmem: stencil -> flatmem -> mem -> meminj -> Prop :=
      | MATCH_FM: forall fm m b s f,
                    (exists v1 v2, Mem.loadbytes m b 0 adr_max = Some v1 /\
                                   Mem.range_perm m b 0 adr_max Cur Writable /\
                                   FlatMem.loadbytes fm 0 adr_max = v2 /\
                                   list_forall2 (memval_inject f) v2 v1)
                    -> find_symbol s FlatMem_LOC = Some b
                    -> match_flatmem s fm m f.
      
      (** Relation between the new raw data at the higher layer with the mememory at lower layer*)
      Inductive match_RData: stencil -> HDATAOps -> mem -> meminj -> Prop :=
      | MATCH_RDATA: forall hadt m s f, 
                       match_flatmem s (HP hadt) m f
                       -> match_RData s hadt m f.
      
      (** Relation between the shared raw data at two layers*)
      Record relate_RData (f:meminj) (hadt: HDATAOps) (ladt: LDATAOps) :=
        mkrelate_RData {
            vmxinfo_re: vmxinfo hadt = vmxinfo ladt;
            MM_re: MM hadt = MM ladt;
            MMSize_re: MMSize hadt = MMSize ladt;
            CR3_re:  CR3 hadt = CR3 ladt;
            ikern_re: ikern hadt = ikern ladt;
            pg_re: pg hadt = pg ladt;
            ihost_re: ihost hadt = ihost ladt;
            ti_fst_re: (fst (ti hadt)) = (fst (ti ladt));
            ti_snd_re: val_inject f (snd (ti hadt)) (snd (ti ladt))
          }.

      Global Instance rel_ops: CompatRelOps HDATAOps LDATAOps :=
        {
          relate_AbData s f d1 d2 := relate_RData f d1 d2;
          match_AbData s d1 m f := match_RData s d1 m f;
          new_glbl := FlatMem_LOC :: nil
        }.

    End REFINEMENT_REL.

    (** ** Properties of relations*)
    Section Rel_Property.

      Lemma list_forall2_memval_compose:
        forall f j v1 v2 v3,
          list_forall2 (memval_inject f) v1 v2 ->
          list_forall2 (memval_inject j) v2 v3 ->
          list_forall2 (memval_inject (compose_meminj f j)) v1 v3.
      Proof.
        induction v1; inversion_clear 1; inversion_clear 1. 
        - constructor.
        - constructor.
          + eapply memval_inject_compose; try eassumption.
          + eapply IHv1; eassumption.
      Qed.

      Lemma list_forall2_memval_incr:
        forall f f' v1 v2,
          list_forall2 (memval_inject f) v1 v2 ->
          inject_incr f f' ->
          list_forall2 (memval_inject f') v1 v2.
      Proof.
        induction v1; inversion_clear 1; intros. 
        - constructor.
        - constructor.
          + eapply memval_inject_incr; try eassumption.
          + eapply IHv1; eassumption.
      Qed.

      Lemma inject_match_correct:
        forall s d1 m2 f m2' j,
          match_RData s d1 m2 f ->
          Mem.inject j m2 m2' ->
          inject_incr (Mem.flat_inj (genv_next s)) j ->
          match_RData s d1 m2' (compose_meminj f j).
      Proof.
        inversion 1; subst; intros. inv H0.
        assert (HFB: j b = Some (b, 0)).
        {
          eapply stencil_find_symbol_inject'; eauto.
        }
        econstructor; eauto; intros.        
        econstructor; eauto; intros.        
        destruct H3 as [v1[v2[HL1[HV1[HL2 HM]]]]].
        specialize (Mem.loadbytes_inject _ _  _ _ _ _ _ _ _ H1 HL1 HFB).
        repeat rewrite Z.add_0_r; intros [v1'[HLD1' HV1']].
        refine_split'; eauto.
        specialize(Mem.range_perm_inject _ _  _ _ _ _ _ _ _ _ HFB H1 HV1).
        repeat rewrite Z.add_0_r; trivial.
        eapply list_forall2_memval_compose; eassumption.
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
        intros. inv H. inv H2.
        econstructor; eauto.
        econstructor; eauto.
        destruct H as [v1[v2[HL1[HV1[HL2 HAT]]]]].
        eapply H0 in H3; simpl; eauto.
        repeat rewrite (Mem.loadbytes_store_other  _ _ _ _ _ _ H1); auto.
        refine_split'; eauto.
        unfold Mem.range_perm in *. intros.
        eapply Mem.perm_store_1; eauto.
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
        intros. inv H. inv H2.
        econstructor; eauto.
        econstructor; eauto. 
        destruct H as [v1[v2[HL1[HV1 [HL2 HAT]]]]].
        eapply H0 in H3; simpl; eauto.
        repeat rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ H1); eauto.
        refine_split'; eauto.
        unfold Mem.range_perm in *. intros.
        eapply Mem.perm_storebytes_1; eauto.
        omega.
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
        intros; inv H; inv H2.
        econstructor; eauto.
        econstructor; eauto.
        destruct H as [v1[v2[HL1[HV1 [HL2 HAT]]]]].
        eapply H0 in H3; simpl; eauto.
        repeat rewrite (Mem.loadbytes_free _ _ _ _ _ H1); auto.
        refine_split'; eauto.
        unfold Mem.range_perm in *. intros.
        eapply Mem.perm_free_1; eauto.
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
        intros. rename H1 into HF1, H2 into HB. inv H; inv H1.
        econstructor; eauto.
        econstructor; eauto. 
        destruct H as [v1[v2[HL1[HV1 [HL2 HAT]]]]].
        refine_split'; eauto.
        erewrite Mem.loadbytes_alloc_unchanged; eauto.
        - unfold Mem.range_perm in HV1.
          assert (HOS: 0<= 0 < adr_max) by omega.
          eapply Mem.perm_valid_block; eapply HV1; eassumption.
        - unfold Mem.range_perm in *. intros.
          eapply Mem.perm_alloc_1; eauto.
        - eapply list_forall2_memval_incr; eauto.
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
      Qed.

    End Rel_Property.

  End WITHMEM.

End Refinement.