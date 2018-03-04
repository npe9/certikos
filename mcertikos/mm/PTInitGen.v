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
(*          Refinement proof for PTInit layer                          *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide the contextual refinement proof between MPTKern layer and MPTInit layer*)
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
Require Import LoadStoreSem2.
Require Import AsmImplLemma.
Require Import LAsm.
Require Import RefinementTactic.
Require Import PrimSemantics.

Require Import MPTKern.
Require Import MPTInit.
Require Import AbstractDataType.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import compcert.cfrontend.Ctypes.
Require Import PTInitGenSpec.

Require Import LayerCalculusLemma.

Require Import XOmega.

(** * Notation of the refinement relation*)
Section Refinement.

  Local Open Scope string_scope.
  Local Open Scope error_monad_scope.
  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Notation HDATA := RData.
  Notation LDATA := RData.

  Notation HDATAOps := (cdata (cdata_ops := mptinit_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := mptintro_data_ops) LDATA).

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.
    Context `{Hmwd: UseMemWithData mem}.

    (** ** Definition the refinement relation: relate_RData + match_RData *)

    Record relate_RData (f: meminj) (hadt: HDATA) (ladt: LDATA) :=
      mkrelate_RData {
          flatmem_re: FlatMem.flatmem_inj (HP hadt) (HP ladt);
          vmxinfo_re: vmxinfo hadt = vmxinfo ladt;
          devout_re: devout hadt = devout ladt;
          ikern_re: ikern ladt = ikern hadt;
          pg_re: pg ladt = pg hadt;
          ihost_re: ihost ladt = ihost hadt;
          AC_re: AC ladt = AC hadt;
          ti_fst_re: (fst (ti ladt)) = (fst (ti hadt));
          ti_snd_re: val_inject f (snd (ti hadt)) (snd (ti ladt));
          nps_re: nps ladt = nps hadt;
          PT_re:  PT ladt = PT hadt;
          ptp_re: ptpool ladt = ptpool hadt;
          idpde_re: idpde ladt = idpde hadt;          
          ipt_re: ipt ladt = ipt hadt;
          init_re: init ladt = init hadt;
          pperm_re: pperm ladt = pperm hadt;
          LAT_re: relate_LATable (AT ladt) (LAT hadt)
        }.

    Inductive match_RData: stencil -> HDATA -> mem -> meminj -> Prop :=
    | MATCH_RDATA: forall habd m f s, match_RData s habd m f.   

    Local Hint Resolve MATCH_RDATA.

    Global Instance rel_ops: CompatRelOps HDATAOps LDATAOps :=
      {
        relate_AbData s f d1 d2 := relate_RData f d1 d2;
        match_AbData s d1 m f := match_RData s d1 m f;
        new_glbl := nil
      }.    

    (** ** Properties of relations*)
    Section Rel_Property.

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
        constructor; intros; simpl; trivial.
        eapply relate_incr; eauto.
        eapply relate_kernel_mode; eauto.
        eapply relate_observe; eauto.
      Qed.

    End Rel_Property.

    (** * Proofs the one-step forward simulations for the low level specifications*)
    Section OneStep_Forward_Relation.

      (** ** The low level specifications exist*)
      Section Exists.

        Lemma pt_init_exist:
          forall habd habd' labd i f,
            pt_init_spec i habd = ret habd'
            -> relate_RData f habd labd
            -> exists labd', MPTKern.pt_init_spec i labd = Some labd' /\ relate_RData f habd' labd'
                             /\ kernel_mode labd.
        Proof.
          unfold MPTKern.pt_init_spec, pt_init_spec; intros until f. exist_simpl.
          apply real_relate_LATable; auto.
        Qed.

        Lemma ptin_exist:
          forall habd habd' labd f,
            ptin_spec habd = Some habd'
            -> relate_RData f habd labd
            -> high_level_invariant habd
            -> exists labd', ptin'_spec labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold ptin_spec, ptin'_spec; intros until f.
          intros HP HR HINV. pose proof HR as HR'; inv HR. inv HINV.
          subrewrite'; subdestruct; simpl.
          rewrite e in *.
          destruct (PMap_kern_dec (ZMap.get 0 (ptpool habd))).          
          - refine_split'; eauto 1. inv HR'. inv HP. split; eauto 1. 
          - elim n; auto.
        Qed.

        Lemma setPT_exist:
          forall habd habd' labd i f,
            setPT_spec i habd = Some habd'
            -> relate_RData f habd labd
            -> high_level_invariant habd
            -> exists labd', setPT'_spec i labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold setPT_spec, setPT'_spec; intros until f. 
          intros HP HR HINV. pose proof HR as HR'.  inv HR. inv HINV.
          subrewrite'. subdestruct; simpl.
          destruct (PMap_valid_dec (ZMap.get i (ptpool habd))).          
          - refine_split'; eauto 1. inv HR'. inv HP; split; eauto 1.
          - elim n. apply valid_PMap; auto; omega.            
        Qed.

        Lemma vadr_PTX_range:
          forall vadr,
            0 <= vadr
            -> vadr < 4294967296
            -> 0 <= PTX vadr /\ PTX vadr <= PTX Int.max_unsigned.
        Proof.
          unfold PTX; simpl.
          change ((Int.max_unsigned / 4096) mod 1024) with 1023.
          intros.
          assert (Hrange: 0<= (vadr / 4096) mod 1024 < 1024) by
              (apply Z.mod_pos_bound; omega).
          omega.
        Qed.

        Lemma vadr_PDX_range:
          forall vadr,
            0 <= vadr
            -> vadr < 4294967296
            -> 0 <= PDX vadr /\ PDX vadr <= PDX Int.max_unsigned.
        Proof.
          unfold PDX; simpl.
          change (Int.max_unsigned / 4194304) with 1023.
          intros. xomega.
        Qed.
        
        Lemma ptFreePDE_exist:
          forall habd habd' labd n i f,
            ptFreePDE0_spec n i habd = ret (habd')
            -> relate_RData f habd labd
            -> high_level_invariant habd
            -> exists labd', ptFreePDE_spec n i labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold ptFreePDE_spec, ptFreePDE0_spec, pt_Arg'.
          intros until f; intros HP HR HH. pose proof HR as HR'.           
          pose proof (valid_PT_kern _ HH) as HPT.
          pose proof (valid_pperm_pmap _ HH) as HPMap.
          inv HR; revert HP. 
          rewrite (valid_pg_init habd) in *; eauto.
          subrewrite'; intros HQ.
          subdestruct.
          rewrite HPT; trivial.
          rewrite zeq_false; [| omega].
          assert (HR1: 0 <= n < num_proc) by omega.
          assert (HR2: 0 <= i < adr_max) by omega.
          specialize (HPMap _ HR1 _ HR2). rewrite Hdestruct5 in HPMap.
          destruct (HPMap _ _ refl_equal) as (Hrange & HW1 & HW2).
          generalize (LAT_re0 pi). subrewrite'.
          inversion 1. simpl in H2. subst.
          exploit valid_nps; eauto. 
          rewrite valid_pg_init; eauto.
          intros nps_range.
          rewrite zle_lt_true; [|omega].
          refine_split'; eauto 1. inv HR'.
          inv HQ; split; eauto 1; simpl.
          intros j. destruct (zeq j pi); subst.
          - repeat rewrite ZMap.gss. constructor; trivial.
          - repeat rewrite ZMap.gso; eauto.
        Qed.
        
        Lemma pfree_exist:
          forall habd habd' labd i f,
            pfree_spec i habd  = Some habd'
            -> relate_RData f habd labd
            -> high_level_invariant habd
            -> exists labd', pfree'_spec i labd = Some labd' /\ relate_RData f habd' labd'.
        Proof.
          unfold pfree_spec, pfree'_spec.
          intros until f; intros HP HR HH. pose proof HR as HR'.           
          inv HR; revert HP.
          rewrite (valid_pg_init habd) in *; eauto.
          subrewrite'; intros HQ.
          subdestruct. specialize (LAT_re0 i). rewrite Hdestruct4 in LAT_re0.
          inv LAT_re0. simpl. refine_split'; trivial.
          inv HR'. 
          inv HQ. constructor; eauto 1; simpl.
          apply relate_LATable_gss; eauto.
          constructor. trivial.
        Qed.

        Lemma first_free_relate_LATable:
          forall a la,
            relate_LATable a la ->
            LATable_nil la ->
            forall n i,
              (0 < i < n /\
               ZMap.get i la = LATValid false ATNorm nil /\
               (forall x,
                  0 < x < i -> ZMap.get x la <> LATValid false ATNorm nil)) ->
              0 < i < n /\
              (exists c, ZMap.get i a = ATValid false ATNorm c) /\
              (forall x,
                 0 < x < i ->
                 ~ (exists c : Z, ZMap.get x a = ATValid false ATNorm c)).
        Proof.
          intros. destruct H1 as (HT1 & HT2 & HT3).
          split; trivial. split.
          - specialize (H i). rewrite HT2 in H.
            inv H. simpl.
            refine_split'; trivial.
          - intros. specialize (HT3 _ H1). red; intros.
            elim HT3. destruct H2 as (c & HT1').
            specialize (H x). rewrite HT1' in H.
            inv H. specialize (H0 x).
            rewrite <- H6 in H0.
            specialize (H0 _ refl_equal). inv H0.
            trivial.
        Qed.

        Lemma first_fre_eq:
          forall a n i i0,
            (0 < i < n /\
             (exists c, ZMap.get i a = ATValid false ATNorm c) /\
             (forall x,
                0 < x < i ->
                ~ (exists c : Z, ZMap.get x a = ATValid false ATNorm c))) ->
            (0 < i0 < n /\
             (exists c, ZMap.get i0 a = ATValid false ATNorm c) /\
             (forall x,
                0 < x < i0 ->
                ~ (exists c : Z, ZMap.get x a = ATValid false ATNorm c))) ->
            i = i0.
        Proof.
          intros. destruct (zeq i i0); trivial.
          destruct (zlt i i0).
          - destruct H0 as (_ & _ & HP).
            destruct H as (HT1 & HT2 & HT3).
            assert (HR: 0 < i < i0) by omega.
            specialize (HP _ HR).
            elim HP; trivial.
          - destruct H0 as (HP1 & HP2 & HP3).
            destruct H as (HT1 & HT2 & HT3).
            assert (HR: 0 < i0 < i) by omega.
            specialize (HT3 _ HR).
            elim HT3; trivial.
        Qed.

        Lemma first_free_relate_LATable':
          forall a la,
            relate_LATable a la ->
            LATable_nil la ->
            forall n,
              (forall i, 0 < i < n -> ZMap.get i la <> LATValid false ATNorm nil) ->
              (forall i, 0 < i < n ->
                         ~ (exists c : Z, ZMap.get i a = ATValid false ATNorm c)).
        Proof.
          intros. specialize (H1 _ H2). red; intros.
          elim H1. destruct H3 as (c & HP).
          specialize (H i). rewrite HP in H.
          inv H. specialize (H0 i).
          rewrite <- H7 in H0.
          specialize (H0 _ refl_equal). inv H0.
          trivial.
        Qed.

        Lemma alloc_exist:
          forall habd habd' labd i n f,
            alloc_spec n habd = Some (habd', i)
            -> relate_RData f habd labd
            -> high_level_invariant habd
            -> exists labd', container_alloc_spec n labd = Some (labd', i) /\ relate_RData f habd' labd'.
        Proof.
          unfold alloc_spec, container_alloc_spec.
          intros until f; intros HP HR HH. pose proof HR as HR'.           
          inv HR; revert HP.
          rewrite (valid_pg_init habd) in *; eauto.
          subrewrite'; intros HQ.
          subdestruct; inv HQ; eauto.
          - pose proof (valid_LATable_nil _ HH) as Hnil.
            exploit first_free_relate_LATable; eauto.
            intros HP. 
            destruct (first_free (AT labd) (nps habd)).
            + destruct s.
              pose proof (first_fre_eq _ _ _ _ HP a0). subst.
              refine_split'; trivial.
              constructor; eauto 2; simpl.
              rewrite (valid_pg_init habd); eauto.
              apply relate_LATable_gss; eauto.
              constructor. trivial.
            + destruct HP as (HP1 & HP2 & _).
              specialize (n0 _ HP1). elim n0. trivial.
        Qed.

        Lemma ptInsertPTE_exist:
          forall habd habd' labd n vadr padr perm f,
            ptInsertPTE0_spec n vadr padr perm habd = Some habd'
            -> relate_RData f habd labd
            -> high_level_invariant habd
            -> exists labd', ptInsertPTE_spec n vadr padr perm labd = Some labd'
                             /\ relate_RData f habd' labd'.
        Proof.
          unfold ptInsertPTE_spec, ptInsertPTE0_spec, pt_Arg, pt_Arg'. intros until f.
          intros HP HR HINV; inv HR. inv HINV.
          rewrite valid_pg_init in *.
          subrewrite'; subdestruct; simpl.
          - rewrite valid_PT_kern; trivial.
            rewrite zeq_false; [|omega].
            unfold consistent_pmap in *.
            assert (HR1: 0 <= n < num_proc) by omega.
            assert (HR2: 0 <= vadr < adr_max) by omega.
            specialize (valid_pperm_pmap _ HR1 _ HR2). 
            rewrite Hdestruct6 in valid_pperm_pmap.
            destruct (valid_pperm_pmap _ _ refl_equal) as (Hrange & HW1 & HW2).
            exploit valid_nps; eauto. intros nps_range.
            rewrite zlt_lt_true; [|rewrite_omega].
            generalize (LAT_re0 padr). subrewrite'.
            intros HRe. inv HRe.
            rewrite zle_lt_true; trivial.
            refine_split'; trivial.
            inv HP.
            constructor; eauto; simpl.
            apply relate_LATable_gss; eauto.
            constructor. Opaque Z.of_nat. simpl.
            rewrite Nat2Z.inj_succ. 
            reflexivity.
          - rewrite valid_PT_kern; trivial.
            rewrite zeq_false; [|omega].
            unfold consistent_pmap in *.
            assert (HR1: 0 <= n < num_proc) by omega.
            assert (HR2: 0 <= vadr < adr_max) by omega.
            specialize (valid_pperm_pmap _ HR1 _ HR2). 
            rewrite Hdestruct6 in valid_pperm_pmap.
            destruct (valid_pperm_pmap _ _ refl_equal) as (Hrange & HW1 & HW2).
            exploit valid_nps; eauto. intros nps_range.
            rewrite zlt_lt_true; [|rewrite_omega].
            generalize (LAT_re0 padr). subrewrite'.
            intros HRe. inv HRe.
            rewrite zle_lt_true; trivial.
            refine_split'; trivial.
            inv HP.
            constructor; eauto; simpl.
            apply relate_LATable_gss; eauto.
            constructor. Opaque Z.of_nat. simpl.
            rewrite Nat2Z.inj_succ. 
            reflexivity.
        Qed.

        Lemma ptAllocPDE_exist:
          forall habd habd' labd n vadr v f,
            ptAllocPDE0_spec n vadr habd = Some (habd', v)
            -> relate_RData f habd labd
            -> high_level_invariant habd
            -> exists labd', ptAllocPDE_spec n vadr labd = Some (labd', v)
                             /\ relate_RData f habd' labd'.
        Proof.
          unfold ptAllocPDE_spec, ptAllocPDE0_spec, pt_Arg, pt_Arg'. intros until f.
          intros HP HR HINV; pose proof HR as HR'; inv HR. pose proof HINV as HINV'. inv HINV.
          rewrite valid_pg_init in *.
          subrewrite'; subdestruct; simpl; inv HP.
          - rewrite valid_PT_kern; trivial.
            rewrite zeq_false; [|omega].
            rename valid_LATable_nil into Hnil.
            exploit first_free_relate_LATable; eauto.
            intros HP.
            destruct (first_free (AT labd) (nps habd)).
            + destruct s.
              pose proof (first_fre_eq _ _ _ _ HP a2). subst.
              refine_split'; trivial.
              constructor; simpl;
              try (eapply FlatMem.free_page_inj'); eauto.
              apply relate_LATable_gss; eauto.
              constructor. trivial.
            + destruct HP as (HP1 & HP2 & _).
              specialize (n0 _ HP1). elim n0. trivial.
          - rewrite valid_PT_kern; trivial.
            rewrite zeq_false; [|omega].
            refine_split'; eauto.
        Qed.

        Lemma ptInsert_exist:
          forall habd habd' labd n vadr padr perm v f,
            ptInsert0_spec n vadr padr perm habd = Some (habd', v)
            -> relate_RData f habd labd
            -> high_level_invariant habd
            -> exists labd', ptInsert_spec n vadr padr perm labd = Some (labd', v)
                             /\ relate_RData f habd' labd'.
        Proof.
          unfold ptInsert_spec, ptInsert0_spec, pt_Arg'. intros until f.
          intros HP HR HINV; pose proof HR as HR'; inv HR. 
          pose proof HINV as HINT'; inv HINV.
          rewrite valid_pg_init in *.
          subrewrite'; subdestruct; simpl.
          - exploit ptInsertPTE_exist; eauto. inv HP.
            intros (labd' & HP & HR).
            rewrite HP. refine_split'; trivial.
          - exploit ptAllocPDE_exist; eauto. inv HP.
            intros (labd' & HP & HR).
            rewrite HP. rewrite zeq_true.
            refine_split'; trivial.
          - exploit ptAllocPDE_exist; eauto. inv HP.
            intros (labd' & HP & HR).
            rewrite HP. rewrite zeq_false; trivial.
            exploit ptInsertPTE_exist; eauto. 
            + eapply ptAllocPDE_high_level_inv; eauto.
            + intros (labd'' & HP' & HR'').
              rewrite HP'. refine_split'; trivial.
        Qed.

        Lemma remove_notIn:
          forall a l,
            ~ In a l ->
            Lremove a l = l.
        Proof.
          induction l; intros; trivial.
          - simpl in *.
            destruct (LATOwner_dec a a0); subst.
            + elim H; left; trivial.
            + rewrite IHl; trivial. red; intros.
              elim H. right; trivial.
        Qed.

        Lemma remove_lenght_one:
          forall a l,
            count_occ LATOwner_dec l a = 1%nat ->
            Z.of_nat (length (Lremove a l)) =
            Z.of_nat (length l) - 1.
        Proof.
          induction l; intros.
          - inv H.
          - simpl in *. destruct (LATOwner_dec a a0); subst.
            + destruct (LATOwner_dec a0 a0); try congruence. 
              assert (notInQ: ~ In a0 l).
              {
                red; intros.
                eapply (count_occ_In LATOwner_dec) in H0.
                inv H. rewrite H2 in H0.
                omega.
              }
              rewrite remove_notIn; eauto.
              rewrite Nat2Z.inj_succ. omega.
            + destruct (LATOwner_dec a0 a); try congruence.
              specialize (IHl H).
              simpl.
              repeat rewrite Nat2Z.inj_succ. 
              rewrite IHl. omega.
        Qed.

        Lemma length_positive:
          forall {A: Type} (a: A) l,
            In a l ->
            0 < Z.of_nat (length l).
        Proof.
          induction l; intros.
          - inv H.
          - simpl. rewrite Nat2Z.inj_succ. 
            omega.
        Qed.

        Lemma length_positive':
          forall a l,
            count_occ LATOwner_dec l a = 1%nat ->
            0 < Z.of_nat (length l).
        Proof.
          intros. eapply (length_positive a); eauto.
          apply (count_occ_In LATOwner_dec). rewrite H. 
          xomega.
        Qed.

        Lemma ptRmv_exist:
          forall habd habd' labd n vadr z f,
            ptRmv0_spec n vadr habd = Some (habd', z)
            -> relate_RData f habd labd
            -> high_level_invariant habd
            -> exists labd', ptRmv_spec n vadr labd = Some (labd', z) /\ relate_RData f habd' labd'.
        Proof.
          unfold ptRmv_spec, ptRmv0_spec, pt_Arg'. intros until f.
          intros HP HR HINV; pose proof HR as HR'; inv HR. 
          pose proof HINV as HINV'. inv HINV.
          rewrite valid_pg_init in *.
          subrewrite'; subdestruct; simpl; inv HP.
          - rewrite valid_PT_kern; trivial.
            rewrite zeq_false; [|omega].
            unfold consistent_pmap_domain in *.
            assert (HR1: 0 <= n < num_proc) by omega.
            assert (HR2: 0 <= vadr < adr_max) by omega.
            specialize (valid_pmap_domain _ HR1 _ HR2 _ _ Hdestruct5 _ _ Hdestruct6). 
            destruct valid_pmap_domain as (HT1 & HT2 & HT3).
            exploit valid_nps; eauto. intros nps_range.
            rewrite zlt_lt_true; [|omega].
            generalize (LAT_re0 z). subrewrite'.
            intros HRe. inv HRe.
            rewrite Hdestruct7 in HT3.
            destruct HT3 as (l' & HT31 & HT32).
            inv HT31.
            assert (Hlt: 0 < Z.of_nat (length l'))
              by (eapply length_positive'; eauto).
            rewrite zlt_le_true; trivial.
            refine_split'; trivial.
            constructor; eauto; simpl.
            apply relate_LATable_gss; eauto.
            constructor.
            + rewrite remove_lenght_one; eauto.
            + split; trivial.
          - rewrite valid_PT_kern; trivial.
            rewrite zeq_false; [|omega].
            refine_split'; trivial.
        Qed.

      End Exists.

      Lemma pt_init_spec_ref:
        compatsim (crel HDATA LDATA) (gensem pt_init_spec) pt_init_spec_low.
      Proof. 
        compatsim_simpl (@match_AbData).
        exploit pt_init_exist; eauto 1.
        intros [labd' [HP [HM Hkern]]].
        refine_split; try econstructor; eauto. constructor.
      Qed.

      Section PASSTHROUGH_PRIM.

        Global Instance: (LoadStoreProp (hflatmem_store:= flatmem_store) (lflatmem_store:= flatmem_store)).
        Proof.
          accessor_prop_tac.
          - eapply flatmem_store_exists; eauto.
        Qed.          

        Lemma passthrough_correct:
          sim (crel HDATA LDATA) mptinit_passthrough mptkern.
        Proof.
          sim_oplus.
          - apply fload_sim.
          - apply fstore_sim. 
          - apply flatmem_copy_sim.
          - apply vmxinfo_get_sim.          
          - apply device_output_sim.
          - (* pfree *)
            layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
            exploit pfree_exist; eauto 1; intros [labd' [HP HM]].
            match_external_states_simpl. 
          - (* setPT *)
            layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
            exploit setPT_exist; eauto 1; intros [labd' [HP HM]].
            match_external_states_simpl. 
          - apply ptRead_sim.
          - apply ptReadPDE_sim.
          - (* ptFreePDE0 *)
            layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
            exploit ptFreePDE_exist; eauto 1; intros [labd' [HP HM]].
            match_external_states_simpl. 
          - (* ptInsert *)
            layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
            exploit ptInsert_exist; eauto 1; intros [labd' [HP HM]].
            match_external_states_simpl. 
          - (* ptRmv*)
            layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
            exploit ptRmv_exist; eauto 1; intros [labd' [HP HM]].
            match_external_states_simpl. 
          - (* ptin*)
            layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
            inv match_extcall_states.
            exploit ptin_exist; eauto 1; intros [labd' [HP HM]].
            match_external_states_simpl. 
          - apply ptout_sim.
          - apply clearCR2_sim.
          - apply container_get_parent_sim.
          - apply container_get_nchildren_sim.
          - apply container_get_quota_sim.
          - apply container_get_usage_sim.
          - apply container_can_consume_sim.
          - apply container_split_sim.
          - (* alloc *)
            layer_sim_simpl; compatsim_simpl (@match_AbData); intros.
            exploit alloc_exist; eauto 1; intros [labd' [HP HM]].
            match_external_states_simpl. 
          - apply trapin_sim.
          - apply trapout_sim.
          - apply hostin_sim.
          - apply hostout_sim.
          - apply trap_info_get_sim.
          - apply trap_info_ret_sim.
          - layer_sim_simpl.
            + eapply load_correct2.
            + eapply store_correct2.
        Qed.

      End PASSTHROUGH_PRIM.

    End OneStep_Forward_Relation.

  End WITHMEM.

End Refinement.
