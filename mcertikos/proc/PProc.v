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
(*              Layers of VM: PProc                                    *)
(*                                                                     *)
(*          Provide the abstraction of PProc                           *)
(*                                                                     *)
(*          Haozhong Zhang <haozhong.zhang@yale.edu>                   *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the abstract data and the primitives for the PProc layer,
which will introduce the primtives of thread*)
Require Import Coqlib.
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Stacklayout.
Require Import Globalenvs.
Require Import AsmX.
Require Import Smallstep.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import FlatMemory.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import RealParams.
Require Import PrimSemantics.
Require Import LAsm.
Require Import LoadStoreSem2.
Require Import XOmega.
Require Import ObservationImpl.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import CalRealPTPool.
Require Import CalRealPT.
Require Import CalRealIDPDE.
Require Import CalRealInitPTE.
Require Import CalRealSMSPool.
Require Import CalRealProcModule.

Require Import INVLemmaContainer.
Require Import INVLemmaMemory.
Require Import INVLemmaThread.
Require Import INVLemmaProc.

Require Import AbstractDataType.

Require Export ObjCPU.
Require Export ObjFlatMem.
Require Export ObjContainer.
Require Export ObjVMM.
Require Export ObjLMM.
Require Export ObjShareMem.
Require Export ObjThread.
Require Export ObjProc.
Require Export ObjSyncIPC.

(** * Abstract Data and Primitives at this layer*)
Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  (** **Definition of the invariants at MPTNew layer*)
  (** [0th page map] is reserved for the kernel thread*)
  Record high_level_invariant (abd: RData) :=
    mkInvariant {
        valid_init_pg: init abd = pg abd;
        valid_nps: pg abd = true -> kern_low <= nps abd <= maxpage;
        valid_AT_kern: pg abd = true -> LAT_kern (LAT abd) (nps abd);
        valid_AT_usr: pg abd = true -> LAT_usr (LAT abd) (nps abd);
        valid_AT_nil: 
          forall i t l,
            ZMap.get i (LAT abd) = LATValid false t l -> l = nil;
        valid_kern: ikern abd = false -> pg abd = true;
        valid_ihost: ihost abd = false -> pg abd = true /\ ikern abd = true;
        valid_container: Container_valid (AC abd);
        valid_preinit_container: 
          init abd = false ->
          forall i, 0 <= i < num_id -> cused (ZMap.get i (AC abd)) = false;
        valid_quota_bounded: quota_bounded (AC abd) (LAT abd) (nps abd);
        valid_pperm_ppage: Lconsistent_ppage (LAT abd) (pperm abd) (nps abd);
        init_pperm: pg abd = false -> (pperm abd) = ZMap.init PGUndef;
        valid_PMap: pg abd = true -> 
                    (forall i, 0<= i < num_proc ->
                               PMap_valid (ZMap.get i (ptpool abd)));
        (* 0th page map is reserved for the kernel thread*)          
        valid_PT_kern: pg abd = true -> ikern abd = true -> (PT abd) = 0;
        valid_PMap_kern: pg abd = true -> PMap_kern (ZMap.get 0 (ptpool abd));
        valid_PT: pg abd = true -> 0<= PT abd < num_proc;
        valid_dirty: dirty_ppage' (pperm abd) (HP abd);

        valid_idpde: pg abd = true -> IDPDE_init (idpde abd);
        valid_pperm_pmap: consistent_pmap (ptpool abd) (pperm abd) (LAT abd) (nps abd);
        valid_pmap_domain: consistent_pmap_domain (ptpool abd) (pperm abd) (LAT abd) (nps abd);
        valid_lat_domain: consistent_lat_domain (ptpool abd) (LAT abd) (nps abd);

        valid_root: pg abd = true -> cused (ZMap.get 0 (AC abd)) = true;

        valid_TCB: pg abd = true -> AbTCBStrong_range (abtcb abd);
        valid_TDQ: pg abd = true -> AbQCorrect_range (abq abd);
        valid_notinQ: pg abd = true -> NotInQ (AC abd) (abtcb abd);
        valid_count: pg abd = true -> QCount (abtcb abd) (abq abd);
        valid_inQ: pg abd = true -> InQ (abtcb abd) (abq abd);

        valid_curid: 0 <= cid abd < num_proc;
        correct_curid: pg abd = true -> CurIDValid (cid abd) (AC abd) (abtcb abd);
        single_curid: pg abd = true -> SingleRun (cid abd) (abtcb abd);
        valid_chan: pg abd = true -> SyncChanPool_Valid (syncchpool abd);
        valid_init_PT_cid: ikern abd = false -> PT abd = cid abd;
        valid_ikern_ipt: ikern abd = ipt abd

      }.

  (** ** Definition of the abstract state ops *)
  Global Instance pproc_data_ops : CompatDataOps RData :=
    {
      empty_data := init_adt;
      high_level_invariant := high_level_invariant;
      low_level_invariant := low_level_invariant;
      kernel_mode adt := ikern adt = true /\ ihost adt = true;
      observe := ObservationImpl.observe
    }.

  (** ** Proofs that the initial abstract_data should satisfy the invariants*)    
  Section Property_Abstract_Data.

    Lemma empty_data_high_level_invariant:
      high_level_invariant init_adt.
    Proof.
      constructor; simpl; intros; auto; try inv H.
      - zmap_simpl; discriminate.
      - apply empty_container_valid.
      - zmap_simpl; auto.
      - unfold quota_bounded; simpl; omega.
      - eapply Lconsistent_ppage_init.
      - eapply dirty_ppage'_init.
      - eapply consistent_pmap_init.
      - eapply consistent_pmap_domain_init.
      - eapply consistent_lat_domain_init.
      - repeat rewrite ZMap.gi; intuition.
    Qed.

    (** ** Definition of the abstract state *)
    Global Instance pproc_data_prf : CompatData RData.
    Proof.
      constructor.
      - apply low_level_invariant_incr.
      - apply empty_data_low_level_invariant.
      - apply empty_data_high_level_invariant.
    Qed.

  End Property_Abstract_Data.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section INV.

    Section ALLOC.

      Section DIRTY_PPAGE'.

        Lemma dirty_ppage'_gso_alloc:
          forall pp h,
            dirty_ppage' pp h ->
            forall n,
              dirty_ppage' (ZMap.set n PGAlloc pp) h.
        Proof.
          intros. apply dirty_ppage'_gso; try assumption.
        Qed.

        (*Lemma dirty_ppage'_gso_undef:
          forall pp h,
            dirty_ppage' pp h ->
            forall n,
              dirty_ppage' (ZMap.set n PGUndef pp) h.
        Proof.
          intros. apply dirty_ppage'_gso; try assumption.
          red; intros; congruence.
        Qed.*)

      End DIRTY_PPAGE'.
      
      Lemma alloc_high_level_inv:
        forall d d' i n,
          alloc_spec i d = Some (d', n) ->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; eauto. 
        inv H0. constructor; simpl; eauto.
        - intros; eapply LAT_kern_norm; eauto. eapply _x.
        - intros; eapply LAT_usr_norm; eauto.
        - intros; zmap_solve; try discriminate; eauto.
        - eapply alloc_container_valid'; eauto.
        - intros; congruence.
        - apply alloc_quota_bounded in H; auto.
        - eapply Lconsistent_ppage_norm_alloc; eauto.
        - intros; congruence.
        - eapply dirty_ppage'_gso_alloc; eauto.
        - eapply consistent_pmap_gso_at_false; eauto. apply _x.
        - eapply consistent_pmap_domain_gso_at_false; eauto. apply _x.
        - eapply consistent_lat_domain_gss_nil; eauto.
        - zmap_solve.
        - intros; apply NotInQ_gso_true; auto.
        - intros; apply CurIDValid_gss_ac; auto.
      Qed.
      
      Lemma alloc_low_level_inv:
        forall d d' i n n',
          alloc_spec i d = Some (d', n) ->
          low_level_invariant n' d ->
          low_level_invariant n' d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        inv H0. constructor; eauto.
      Qed.

      Lemma alloc_kernel_mode:
        forall d d' i n,
          alloc_spec i d = Some (d', n) ->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; eauto.
      Qed.

      Global Instance alloc_inv: PreservesInvariants alloc_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply alloc_low_level_inv; eassumption.
        - eapply alloc_high_level_inv; eassumption.
        - eapply alloc_kernel_mode; eassumption.
      Qed.

    End ALLOC.

    (*Global Instance pfree_inv: PreservesInvariants pfree_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto 2.
      - intros; eapply LAT_kern_norm; eauto. 
      - intros; eapply LAT_usr_norm; eauto.
      - eapply Lconsistent_ppage_norm_undef; eauto.
      - eapply dirty_ppage_gso_undef; eauto.
      - eapply consistent_pmap_gso_pperm_alloc; eauto.
      - eapply consistent_pmap_domain_gso_at_0; eauto.
      - eapply consistent_lat_domain_gss_nil; eauto.
    Qed.*)

    Global Instance hostin_inv: PrimInvariants hostin_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance hostout_inv: PrimInvariants hostout_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance fstore_inv: PreservesInvariants fstore_spec.
    Proof.
      split; intros; inv_generic_sem H; inv H0; functional inversion H2.
      - functional inversion H. split; trivial.        
      - functional inversion H.
        split; subst; simpl;
        try (eapply dirty_ppage'_store_unmapped; try eassumption; try reflexivity); trivial.
      - functional inversion H0.
        split; simpl; try assumption.
    Qed.

    Section PTINSERT.
      
      Section PTINSERT_PTE.

        Lemma ptInsertPTE_high_level_inv:
          forall d d' n vadr padr p,
            ptInsertPTE0_spec n vadr padr p d = Some d' ->
            high_level_invariant d ->
            high_level_invariant d'.
        Proof.
          intros. functional inversion H; subst; eauto.
          inv H0; constructor_gso_simpl_tac; intros.
          - eapply LAT_kern_norm; eauto. 
          - eapply LAT_usr_norm; eauto.
          - zmap_solve; try discriminate; eauto.
          - apply ptInsertPTE0_quota_bounded in H; auto.
          - eapply Lconsistent_ppage_norm; eassumption.
          - eapply PMap_valid_gso_valid; eauto.
          - functional inversion H2. functional inversion H1. 
            eapply PMap_kern_gso; eauto.
          - functional inversion H2. functional inversion H0.
            eapply consistent_pmap_ptp_same; try eassumption.
            eapply consistent_pmap_gso_pperm_alloc'; eassumption.
          - functional inversion H2.
            eapply consistent_pmap_domain_append; eauto.
            destruct (ZMap.get pti pdt); try contradiction;
            red; intros (v0 & p0 & He); contra_inv. 
          - eapply consistent_lat_domain_gss_append; eauto.
            subst pti; destruct (ZMap.get (PTX vadr) pdt); try contradiction;
            red; intros (v0 & p0 & He); contra_inv. 
        Qed.

        Lemma ptInsertPTE_low_level_inv:
          forall d d' n vadr padr p n',
            ptInsertPTE0_spec n vadr padr p d = Some d' ->
            low_level_invariant n' d ->
            low_level_invariant n' d'.
        Proof.
          intros. functional inversion H; subst; eauto.
          inv H0. constructor; eauto.
        Qed.

        Lemma ptInsertPTE_kernel_mode:
          forall d d' n vadr padr p,
            ptInsertPTE0_spec n vadr padr p d = Some d' ->
            kernel_mode d ->
            kernel_mode d'.
        Proof.
          intros. functional inversion H; subst; eauto.
        Qed.

      End PTINSERT_PTE.

      Section PTALLOCPDE.

        Lemma ptAllocPDE_high_level_inv:
          forall d d' n vadr v,
            ptAllocPDE0_spec n vadr d = Some (d', v) ->
            high_level_invariant d ->
            high_level_invariant d'.
        Proof.
          intros. functional inversion H; subst; eauto. 
          inv H0; constructor_gso_simpl_tac; intros.
          - eapply LAT_kern_norm; eauto. eapply _x.
          - eapply LAT_usr_norm; eauto.
          - zmap_solve; try discriminate; eauto.
          - eapply alloc_container_valid'; eauto.
          - congruence.
          - apply ptAllocPDE0_quota_bounded in H; auto.
          - apply Lconsistent_ppage_norm_hide; try assumption.
          - congruence.
          - eapply PMap_valid_gso_pde_unp; eauto.
            eapply real_init_PTE_defined.
          - functional inversion H3. 
            eapply PMap_kern_gso; eauto.
          - eapply dirty_ppage'_gss; eauto.
          - eapply consistent_pmap_ptp_gss; eauto; apply _x.
          - eapply consistent_pmap_domain_gso_at_false; eauto; try apply _x.
            eapply consistent_pmap_domain_ptp_unp; eauto.
            apply real_init_PTE_unp.
          - apply consistent_lat_domain_gss_nil; eauto.
            apply consistent_lat_domain_gso_p; eauto.
          - zmap_solve.
          - apply NotInQ_gso_true; auto.
          - apply CurIDValid_gss_ac; auto.
        Qed.

        Lemma ptAllocPDE_low_level_inv:
          forall d d' n vadr v n',
            ptAllocPDE0_spec n vadr d = Some (d', v) ->
            low_level_invariant n' d ->
            low_level_invariant n' d'.
        Proof.
          intros. functional inversion H; subst; eauto.
          inv H0. constructor; eauto.
        Qed.

        Lemma ptAllocPDE_kernel_mode:
          forall d d' n vadr v,
            ptAllocPDE0_spec n vadr d = Some (d', v) ->
            kernel_mode d ->
            kernel_mode d'.
        Proof.
          intros. functional inversion H; subst; eauto.
        Qed.

      End PTALLOCPDE.

      Lemma ptInsert_high_level_inv:
        forall d d' n vadr padr p v,
          ptInsert0_spec n vadr padr p d = Some (d', v) ->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; eauto. 
        - eapply ptInsertPTE_high_level_inv; eassumption.
        - eapply ptAllocPDE_high_level_inv; eassumption.
        - eapply ptInsertPTE_high_level_inv; try eassumption.
          eapply ptAllocPDE_high_level_inv; eassumption.
      Qed.

      Lemma ptInsert_low_level_inv:
        forall d d' n vadr padr p n' v,
          ptInsert0_spec n vadr padr p d = Some (d', v) ->
          low_level_invariant n' d ->
          low_level_invariant n' d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        - eapply ptInsertPTE_low_level_inv; eassumption.
        - eapply ptAllocPDE_low_level_inv; eassumption.
        - eapply ptInsertPTE_low_level_inv; try eassumption.
          eapply ptAllocPDE_low_level_inv; eassumption.
      Qed.

      Lemma ptInsert_kernel_mode:
        forall d d' n vadr padr p v,
          ptInsert0_spec n vadr padr p d = Some (d', v) ->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        - eapply ptInsertPTE_kernel_mode; eassumption.
        - eapply ptAllocPDE_kernel_mode; eassumption.
        - eapply ptInsertPTE_kernel_mode; try eassumption.
          eapply ptAllocPDE_kernel_mode; eassumption.
      Qed.

    End PTINSERT.

    Section PTRESV.

      Lemma ptResv_high_level_inv:
        forall d d' n vadr p v,
          ptResv_spec n vadr p d = Some (d', v) ->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; eauto. 
        eapply ptInsert_high_level_inv; try eassumption.
        eapply alloc_high_level_inv; eassumption.
      Qed.

      Lemma ptResv_low_level_inv:
        forall d d' n vadr p n' v,
          ptResv_spec n vadr p d = Some (d', v) ->
          low_level_invariant n' d ->
          low_level_invariant n' d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        eapply ptInsert_low_level_inv; try eassumption.
        eapply alloc_low_level_inv; eassumption.
      Qed.

      Lemma ptResv_kernel_mode:
        forall d d' n vadr p v,
          ptResv_spec n vadr p d = Some (d', v) ->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        eapply ptInsert_kernel_mode; try eassumption.
        eapply alloc_kernel_mode; eassumption.
      Qed.

      Global Instance ptResv_inv: PreservesInvariants ptResv_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply ptResv_low_level_inv; eassumption.
        - eapply ptResv_high_level_inv; eassumption.
        - eapply ptResv_kernel_mode; eassumption.
      Qed.

    End PTRESV.

    Section OFFER_SHARE.

      Section PTRESV2.

        Lemma ptResv2_high_level_inv:
          forall d d' n vadr p n' vadr' p' v,
            ptResv2_spec n vadr p n' vadr' p' d = Some (d', v) ->
            high_level_invariant d ->
            high_level_invariant d'.
        Proof.
          intros; functional inversion H; subst; eauto;
          eapply ptInsert_high_level_inv; try eassumption.
          - eapply alloc_high_level_inv; eassumption.
          - eapply ptInsert_high_level_inv; try eassumption.
            eapply alloc_high_level_inv; eassumption.
        Qed.

        Lemma ptResv2_low_level_inv:
          forall d d' n vadr p n' vadr' p' l v,
            ptResv2_spec n vadr p n' vadr' p' d = Some (d', v) ->
            low_level_invariant l d ->
            low_level_invariant l d'.
        Proof.
          intros; functional inversion H; subst; eauto;
          eapply ptInsert_low_level_inv; try eassumption.
          - eapply alloc_low_level_inv; eassumption.
          - eapply ptInsert_low_level_inv; try eassumption.
            eapply alloc_low_level_inv; eassumption.
        Qed.

        Lemma ptResv2_kernel_mode:
          forall d d' n vadr p n' vadr' p' v,
            ptResv2_spec n vadr p n' vadr' p' d = Some (d', v) ->
            kernel_mode d ->
            kernel_mode d'.
        Proof.
          intros; functional inversion H; subst; eauto;
          eapply ptInsert_kernel_mode; try eassumption.
          - eapply alloc_kernel_mode; eassumption.
          - eapply ptInsert_kernel_mode; try eassumption.
            eapply alloc_kernel_mode; eassumption.
        Qed.

      End PTRESV2.

      Lemma offer_shared_mem_high_level_inv:
        forall d d' i1 i2 vadr v,
          offer_shared_mem_spec i1 i2 vadr d = Some (d', v) ->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros; functional inversion H; subst; eauto; try eassumption.
        - exploit ptResv2_high_level_inv; eauto.
          intros HP; inv HP. constructor; trivial.
        - exploit ptResv2_high_level_inv; eauto.
          intros HP; inv HP. constructor; trivial.
        - inv H0; constructor; trivial.
      Qed.

      Lemma offer_shared_mem_low_level_inv:
        forall d d' i1 i2 vadr v l,
          offer_shared_mem_spec i1 i2 vadr d = Some (d', v) ->
          low_level_invariant l d ->
          low_level_invariant l d'.
      Proof.
        intros; functional inversion H; subst; eauto; try eassumption.
        - exploit ptResv2_low_level_inv; eauto.
          intros HP; inv HP. constructor; trivial.
        - exploit ptResv2_low_level_inv; eauto.
          intros HP; inv HP. constructor; trivial.
        - inv H0; constructor; trivial.
      Qed.        

      Lemma offer_shared_mem_kernel_mode:
        forall d d' i1 i2 vadr v,
          offer_shared_mem_spec i1 i2 vadr d = Some (d', v) ->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros; functional inversion H; subst; eauto; try eassumption.
        - exploit ptResv2_kernel_mode; eauto.
        - exploit ptResv2_kernel_mode; eauto.
      Qed.        

      Global Instance offer_shared_mem_inv: 
        PreservesInvariants offer_shared_mem_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply offer_shared_mem_low_level_inv; eassumption.
        - eapply offer_shared_mem_high_level_inv; eassumption.
        - eapply offer_shared_mem_kernel_mode; eassumption.
      Qed.

    End OFFER_SHARE.

    Global Instance shared_mem_status_inv: 
      PreservesInvariants shared_mem_status_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto 2.
    Qed.

    Local Opaque remove.

    Global Instance thread_yield_inv: ThreadScheduleInvariants thread_yield_spec.
    Proof.
      constructor; intros; functional inversion H. 
      - inv H1. constructor; trivial. 
        eapply kctxt_inject_neutral_gss_mem; eauto.
      - inv H0. subst.
        assert (HOS: 0<= num_chan <= num_chan) by omega.
        exploit last_range_AbQ; eauto. intros Hrange.
        constructor; auto; simpl in *; intros; try congruence.
        + eapply AbTCBStrong_range_gss_RUN; eauto. 
          eapply AbTCBStrong_range_gss_READY; eauto. 
        + eapply AbQCorrect_range_gss_remove'; eauto.
          eapply list_range_enqueue; eauto.
          eapply AbQCorrect_range_impl; eauto.
        + eapply NotInQ_gso_neg; eauto.
          eapply NotInQ_gso_ac; eauto. 
          eapply correct_curid0; eauto.
        + eapply QCount_gss_yield; eauto.
        + eapply InQ_gss_yield; eauto.
        + eapply CurIDValid_gss_last; eauto. 
        + eapply SingleRun_gss_gso_cid; eauto. congruence.
    Qed.

    Global Instance thread_sleep_inv: ThreadTransferInvariants thread_sleep_spec.
    Proof.
      constructor; intros; functional inversion H. 
      - inv H1. constructor; trivial. 
        eapply kctxt_inject_neutral_gss_mem; eauto.
      - inv H0. subst.
        assert (HOS: 0<= num_chan <= num_chan) by omega.
        assert (HNeq: 64 <> n') by omega.
        exploit last_range_AbQ; eauto. intros Hrange.
        assert (HOS': 0 <= n' <= num_proc) by omega.
        assert (Hcid: ZMap.get (cid d) (abtcb d) = AbTCBValid RUN (-1)) 
          by (eapply correct_curid0; eauto).
        constructor; auto; simpl in *; intros; try congruence.
        + eapply AbTCBStrong_range_gss_RUN; eauto. 
          eapply AbTCBStrong_range_gss_SLEEP; eauto. 
        + eapply AbQCorrect_range_gss_remove; eauto.
          * eapply AbQCorrect_range_gss_enqueue; eauto.
          * rewrite ZMap.gso; eauto. 
        + eapply NotInQ_gso_neg; eauto.
          eapply NotInQ_gso_ac; eauto. 
          eapply correct_curid0; eauto.
        + eapply QCount_gss_remove; eauto.
          * eapply QCount_gss_enqueue; eauto.
          * rewrite ZMap.gso; eauto. 
        + eapply InQ_gss_remove; eauto.
          * eapply InQ_gss_enqueue; eauto.
          * eapply QCount_gss_enqueue; eauto.
          * rewrite ZMap.gso; eauto.  
          * apply last_correct; eauto.
        + eapply CurIDValid_gss_last; eauto. 
        + eapply SingleRun_gss_gso_cid; eauto. congruence.
    Qed.

    (*Section SENDTOCHAN.

      Lemma sendto_chan_high_inv:
        forall d d' i0 i1 z,
          sendto_chan_spec i0 i1 d = Some (d', z)->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. inv H0; functional inversion H; subst; constructor; trivial; simpl.
        intros. eapply ChanPool_Valid_gss; eauto.
      Qed.

      Lemma sendto_chan_low_inv:
        forall d d' i0 i1 z n,
          sendto_chan_spec i0 i1 d = Some (d', z)->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. inv H0; functional inversion H; subst; constructor; trivial.
      Qed.

      Lemma sendto_chan_kernel_mode:
        forall d d' i0 i1 z,
          sendto_chan_spec i0 i1 d = Some (d', z)->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; constructor; trivial.
      Qed.

      Global Instance sendto_chan_inv: PreservesInvariants sendto_chan_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply sendto_chan_low_inv; eauto.
        - eapply sendto_chan_high_inv; eauto.
        - eapply sendto_chan_kernel_mode; eauto.
      Qed.

    End SENDTOCHAN.*)

    Section THREAD_WAKEUP.
      
      Lemma thread_wakeup_high_level_inv:
        forall d d' n,
          thread_wakeup_spec n d = Some d' ->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        inv H0. constructor; simpl; eauto; intros.
        - eapply AbTCBStrong_range_gss_READY; eauto. 
        - eapply AbQCorrect_range_gss_wakeup; eauto.
        - clear valid_curid0. eapply NotInQ_InQ_gss_wakeup; eauto.
        - eapply QCount_gss_wakeup; eauto.
        - eapply InQ_gss_wakeup; eauto.
        - eapply CurIDValid_gso_tcb; eauto.
          eapply last_neq_cid; eauto. omega.
        - eapply SingleRun_gso_state_READY; eauto.
      Qed.
      
      Lemma thread_wakeup_low_level_inv:
        forall d d' n n',
          thread_wakeup_spec n d = Some d' ->
          low_level_invariant n' d ->
          low_level_invariant n' d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        inv H0. constructor; eauto.
      Qed.

      Lemma thread_wakeup_kernel_mode:
        forall d d' n,
          thread_wakeup_spec n d = Some d' ->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; eauto.
      Qed.

      Global Instance thread_wakeup_inv: PreservesInvariants thread_wakeup_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply thread_wakeup_low_level_inv; eassumption.
        - eapply thread_wakeup_high_level_inv; eassumption.
        - eapply thread_wakeup_kernel_mode; eassumption.
      Qed.

    End THREAD_WAKEUP.

    Section SYNCSENDTOCHAN.

      Lemma syncsendto_chan_pre_high_inv:
        forall d d' i0 i1 i2 z,
          syncsendto_chan_pre_spec i0 i1 i2 d = Some (d', z)->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. inv H0; functional inversion H; subst; constructor; trivial; simpl.
        intros. eapply SyncChanPool_Valid_gss; eauto.
      Qed.

      Lemma syncsendto_chan_pre_low_inv:
        forall d d' i0 i1 i2 z n,
          syncsendto_chan_pre_spec i0 i1 i2 d = Some (d', z)->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. inv H0; functional inversion H; subst; constructor; trivial.
      Qed.

      Lemma syncsendto_chan_pre_kernel_mode:
        forall d d' i0 i1 i2 z,
          syncsendto_chan_pre_spec i0 i1 i2 d = Some (d', z)->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; constructor; trivial.
      Qed.

      Global Instance syncsendto_chan_pre_inv: PreservesInvariants syncsendto_chan_pre_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply syncsendto_chan_pre_low_inv; eauto.
        - eapply syncsendto_chan_pre_high_inv; eauto.
        - eapply syncsendto_chan_pre_kernel_mode; eauto.
      Qed.

      Lemma syncsendto_chan_post_high_inv:
        forall d d' z,
          syncsendto_chan_post_spec d = Some (d', z)->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. inv H0; functional inversion H; subst; constructor; trivial; simpl.
        intros. eapply SyncChanPool_Valid_gss; eauto.
      Qed.

      Lemma syncsendto_chan_post_low_inv:
        forall d d' z n,
          syncsendto_chan_post_spec d = Some (d', z)->
          low_level_invariant n d ->
          low_level_invariant n d'.
      Proof.
        intros. inv H0; functional inversion H; subst; constructor; trivial.
      Qed.

      Lemma syncsendto_chan_post_kernel_mode:
        forall d d' z,
          syncsendto_chan_post_spec d = Some (d', z)->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; constructor; trivial.
      Qed.

      Global Instance syncsendto_chan_post_inv: PreservesInvariants syncsendto_chan_post_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply syncsendto_chan_post_low_inv; eauto.
        - eapply syncsendto_chan_post_high_inv; eauto.
        - eapply syncsendto_chan_post_kernel_mode; eauto.
      Qed.

    End SYNCSENDTOCHAN.

    Section MEMCPY.

      Lemma dirty_ppage'_gss_copy_plus:
        forall n h h' pp from to,
          ZMap.get (PageI to) pp = PGAlloc ->
          (4 | to) ->
          PageI to = PageI (to + (Z.of_nat (n + 1)) * 4 - 4) ->
          dirty_ppage' pp h ->
          flatmem_copy_aux (n + 1) from to h = Some h' ->
          dirty_ppage' pp h'.
      Proof.
        intros until n.
        induction n.
        - simpl; intros. 
          subdestruct. inv H3.
          eapply dirty_ppage'_store_unmapped'; eauto.
          eapply to_mod_le; eauto.
        - simpl; intros. subdestruct.
          eapply (IHn (FlatMem.store Mint32 h to (Vint i)));
            try eapply H3.        
          + erewrite PageI_range; eauto.
            eapply to_range.
          + apply to_add_divide; eauto.
          + eapply PageI_eq; eauto.
          + eapply dirty_ppage'_store_unmapped'; eauto.
            eapply to_mod_le; eauto.
      Qed.

      Lemma dirty_ppage'_gss_copy':
        forall n h h' pp from to,
          ZMap.get (PageI to) pp = PGAlloc ->
          (PgSize | to)  ->
          Z.of_nat n <= one_k ->
          dirty_ppage' pp h ->
          flatmem_copy_aux n from to h = Some h' ->
          dirty_ppage' pp h'.
      Proof.
        destruct n; intros.
        - simpl in *. inv H3. assumption.
        - replace (S n) with ((n + 1)%nat) in * by omega.
          eapply dirty_ppage'_gss_copy_plus; eauto.
          destruct H0 as (i & He).
          exists (i * 1024).
          subst. omega.
          eapply PageI_divide; eauto.
      Qed.

      Lemma dirty_ppage'_gss_copy:
        forall n h h' pp from to,
          flatmem_copy_aux (Z.to_nat n) from to h = Some h' ->
          ZMap.get (PageI to) pp = PGAlloc ->
          (PgSize | to)  ->
          0 <= n <= one_k ->
          dirty_ppage' pp h ->
          dirty_ppage' pp h'.
      Proof.
        intros.
        eapply dirty_ppage'_gss_copy'; eauto.
        rewrite Z2Nat.id; try omega.
      Qed.

      Lemma flatmem_copy_high_level_inv:
        forall d d' from to len,
          flatmem_copy_spec len to from d = Some d'
          -> high_level_invariant d
          -> high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; eauto. 
        inv H0.
        constructor; simpl; intros;
        try eapply dirty_ppage'_gss_copy; eauto.
      Qed.

      Lemma flatmem_copy_low_level_inv:
        forall d d' from to len n,
          flatmem_copy_spec len to from d = Some d'
          -> low_level_invariant n d
          -> low_level_invariant n d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        inv H0. constructor; eauto 2.
      Qed.

      Lemma flatmem_copy_kernel_mode:
        forall d d' from to len,
          flatmem_copy_spec len to from d = Some d'
          -> kernel_mode d
          -> kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; eauto.
      Qed.

    End MEMCPY.

    Section SYNCRECEIVE_CHAN.
      
      Lemma syncreceive_chan_high_level_inv:
        forall fromid vaddr count d d' n,
          syncreceive_chan_spec fromid vaddr count d = Some (d', n) ->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; eauto. 
        exploit thread_wakeup_high_level_inv; eauto.
        exploit flatmem_copy_high_level_inv; eauto.
        intros Hh. inv Hh. constructor; eauto 2; simpl; intros.
        eapply SyncChanPool_Valid_gss; eauto.
      Qed.
      
      Lemma syncreceive_chan_low_level_inv:
        forall fromid vaddr count d d' n n',
          syncreceive_chan_spec fromid vaddr count d = Some (d', n) ->
          low_level_invariant n' d ->
          low_level_invariant n' d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        exploit thread_wakeup_low_level_inv; eauto.
        exploit flatmem_copy_low_level_inv; eauto.
        intros Hh. inv Hh. constructor; eauto 2.
      Qed.

      Lemma syncreceive_chan_kernel_mode:
        forall fromid vaddr count d d' n,
          syncreceive_chan_spec fromid vaddr count d = Some (d', n) ->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        exploit thread_wakeup_kernel_mode; eauto.
        exploit flatmem_copy_kernel_mode; eauto.
      Qed.

      Global Instance syncreceive_chan_inv: PreservesInvariants syncreceive_chan_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply syncreceive_chan_low_level_inv; eassumption.
        - eapply syncreceive_chan_high_level_inv; eassumption.
        - eapply syncreceive_chan_kernel_mode; eassumption.
      Qed.

    End SYNCRECEIVE_CHAN.

    Global Instance proc_init_inv: PreservesInvariants proc_init_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant.
      - apply real_nps_range.
      - apply real_lat_kern_valid.
      - apply real_lat_usr_valid.
      - assert (Hcases: (i0 < 0 \/ real_nps <= i0) \/ 0 <= i0 < real_nps) by omega.
        destruct Hcases.
        rewrite real_LAT_outside in H; eauto.
        destruct (zeq i0 0); subst.
        + rewrite (real_lat_kern_valid (LAT d)) in H; try omega; inv H; auto.
        + destruct (real_LAT_all_valid_false_nil (LAT d) i0); try omega; rewrites; auto.
      - apply real_container_valid.
      - apply real_quota_bounded.
      - rewrite init_pperm0; try assumption.
        apply Lreal_pperm_valid.        
      - eapply real_pt_PMap_valid; eauto.
      - apply real_pt_PMap_kern.
      - omega.
      - assumption.
      - apply real_idpde_init.
      - apply real_pt_consistent_pmap. 
      - apply real_pt_consistent_pmap_domain. 
      - apply Lreal_at_consistent_lat_domain.
      - apply real_abtcb_strong_range'; eauto.
      - apply real_abq_range; auto.
      - eapply real_abtcb_pb_notInQ'; eauto.
      - eapply real_abtcb_abq_QCount'; eauto.
      - eapply real_abq_tcb_inQ; eauto.
      - omega.
      - eapply real_abtcb_AC_CurIDValid; eauto. 
      - eapply real_abtcb_SingleRun; eauto. 
      - eapply real_syncchpool_valid'; eauto.
    Qed.

    Global Instance uctx_set_inv: PreservesInvariants uctx_set_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto 2.
      eapply uctxt_inject_neutral_gss; eauto.
      eapply uctxt_inject_neutral0_gss; eauto.
      eapply uctxt_inject_neutral0_Vint.
    Qed.

    Global Instance proc_start_user_inv: StartUserInvariants proc_start_user_spec.
    Proof.
      constructor; intros; functional inversion H; inv H0.
      - constructor; trivial.
      - subst. constructor; auto; simpl in *; intros; congruence.
    Qed.

    Global Instance proc_exit_user_inv: ExitUserInvariants proc_exit_user_spec.
    Proof.
      constructor; intros; functional inversion H; inv H0.
      - constructor; trivial.
        eapply uctxt_inject_neutral_gss; eauto.
        repeat eapply uctxt_inject_neutral0_gss;
        try eapply uctxt_inject_neutral0_Vint.
        eapply uctxt_inject_neutral0_init.
      - constructor; auto; simpl in *; intros.
        omega. congruence.
    Qed.

    Global Instance proc_create_inv: PCreateInvariants proc_create_spec.
    Proof.
      constructor; intros;
      assert (Hspec:= H); inv H0;
      unfold proc_create_spec in H;
      subdestruct; inv H; simpl; auto.

      - (* low level invariant *)
        constructor; trivial; intros; simpl in *.
        + eapply kctxt_inject_neutral_gss_flatinj'; eauto.
          eapply kctxt_inject_neutral_gss_flatinj; eauto.
        + eapply uctxt_inject_neutral_gss; eauto.
          repeat eapply uctxt_inject_neutral0_gss;
          try eapply uctxt_inject_neutral0_Vint.
          * eapply uctxt_inject_neutral_impl; eauto.
          * eapply uctxt_inject_neutral0_Vptr_flat; eauto.
      - (* high_level_invariant *)
        destruct (correct_curid0 eq_refl) as [Hcur _]; auto.
        constructor; simpl; eauto 2; try congruence; intros.
        + exploit split_container_valid; eauto.
          eapply container_split_some; eauto.
          auto.
        + apply proc_create_quota_bounded in Hspec; auto.
        + unfold update_cusage, update_cchildren; zmap_solve.
        + eapply AbTCBStrong_range_gss_READY; eauto. 
        + eapply AbQCorrect_range_gss_enqueue; eauto.
        + unfold update_cusage, update_cchildren; apply NotInQ_gso_ac_true; eauto.
          zmap_simpl; repeat apply NotInQ_gso_true; auto.
        + eapply QCount_gss_spawn; eauto. 
          eapply AbTCBStrong_range_impl; eauto.
          split; [|split; [|eauto]].
          assert (Hpos:= cvalid_child_id_pos _ valid_container0 _ Hcur 0); omega.
          apply cvalid_unused_next_child; auto.
        + eapply InQ_gss_spawn; eauto.
          eapply AbTCBStrong_range_impl; eauto.
          split; [|split; [|eauto]].
          assert (Hpos:= cvalid_child_id_pos _ valid_container0 _ Hcur 0); omega.
          apply cvalid_unused_next_child; auto.
        + unfold update_cusage, update_cchildren; apply CurIDValid_gso_neq_true; auto.
          zmap_simpl; repeat apply CurIDValid_gss_ac; auto.
          assert (Hneq:= cvalid_child_id_neq _ valid_container0 _ Hcur); zmap_simpl.
          apply cvalid_unused_next_child; auto.
        + eapply SingleRun_gso_state_READY; eauto.
    Qed.

    Global Instance device_output_inv: PreservesInvariants device_output_spec.
    Proof. 
      preserves_invariants_simpl'' low_level_invariant high_level_invariant; eauto.
    Qed.

  End INV.

  Definition exec_loadex {F V} := exec_loadex2 (F := F) (V := V).

  Definition exec_storeex {F V} :=  exec_storeex2 (flatmem_store:= flatmem_store) (F := F) (V := V).

  Global Instance flatmem_store_inv: FlatmemStoreInvariant (flatmem_store:= flatmem_store).
  Proof.
    split; inversion 1; intros. 
    - functional inversion H0. split; trivial.
    - functional inversion H1. 
      split; simpl;
      try (eapply dirty_ppage'_store_unmapped'; try eassumption; try reflexivity); trivial.
  Qed.

  Global Instance trapinfo_set_inv: TrapinfoSetInvariant.
  Proof.
    split; inversion 1; intros; constructor; auto.
  Qed.

  (** * Layer Definition *)
  Definition pproc_fresh_c : compatlayer (cdata RData) :=
    proc_create ↦ proc_create_compatsem proc_create_spec.

  Definition pproc_fresh_asm : compatlayer (cdata RData) :=
    proc_start_user ↦ primcall_start_user_compatsem proc_start_user_spec
           ⊕ proc_exit_user ↦ primcall_exit_user_compatsem proc_exit_user_spec.

  Definition pproc_passthrough : compatlayer (cdata RData) :=
    fload ↦ gensem fload_spec
          ⊕ fstore ↦ gensem fstore_spec
          ⊕ vmxinfo_get ↦ gensem vmxinfo_get_spec
          ⊕ device_output ↦ gensem device_output_spec
          ⊕ pt_read ↦ gensem ptRead_spec
          ⊕ pt_resv ↦ gensem ptResv_spec
          ⊕ shared_mem_status ↦ gensem shared_mem_status_spec
          ⊕ offer_shared_mem ↦ gensem offer_shared_mem_spec

          ⊕ get_curid ↦ gensem get_curid_spec
          ⊕ thread_wakeup ↦ gensem thread_wakeup_spec
          (*⊕ is_chan_ready ↦ gensem is_chan_ready_spec
          ⊕ sendto_chan ↦ gensem sendto_chan_spec
          ⊕ receive_chan ↦ gensem receive_chan_spec*)
          ⊕ syncreceive_chan ↦ gensem syncreceive_chan_spec
          ⊕ syncsendto_chan_pre ↦ gensem syncsendto_chan_pre_spec
          ⊕ syncsendto_chan_post ↦ gensem syncsendto_chan_post_spec

          ⊕ proc_init ↦ gensem proc_init_spec
          ⊕ uctx_get ↦ gensem uctx_get_spec
          ⊕ uctx_set ↦ gensem uctx_set_spec

          ⊕ container_get_nchildren ↦ gensem container_get_nchildren_spec
          ⊕ container_get_quota ↦ gensem container_get_quota_spec
          ⊕ container_get_usage ↦ gensem container_get_usage_spec
          ⊕ container_can_consume ↦ gensem container_can_consume_spec
          ⊕ container_alloc ↦ gensem alloc_spec
          ⊕ host_in ↦ primcall_general_compatsem hostin_spec
          ⊕ host_out ↦ primcall_general_compatsem hostout_spec
          ⊕ trap_get ↦ primcall_trap_info_get_compatsem trap_info_get_spec
          ⊕ trap_set ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec

          ⊕ thread_yield ↦ primcall_thread_schedule_compatsem thread_yield_spec (prim_ident:= thread_yield)
          ⊕ thread_sleep ↦ primcall_thread_transfer_compatsem thread_sleep_spec

          ⊕ accessors ↦ {| exec_load := @exec_loadex; exec_store := @exec_storeex |}.

  Definition pproc : compatlayer (cdata RData) :=
    (pproc_fresh_c ⊕ pproc_fresh_asm) ⊕ pproc_passthrough.

  (*Definition pproc_impl : compatlayer (cdata RData) :=
    get_curid ↦ gensem (fun d : RData => get_curid_spec d)
      ⊕ uctx_get ↦ gensem (fun (a b : Z) (d : RData) => PUCtxtIntro.uctx_get_spec d a b)
      ⊕ uctx_set ↦ gensem (fun (a b c : Z) (d : RData) => PUCtxtIntro.uctx_set_spec d a b c).
  Definition pproc_rest : compatlayer (cdata RData) :=
    proc_create ↦ proc_create_compatsem proc_create_spec
      ⊕ proc_start_user ↦ primcall_start_user_compatsem proc_start_user_spec
      ⊕ proc_exit_user ↦ primcall_exit_user_compatsem proc_exit_user_spec
      ⊕ palloc ↦ gensem palloc_spec
      ⊕ pfree ↦ gensem (fun n d => pfree_spec d n)
      ⊕ pt_read ↦ gensem (fun a b d => ptRead_spec d a b)
      ⊕ pt_resv ↦ gensem (fun a b c d => ptResv_spec d a b c)
      ⊕ host_in ↦ primcall_general_compatsem hostin_spec
      ⊕ host_out ↦ primcall_general_compatsem hostout_spec
      ⊕ trap_get ↦ primcall_trap_info_get_compatsem trap_info_get_spec
      ⊕ trap_set ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec
      ⊕ thread_kill ↦ gensem (fun a b d => thread_kill_spec d a b)
      ⊕ thread_wakeup ↦ gensem (fun a d => thread_wakeup_spec d a)
      ⊕ thread_yield ↦ primcall_thread_schedule_compatsem thread_yield_spec (prim_ident:= thread_yield)
      ⊕ thread_sleep ↦ primcall_thread_transfer_compatsem thread_sleep_spec
      ⊕ is_chan_ready ↦ gensem is_chan_ready_spec
      ⊕ sendto_chan ↦ gensem (fun a b d => sendto_chan_spec d a b)
      ⊕ receive_chan ↦ gensem receive_chan_spec
      ⊕ proc_init ↦ gensem (fun n d => proc_init_spec d n)
      ⊕ accessors ↦ {| exec_load := @exec_loadex; exec_store := @exec_storeex |}.

  Lemma pproc_impl_eq : pproc ≡ pproc_impl ⊕ pproc_rest.
  Proof. reflexivity. Qed.

  Definition semantics := LAsm.Lsemantics pproc.*)

End WITHMEM.
