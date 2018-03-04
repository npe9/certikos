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
(*              Layers of VMM: MPTInit                                 *)
(*                                                                     *)
(*          initialize the page map and enable the page mechanism      *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the abstract data and the primitives for the MPTInit layer, which will initialize the page tables and enable the paging mechanism*)
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
Require Import INVLemmaContainer.
Require Import INVLemmaMemory.

Require Import AbstractDataType.

Require Export ObjCPU.
Require Export ObjFlatMem.
Require Export ObjContainer.
Require Export ObjPMM.
Require Export ObjVMM.
Require Export ObjLMM.

Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  Definition LATable_nil (lat: LATable):= 
    forall i l, ZMap.get i lat = LATValid false ATNorm l -> l = nil.

  Section LATABLE_NIL.

    Lemma LATable_nil_int:
      LATable_nil (ZMap.init LATUndef).
    Proof.
      intros i. intros.
      rewrite ZMap.gi in H. inv H.
    Qed.

    Lemma LATable_nil_gss_nil:
      forall la n t a,
        LATable_nil la ->
        LATable_nil (ZMap.set n (LATValid t a nil) la).
    Proof.
      unfold LATable_nil; intros.
      destruct (zeq i n); subst.
      - rewrite ZMap.gss in H0. inv H0. trivial.
      - rewrite ZMap.gso in H0; eauto.        
    Qed.

    Lemma LATable_nil_real:
      forall la,
        LATable_nil la ->
        LATable_nil (real_LAT la).
    Proof.
      unfold real_LAT.
      generalize (Z.to_nat (real_nps - 1)). 
      induction n.
      - simpl. intros.
        eapply LATable_nil_gss_nil; eauto.
      - simpl. intros.
        destruct (Z_le_dec 262144 (Z.pos (Pos.of_succ_nat n))).
        destruct (Z_lt_dec (Z.pos (Pos.of_succ_nat n)) (Z.min 983040 real_nps)).
        destruct ( MM_kern_valid_dec real_mm (Z.pos (Pos.of_succ_nat n)) real_size).
        + eapply LATable_nil_gss_nil; eauto.
        + eapply LATable_nil_gss_nil; eauto.
        + eapply LATable_nil_gss_nil; eauto.
        + eapply LATable_nil_gss_nil; eauto.
    Qed.

    Lemma LATable_nil_gso_true:
      forall la n l a,
        LATable_nil la ->
        LATable_nil (ZMap.set n (LATValid true a l) la).
    Proof.
      unfold LATable_nil; intros.
      destruct (zeq i n); subst.
      - rewrite ZMap.gss in H0. inv H0. 
      - rewrite ZMap.gso in H0; eauto.        
    Qed.

  End LATABLE_NIL.
    
  (** ** Invariants at this layer *)
  (** [0th page map] is reserved for the kernel thread*)
  Record high_level_invariant (abd: RData) :=
    mkInvariant {
        valid_nps: pg abd = true -> kern_low <= nps abd <= maxpage;
        valid_AT_kern: pg abd = true -> LAT_kern (LAT abd) (nps abd);
        valid_AT_usr: pg abd = true -> LAT_usr (LAT abd) (nps abd);
        valid_kern: ipt abd = false -> pg abd = true;
        valid_iptt: ipt abd = true -> ikern abd = true; 
        valid_iptf: ikern abd = false -> ipt abd = false; 
        valid_ihost: ihost abd = false -> pg abd = true /\ ikern abd = true;
        valid_container: Container_valid (AC abd);
        valid_pperm_ppage: Lconsistent_ppage (LAT abd) (pperm abd) (nps abd);
        init_pperm: pg abd = false -> (pperm abd) = ZMap.init PGUndef;
        valid_PMap: pg abd = true -> 
                    (forall i, 0<= i < num_proc ->
                               PMap_valid (ZMap.get i (ptpool abd)));
        (* 0th page map is reserved for the kernel thread*)          
        valid_PT_kern: pg abd = true -> ipt abd = true -> (PT abd) = 0;
        valid_PMap_kern: pg abd = true -> PMap_kern (ZMap.get 0 (ptpool abd));
        valid_PT: pg abd = true -> 0<= PT abd < num_proc;
        valid_dirty: dirty_ppage (pperm abd) (HP abd);

        valid_idpde: pg abd = true -> IDPDE_init (idpde abd);
        valid_pperm_pmap: consistent_pmap (ptpool abd) (pperm abd) (LAT abd) (nps abd);
        valid_pmap_domain: consistent_pmap_domain (ptpool abd) (pperm abd) (LAT abd) (nps abd);
        valid_lat_domain: consistent_lat_domain (ptpool abd) (LAT abd) (nps abd);
        valid_LATable_nil: LATable_nil (LAT abd);
        valid_pg_init: pg abd = init abd
        
      }.
  
  (** ** Definition of the abstract state ops *)
  Global Instance mptinit_data_ops : CompatDataOps RData :=
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
      - apply empty_container_valid.
      - eapply Lconsistent_ppage_init.
      - eapply dirty_ppage_init.
      - eapply consistent_pmap_init.
      - eapply consistent_pmap_domain_init.
      - eapply consistent_lat_domain_init.
      - eapply LATable_nil_int.
    Qed.

  End Property_Abstract_Data.

  (** ** Definition of the abstract state *)
  Global Instance mptinit_data_prf : CompatData RData.
  Proof.
    constructor.
    - apply low_level_invariant_incr.
    - apply empty_data_low_level_invariant.
    - apply empty_data_high_level_invariant.
  Qed.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  (** * Proofs that the primitives satisfies the invariants at this layer *)
  Section INV.

    Section ALLOC.

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
        - eapply alloc_container_valid'; eauto.
        - eapply Lconsistent_ppage_norm_alloc; eauto.
        - intros; congruence.
        - eapply dirty_ppage_gso_alloc; eauto.
        - eapply consistent_pmap_gso_at_false; eauto. apply _x.
        - eapply consistent_pmap_domain_gso_at_false; eauto. apply _x.
        - eapply consistent_lat_domain_gss_nil; eauto.
        - eapply LATable_nil_gss_nil; eauto.
      Qed.
      
      Lemma alloc_low_level_inv:
        forall d d' n n' i,
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

    Global Instance pfree_inv: PreservesInvariants pfree_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      - intros; eapply LAT_kern_norm; eauto. 
      - intros; eapply LAT_usr_norm; eauto.
      - eapply Lconsistent_ppage_norm_undef; eauto.
      - eapply dirty_ppage_gso_undef; eauto.
      - eapply consistent_pmap_gso_pperm_alloc; eauto.
      - eapply consistent_pmap_domain_gso_at_0; eauto.
      - eapply consistent_lat_domain_gss_nil; eauto.
      - eapply LATable_nil_gss_nil; eauto.
    Qed.

    Global Instance clearCR2_inv: PreservesInvariants clearCR2_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
    Qed.

    Global Instance container_split_inv: PreservesInvariants container_split_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      rewrite <- H0 in H2.
      exploit split_container_valid; eauto.
    Qed.

    Global Instance trapin_inv: PrimInvariants trapin_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance trapout_inv: PrimInvariants trapout_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance hostin_inv: PrimInvariants hostin_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance hostout_inv: PrimInvariants hostout_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance ptin_inv: PrimInvariants ptin_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance ptout_inv: PrimInvariants ptout_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance fstore_inv: PreservesInvariants fstore_spec.
    Proof.
      split; intros; inv_generic_sem H; inv H0; functional inversion H2.
      - functional inversion H. split; trivial.        
      - functional inversion H.
        split; subst; simpl; 
        try (eapply dirty_ppage_store_unmaped; try reflexivity; try eassumption); trivial. 
      - functional inversion H0.
        split; simpl; try assumption.
    Qed.

    Global Instance setPT_inv: PreservesInvariants setPT_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
    Qed.

    Global Instance pt_init_inv: PreservesInvariants pt_init_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant.
      - apply real_nps_range.
      - apply real_lat_kern_valid.
      - apply real_lat_usr_valid.
      - apply real_container_valid.
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
      - eapply LATable_nil_real; eauto.
    Qed.

    Global Instance ptRmv_inv: PreservesInvariants ptRmv0_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto;
      try (rewrite ZMap.gso; eauto; fail).
      - intros; eapply LAT_kern_norm; eauto. 
      - intros; eapply LAT_usr_norm; eauto.
      - eapply Lconsistent_ppage_norm; eassumption.
      - eapply PMap_valid_gso_unp; eauto.
      - functional inversion H1. 
        eapply PMap_kern_gso; eauto.
      - functional inversion H1.
        eapply consistent_pmap_at_ptp_same; try eassumption; omega.
      - eapply consistent_pmap_domain_remove; eauto.
      - functional inversion H1.
        eapply consistent_lat_domain_gss_remove; eauto; omega. 
      - eapply LATable_nil_gso_true; eauto.
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
          - eapply LATable_nil_gso_true; eauto.
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
          - eapply alloc_container_valid'; eauto.
          - apply Lconsistent_ppage_norm_hide; try assumption.
          - congruence.
          - eapply PMap_valid_gso_pde_unp; eauto.
            eapply real_init_PTE_defined.
          - functional inversion H3. 
            eapply PMap_kern_gso; eauto.
          - eapply dirty_ppage_gss; eauto.
          - eapply consistent_pmap_ptp_gss; eauto; apply _x.
          - eapply consistent_pmap_domain_gso_at_false; eauto; try apply _x.
            eapply consistent_pmap_domain_ptp_unp; eauto.
            apply real_init_PTE_unp.
          - apply consistent_lat_domain_gss_nil; eauto.
            apply consistent_lat_domain_gso_p; eauto.
          - eapply LATable_nil_gso_true; eauto.
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

      Global Instance ptInsert_inv: PreservesInvariants ptInsert0_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply ptInsert_low_level_inv; eassumption.
        - eapply ptInsert_high_level_inv; eassumption.
        - eapply ptInsert_kernel_mode; eassumption.
      Qed.

    End PTINSERT.

    Global Instance ptFreePDE_inv: PreservesInvariants ptFreePDE0_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto;
      try (rewrite ZMap.gso; eauto; fail); intros.
      - functional inversion H0. 
        eapply LAT_kern_consistent_pmap; try eassumption; eauto; omega.
      - eapply LAT_usr_norm; eauto.
      - apply Lconsistent_ppage_norm_undef; try assumption.
      - eapply PMap_valid_gss_pde_unp; eauto.
      - functional inversion H0.
        eapply PMap_kern_gso; eauto.
      - eapply dirty_ppage_gso_undef; eauto.
      - functional inversion H0.
        eapply consistent_pmap_ptp_gss'; eauto; omega.
      - eapply consistent_pmap_domain_gso_at_0.
        eapply consistent_pmap_domain_ptp_pde_unp; eauto.
        functional inversion H0. 
        eapply valid_pperm_pmap0; try eassumption; omega.
      - apply consistent_lat_domain_gss_nil; eauto.
        eapply consistent_lat_domain_gso_free; eauto.
      - eapply LATable_nil_gss_nil; eauto.
    Qed.

    Global Instance flatmem_copy_inv: PreservesInvariants flatmem_copy_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant;      
      try eapply dirty_ppage_gss_copy; eauto.
    Qed.

    Global Instance device_output_inv: PreservesInvariants device_output_spec.
    Proof. 
      preserves_invariants_simpl'' low_level_invariant high_level_invariant; eauto.
    Qed.

  End INV.

  (** * Specification of primitives that will be implemented at this layer*)
  Definition exec_loadex {F V} := exec_loadex2 (F := F) (V := V).

  Definition exec_storeex {F V} :=  exec_storeex2 (flatmem_store:= flatmem_store) (F := F) (V := V).

  Global Instance flatmem_store_inv: FlatmemStoreInvariant (flatmem_store:= flatmem_store).
  Proof.
    split; inversion 1; intros. 
    - functional inversion H0. split; trivial.
    - functional inversion H1. 
      split; simpl; try (eapply dirty_ppage_store_unmaped'; try reflexivity; try eassumption); trivial.
  Qed.

  Global Instance trapinfo_set_inv: TrapinfoSetInvariant.
  Proof.
    split; inversion 1; intros; constructor; auto.
  Qed.

  (** * Layer Definition *)
  (** ** Layer Definition newly introduced  *)
  Definition mptinit_fresh : compatlayer (cdata RData) :=
    pt_init ↦ gensem pt_init_spec.

  (** ** Layer Definition passthrough  *)
  Definition mptinit_passthrough : compatlayer (cdata RData) :=
    fload ↦ gensem fload_spec
          ⊕ fstore ↦ gensem fstore_spec
          ⊕ flatmem_copy ↦ gensem flatmem_copy_spec
          ⊕ vmxinfo_get ↦ gensem vmxinfo_get_spec
          ⊕ device_output ↦ gensem device_output_spec
          ⊕ pfree ↦ gensem pfree_spec
          ⊕ set_pt ↦ gensem setPT_spec
          ⊕ pt_read ↦ gensem ptRead_spec
          ⊕ pt_read_pde ↦ gensem ptReadPDE_spec
          ⊕ pt_free_pde ↦ gensem ptFreePDE0_spec
          ⊕ pt_insert ↦ gensem ptInsert0_spec
          ⊕ pt_rmv ↦ gensem ptRmv0_spec
          ⊕ pt_in ↦ primcall_general_compatsem' ptin_spec (prim_ident:= pt_in)
          ⊕ pt_out ↦ primcall_general_compatsem' ptout_spec (prim_ident:= pt_out)
          ⊕ clear_cr2 ↦ gensem clearCR2_spec
          ⊕ container_get_parent ↦ gensem container_get_parent_spec
          ⊕ container_get_nchildren ↦ gensem container_get_nchildren_spec
          ⊕ container_get_quota ↦ gensem container_get_quota_spec
          ⊕ container_get_usage ↦ gensem container_get_usage_spec
          ⊕ container_can_consume ↦ gensem container_can_consume_spec
          ⊕ container_split ↦ gensem container_split_spec
          ⊕ container_alloc ↦ gensem alloc_spec
          ⊕ trap_in ↦ primcall_general_compatsem trapin_spec
          ⊕ trap_out ↦ primcall_general_compatsem trapout_spec
          ⊕ host_in ↦ primcall_general_compatsem hostin_spec
          ⊕ host_out ↦ primcall_general_compatsem hostout_spec
          ⊕ trap_get ↦ primcall_trap_info_get_compatsem trap_info_get_spec
          ⊕ trap_set ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec
          ⊕ accessors ↦ {| exec_load := @exec_loadex; exec_store := @exec_storeex |}.

  (** * Layer Definition *)
  Definition mptinit : compatlayer (cdata RData) := mptinit_fresh ⊕ mptinit_passthrough.

  (*Definition semantics := LAsm.Lsemantics mptinit.*)

End WITHMEM.
