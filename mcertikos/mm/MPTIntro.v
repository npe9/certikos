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
(*              Layers of VMM: MPTINTRO                                *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the abstract data and the primitives for the MPTIntro layer, which will abstract the page table pool from the memory*)
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
Require Import ObservationImpl.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import INVLemmaContainer.
Require Import INVLemmaMemory.
Require Import CalRealIDPDE.

Require Import AbstractDataType.

Require Export ObjCPU.
Require Export ObjMM.
Require Export ObjFlatMem.
Require Export ObjContainer.
Require Export ObjPMM.
Require Export ObjVMM.

Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  (** * Raw Abstract Data*)
  (*Record RData :=
    mkRData {
        HP: flatmem; (**r we model the memory from 1G to 3G as heap*)
        ti: trapinfo; (**r abstract of CR2, stores the address where page fault happens*)
        pg: bool; (**r abstract of CR0, indicates whether the paging is enabled or not*)
        ikern: bool; (**r pure logic flag, shows whether it's in kernel mode or not*)
        ihost: bool; (**r logic flag, shows whether it's in the host mode or not*)         

        AT: ATable; (**r allocation table*)
        nps: Z; (**r number of the pages*)
        init: bool; (**r pure logic flag, show whether the initialization at this layer has been called or not*)
        pperm: PPermT; (**r physical page permission table *)

        PT: Z; (**r the current page table index*)
        ptpool: PMapPool; (**r page table pool*)
        idpde: IDPDE; (**r shared identity maps *)
        ipt: bool (**r pure logic flag, shows whether the current page map is the kernel's page map*)
      }.*)

  Definition PMap_uninitialized (ptp: PMapPool) :=
    forall n i pi pte,
      ZMap.get i (ZMap.get n ptp) <> PDEValid pi pte.

  Lemma PMap_uninitialized_undef:
    PMap_uninitialized (ZMap.init (ZMap.init PDEUndef)).
  Proof.
    intros n. intros.
    repeat rewrite ZMap.gi. congruence.
  Qed.

(*
  Definition PMap_PTE_range (ptp: PMapPool): Prop :=
    forall i j pte pi,
      ZMap.get j (ZMap.get i ptp) = PDEValid pi pte ->
      forall k v p,
        ZMap.get k pte = PTEValid v p ->
        0 < v < maxpage.

  Lemma PMap_PTE_range_undef:
    PMap_PTE_range (ZMap.init (ZMap.init PDEUndef)).
  Proof.
    unfold PMap_PTE_range; intros.
    repeat rewrite ZMap.gi in H. congruence.
  Qed.

    Lemma PMap_PTE_range_gso_pde:
      forall ptp,
        PMap_PTE_range ptp ->
        forall pde,
          (forall pi pte, pde <> PDEValid pi pte) ->
          forall i j,
            PMap_PTE_range (ZMap.set i (ZMap.set j pde (ZMap.get i ptp)) ptp).
    Proof.
      unfold PMap_PTE_range; intros.
      destruct (zeq i i0); subst.
      - rewrite ZMap.gss in H1.
        destruct (zeq j j0); subst.
        + rewrite ZMap.gss in H1. rewrite H1 in H0.
          specialize (H0 pi pte). congruence.
        + rewrite ZMap.gso in H1; eauto.
      - rewrite ZMap.gso in H1; eauto.
    Qed.

    Lemma PMap_PTE_range_gso_PDEID:
      forall ptp,
        PMap_PTE_range ptp ->
        forall i j,
          PMap_PTE_range (ZMap.set i (ZMap.set j PDEID (ZMap.get i ptp)) ptp).
    Proof.
      intros. eapply PMap_PTE_range_gso_pde; eauto.
      red; intros. congruence.
    Qed.

    Lemma PMap_PTE_range_gso_PDEUnPresent:
      forall ptp,
        PMap_PTE_range ptp ->
        forall i j,
          PMap_PTE_range (ZMap.set i (ZMap.set j PDEID (ZMap.get i ptp)) ptp).
    Proof.
      intros. eapply PMap_PTE_range_gso_pde; eauto.
      red; intros. congruence.
    Qed.*)
    
  (** ** Invariants at this layer *)
  Record high_level_invariant (abd: RData) :=
    mkInvariant {
        valid_nps: init abd = true -> kern_low <= nps abd <= maxpage;
        valid_AT_kern: init abd = true -> AT_kern (AT abd) (nps abd);
        valid_AT_usr: init abd = true -> AT_usr (AT abd) (nps abd);
        valid_kern: ipt abd = false -> pg abd = true /\ init abd = true;
        valid_iptt: ipt abd = true -> ikern abd = true; 
        valid_iptf: ikern abd = false -> ipt abd = false; 
        valid_ihost: ihost abd = false -> pg abd = true /\ init abd = true /\ ikern abd = true;
        valid_container: Container_valid (AC abd);
        valid_quota_bounded: quota_bounded_AT (AC abd) (AT abd) (nps abd);
        valid_pperm_ppage: consistent_ppage (AT abd) (pperm abd) (nps abd);
        init_pperm: init abd = false -> (pperm abd) = ZMap.init PGUndef;
        valid_PMap: pg abd = true -> PMap_valid (ZMap.get (PT abd) (ptpool abd));
        valid_PMap_kern: pg abd = true -> ipt abd = true -> 
                         PMap_kern (ZMap.get (PT abd) (ptpool abd));
        valid_PT: pg abd = true -> 0<= PT abd < num_proc;
        valid_dirty: dirty_ppage (pperm abd) (HP abd);

        valid_uninitialized: init abd = false -> PMap_uninitialized (ptpool abd)
        (*valid_pte: PMap_PTE_range (ptpool abd)*)

      (*;
        valid_pmap_domain: consistent_pmap_domain (ptpool abd) (pperm abd) (nps abd);
        valid_pperm_pmap: consistent_pmap (ptpool abd) (pperm abd) (nps abd)*)
      }.

  (** ** Definition of the abstract state ops *)
  Global Instance mptintro_data_ops : CompatDataOps RData :=
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
      - unfold quota_bounded_AT; simpl; omega.
      - eapply consistent_ppage_init.
      - eapply dirty_ppage_init.
      - eapply PMap_uninitialized_undef.
      (*- eapply PMap_PTE_range_undef.*)
    Qed.

    (** ** Definition of the abstract state *)
    Global Instance mptintro_data_prf : CompatData RData.
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
    
    Section CONTAINER_ALLOC.

      Lemma container_alloc_high_level_inv:
        forall d d' i n,
          container_alloc_spec i d = Some (d', n) ->
          high_level_invariant d ->
          high_level_invariant d'.
      Proof.
        intros. functional inversion H; subst; eauto. 
        inv H0. constructor; simpl; eauto.
        - intros; eapply AT_kern_norm'; eauto.
        - intros; eapply AT_usr_norm; eauto.
        - eapply alloc_container_valid'; eauto.
        - apply container_alloc_quota_bounded_AT in H; auto.
        - eapply consistent_ppage_norm_alloc; eauto.
        - intros; congruence.
        - eapply dirty_ppage_gso_alloc; eauto.
      Qed.

      Lemma container_alloc_low_level_inv:
        forall d d' n n' i,
          container_alloc_spec i d = Some (d', n) ->
          low_level_invariant n' d ->
          low_level_invariant n' d'.
      Proof.
        intros. functional inversion H; subst; eauto.
        inv H0. constructor; eauto.
      Qed.

      Lemma container_alloc_kernel_mode:
        forall d d' i n,
          container_alloc_spec i d = Some (d', n) ->
          kernel_mode d ->
          kernel_mode d'.
      Proof.
        intros. functional inversion H; subst; eauto.
      Qed.

      Global Instance container_alloc_inv: PreservesInvariants container_alloc_spec.
      Proof.
        preserves_invariants_simpl'.
        - eapply container_alloc_low_level_inv; eassumption.
        - eapply container_alloc_high_level_inv; eassumption.
        - eapply container_alloc_kernel_mode; eassumption.
      Qed.

    End CONTAINER_ALLOC.

    Global Instance pfree'_inv: PreservesInvariants pfree'_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      - intros; eapply AT_kern_norm; eauto. 
      - intros; eapply AT_usr_norm; eauto.
      - apply pfree_quota_bounded_AT; auto.
      - eapply consistent_ppage_norm_undef; eauto.
      - eapply dirty_ppage_gso_undef; eauto.
    Qed.

    Global Instance container_split_inv: PreservesInvariants container_split_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      rewrite <- H0 in H2.
      exploit split_container_valid; eauto.
      apply split_quota_bounded_AT in H2; auto.
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

    Global Instance container_init_inv: PreservesInvariants container_init0_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      - apply real_nps_range.
      - apply real_at_kern_valid.
      - apply real_at_usr_valid.
      - apply real_container_valid.
      - apply real_quota_bounded_AT.
      - rewrite init_pperm0; try assumption.
        apply real_pperm_valid.        
    Qed.

    Global Instance ptin_inv: PrimInvariants ptin'_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance ptout_inv: PrimInvariants ptout_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance setPG_inv: PreservesInvariants setPG1_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
    Qed.

    Global Instance clearCR2_inv: PreservesInvariants clearCR2_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
    Qed.

    Global Instance set_at_c_inv: PreservesInvariants set_at_c0_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      - intros; eapply AT_kern_norm; eauto. 
      - intros; eapply AT_usr_norm; eauto.
      - unfold quota_bounded_AT in *; rewrite unused_pages_AT_set; cases; omega.
      - eapply consistent_ppage_norm; eauto.
    Qed.

    Global Instance fstore_inv: PreservesInvariants fstore_spec.
    Proof.
      split; intros; inv_generic_sem H.
      - inv H0. functional inversion H2. functional inversion H.
        split; trivial.
      - inv H0. functional inversion H2. functional inversion H.
        split; subst; simpl; 
        try (eapply dirty_ppage_store_unmaped; try reflexivity; try eassumption); trivial. 
      - inv H0. functional inversion H2. functional inversion H0.
        split; simpl; try assumption.
    Qed.

    Global Instance setPT_inv: PreservesInvariants setPT'_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      - rewrite H5 in *. contradiction. 
    Qed.

    Global Instance setPDE_inv: PreservesInvariants setPDE_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      (*eapply PMap_PTE_range_gso_PDEID; eauto.*)
    Qed.

    Global Instance rmvPDE_inv: PreservesInvariants rmvPDE_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto;
      try (rewrite ZMap.gso; eauto; fail).
      - eapply consistent_ppage_hide_alloc; eassumption.
      - eapply dirty_ppage_gso_alloc; eauto.
      - eapply consistent_ppage_hide_alloc; eassumption.
      - eapply dirty_ppage_gso_alloc; eauto.
    Qed.

    Global Instance setPDEU_inv: PreservesInvariants setPDEU_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto;
      try (rewrite ZMap.gso; eauto; fail).
      - apply consistent_ppage_alloc_hide; assumption. 
      - apply dirty_ppage_gss. assumption.        
    Qed.

    Global Instance setPTE_inv: 
      PreservesInvariants setPTE_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto;
      try (rewrite ZMap.gso; eauto; fail).
    Qed.

    Global Instance rmvPTE_inv: PreservesInvariants rmvPTE_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto;
      try (rewrite ZMap.gso; eauto; fail).
    Qed.

    Global Instance setIDPTE_inv: 
      PreservesInvariants setIDPTE_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
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
  Definition mptintro_fresh : compatlayer (cdata RData) :=
    (set_pt ↦ gensem setPT'_spec
            ⊕ get_PDE ↦ gensem getPDE_spec
            ⊕ set_PDE ↦ gensem setPDE_spec
            ⊕ rmv_PDE ↦ gensem rmvPDE_spec
            ⊕ set_PDEU ↦ gensem setPDEU_spec
            ⊕ get_PTE ↦ gensem getPTE_spec
            ⊕ set_PTE ↦ gensem setPTE_spec
            ⊕ rmv_PTE ↦ gensem rmvPTE_spec
            ⊕ set_IDPTE ↦ gensem setIDPTE_spec)
      ⊕ (pt_in ↦ primcall_general_compatsem' (prim_ident:= pt_in) ptin'_spec
               ⊕ pt_out ↦ primcall_general_compatsem' (prim_ident:= pt_out) ptout_spec).

  (** ** Layer Definition passthrough  *)
  Definition mptintro_passthrough : compatlayer (cdata RData) :=
    fload ↦ gensem fload_spec
          ⊕ fstore ↦ gensem fstore_spec
          ⊕ flatmem_copy ↦ gensem flatmem_copy_spec
          ⊕ vmxinfo_get ↦ gensem vmxinfo_get_spec
          ⊕ device_output ↦ gensem device_output_spec
          ⊕ set_pg ↦ gensem setPG1_spec
          ⊕ at_get_c ↦ gensem get_at_c_spec
          ⊕ at_set_c ↦ gensem set_at_c0_spec
          ⊕ pfree ↦ gensem pfree'_spec          
          ⊕ clear_cr2 ↦ gensem clearCR2_spec
          ⊕ container_init ↦ gensem container_init0_spec
          ⊕ container_get_parent ↦ gensem container_get_parent_spec
          ⊕ container_get_nchildren ↦ gensem container_get_nchildren_spec
          ⊕ container_get_quota ↦ gensem container_get_quota_spec
          ⊕ container_get_usage ↦ gensem container_get_usage_spec
          ⊕ container_can_consume ↦ gensem container_can_consume_spec
          ⊕ container_split ↦ gensem container_split_spec
          ⊕ container_alloc ↦ gensem container_alloc_spec
          ⊕ trap_in ↦ primcall_general_compatsem trapin_spec
          ⊕ trap_out ↦ primcall_general_compatsem trapout_spec
          ⊕ host_in ↦ primcall_general_compatsem hostin_spec
          ⊕ host_out ↦ primcall_general_compatsem hostout_spec
          ⊕ trap_get ↦ primcall_trap_info_get_compatsem trap_info_get_spec
          ⊕ trap_set ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec
          ⊕ accessors ↦ {| exec_load := @exec_loadex; exec_store := @exec_storeex |}.

  (** * Layer Definition *)
  Definition mptintro : compatlayer (cdata RData) := mptintro_fresh ⊕ mptintro_passthrough.

  (*Definition semantics := LAsm.Lsemantics mptintro.*)
End WITHMEM.
