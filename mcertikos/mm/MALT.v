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
(*              Layers of VMM: MAL                                     *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the abstract data and the primitives for the MAL layer, which will introduce the palloc and pfree primitives*)
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
Require Import LoadStoreSem1.
Require Import ObservationImpl.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.

Require Import INVLemmaMemory.

Require Import AbstractDataType.

Require Export ObjCPU.
Require Export ObjMM.
Require Export ObjFlatMem.
Require Export ObjPMM.

Section WITHMEM.

  Local Open Scope Z_scope.

  Context `{real_params: RealParams}.

  (** * Raw Abstract Data*)
  (*Record RData :=
    mkRData {
        HP: flatmem; (**r we model the memory from 1G to 3G as heap*)
        MM: MMTable; (**r table of the physical memory's information*)
        MMSize: Z; (**r size of MMTable*)
        CR3: globalpointer; (**r abstract of CR3, stores the pointer to page table*)          
        ti: trapinfo; (**r abstract of CR2, stores the address where page fault happens*)
        pg: bool; (**r abstract of CR0, indicates whether the paging is enabled or not*)
        ikern: bool; (**r pure logic flag, shows whether it's in kernel mode or not*)
        ihost: bool; (**r logic flag, shows whether it's in the host mode or not*)         

        AT: ATable; (**r allocation table*)
        nps: Z; (**r number of the pages*)
        init: bool; (**r pure logic flag, show whether the initialization at this layer has been called or not*)
        pperm: PPermT (**r physical page permission table *)
      }.*)

  (** ** Invariants at this layer *)
  Record high_level_invariant (abd: RData) :=
    mkInvariant {
        valid_nps: init abd= true -> kern_low <= nps abd <= maxpage;
        valid_kern: ikern abd = false -> pg abd = true /\ init abd = true;
        valid_AT_kern: init abd = true -> AT_kern (AT abd) (nps abd);
        valid_AT_usr: init abd = true -> AT_usr (AT abd) (nps abd);
        valid_CR3: pg abd= true -> CR3_valid (CR3 abd);
        valid_ihost: ihost abd = false -> pg abd = true /\ init abd = true /\ ikern abd = true;
        valid_pperm: consistent_ppage (AT abd) (pperm abd) (nps abd);
        init_pperm: init abd = false -> (pperm abd) = ZMap.init PGUndef
      }.

  (** ** Definition of the abstract state ops *)
  Global Instance malt_data_ops : CompatDataOps RData :=
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
      - eapply consistent_ppage_init.
    Qed.

  End Property_Abstract_Data.

  (** ** Definition of the abstract state *)
  Global Instance malt_data_prf : CompatData RData.
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

    Global Instance setPG_inv: PreservesInvariants setPG0_spec.
    Proof. 
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
    Qed.

    Global Instance clearCR2_inv: PreservesInvariants clearCR2_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
    Qed.

    Global Instance mem_init_inv: PreservesInvariants mem_init_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant.
      - apply real_nps_range.
      - apply real_at_kern_valid.
      - apply real_at_usr_valid.
      - rewrite init_pperm0; try assumption.
        apply real_pperm_valid.
    Qed.

    Global Instance setCR3_inv: SetCR3Invariants setCR30_spec.
    Proof.
      constructor; intros; functional inversion H.
      - inv H0; constructor; trivial.
      - inv H0; constructor; auto.
      - assumption.
    Qed.

    Global Instance trapin_inv: PrimInvariants trapin_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance trapout_inv: PrimInvariants trapout0_spec.
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

    Global Instance fstore_inv: PreservesInvariants fstore0_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; trivial;
      functional inversion H; subst; auto.
    Qed.

    Global Instance set_at_c_inv: PreservesInvariants set_at_c0_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      - intros; eapply AT_kern_norm; eauto. 
      - intros; eapply AT_usr_norm; eauto.
      - eapply consistent_ppage_norm; eauto.
    Qed.

    Global Instance palloc_inv: PreservesInvariants palloc'_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      - intros; eapply AT_kern_norm'; eauto.
      - intros; eapply AT_usr_norm; eauto.
      - eapply consistent_ppage_norm_alloc; eauto.
    Qed.

    Global Instance pfree_inv: PreservesInvariants pfree'_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
      - intros; eapply AT_kern_norm; eauto. 
      - intros; eapply AT_usr_norm; eauto.
      - eapply consistent_ppage_norm_undef; eauto.
    Qed.

    Global Instance flatmem_copy_inv: PreservesInvariants flatmem_copy0_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; eauto.      
    Qed.

    Global Instance device_output_inv: PreservesInvariants device_output_spec.
    Proof. 
      preserves_invariants_simpl'' low_level_invariant high_level_invariant; eauto.
    Qed.

  End INV.

  Definition exec_loadex {F V} := exec_loadex1 (F := F) (V := V).

  Definition exec_storeex {F V} := exec_storeex1 (flatmem_store:= flatmem_store) (F := F) (V := V).

  Global Instance flatmem_store_inv: FlatmemStoreInvariant (flatmem_store:= flatmem_store).
  Proof.
    split; inversion 1; intros. 
    - functional inversion H0; constructor; auto.
    - functional inversion H1; constructor; auto.
  Qed.

  Global Instance trapinfo_set_inv: TrapinfoSetInvariant.
  Proof.
    split; inversion 1; intros; constructor; auto.
  Qed.

  (** * Layer Definition *)
  (** ** Layer Definition newly introduced  *)
  Definition malt_fresh: compatlayer (cdata RData) :=
    palloc ↦ gensem palloc'_spec
           ⊕ pfree ↦ gensem pfree'_spec.

  (** ** Layer Definition passthrough  *)
  Definition malt_passthrough : compatlayer (cdata RData) :=
    fload ↦ gensem fload'_spec
          ⊕ fstore ↦ gensem fstore0_spec
          ⊕ flatmem_copy ↦ gensem flatmem_copy0_spec
          ⊕ vmxinfo_get ↦ gensem vmxinfo_get_spec
          ⊕ device_output ↦ gensem device_output_spec
          ⊕ set_pg ↦ gensem setPG0_spec
          ⊕ clear_cr2 ↦ gensem clearCR2_spec
          ⊕ set_cr3 ↦ setCR3_compatsem setCR30_spec
          ⊕ get_nps ↦ gensem get_nps_spec
          ⊕ is_norm ↦ gensem is_at_norm_spec
          ⊕ at_get ↦ gensem get_at_u_spec
          ⊕ at_get_c ↦ gensem get_at_c_spec
          ⊕ at_set_c ↦ gensem set_at_c0_spec
          ⊕ mem_init ↦ gensem mem_init_spec
          ⊕ trap_in ↦ primcall_general_compatsem trapin_spec
          ⊕ trap_out ↦ primcall_general_compatsem trapout0_spec
          ⊕ host_in ↦ primcall_general_compatsem hostin_spec
          ⊕ host_out ↦ primcall_general_compatsem hostout_spec
          ⊕ trap_get ↦ primcall_trap_info_get_compatsem trap_info_get_spec
          ⊕ trap_set ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec
          ⊕ accessors ↦ {| exec_load := @exec_loadex; exec_store := @exec_storeex |}.

  (** ** Layer Definition *)
  Definition malt : compatlayer (cdata RData) := malt_fresh ⊕ malt_passthrough.
  
  (*Definition semantics := LAsm.Lsemantics malt.*)

End WITHMEM.
