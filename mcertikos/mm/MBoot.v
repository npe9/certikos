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
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the raw abstract data and the primitives for the MBoot layer, 
which is also the bottom layer of memory management*)
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

Require Import AbstractDataType.

Require Export ObjCPU.
Require Export ObjMM.
Require Export ObjFlatMem.

(** Since MBoot is the bottom layer, we should avoid introducing too many hypotheses over the hardware. 
Therefore, there aren't any invariants over the abstract data at this layer*)

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
        ihost: bool (**r logic flag, shows whether it's in the host mode or not*)         
      }.*)

  (** ** Invariants at this layer *)
  Definition high_level_invariant (abd: RData) := True.

  (** ** Definition of the abstract state ops *)
  Global Instance mboot_data_ops : CompatDataOps RData :=
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
      constructor; trivial. 
    Qed.

    (** ** Definition of the abstract state *)
    Global Instance mboot_data_prf : CompatData RData.
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

    Global Instance setPG_inv: PreservesInvariants setPG_spec.
    Proof. 
      preserves_invariants_simpl low_level_invariant high_level_invariant.
    Qed.

    Global Instance device_output_inv: PreservesInvariants device_output_spec.
    Proof. 
      preserves_invariants_simpl'' low_level_invariant high_level_invariant.
    Qed.

    Global Instance clearCR2_inv: PreservesInvariants clearCR2_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant; auto.
    Qed.

    Global Instance fstore_inv: PreservesInvariants fstore'_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant.
    Qed.

    Global Instance setCR3_inv: SetCR3Invariants setCR3_spec.
    Proof.
      constructor; intros.
      - functional inversion H; inv H0; constructor; trivial.
      - functional inversion H; inv H0; constructor; auto.
      - functional inversion H; simpl in *; assumption.
    Qed.

    Global Instance bootloader0_inv: PreservesInvariants bootloader0_spec.
    Proof.
      preserves_invariants_simpl low_level_invariant high_level_invariant.
    Qed.

    Global Instance trapin_inv: PrimInvariants trapin_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance trapout_inv: PrimInvariants trapout'_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance hostin_inv: PrimInvariants hostin_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

    Global Instance hostout_inv: PrimInvariants hostout'_spec.
    Proof.
      PrimInvariants_simpl H H0.
    Qed.

  End INV.

  Definition exec_loadex {F V} := exec_loadex1 (F := F) (V := V).

  Definition exec_storeex {F V} := exec_storeex1 (flatmem_store:= flatmem_store') (F := F) (V := V).

  Global Instance flatmem_store_inv: FlatmemStoreInvariant (flatmem_store:= flatmem_store').
  Proof.
    split; inversion 1; intros. 
    - functional inversion H0; constructor; auto.
    - functional inversion H1; constructor; auto.
  Qed.

  Global Instance trapinfo_set_inv: TrapinfoSetInvariant.
  Proof.
    split; inversion 1; intros; constructor; auto.
  Qed.

  Global Instance flatmem_copy_inv: PreservesInvariants flatmem_copy'_spec.
  Proof.
    preserves_invariants_simpl low_level_invariant high_level_invariant.      
  Qed.

  (** * Layer Definition *)
  Definition mboot_fresh : compatlayer (cdata RData) :=
    fload ↦ gensem fload'_spec
           ⊕ fstore ↦ gensem fstore'_spec
           ⊕ flatmem_copy ↦ gensem flatmem_copy'_spec.

  Definition mboot_passthrough : compatlayer (cdata RData) :=
    vmxinfo_get ↦ gensem vmxinfo_get_spec
                ⊕ device_output ↦ gensem device_output_spec
                ⊕ set_pg ↦ gensem setPG_spec
                ⊕ clear_cr2 ↦ gensem clearCR2_spec
                ⊕ set_cr3 ↦ setCR3_compatsem setCR3_spec
                ⊕ get_size ↦ gensem MMSize
                ⊕ is_usable ↦ gensem is_mm_usable_spec
                ⊕ get_mms ↦ gensem get_mm_s_spec
                ⊕ get_mml ↦ gensem get_mm_l_spec
                ⊕ boot_loader ↦ gensem bootloader0_spec
                ⊕ trap_in ↦ primcall_general_compatsem trapin_spec
                ⊕ trap_out ↦ primcall_general_compatsem trapout'_spec
                ⊕ host_in ↦ primcall_general_compatsem hostin_spec
                ⊕ host_out ↦ primcall_general_compatsem hostout'_spec
                ⊕ trap_get ↦ primcall_trap_info_get_compatsem trap_info_get_spec
                ⊕ trap_set ↦ primcall_trap_info_ret_compatsem trap_info_ret_spec
                ⊕ accessors ↦ {| exec_load := @exec_loadex; exec_store := @exec_storeex |}.

  Definition mboot : compatlayer (cdata RData) := mboot_fresh ⊕ mboot_passthrough.

End WITHMEM.
