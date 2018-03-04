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
(*          Load and Store Semantics for Primitives                    *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the load and store semantics for primitives at all layers*)

Require Import Coqlib.
Require Import Maps.
Require Import Globalenvs.
Require Import ASTExtra.
Require Import AsmX.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import LAsm.
Require Import AuxStateDataType.
Require Import Constant.
Require Import FlatMemory.
Require Import GlobIdent.
Require Import Integers.
Require Import CommonTactic.
Require Import AuxLemma.
Require Import AsmImplLemma.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.ClightModules.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatClightSem.
Require Import liblayers.compcertx.MemWithData.

Require Import AbstractDataType.
Require Export GuestAccessIntelDef0.

Section Load_Store.

  Context `{Hmem: Mem.MemoryModel}.
  Context `{HD: CompatData RData}.
  Context `{Hmwd: UseMemWithData mem}.

  Notation HDATAOps := (cdata (cdata_ops := data_ops) RData).
  
  Section GE.
    
    Context {F V} (ge: Genv.t F V).

      Local Existing Instance Asm.mem_accessors_default.
      Local Existing Instance AsmX.mem_accessors_default_invariant.

      Definition load_accessor0 (n: int64) (ofs: Z) (chunk: memory_chunk) (m: mwd HDATAOps) (rs: regset) (rd: preg) :=
        let adr' := (Int.repr (EPTADDR ((Int.unsigned (Int.repr (Int64.unsigned n)))/PgSize) ofs)) in
        Asm.exec_load ge chunk m (Addrmode None None (inr (FlatMem_LOC, adr'))) rs rd.        
 
      Definition exec_guest_intel_load0 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) (rs: regset) (rd: preg) :=
        exec_guest_intel_accessor1 ge load_accessor0 adr chunk m rs rd.

      Lemma exec_guest_intel_load0_high_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_guest_intel_load0 adr chunk m rs rd = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_guest_intel_load0. intros.
        eapply exec_guest_intel_accessor1_high_level_invariant; eauto.
        unfold load_accessor0, Asm.exec_load. intros.
        subdestruct. inv H1. assumption.
      Qed.

      Lemma exec_guest_intel_load0_asm_invariant:
        forall chunk rd,
        forall TYP: subtype (type_of_chunk chunk) (typ_of_preg rd) = true,
        forall adr m rs rs' m',
          exec_guest_intel_load0 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_guest_intel_load0. intros. 
        eapply exec_guest_intel_accessor1_asm_invariant; eauto.
        unfold load_accessor0, Asm.exec_load. intros.
        eapply exec_load_invariant; try eassumption.
      Qed.

      Lemma exec_guest_intel_load0_low_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_guest_intel_load0 adr chunk m rs rd = Next rs' m' ->
          CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
          CompatData.low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_guest_intel_load0. intros.
        eapply exec_guest_intel_accessor1_low_level_invariant; eauto.
        unfold load_accessor0, Asm.exec_load. intros.
        subdestruct. inv H1. assumption.
      Qed.

      Definition store_accessor0 (destroyed: list preg) (n: int64) (ofs: Z)
                 (chunk: memory_chunk) (m: mwd HDATAOps) (rs: regset) (rd: preg) :=
        let adr' := (Int.repr (EPTADDR ((Int.unsigned(Int.repr (Int64.unsigned n)))/PgSize) ofs)) in
        Asm.exec_store ge chunk m (Addrmode None None (inr (FlatMem_LOC, adr'))) rs rd destroyed.        

      Definition exec_guest_intel_store0 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) 
                 (rs: regset) (rd: preg) (destroyed: list preg) :=
        exec_guest_intel_accessor1 ge (store_accessor0 destroyed) adr chunk m rs rd.

      Lemma exec_guest_intel_store0_high_level_invariant:
        forall adr chunk m rs rd rs' ds m',
          exec_guest_intel_store0 adr chunk m rs rd ds = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_guest_intel_store0. intros.
        eapply exec_guest_intel_accessor1_high_level_invariant; eauto.
        unfold store_accessor0, Asm.exec_store. simpl; intros. 
        subdestruct. lift_unfold.
        destruct Hdestruct0 as [? DATA].
        unfold π_data in DATA. simpl in * |- *. congruence.
      Qed.

      Lemma exec_guest_intel_store0_asm_invariant:
        forall chunk rd,
        forall adr m rs rs' ds m',
          exec_guest_intel_store0 adr chunk m rs rd ds = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_guest_intel_store0. intros.
        eapply exec_guest_intel_accessor1_asm_invariant; eauto.
        unfold store_accessor0. intros.
        eapply exec_store_invariant; try eassumption.
      Qed.

      Lemma exec_guest_intel_store0_low_level_invariant:
        forall adr chunk m rs rd rs' ds m',
          exec_guest_intel_store0 adr chunk m rs rd ds = Next rs' m' ->
          CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
          CompatData.low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_guest_intel_store0. intros.
        eapply exec_guest_intel_accessor1_low_level_invariant; eauto.
        unfold store_accessor0, Asm.exec_store. simpl; intros. 
        subdestruct. lift_unfold.
        destruct Hdestruct0 as [? DATA].
        unfold π_data in DATA. simpl in * |- *. inv H1.
        erewrite Mem.nextblock_store; eauto.
        congruence.
      Qed.

  End GE.      

End Load_Store.