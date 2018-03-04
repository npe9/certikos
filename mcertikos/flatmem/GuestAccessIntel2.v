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
(*              Load and Store Semantics for Primitives                *)
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
Require Import Observation.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.ClightModules.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatClightSem.
Require Import liblayers.compcertx.MemWithData.

Require Import AbstractDataType.
Require Export FlatLoadStoreSem.
Require Import LoadStoreDef.
Require Export GuestAccessIntelDef2.

Section Load_Store.

  Context `{Hmem: Mem.MemoryModel}.
  Context `{HD: CompatData RData}.
  Context `{Hmwd: UseMemWithData mem}.

  Notation HDATAOps := (cdata (cdata_ops := data_ops) RData).
  
  Section GE.
    
    Context {F V} (ge: Genv.t F V).

    Section Load_Store2.

      Open Scope Z_scope.

      Definition load_accessor2 (n: Z) (ofs: Z) (chunk: memory_chunk) (m: mwd HDATAOps) (rs: regset) (rd: preg) :=
        let adr' := (EPTADDR (n / PgSize) ofs) in
        if (zle (ofs mod PgSize) (PgSize - size_chunk chunk)) then
          if (Zdivide_dec (align_chunk chunk) (ofs mod PgSize) (align_chunk_pos chunk)) then
            exec_flatmem_load chunk m adr' rs rd
          else Stuck
        else Stuck.

      Definition exec_guest_intel_load2 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) (rs: regset) (rd: preg) :=
        exec_guest_intel_accessor2 load_accessor2 adr chunk m rs rd.

      Lemma exec_guest_intel_load2_high_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_guest_intel_load2 adr chunk m rs rd = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_guest_intel_load2. intros.
        eapply exec_guest_intel_accessor2_high_level_invariant; eauto.
        unfold load_accessor2. intros.
        subdestruct. 
        eapply exec_flatmem_load_mem in H1; eauto. inv H1. assumption.
      Qed.

      Lemma exec_guest_intel_load2_asm_invariant:
        forall chunk rd,
        forall TYP: subtype (type_of_chunk chunk) (typ_of_preg rd) = true,
        forall adr m rs rs' m',
          exec_guest_intel_load2 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_guest_intel_load2. intros. 
        eapply exec_guest_intel_accessor2_asm_invariant; eauto.
        unfold load_accessor2. intros. subdestruct.
        eapply exec_flatmem_load_asm_invariant; eauto.
      Qed.

      Lemma exec_guest_intel_load2_low_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_guest_intel_load2 adr chunk m rs rd = Next rs' m' ->
          CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
          CompatData.low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_guest_intel_load2. intros.
        eapply exec_guest_intel_accessor2_low_level_invariant; eauto.
        unfold load_accessor2. intros.
        subdestruct. 
        eapply exec_flatmem_load_mem in H1; eauto. inv H1. assumption.
      Qed.

      Context `{flatmem_store: RData -> memory_chunk -> Z -> val -> option (cdata RData)}.

      Definition store_accessor2 (destroyed: list preg) (n: Z) (ofs: Z)
                 (chunk: memory_chunk) (m: mwd HDATAOps) (rs: regset) (rd: preg) :=
        let adr' := (EPTADDR (n / PgSize) ofs) in
        if (zle (ofs mod PgSize) (PgSize - size_chunk chunk)) then
          if (Zdivide_dec (align_chunk chunk) (ofs mod PgSize) (align_chunk_pos chunk)) then
            exec_flatmem_store (flatmem_store:= flatmem_store) chunk m adr' rs rd destroyed
          else Stuck
        else Stuck.

      Definition exec_guest_intel_store2 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) 
                 (rs: regset) (rd: preg) (destroyed: list preg) :=
        exec_guest_intel_accessor2 (store_accessor2 destroyed) adr chunk m rs rd.

      Context {flat_inv: FlatmemStoreInvariant (data_ops := data_ops) (flatmem_store:= flatmem_store)}.

      Lemma exec_guest_intel_store2_high_level_invariant:
        forall adr chunk m rs rd rs' ds m',
          exec_guest_intel_store2 adr chunk m rs rd ds = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_guest_intel_store2. intros.
        eapply exec_guest_intel_accessor2_high_level_invariant; eauto.
        unfold store_accessor2. intros. subdestruct.
        eapply exec_flatmem_store_high_level_invariant; eauto 1.
        eapply PTADDR_mod_lt; assumption.
      Qed.

      Lemma exec_guest_intel_store2_asm_invariant:
        forall chunk rd,
        forall adr m rs rs' ds m',
          exec_guest_intel_store2 adr chunk m rs rd ds = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_guest_intel_store2. intros.
        eapply exec_guest_intel_accessor2_asm_invariant; eauto.
        unfold store_accessor2. intros. subdestruct.
        eapply exec_flatmem_store_asm_invariant; eauto.
      Qed.

      Lemma exec_guest_intel_store2_low_level_invariant:
        forall adr chunk m rs rd rs' ds m',
          exec_guest_intel_store2 adr chunk m rs rd ds = Next rs' m' ->
          CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
          CompatData.low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_guest_intel_store2. intros.
        eapply exec_guest_intel_accessor2_low_level_invariant; eauto.
        unfold store_accessor2. intros. subdestruct. 
        eapply exec_flatmem_store_low_level_invariant in H1; eauto.
      Qed.

    End Load_Store2.

  End GE.      

End Load_Store.

Section Refinement.

  Context `{Hobs: Observation}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.
  Context `{HD: CompatData(Obs:=Obs) RData}.
  Context `{HD0: CompatData(Obs:=Obs) RData}.

  Notation HDATAOps := (cdata (cdata_ops := data_ops) RData).
  Notation LDATAOps := (cdata (cdata_ops := data_ops0) RData).
  Context `{rel_prf: CompatRel (Obs:=Obs) (mem:=mem) (memory_model_ops:= memory_model_ops) (D1 := HDATAOps) (D2:=LDATAOps)}. 
  Context `{Hstencil: Stencil stencil (stencil_ops:= stencil_ops)}.
  Context `{trapinfo_inv: TrapinfoSetInvariant (Obs:=Obs) (data_ops:= data_ops)}.

  Context `{hflatmem_store: RData -> memory_chunk -> Z -> val -> option RData}.
  Context `{lflatmem_store: RData -> memory_chunk -> Z -> val -> option RData}.

  Notation hexec_flatmem_store := (exec_flatmem_store (flatmem_store:= hflatmem_store)).
  Notation lexec_flatmem_store := (exec_flatmem_store (flatmem_store:= lflatmem_store)).

  Section General.

    Context {loadstoreprop: LoadStoreProp (hflatmem_store:= hflatmem_store) (lflatmem_store:= lflatmem_store)}.
    Context {re1: relate_impl_HP'}.
    Context {re2: relate_impl_ept}.

    Opaque align_chunk Z.mul Z.div Z.sub. 

    Lemma guest_intel_load_correct2:
      forall m1 m1' m2 d1 d2 d1' rs1 rs2 rs1' f s rd t i,
        exec_guest_intel_load2 i t (m1, d1) rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1 m1 d1 rs2 m2 d2
        -> exists r'0 m2' d2',
             exec_guest_intel_load2 i t (m2, d2) rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros. eapply guest_intel_correct2; eauto.
      unfold load_accessor2; intros.
      subdestruct.
      eapply exec_flatmem_load_correct; eauto.
    Qed.

    Lemma guest_intel_store_correct2:
      forall m1 m1' m2 d1 d2 d1' rs1 rs2 rs1' f s rd t i ds,
        exec_guest_intel_store2 (flatmem_store:= hflatmem_store) i t (m1, d1) rs1 rd ds = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1 m1 d1 rs2 m2 d2
        -> exists r'0 m2' d2',
             exec_guest_intel_store2 (flatmem_store:= lflatmem_store) i t (m2, d2) rs2 rd ds = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros. eapply guest_intel_correct2; eauto.
      unfold store_accessor2; intros.
      subdestruct.
      eapply exec_flatmem_store_correct; eauto.
      apply PTADDR_mod_lt. assumption.
    Qed.

  End General.

End Refinement.