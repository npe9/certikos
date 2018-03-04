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

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.ClightModules.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatClightSem.
Require Import liblayers.compcertx.MemWithData.

Require Import AbstractDataType.
Require Import FlatLoadStoreSem.
Require Import LoadStoreDef.

Section Load_Store.

  Context `{Hmem: Mem.MemoryModel}.
  Context `{HD: CompatData RData}.
  Context `{Hmwd: UseMemWithData mem}.

  Notation HDATAOps := (cdata (cdata_ops := data_ops) RData).
  
  Section GE.
    
    Context {F V} (ge: Genv.t F V).

    Section Accessor.

      Variable accessor: int64 -> Z -> memory_chunk -> (mwd HDATAOps) -> regset -> preg -> Asm.outcome (mem:= mwd HDATAOps).

      Open Scope Z_scope.

      Definition exec_guest_intel_accessor1 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) (rs: regset) (rd: preg) :=
        let ofs := (Int.unsigned adr) in 
        match (Genv.find_symbol ge EPT_LOC) with
          | Some b => 
            match Mem.loadv Mint32 m (Vptr b (Int.repr ((EPT_PML4_INDEX ofs) * 8 + 4))) with
              | Some (Vptr b0 adr1) =>
                if (peq b0 b) then
                  let ofs1 := (Int.unsigned adr1) / PgSize * PgSize + 4 in
                  match Mem.loadv Mint32 m (Vptr b (Int.repr (ofs1 + (EPT_PDPT_INDEX ofs) * 8))) with
                    | Some (Vptr b0 adr2) =>
                      if peq b0 b then
                        let ofs2 := (Int.unsigned adr2) / PgSize * PgSize + 4 in
                        match Mem.loadv Mint32 m (Vptr b (Int.repr (ofs2 + (EPT_PDIR_INDEX ofs) * 8))) with
                          | Some (Vptr b0 adr3) =>
                            if peq b0 b then
                              let ofs3 := (Int.unsigned adr3) / PgSize * PgSize in
                              match Mem.loadv Mint64 m (Vptr b (Int.repr (ofs3 + (EPT_PTAB_INDEX ofs) * 8))) with
                                | Some (Vlong n) =>
                                  accessor n ofs chunk m rs rd
                                | _ => Stuck
                              end
                            else Stuck
                          | _ => Stuck
                        end
                      else Stuck
                    | _ => Stuck
                  end
                else Stuck
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_guest_intel_accessor1_high_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_guest_intel_accessor1 adr chunk m rs rd = Next rs' m' ->
          high_level_invariant (snd m) ->
          (forall i i',
             accessor i i' chunk m rs rd = Next rs' m' ->
             high_level_invariant (snd m')) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_guest_intel_accessor1. intros until m'.
        destruct (Genv.find_symbol ge EPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m
                            (Vptr b (Int.repr (EPT_PML4_INDEX (Int.unsigned adr) * 8 + 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (peq b0 b); contra_inv; subst.
        destruct (Mem.loadv Mint32 m
                            (Vptr b (Int.repr (Int.unsigned i / 4096 * 4096 + 4 + EPT_PDPT_INDEX (Int.unsigned adr) * 8)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (peq b0 b); contra_inv; subst.
        destruct (Mem.loadv Mint32 m
                            (Vptr b (Int.repr (Int.unsigned i0 / 4096 * 4096 + 4 + EPT_PDIR_INDEX (Int.unsigned adr) * 8)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (peq b0 b); contra_inv; subst.
        destruct (Mem.loadv Mint64 m
                            (Vptr b (Int.repr (Int.unsigned i1 / 4096 * 4096 + EPT_PTAB_INDEX (Int.unsigned adr) * 8)))); 
          try discriminate.
        destruct v; try discriminate.
        intros. eauto.
      Qed.

      Lemma exec_guest_intel_accessor1_asm_invariant:
        forall chunk rd,
        forall adr m rs rs' m',
          exec_guest_intel_accessor1 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          (forall i i',
             accessor i i' chunk m rs rd = Next rs' m' ->
             AsmX.asm_invariant ge rs' m') ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_guest_intel_accessor1. intros until m'.
        destruct (Genv.find_symbol ge EPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m
                            (Vptr b (Int.repr (EPT_PML4_INDEX (Int.unsigned adr) * 8 + 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (peq b0 b); contra_inv; subst.
        destruct (Mem.loadv Mint32 m
                            (Vptr b (Int.repr (Int.unsigned i / 4096 * 4096 + 4 + EPT_PDPT_INDEX (Int.unsigned adr) * 8)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (peq b0 b); contra_inv; subst.
        destruct (Mem.loadv Mint32 m
                            (Vptr b (Int.repr (Int.unsigned i0 / 4096 * 4096 + 4 + EPT_PDIR_INDEX (Int.unsigned adr) * 8)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (peq b0 b); contra_inv; subst.
        destruct (Mem.loadv Mint64 m
                            (Vptr b (Int.repr (Int.unsigned i1 / 4096 * 4096 + EPT_PTAB_INDEX (Int.unsigned adr) * 8)))); 
          try discriminate.
        destruct v; try discriminate.
        intros; eauto.
      Qed.

      Lemma exec_guest_intel_accessor1_low_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_guest_intel_accessor1 adr chunk m rs rd = Next rs' m' ->
          CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
          (forall i i',
             accessor i i' chunk m rs rd = Next rs' m' ->
             CompatData.low_level_invariant (Mem.nextblock m') (snd m')) ->
          CompatData.low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_guest_intel_accessor1. intros until m'.
        destruct (Genv.find_symbol ge EPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m
                            (Vptr b (Int.repr (EPT_PML4_INDEX (Int.unsigned adr) * 8 + 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (peq b0 b); contra_inv; subst.
        destruct (Mem.loadv Mint32 m
                            (Vptr b (Int.repr (Int.unsigned i / 4096 * 4096 + 4 + EPT_PDPT_INDEX (Int.unsigned adr) * 8)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (peq b0 b); contra_inv; subst.
        destruct (Mem.loadv Mint32 m
                            (Vptr b (Int.repr (Int.unsigned i0 / 4096 * 4096 + 4 + EPT_PDIR_INDEX (Int.unsigned adr) * 8)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (peq b0 b); contra_inv; subst.
        destruct (Mem.loadv Mint64 m
                            (Vptr b (Int.repr (Int.unsigned i1 / 4096 * 4096 + EPT_PTAB_INDEX (Int.unsigned adr) * 8)))); 
          try discriminate.
        destruct v; try discriminate.
        intros; eauto.
      Qed.

    End Accessor.

  End GE.

  Section EQ.

    Context `{accessor1: int64 -> Z -> memory_chunk -> (mwd HDATAOps) -> regset -> preg -> Asm.outcome (mem:= mwd HDATAOps)}.
    Context `{accessor2: int64 -> Z -> memory_chunk -> (mwd HDATAOps) -> regset -> preg -> Asm.outcome (mem:= mwd HDATAOps)}.
 
    Lemma exec_guest_intel_accessor1_eq:
      forall {F V} (ge1 ge2: Genv.t F V) i chunk m rs r
             (SYMB : (forall i, Genv.find_symbol ge2 i = Genv.find_symbol ge1 i))
             (ACC: (forall i1 i2, accessor2 i1 i2 chunk m rs r = accessor1 i1 i2 chunk m rs r)),
        exec_guest_intel_accessor1 ge2 accessor2 i chunk m rs r =
        exec_guest_intel_accessor1 ge1 accessor1 i chunk m rs r.
    Proof.
      intros. unfold exec_guest_intel_accessor1.
      repeat rewrite SYMB.
      destruct (Genv.find_symbol ge1 EPT_LOC); try reflexivity.
      destruct (Mem.loadv Mint32 m
                          (Vptr b (Int.repr (EPT_PML4_INDEX (Int.unsigned i) * 8 + 4)))); try reflexivity.
      destruct v; try reflexivity.
      destruct (Mem.loadv Mint32 m
                          (Vptr b (Int.repr (Int.unsigned i0 / 4096 * 4096 + 4 + EPT_PDPT_INDEX (Int.unsigned i) * 8)))); try reflexivity.
      destruct v; try reflexivity.
      destruct (Mem.loadv Mint32 m
                          (Vptr b (Int.repr (Int.unsigned i1 / 4096 * 4096 + 4 + EPT_PDIR_INDEX (Int.unsigned i) * 8)))); try reflexivity.
      destruct v; try reflexivity.
      destruct (Mem.loadv Mint64 m
                          (Vptr b (Int.repr (Int.unsigned i2 / 4096 * 4096 + EPT_PTAB_INDEX (Int.unsigned i) * 8)))); try reflexivity.
      destruct v; try reflexivity.
      erewrite ACC; trivial.
    Qed.

  End EQ.

End Load_Store.