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
Require Export FlatLoadStoreSem.
Require Import LoadStoreDef.

Section Load_Store.

  Context `{Hmem: Mem.MemoryModel}.
  Context `{HD: CompatData RData}.
  Context `{Hmwd: UseMemWithData mem}.

  Notation HDATAOps := (cdata (cdata_ops := data_ops) RData).
  
  Section GE.
    
    Context {F V} (ge: Genv.t F V).

    Section Load_Store1.

      Definition exec_guest_load1 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) (rs: regset) (rd: preg) :=
        let ofs := (Int.unsigned adr) in 
        match (Genv.find_symbol ge NPT_LOC) with
          | Some b => 
            match Mem.loadv Mint32 m (Vptr b (Int.repr ((PDX ofs) * 4))) with
              | Some (Vptr b1 ofs1) =>
                match Mem.loadv Mint32 m (Vptr b1 (Int.repr (((Int.unsigned ofs1)/PgSize)*PgSize + (PTX ofs) *4))) with
                  | Some (Vint n) => 
                    let adr' := (PTADDR ((Int.unsigned n)/PgSize) ofs) in
                    if (zle (ofs mod PgSize) (PgSize - size_chunk chunk)) then
                      if (Zdivide_dec (align_chunk chunk) (ofs mod PgSize) (align_chunk_pos chunk)) then
                        exec_flatmem_load chunk m adr' rs rd
                      else Stuck
                    else Stuck
                  | _ => Stuck
                end
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_guest_load1_high_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_guest_load1 adr chunk m rs rd = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_guest_load1. intros until m'.
        destruct (Genv.find_symbol ge NPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b (Int.repr (PDX (Int.unsigned adr) * 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
        destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                              (align_chunk_pos chunk)); contra_inv.
        intros. exploit exec_flatmem_load_mem; eauto. congruence.
      Qed.

      Lemma exec_guest_load1_asm_invariant:
        forall chunk rd,
        forall TYP: subtype (type_of_chunk chunk) (typ_of_preg rd) = true,
        forall adr m rs rs' m',
          exec_guest_load1 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_guest_load1. intros until m'.
        destruct (Genv.find_symbol ge NPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b (Int.repr (PDX (Int.unsigned adr) * 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
        destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                              (align_chunk_pos chunk)); contra_inv.
        intros; eapply exec_flatmem_load_asm_invariant; eauto.
      Qed.

      Lemma exec_guest_load1_low_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_guest_load1 adr chunk m rs rd = Next rs' m' ->
          CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
          CompatData.low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_guest_load1. intros until m'.
        destruct (Genv.find_symbol ge NPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b (Int.repr (PDX (Int.unsigned adr) * 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
        destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                              (align_chunk_pos chunk)); contra_inv.
        intros. exploit exec_flatmem_load_mem; eauto. congruence.
      Qed.

      Context `{flatmem_store: RData -> memory_chunk -> Z -> val -> option (cdata RData)}.

      Definition exec_guest_store1 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) (rs: regset) 
                 (rd: preg) (destroyed: list preg) :=
        let ofs := (Int.unsigned adr) in 
        match (Genv.find_symbol ge NPT_LOC) with
          | Some b => 
            match Mem.loadv Mint32 m (Vptr b (Int.repr ((PDX ofs) * 4))) with
              | Some (Vptr b1 ofs1) =>
                match Mem.loadv Mint32 m (Vptr b1 (Int.repr (((Int.unsigned ofs1)/PgSize)*PgSize + (PTX ofs) *4))) with
                  | Some (Vint n) => 
                    let adr' := (PTADDR ((Int.unsigned n)/PgSize) ofs) in
                    if (zle (ofs mod PgSize) (PgSize - size_chunk chunk)) then
                      if (Zdivide_dec (align_chunk chunk) (ofs mod PgSize) (align_chunk_pos chunk)) then
                        exec_flatmem_store (flatmem_store:= flatmem_store) chunk m adr' rs rd destroyed
                      else Stuck
                    else Stuck
                  | _ => Stuck
                end
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Context {flat_inv: FlatmemStoreInvariant (data_ops := data_ops) (flatmem_store:= flatmem_store)}.

      Lemma exec_guest_store1_high_level_invariant:
        forall adr chunk m rs rd rs' ds m',
          exec_guest_store1 adr chunk m rs rd ds = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_guest_store1. intros until m'.
        destruct (Genv.find_symbol ge NPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b (Int.repr (PDX (Int.unsigned adr) * 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
        destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                              (align_chunk_pos chunk)); contra_inv.
        intros. eapply exec_flatmem_store_high_level_invariant; eauto 1.
        eapply PTADDR_mod_lt; assumption.
      Qed.

      Lemma exec_guest_store1_asm_invariant:
        forall chunk rd,
        forall adr m rs rs' ds m',
          exec_guest_store1 adr chunk m rs rd ds = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_guest_store1. intros until m'.
        destruct (Genv.find_symbol ge NPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b (Int.repr (PDX (Int.unsigned adr) * 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4))));
          try discriminate.
        destruct v; try discriminate.
        destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
        destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                              (align_chunk_pos chunk)); contra_inv.
        intros; eapply exec_flatmem_store_asm_invariant; eauto.
      Qed.

      Lemma exec_guest_store1_low_level_invariant:
        forall adr chunk m rs rd rs' ds m',
          exec_guest_store1 adr chunk m rs rd ds = Next rs' m' ->
          CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
          CompatData.low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_guest_store1. intros until m'.
        destruct (Genv.find_symbol ge NPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b (Int.repr (PDX (Int.unsigned adr) * 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
        destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                              (align_chunk_pos chunk)); contra_inv.
        eapply exec_flatmem_store_low_level_invariant.
      Qed.

    End Load_Store1.

  End GE.      

End Load_Store.

Section Refinement.

  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.
  Context `{HD: CompatData RData}.
  Context `{HD0: CompatData RData}.

  Notation HDATAOps := (cdata (cdata_ops := data_ops) RData).
  Notation LDATAOps := (cdata (cdata_ops := data_ops0) RData).
  Context `{rel_prf: CompatRel (mem:=mem) (memory_model_ops:= memory_model_ops) (D1 := HDATAOps) (D2:=LDATAOps)}. 
  Context `{Hstencil: Stencil stencil (stencil_ops:= stencil_ops)}.
  Context `{trapinfo_inv: TrapinfoSetInvariant (data_ops:= data_ops)}.

  Context `{hflatmem_store: RData -> memory_chunk -> Z -> val -> option RData}.
  Context `{lflatmem_store: RData -> memory_chunk -> Z -> val -> option RData}.

  Notation hexec_flatmem_store := (exec_flatmem_store (flatmem_store:= hflatmem_store)).
  Notation lexec_flatmem_store := (exec_flatmem_store (flatmem_store:= lflatmem_store)).

  Section General.

    Context {loadstoreprop: LoadStoreProp (hflatmem_store:= hflatmem_store) (lflatmem_store:= lflatmem_store)}.
    Context {re1: relate_impl_HP'}.

    Opaque align_chunk Z.mul Z.div Z.sub. 

    Lemma guest_load_correct1:
      forall {F V} (ge1 ge2: Genv.t F V) m1 m1' m2 d1 d2 d1' rs1 rs2 rs1' f s rd t i,
        exec_guest_load1 ge1 i t (m1, d1) rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1 m1 d1 rs2 m2 d2
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> exists r'0 m2' d2',
             exec_guest_load1 ge2 i t (m2, d2) rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros. unfold exec_guest_load1 in *.
      pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H1 H2) as [Hpre _].            
      rewrite Hpre.
      destruct (Genv.find_symbol ge1 NPT_LOC) eqn: HF; contra_inv.
      exploit (stencil_find_symbol_inject (ge:= ge1)); eauto. intros HF0.
      revert H; simpl; lift_trivial; intros H.
      destruct (Mem.load Mint32 m1 b (Int.unsigned (Int.repr (PDX (Int.unsigned i) * 4)))) eqn: HLD; contra_inv.
      pose proof H0 as Hmatch.
      inv H0. inv match_extcall_states.
      exploit Mem.load_inject; eauto.
      rewrite Z.add_0_r; intros [v1[HLD1 HVAL]].
      rewrite HLD1.
      clear HLD HLD1.
      destruct v; contra_inv; inv HVAL.
      destruct (Mem.load Mint32 m1 b0
                       (Int.unsigned (Int.repr (Int.unsigned i0 / 4096 * 4096 + PTX (Int.unsigned i) * 4)))) eqn: HLD; contra_inv.
      specialize (proj1 (match_inject_forward _ _ _ H4)); intros HDZ.
      rewrite HDZ in *.
      exploit Mem.load_inject; eauto.
      repeat (rewrite Int.add_zero).
      rewrite Z.add_0_r.
      intros [v1'[HLD1 HVAL]].
      rewrite HLD1.
      destruct v; contra_inv. inv HVAL.
      subdestruct.
      eapply exec_flatmem_load_correct; eauto.
    Qed.

    Lemma guest_store_correct1:
      forall {F V} (ge1 ge2: Genv.t F V) m1 m1' m2 d1 d2 d1' rs1 rs2 rs1' f s rd t i ds,
        exec_guest_store1 (flatmem_store:= hflatmem_store) ge1 i t (m1, d1) rs1 rd ds = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1 m1 d1 rs2 m2 d2
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> exists r'0 m2' d2',
             exec_guest_store1 (flatmem_store:= lflatmem_store) ge2 i t (m2, d2) rs2 rd ds = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros. unfold exec_guest_store1 in *.
      pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H1 H2) as [Hpre _].            
      rewrite Hpre.
      destruct  (Genv.find_symbol ge1 NPT_LOC) eqn: HF; contra_inv.
      exploit (stencil_find_symbol_inject (ge:= ge1)); eauto. intros HF0.
      revert H; simpl; lift_trivial; intros H.
      destruct (Mem.load Mint32 m1 b (Int.unsigned (Int.repr (PDX (Int.unsigned i) * 4)))) eqn: HLD; contra_inv.
      pose proof H0 as Hmatch.
      inv H0. inv match_extcall_states.
      exploit Mem.load_inject; eauto.
      rewrite Z.add_0_r; intros [v1[HLD1 HVAL]].
      rewrite HLD1.
      clear HLD HLD1.
      destruct v; contra_inv. inv HVAL.
      destruct (Mem.load Mint32 m1 b0
                         (Int.unsigned (Int.repr (Int.unsigned i0 / 4096 * 4096 + PTX (Int.unsigned i) * 4)))) eqn: HLD; contra_inv.
      specialize (proj1 (match_inject_forward _ _ _ H4)); intros HDZ.
      rewrite HDZ in *.
      exploit Mem.load_inject; eauto.
      repeat (rewrite Int.add_zero).
      rewrite Z.add_0_r.
      intros [v1'[HLD1 HVAL]].
      rewrite HLD1.
      destruct v; contra_inv. inv HVAL.
      subdestruct.
      eapply exec_flatmem_store_correct; eauto.
      apply PTADDR_mod_lt. assumption.
    Qed.

  End General.

End Refinement.