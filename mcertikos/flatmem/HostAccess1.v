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
Require Export PageFault.
Require Export FlatLoadStoreSem.
Require Import LoadStoreDef.

Section Load_Store.

  Context `{Hobs: Observation}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{HD: CompatData(Obs:=Obs) RData}.
  Context `{Hmwd: UseMemWithData mem}.

  Notation HDATAOps := (cdata (cdata_ops := data_ops) RData).
  Context `{flatmem_store: RData -> memory_chunk -> Z -> val -> option (cdata RData)}.
  
  Section GE.
    
    Context {F V} (ge: Genv.t F V).

    Section Load_Store1.

      Definition exec_host_load1 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) (rs: regset) (rd: preg):=
        let adt:= (snd m) in
        let ofs := (Int.unsigned adr) in 
        match (CR3 adt) with
          | GLOBP idpt ofs' =>
            match Genv.find_symbol ge idpt with
              | Some b =>
                match Mem.loadv Mint32 m (Vptr b (Int.repr ((Int.unsigned ofs') + (PDX ofs) * 4))) with
                  | Some (Vint ofs1) =>
                    match FlatMem.load Mint32 (HP (snd m)) (((Int.unsigned ofs1)/PgSize)*PgSize + (PTX ofs) *4) with
                      | Vint n => 
                        let pz:= (Int.unsigned n) mod PgSize in
                        let adr' := (PTADDR ((Int.unsigned n)/PgSize) ofs) in
                        if (zle (ofs mod PgSize) (PgSize - size_chunk chunk)) then
                          if (Zdivide_dec (align_chunk chunk) (ofs mod PgSize) (align_chunk_pos chunk)) then
                            if zeq pz PT_PERM_P then
                              exec_flatmem_load chunk m adr' rs rd
                            else 
                              if zeq pz PT_PERM_PTU then
                                exec_flatmem_load chunk m adr' rs rd
                              else
                                if zeq pz PT_PERM_UP then
                                  exec_pagefault ge m adr rs
                                else
                                  Stuck
                          else
                            Stuck
                        else Stuck
                      | _ => Stuck
                    end
                  (*| Some (Vptr b1 ofs1) => 
                    match Genv.find_symbol ge IDPMap_LOC with
                      | Some b2 =>
                        if Pos.eq_dec b1 b2 then
                          exec_host_load_snd0 adr chunk m rs rd b1 ofs1 IDPMap_LOC
                        else Stuck
                      | _ => Stuck
                    end*)
                  | _ => Stuck
                end
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Context `{trap_inv: TrapinfoSetInvariant (Obs:=Obs) (data_ops := data_ops)}.

      Lemma exec_host_load1_high_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_host_load1 adr chunk m rs rd = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_host_load1. intros until m'.
        destruct (CR3 (snd m)); try discriminate.
        destruct (Genv.find_symbol ge b); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned ofs + PDX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        - destruct (FlatMem.load Mint32 (HP (snd m)) (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4));
          try discriminate.
          destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
          destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                                (align_chunk_pos chunk)); contra_inv.
          destruct (zeq (Int.unsigned i0 mod 4096) 1); try discriminate.
          + intros. exploit exec_flatmem_load_mem; eauto. congruence.
          + destruct (zeq (Int.unsigned i0 mod 4096) 7).
            * intros. exploit exec_flatmem_load_mem; eauto. congruence.
            * destruct (zeq (Int.unsigned i0 mod 4096) 0); try discriminate.
              eapply exec_pagefault_high_level_invariant. assumption.
        (*- destruct (Genv.find_symbol ge IDPMap_LOC); try discriminate.
          destruct (Pos.eq_dec b1 b2); try discriminate.
          eapply exec_host_load_snd0_high_level_invariant; eauto.*)
      Qed.

      Lemma exec_host_load1_asm_invariant:
        forall chunk rd,
        forall TYP: subtype (type_of_chunk chunk) (typ_of_preg rd) = true,
        forall adr m rs rs' m',
          exec_host_load1 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_host_load1. intros until m'.
        destruct (CR3 (snd m)); try discriminate.
        destruct (Genv.find_symbol ge b); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned ofs + PDX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        - destruct (FlatMem.load Mint32 (HP (snd m)) (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)); 
          try discriminate.
          destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
          destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                                (align_chunk_pos chunk)); contra_inv.
          destruct (zeq (Int.unsigned i0 mod 4096) 1); try discriminate.
          + intros; eapply exec_flatmem_load_asm_invariant; eauto.
          + destruct (zeq (Int.unsigned i0 mod 4096) 7).
            * intros; eapply exec_flatmem_load_asm_invariant; eauto.
            * destruct (zeq (Int.unsigned i0 mod 4096) 0); try discriminate.
              intros; eapply exec_pagefault_asm_invariant; eauto.
        (*- destruct (Genv.find_symbol ge IDPMap_LOC); try discriminate.
          destruct (Pos.eq_dec b1 b2); try discriminate.
          eapply exec_host_load_snd0_asm_invariant; eauto.*)
      Qed.

      Lemma exec_host_load1_low_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_host_load1 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
          CompatData.low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_host_load1. intros until m'.
        destruct (CR3 (snd m)); try discriminate.
        destruct (Genv.find_symbol ge b); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned ofs + PDX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        - destruct (FlatMem.load Mint32 (HP (snd m)) (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)); 
          try discriminate.
          destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
          destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                                (align_chunk_pos chunk)); contra_inv.
          destruct (zeq (Int.unsigned i0 mod 4096) 1); try discriminate.
          + intros. exploit exec_flatmem_load_mem; eauto. congruence.
          + destruct (zeq (Int.unsigned i0 mod 4096) 7).
            * intros. exploit exec_flatmem_load_mem; eauto. congruence.
            * destruct (zeq (Int.unsigned i0 mod 4096) 0); try discriminate.
              eapply exec_pagefault_low_level_invariant. assumption.
        (*- destruct (Genv.find_symbol ge IDPMap_LOC); try discriminate.
          destruct (Pos.eq_dec b1 b2); try discriminate.
          eapply exec_host_load_snd0_low_level_invariant; eauto.*)
      Qed.

      Definition exec_host_store1 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) 
                 (rs: regset) (rd: preg) (destroyed: list preg) :=
        let adt:= (snd m) in
        let ofs := (Int.unsigned adr) in 
        match (CR3 adt) with
          | GLOBP idpt ofs' =>
            match Genv.find_symbol ge idpt with
              | Some b =>
                match Mem.loadv Mint32 m (Vptr b (Int.repr ((Int.unsigned ofs') + (PDX ofs) * 4))) with
                  | Some (Vint ofs1) =>
                    match FlatMem.load Mint32 (HP (snd m)) (((Int.unsigned ofs1)/PgSize)*PgSize + (PTX ofs) *4) with
                      | Vint n => 
                        let pz:= (Int.unsigned n) mod PgSize in
                        let adr' := (PTADDR ((Int.unsigned n)/PgSize) ofs) in
                        if (zle (ofs mod PgSize) (PgSize - size_chunk chunk)) then
                          if (Zdivide_dec (align_chunk chunk) (ofs mod PgSize) (align_chunk_pos chunk)) then
                            if zeq pz PT_PERM_P then
                              exec_flatmem_store (flatmem_store:= flatmem_store) chunk m adr' rs rd destroyed
                            else 
                              if zeq pz PT_PERM_PTU then
                                exec_flatmem_store (flatmem_store:= flatmem_store) chunk m adr' rs rd destroyed
                              else
                                if zeq pz PT_PERM_UP then
                                  exec_pagefault ge m adr rs
                                else
                                  Stuck
                          else
                            Stuck
                        else Stuck
                      | _ => Stuck
                    end
                  (*| Some (Vptr b1 ofs1) => 
                    match Genv.find_symbol ge IDPMap_LOC with
                      | Some b2 =>
                        if Pos.eq_dec b1 b2 then
                          exec_host_store_snd0 adr chunk m rs rd destroyed b1 ofs1 IDPMap_LOC
                        else Stuck
                      | _ => Stuck
                    end*)
                  | _ => Stuck
                end
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Context {flat_inv: FlatmemStoreInvariant (data_ops := data_ops) (flatmem_store:= flatmem_store)}.

      Lemma exec_host_store1_high_level_invariant:
        forall adr chunk m rs rd rs' ds m',
          exec_host_store1 adr chunk m rs rd ds = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_host_store1. intros until m'.
        destruct (CR3 (snd m)); try discriminate.
        destruct (Genv.find_symbol ge b); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned ofs + PDX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        {
          destruct (FlatMem.load Mint32 (HP (snd m)) (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)); 
          try discriminate.
          destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
          specialize (PTADDR_mod_lt _ _ l (Int.unsigned i0 / PgSize)). intros.
          destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                                (align_chunk_pos chunk)); contra_inv.
          destruct (zeq (Int.unsigned i0 mod 4096) 1); try discriminate.
          - intros; eapply exec_flatmem_store_high_level_invariant; eauto 1.
          - destruct (zeq (Int.unsigned i0 mod 4096) 7).
            + intros; eapply exec_flatmem_store_high_level_invariant; eauto.
            + destruct (zeq (Int.unsigned i0 mod 4096) 0); try discriminate.
              eapply exec_pagefault_high_level_invariant; eassumption.
        }
        (*{
          destruct (Genv.find_symbol ge IDPMap_LOC); try discriminate.
          destruct (Pos.eq_dec b1 b2); try discriminate.
          eapply exec_host_store_snd0_high_level_invariant; eauto.
        }*)
      Qed.

      Lemma exec_host_store1_asm_invariant:
        forall chunk rd,
        forall adr m rs rs' ds m',
          exec_host_store1 adr chunk m rs rd ds = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_host_store1. intros until m'.
        destruct (CR3 (snd m)); try discriminate.
        destruct (Genv.find_symbol ge b); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned ofs + PDX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        - destruct (FlatMem.load Mint32 (HP (snd m)) (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)); 
          try discriminate.
          destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
          destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                                (align_chunk_pos chunk)); contra_inv.
          destruct (zeq (Int.unsigned i0 mod 4096) 1); try discriminate.
          + intros; eapply exec_flatmem_store_asm_invariant; eauto.
          + destruct (zeq (Int.unsigned i0 mod 4096) 7).
            * intros; eapply exec_flatmem_store_asm_invariant; eauto.
            * destruct (zeq (Int.unsigned i0 mod 4096) 0); try discriminate.
              intros; eapply exec_pagefault_asm_invariant; eauto.
        (*- destruct (Genv.find_symbol ge IDPMap_LOC); try discriminate.
          destruct (Pos.eq_dec b1 b2); try discriminate.
          eapply exec_host_store_snd0_asm_invariant; eauto.*)
      Qed.

      Lemma exec_host_store1_low_level_invariant:
        forall adr chunk m rs rd rs' ds m',
          exec_host_store1 adr chunk m rs rd ds = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
          CompatData.low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_host_store1. intros until m'.
        destruct (CR3 (snd m)); try discriminate.
        destruct (Genv.find_symbol ge b); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned ofs + PDX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        - destruct (FlatMem.load Mint32 (HP (snd m)) (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)); 
          try discriminate.
          destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
          destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                                (align_chunk_pos chunk)); contra_inv.
          destruct (zeq (Int.unsigned i0 mod 4096) 1); try discriminate.
          + intros; eapply exec_flatmem_store_low_level_invariant; eauto.
          + destruct (zeq (Int.unsigned i0 mod 4096) 7).
            * intros; eapply exec_flatmem_store_low_level_invariant; eauto.
            * destruct (zeq (Int.unsigned i0 mod 4096) 0); try discriminate.
              eapply exec_pagefault_low_level_invariant. assumption.
        (*- destruct (Genv.find_symbol ge IDPMap_LOC); try discriminate.
          destruct (Pos.eq_dec b1 b2); try discriminate.
          eapply exec_host_store_snd0_low_level_invariant; eauto.*)
      Qed.

    End Load_Store1.

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
  
  Section Load_Store1.
 
    Context {loadstoreprop: LoadStoreProp (hflatmem_store:= hflatmem_store) (lflatmem_store:= lflatmem_store)}.
    Context {re: relate_impl_CR3}.
    Context {re1: relate_impl_HP'}.
    Opaque align_chunk Z.mul Z.div Z.sub. 

    Lemma host_load_correct1:
      forall {F V} (ge1 ge2: Genv.t F V) t m1 m1' m2 d1 d2 d1' rs1 rd rs2 rs1' f i s,
        exec_host_load1 ge1 i t (m1, d1) rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1 m1 d1 rs2 m2 d2
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> exists r'0 m2' d2',
             exec_host_load1 ge2 i t (m2, d2) rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' r'0 m2' d2'.
    Proof. 
      intros. unfold exec_host_load1 in *; simpl in *.
      pose proof H0 as Hmatch.
      inv H0. inv match_extcall_states.
      exploit relate_impl_CR3_eq; eauto. intros HCR3.
      rewrite <- HCR3.
      destruct (CR3 d1); contra_inv.
      pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H1 H2) as [Hpre _].            
      repeat rewrite Hpre.
      destruct (Genv.find_symbol ge1 b) eqn:HF; contra_inv.
      revert H. lift_trivial. intros H.
      exploit (stencil_find_symbol_inject (ge:= ge1)); eauto. intros HF0.
      destruct (Mem.load Mint32 m1 b0 (Int.unsigned (Int.repr (Int.unsigned ofs + PDX (Int.unsigned i) * 4)))) eqn: HLD; contra_inv.
      exploit Mem.load_inject; eauto.
      rewrite Z.add_0_r; intros [v1[HLD1 HVAL]].
      rewrite HLD1.
      clear HLD HLD1.
      destruct v; contra_inv; inv HVAL.
      - destruct (FlatMem.load Mint32 (HP d1)
                               (Int.unsigned i0 / 4096 * 4096 + PTX (Int.unsigned i) * 4)) eqn: HLD; contra_inv.
        pose proof match_related as Hflat_inj.
        eapply relate_impl_HP'_eq in Hflat_inj; eauto.
        exploit FlatMem.load_inj; eauto. instantiate (1:= f).
        intros [v1'[HLD1 HVAL]].
        rewrite HLD1. inv HVAL.
        subdestruct.
        eapply exec_flatmem_load_correct; eauto.
        eapply exec_flatmem_load_correct; eauto.
        eapply pagefault_correct; eauto.
      (*- clear HF. destruct (Genv.find_symbol ge1 IDPMap_LOC) eqn: HF; contra_inv.
        destruct (Pos.eq_dec b1 b2); contra_inv; subst.
        exploit (stencil_find_symbol_inject (ge:= ge1)); eauto. intros HF1.
        rewrite H5 in HF1. inv HF1.
        destruct (Pos.eq_dec b2 b2); try congruence.        
        exploit match_inject_forward; eauto 1.
        intros [? _]; subst. rewrite Int.add_zero.
        eapply host_load_snd_correct0; eauto.*)
    Qed.

    Context {flatmemstore_inv: FlatmemStoreInvariant (data_ops:= data_ops) (flatmem_store:= hflatmem_store)}.

    Lemma host_store_correct1:
      forall {F V} (ge1 ge2: Genv.t F V) t m1 m1' m2 d1 d2 d1' rs1 rd rs2 rs1' f i s ds,
        exec_host_store1 (flatmem_store:= hflatmem_store) ge1 i t (m1, d1) rs1 rd ds = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1 m1 d1 rs2 m2 d2
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> exists r'0 m2' d2',
             exec_host_store1 (flatmem_store:= lflatmem_store) ge2 i t (m2, d2) rs2 rd ds = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros. unfold exec_host_store1 in *; simpl in *.
      pose proof H0 as Hmatch.
      inv H0. inv match_extcall_states.
      exploit relate_impl_CR3_eq; eauto. intros HCR3.
      rewrite <- HCR3.
      destruct (CR3 d1); contra_inv.
      pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H1 H2) as [Hpre _].            
      repeat rewrite Hpre.
      destruct (Genv.find_symbol ge1 b) eqn: HF; contra_inv.
      revert H; simpl; lift_trivial; intros H.
      exploit (stencil_find_symbol_inject (ge:= ge1)); eauto. intros HF0.
      destruct (Mem.load Mint32 m1 b0 (Int.unsigned (Int.repr (Int.unsigned ofs + PDX (Int.unsigned i) * 4)))) eqn: HLD; contra_inv.
      exploit Mem.load_inject; eauto.
      rewrite Z.add_0_r; intros [v1[HLD1 HVAL]].
      rewrite HLD1.
      clear HLD HLD1.
      destruct v; contra_inv; inv HVAL.
      - destruct (FlatMem.load Mint32 (HP d1)
                               (Int.unsigned i0 / 4096 * 4096 + PTX (Int.unsigned i) * 4)) eqn: HLD; contra_inv.
        pose proof match_related as Hflat_inj.
        eapply relate_impl_HP'_eq in Hflat_inj; eauto.
        exploit FlatMem.load_inj; eauto. instantiate (1:= f).
        intros [v1'[HLD1 HVAL]].
        rewrite HLD1. inv HVAL.
        subdestruct.
        eapply exec_flatmem_store_correct; eauto.
        apply PTADDR_mod_lt; assumption.
        eapply exec_flatmem_store_correct; eauto.
        apply PTADDR_mod_lt; assumption.
        eapply pagefault_correct; eauto.
      (*- clear HF. destruct (Genv.find_symbol ge1 IDPMap_LOC) eqn: HF; contra_inv.
        destruct (Pos.eq_dec b1 b2); contra_inv; subst.
        exploit (stencil_find_symbol_inject (ge:= ge1)); eauto. intros HF1.
        rewrite H5 in HF1. inv HF1.
        destruct (Pos.eq_dec b2 b2); try congruence.        
        exploit match_inject_forward; eauto 1.
        intros [? _]; subst. rewrite Int.add_zero.
        eapply host_store_snd_correct0; eauto.*)
    Qed.

  End Load_Store1.

End Refinement.