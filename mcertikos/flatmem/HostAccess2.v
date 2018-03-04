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
  
  Section GE.
    
    Context {F V} (ge: Genv.t F V).

    Section Load_Store2.

      Definition exec_host_load2 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) (rs: regset) (rd: preg) :=
        let adt:= (snd m) in
        let ofs := (Int.unsigned adr) in 
        match ZMap.get (PDX ofs) (ZMap.get (PT adt) (ptpool adt))with
          | PDEValid _ pte => 
            if (zle (ofs mod PgSize) (PgSize - size_chunk chunk)) then
              if (Zdivide_dec (align_chunk chunk) (ofs mod PgSize) (align_chunk_pos chunk)) then
                match ZMap.get (PTX ofs) pte with 
                  | PTEValid v p => 
                    match p with
                      | PTK _ => Stuck
                      | _ => exec_flatmem_load chunk m (PTADDR v ofs) rs rd     
                    end
                  | PTEUnPresent => exec_pagefault ge m adr rs
                  |_ => Stuck
                end
              else Stuck
            else Stuck
          | _ => Stuck
        end.

      Context `{trap_inv: TrapinfoSetInvariant (Obs:=Obs) (data_ops := data_ops)}.

      Lemma exec_host_load2_high_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_host_load2 adr chunk m rs rd = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_host_load2. intros until m'.
        destruct (
            ZMap.get (PDX (Int.unsigned adr))
                     (ZMap.get (PT (snd m)) (ptpool (snd m)))
          ); try discriminate.
        destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
        destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                              (align_chunk_pos chunk)); contra_inv.
        destruct (ZMap.get (PTX (Int.unsigned adr)) pte); try discriminate.
        destruct p; try discriminate.
        * intros. exploit exec_flatmem_load_mem; eauto. congruence.
        * intros. exploit exec_flatmem_load_mem; eauto. congruence.
        * eapply exec_pagefault_high_level_invariant; eauto.
      Qed.

      Lemma exec_host_load2_asm_invariant:
        forall chunk rd,
        forall TYP: subtype (type_of_chunk chunk) (typ_of_preg rd) = true,
        forall adr m rs rs' m',
          exec_host_load2 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_host_load2. intros until m'.
        destruct (
            ZMap.get (PDX (Int.unsigned adr))
                     (ZMap.get (PT (snd m)) (ptpool (snd m)))
          ); try discriminate.
        destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
        destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                              (align_chunk_pos chunk)); contra_inv.
        destruct (ZMap.get (PTX (Int.unsigned adr)) pte); try discriminate.
        destruct p; try discriminate.
        * intros; eapply exec_flatmem_load_asm_invariant; eauto.
        * intros; eapply exec_flatmem_load_asm_invariant; eauto.
        * intros; eapply exec_pagefault_asm_invariant; eauto.
      Qed.

      Lemma exec_host_load2_low_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_host_load2 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
          CompatData.low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_host_load2. intros until m'.
        destruct (
            ZMap.get (PDX (Int.unsigned adr))
                     (ZMap.get (PT (snd m)) (ptpool (snd m)))
          ); try discriminate.
        destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
        destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                              (align_chunk_pos chunk)); contra_inv.
        destruct (ZMap.get (PTX (Int.unsigned adr)) pte); try discriminate.
        destruct p; try discriminate.
        * intros. exploit exec_flatmem_load_mem; eauto. congruence.
        * intros. exploit exec_flatmem_load_mem; eauto. congruence.
        * eapply exec_pagefault_low_level_invariant; eauto.
      Qed.

      Context `{flatmem_store: RData -> memory_chunk -> Z -> val -> option (cdata RData)}.

      Definition exec_host_store2 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) 
                 (rs: regset) (rd: preg) (destroyed: list preg) :=
        let adt:= (snd m) in
        let ofs := (Int.unsigned adr) in 
        match ZMap.get (PDX ofs) (ZMap.get (PT adt) (ptpool adt)) with
          | PDEValid _ pte => 
            if (zle (ofs mod PgSize) (PgSize - size_chunk chunk)) then
              if (Zdivide_dec (align_chunk chunk) (ofs mod PgSize) (align_chunk_pos chunk)) then
                match ZMap.get (PTX ofs) pte with 
                  | PTEValid v p => 
                    match p with
                      | PTK _ => Stuck
                      | _ => exec_flatmem_store (flatmem_store:= flatmem_store) chunk m (PTADDR v ofs) rs rd destroyed
                    end
                  | PTEUnPresent => exec_pagefault ge m adr rs
                  |_ => Stuck
                end
              else Stuck
            else Stuck
          | _ => Stuck
        end.

      Context {flat_inv: FlatmemStoreInvariant (data_ops := data_ops) (flatmem_store:= flatmem_store)}.

      Lemma exec_host_store2_high_level_invariant:
        forall adr chunk m rs rd rs' ds m',
          exec_host_store2 adr chunk m rs rd ds = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_host_store2. intros until m'.
        destruct (
            ZMap.get (PDX (Int.unsigned adr))
                     (ZMap.get (PT (snd m)) (ptpool (snd m)))
          ); try discriminate.
        destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
        destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                              (align_chunk_pos chunk)); contra_inv.
        destruct (ZMap.get (PTX (Int.unsigned adr)) pte); try discriminate.
        destruct p; try discriminate.
        * intros; eapply exec_flatmem_store_high_level_invariant; eauto.
          eapply PTADDR_mod_lt. assumption.
        * intros; eapply exec_flatmem_store_high_level_invariant; eauto.
          eapply PTADDR_mod_lt. assumption.
        * eapply exec_pagefault_high_level_invariant; eauto.
      Qed.

      Lemma exec_host_store2_asm_invariant:
        forall chunk rd,
        forall adr m rs rs' ds m',
          exec_host_store2 adr chunk m rs rd ds = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_host_store2. intros until m'.
        destruct (
            ZMap.get (PDX (Int.unsigned adr))
                     (ZMap.get (PT (snd m)) (ptpool (snd m)))
          ); try discriminate.
        destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
        destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                              (align_chunk_pos chunk)); contra_inv.
        destruct (ZMap.get (PTX (Int.unsigned adr)) pte); try discriminate.
        destruct p; try discriminate.
        * intros; eapply exec_flatmem_store_asm_invariant; eauto.
        * intros; eapply exec_flatmem_store_asm_invariant; eauto.
        * intros; eapply exec_pagefault_asm_invariant; eauto.
      Qed.

      Lemma exec_host_store2_low_level_invariant:
        forall adr chunk m rs rd rs' ds m',
          exec_host_store2 adr chunk m rs rd ds = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
          CompatData.low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_host_store2. intros until m'.
        destruct (
            ZMap.get (PDX (Int.unsigned adr))
                     (ZMap.get (PT (snd m)) (ptpool (snd m)))
          ); try discriminate.
        destruct (zle (Int.unsigned adr mod 4096) (4096 - size_chunk chunk)); contra_inv.
        destruct (Zdivide_dec (align_chunk chunk) (Int.unsigned adr mod 4096)
                              (align_chunk_pos chunk)); contra_inv.
        destruct (ZMap.get (PTX (Int.unsigned adr)) pte); try discriminate.
        destruct p; try discriminate.
        * intros; eapply exec_flatmem_store_low_level_invariant; eauto.
        * intros; eapply exec_flatmem_store_low_level_invariant; eauto.
        * eapply exec_pagefault_low_level_invariant; eauto.
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
    Context {re1: relate_impl_PT}.
    Context {re2: relate_impl_ptpool}.
    Context {re3: relate_impl_HP'}.

    Lemma host_load_correct2:
      forall {F V} (ge1 ge2: Genv.t F V) t m1 m1' m2 d1 d2 d1' rs1 rd rs2 rs1' f i s,
        exec_host_load2 ge1 i t (m1, d1) rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1 m1 d1 rs2 m2 d2
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> exists r'0 m2' d2',
             exec_host_load2 ge2 i t (m2, d2) rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      Local Opaque Z.sub.
      intros. unfold exec_host_load2 in *; simpl in *.
      pose proof H0 as HM. inv H0. inv match_extcall_states.
      exploit relate_impl_PT_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto. intros.
      rewrite <- H3, <- H0. subdestruct.
      - eapply exec_flatmem_load_correct; eauto.
      - eapply exec_flatmem_load_correct; eauto.
      - eapply pagefault_correct; eauto.
    Qed.

    Lemma host_store_correct2:
      forall {F V} (ge1 ge2: Genv.t F V) t m1 m1' m2 d1 d2 d1' rs1 rd rs2 rs1' f i s ds,
        exec_host_store2 (flatmem_store:= hflatmem_store) ge1 i t (m1, d1) rs1 rd ds = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1 m1 d1 rs2 m2 d2
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> exists r'0 m2' d2',
             exec_host_store2 (flatmem_store:= lflatmem_store) ge2 i t (m2, d2) rs2 rd ds = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros. unfold exec_host_store2 in *; simpl in *.
      pose proof H0 as HM. inv H0. inv match_extcall_states.
      exploit relate_impl_PT_eq; eauto.
      exploit relate_impl_ptpool_eq; eauto. intros.
      rewrite <- H3, <- H0. subdestruct.
      - eapply exec_flatmem_store_correct; eauto.
        apply PTADDR_mod_lt. assumption.
      - eapply exec_flatmem_store_correct; eauto.
        apply PTADDR_mod_lt. assumption.
      - eapply pagefault_correct; eauto.
    Qed.

  End General.  

End Refinement.