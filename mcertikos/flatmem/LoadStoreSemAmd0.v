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
Require Import HostAccess0.
Require Import GuestAccess0.
Require Export LoadStoreDef.

Section Load_Store.

  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.
  Context `{HD: CompatData RData}.

  Notation HDATAOps := (cdata (cdata_ops := data_ops) RData).

  Section GE.
    
    Context {F V} (ge: Genv.t F V).

    Definition exec_loadex0 (chunk: memory_chunk) (m: mwd HDATAOps)
               (a: addrmode) (rs: regset) (rd: preg) :=
      let adt:= (snd m) in
      match (eval_addrmode ge a rs) with
        | Vptr b ofs => 
          match (ikern adt, ihost adt) with
            | (true, true) => Asm.exec_load ge chunk m a rs rd
            | _ => Stuck     
          end
        | Vint adr => 
          match (ihost adt, pg adt) with
            | (true, true) => exec_host_load0 ge adr chunk m rs rd
            | (false, _) => exec_guest_load0 ge adr chunk m rs rd                                         
            | _ => Stuck
          end
        | _ => Stuck
      end.

    Definition exec_storeex0 (chunk: memory_chunk) (m: mwd HDATAOps)
               (a: addrmode) (rs: regset) (rd: preg) (destroyed: list preg) := 
      let adt:= (snd m) in
      match  (eval_addrmode ge a rs) with
        | Vptr b ofs => 
          match (ikern adt, ihost adt) with
            | (true, true) => Asm.exec_store ge chunk m a rs rd destroyed
            | _ => Stuck     
          end
        | Vint adr => 
          match (ihost adt, pg adt) with
            | (true, true) => exec_host_store0 ge adr chunk m rs rd destroyed
            | (false, _) => exec_guest_store0 ge adr chunk m rs rd destroyed                                         
            | _ => Stuck
          end
        | _ => Stuck
      end.

    Local Existing Instance Asm.mem_accessors_default.
    Local Existing Instance AsmX.mem_accessors_default_invariant.

    Context `{trap_inv: TrapinfoSetInvariant (data_ops := data_ops)}.

    Lemma exec_loadex0_high_level_invariant:
      forall adr chunk m rs rd rs' m',
        exec_loadex0 chunk m adr rs rd = Next rs' m' ->
        high_level_invariant (snd m) ->
        high_level_invariant (snd m').
    Proof.
      unfold exec_loadex0. intros until m'.
      destruct (eval_addrmode ge adr rs); try discriminate.
      - destruct (ihost (snd m)); try discriminate.
        destruct (pg (snd m)); try discriminate.
        + eapply exec_host_load0_high_level_invariant; eauto.
        + eapply exec_guest_load0_high_level_invariant; eauto.
      - destruct (ikern (snd m)); try discriminate.
        destruct (ihost (snd m)); try discriminate.
        unfold Asm.exec_load. 
        destruct (Mem.loadv chunk m (eval_addrmode ge adr rs)); 
          try discriminate. congruence.
    Qed.

    Lemma exec_loadex0_asm_invariant:
      forall chunk rd,
      forall TYP: subtype (type_of_chunk chunk) (typ_of_preg rd) = true,
      forall adr m rs rs' m',
        exec_loadex0 chunk m adr rs rd = Next rs' m' ->
        AsmX.asm_invariant ge rs m ->
        AsmX.asm_invariant ge rs' m'.
    Proof.
      unfold exec_loadex0. intros until m'.
      destruct (eval_addrmode ge adr rs); try discriminate.
      - destruct (ihost (snd m)); try discriminate.
        destruct (pg (snd m)); try discriminate.
        + eapply exec_host_load0_asm_invariant; eauto.
        + intros; eapply exec_guest_load0_asm_invariant; eauto.
      - destruct (ikern (snd m)); try discriminate.
        destruct (ihost (snd m)); try discriminate.
        intros; eapply exec_load_invariant; eauto.
    Qed.

    Lemma exec_loadex0_low_level_invariant:
      forall adr chunk m rs rd rs' m',
        exec_loadex0 chunk m adr rs rd = Next rs' m' ->
        AsmX.asm_invariant ge rs m ->
        CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
        CompatData.low_level_invariant (Mem.nextblock m') (snd m').
    Proof.
      unfold exec_loadex0. intros until m'.
      destruct (eval_addrmode ge adr rs); try discriminate.
      - destruct (ihost (snd m)); try discriminate.
        destruct (pg (snd m)); try discriminate.
        + eapply exec_host_load0_low_level_invariant; eauto.
        + intros; eapply exec_guest_load0_low_level_invariant; eauto.
      - destruct (ikern (snd m)); try discriminate.
        destruct (ihost (snd m)); try discriminate.
        unfold Asm.exec_load. 
        destruct (Mem.loadv chunk m (eval_addrmode ge adr rs)); try discriminate.
        congruence.
    Qed.

    Lemma exec_storeex0_high_level_invariant:
      forall adr chunk m rs rd des rs' m',
        exec_storeex0 chunk m adr rs rd des = Next rs' m' ->
        high_level_invariant (snd m) ->
        high_level_invariant (snd m').
    Proof.
      unfold exec_storeex0. intros until m'.
      destruct (eval_addrmode ge adr rs); try discriminate.
      - destruct (ihost (snd m)); try discriminate.
        destruct (pg (snd m)); try discriminate.
        + eapply exec_host_store0_high_level_invariant; eauto.
        + eapply exec_guest_store0_high_level_invariant; eauto.
      - destruct (ikern (snd m)); try discriminate.
        destruct (ihost (snd m)); try discriminate.
        unfold Asm.exec_store. 
        destruct (Mem.storev chunk m (eval_addrmode ge adr rs) (rs rd)) eqn:Heqo; 
          try discriminate.
        destruct (eval_addrmode ge adr rs); try discriminate.
        lift_unfold.
        destruct Heqo as [? DATA].
        unfold π_data in DATA. simpl in * |- *. congruence.
    Qed.

    Lemma exec_storeex0_asm_invariant:
      forall chunk rd,
      forall adr m des rs rs' m',
        exec_storeex0 chunk m adr rs rd des = Next rs' m' ->
        AsmX.asm_invariant ge rs m ->
        AsmX.asm_invariant ge rs' m'.
    Proof.
      unfold exec_storeex0. intros until m'.
      destruct (eval_addrmode ge adr rs); try discriminate.
      - destruct (ihost (snd m)); try discriminate.
        destruct (pg (snd m)); try discriminate.
        + eapply exec_host_store0_asm_invariant; eauto.
        + intros; eapply exec_guest_store0_asm_invariant; eauto.
      - destruct (ikern (snd m)); try discriminate.
        destruct (ihost (snd m)); try discriminate.
        intros; eapply exec_store_invariant; eauto.
    Qed.

    Lemma exec_storeex0_low_level_invariant:
      forall adr chunk m rs rd des rs' m',
        exec_storeex0 chunk m adr rs rd des = Next rs' m' ->
        AsmX.asm_invariant ge rs m ->
        CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
        CompatData.low_level_invariant (Mem.nextblock m') (snd m').
    Proof.
      unfold exec_storeex0. intros until m'.
      destruct (eval_addrmode ge adr rs); try discriminate.
      - destruct (ihost (snd m)); try discriminate.
        destruct (pg (snd m)); try discriminate.
        + eapply exec_host_store0_low_level_invariant; eauto.
        + intros; eapply exec_guest_store0_low_level_invariant; eauto.
      - destruct (ikern (snd m)); try discriminate.
        destruct (ihost (snd m)); try discriminate.
        unfold Asm.exec_store. destruct (Mem.storev chunk m (eval_addrmode ge adr rs) (rs rd)) eqn:Heqo; 
                               try discriminate.
        destruct (eval_addrmode ge adr rs); try discriminate.
        lift_unfold.
        destruct Heqo as [? DATA].
        unfold π_data in DATA. simpl in * |- *.
        injection 1; intros; subst.
        erewrite Mem.nextblock_store; eauto.
        congruence.
    Qed.

  End GE.      

  Context `{KernelModeImplies (data_ops:= data_ops)}.
  Context `{TrapinfoSetInvariant (data_ops:= data_ops)}.

  Global Instance load_accessor_prf0 :
    LoadAccessor _ (@exec_loadex0).
  Proof.
    constructor.
    {
      unfold exec_loadex0.
      intros.
      erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
      destruct (eval_addrmode ge1 a rs); try reflexivity.
      - destruct (ihost (snd m)); try reflexivity.
        destruct (pg (snd m)); try reflexivity.
        + unfold exec_host_load0.
          destruct (CR3 (snd m)); try reflexivity.
          unfold exec_host_load_snd0.
          unfold exec_pagefault. repeat rewrite SYMB.
          destruct (Genv.find_symbol ge1 b); try reflexivity.
          destruct (Mem.loadv Mint32 m
                              (Vptr b0 (Int.repr (Int.unsigned ofs + PDX (Int.unsigned i) * 4)))); try reflexivity.
          destruct v; try reflexivity.
          * destruct (Genv.find_symbol ge1 FlatMem_LOC); try reflexivity.
            destruct (Mem.loadv Mint32 m
                                (Vptr b1
                                      (Int.repr
                                         (Int.unsigned i0 / 4096 * 4096 + PTX (Int.unsigned i) * 4)))); try reflexivity.
            destruct v; try reflexivity.
            unfold Asm.exec_load. 
            erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
          (** destruct (Mem.loadv Mint32 m
                                (Vptr b1
                                      (Int.repr
                                         (Int.unsigned i0 / 4096 * 4096 + PTX (Int.unsigned i) * 4)))); try reflexivity.
            destruct v; try reflexivity.
            unfold Asm.exec_load. 
            erewrite AsmX.eval_addrmode_symbols_preserved; eauto.*)
        + unfold exec_guest_load0.
          repeat rewrite SYMB.
          destruct (Genv.find_symbol ge1 NPT_LOC); try reflexivity.
          destruct (Mem.loadv Mint32 m
                              (Vptr b (Int.repr (PDX (Int.unsigned i) * 4)))); try reflexivity.
          destruct v; try reflexivity.
          destruct (Mem.loadv Mint32 m
                              (Vptr b0
                                    (Int.repr
                                       (Int.unsigned i0 / 4096 * 4096 + PTX (Int.unsigned i) * 4)))); try reflexivity.
          destruct v; try reflexivity.
          unfold Asm.exec_load. 
          erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
      - unfold Asm.exec_load. erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
    }
    {
      intros.
      apply kernel_mode_implies in H2.
      destruct H2 as [IKERN IHOST].
      unfold exec_loadex0.
      unfold Asm.exec_load in H1 |- *.
      destruct (eval_addrmode ge a rs); try discriminate.
      unfold π_data in IKERN, IHOST.
      rewrite IKERN. rewrite IHOST.
      assumption.
    }
    {
      intros; eapply exec_loadex0_asm_invariant; eauto.
    }     
    {
      intros; eapply exec_loadex0_low_level_invariant; eauto.
    }
    {
      intros; eapply exec_loadex0_high_level_invariant; eauto.
    }
  Qed.

  Global Instance store_accessor_prf0:
    StoreAccessor _ (@exec_storeex0).
  Proof.
    constructor.
    {
      unfold exec_storeex0.
      intros.
      erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
      destruct (eval_addrmode ge1 a rs); try reflexivity.
      - destruct (ihost (snd m)); try reflexivity.
        destruct (pg (snd m)); try reflexivity.
        + unfold exec_host_store0.
          destruct (CR3 (snd m)); try reflexivity.
          unfold exec_host_store_snd0.
          unfold exec_pagefault. repeat rewrite SYMB.
          destruct (Genv.find_symbol ge1 b); try reflexivity.
          destruct (Mem.loadv Mint32 m
                              (Vptr b0 (Int.repr (Int.unsigned ofs + PDX (Int.unsigned i) * 4)))); try reflexivity.
          destruct v; try reflexivity.
          * destruct (Genv.find_symbol ge1 FlatMem_LOC); try reflexivity.
            destruct (Mem.loadv Mint32 m
                                (Vptr b1
                                      (Int.repr
                                         (Int.unsigned i0 / 4096 * 4096 + PTX (Int.unsigned i) * 4)))); try reflexivity.
            destruct v; try reflexivity.
            unfold Asm.exec_store. 
            erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
          (** destruct (Mem.loadv Mint32 m
                                (Vptr b1
                                      (Int.repr
                                         (Int.unsigned i0 / 4096 * 4096 + PTX (Int.unsigned i) * 4)))); try reflexivity.
            destruct v; try reflexivity.
            unfold Asm.exec_store. 
            erewrite AsmX.eval_addrmode_symbols_preserved; eauto.*)
        + unfold exec_guest_store0.
          repeat rewrite SYMB.
          destruct (Genv.find_symbol ge1 NPT_LOC); try reflexivity.
          destruct (Mem.loadv Mint32 m
                              (Vptr b (Int.repr (PDX (Int.unsigned i) * 4)))); try reflexivity.
          destruct v; try reflexivity.
          destruct (Mem.loadv Mint32 m
                              (Vptr b0
                                    (Int.repr
                                       (Int.unsigned i0 / 4096 * 4096 + PTX (Int.unsigned i) * 4)))); try reflexivity.
          destruct v; try reflexivity.
          unfold Asm.exec_store. 
          erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
      - unfold Asm.exec_store. erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
    }
    {
      intros.
      apply kernel_mode_implies in H2.
      destruct H2 as [IKERN IHOST].
      unfold exec_storeex0.
      unfold Asm.exec_store in H1 |- *.
      destruct (eval_addrmode ge a rs); try discriminate.
      unfold π_data in IKERN, IHOST.
      rewrite IKERN. rewrite IHOST.
      assumption.
    }
    {
      intros; eapply exec_storeex0_asm_invariant; eauto.
    }     
    {
      intros; eapply exec_storeex0_low_level_invariant; eauto.
    }
    {
      intros; eapply exec_storeex0_high_level_invariant; eauto.
    }
  Qed.

End Load_Store.