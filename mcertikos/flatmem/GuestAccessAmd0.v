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

Section Load_Store.

  Context `{Hmem: Mem.MemoryModel}.
  Context `{HD: CompatData RData}.
  Context `{Hmwd: UseMemWithData mem}.

  Notation HDATAOps := (cdata (cdata_ops := data_ops) RData).
  
  Section GE.
    
    Context {F V} (ge: Genv.t F V).

      Local Existing Instance Asm.mem_accessors_default.
      Local Existing Instance AsmX.mem_accessors_default_invariant.

      Definition exec_guest_load0 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) (rs: regset) (rd: preg) :=
        let ofs := (Int.unsigned adr) in 
        match (Genv.find_symbol ge NPT_LOC) with
          | Some b => 
            match Mem.loadv Mint32 m (Vptr b (Int.repr ((PDX ofs) * 4))) with
              | Some (Vptr b1 ofs1) =>
                match Mem.loadv Mint32 m (Vptr b1 (Int.repr (((Int.unsigned ofs1)/PgSize)*PgSize + (PTX ofs) *4))) with
                  | Some (Vint n) => 
                    let adr' := (Int.repr (PTADDR ((Int.unsigned n)/PgSize) ofs)) in
                    Asm.exec_load ge chunk m (Addrmode None None (inr (FlatMem_LOC, adr'))) rs rd
                  | _ => Stuck
                end
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_guest_load0_high_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_guest_load0 adr chunk m rs rd = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_guest_load0. intros until m'.
        destruct (Genv.find_symbol ge NPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b (Int.repr (PDX (Int.unsigned adr) * 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        unfold Asm.exec_load.
        destruct (Mem.loadv chunk m
                            (eval_addrmode ge
                                           (Addrmode None None
                                                     (inr (FlatMem_LOC,
                                                           Int.repr (PTADDR (Int.unsigned i0 / 4096) (Int.unsigned adr))))) rs))
        ; try discriminate.
        congruence.
      Qed.

      Lemma exec_guest_load0_asm_invariant:
        forall chunk rd,
        forall TYP: subtype (type_of_chunk chunk) (typ_of_preg rd) = true,
        forall adr m rs rs' m',
          exec_guest_load0 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_guest_load0. intros until m'.
        destruct (Genv.find_symbol ge NPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b (Int.repr (PDX (Int.unsigned adr) * 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        intros; eapply exec_load_invariant; try eassumption.
      Qed.

      Lemma exec_guest_load0_low_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_guest_load0 adr chunk m rs rd = Next rs' m' ->
          CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
          CompatData.low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_guest_load0. intros until m'.
        destruct (Genv.find_symbol ge NPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b (Int.repr (PDX (Int.unsigned adr) * 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        unfold Asm.exec_load.
        destruct (Mem.loadv chunk m
                            (eval_addrmode ge
                                           (Addrmode None None
                                                     (inr (FlatMem_LOC,
                                                           Int.repr (PTADDR (Int.unsigned i0 / 4096) (Int.unsigned adr))))) rs))
        ; try discriminate.
        congruence.
      Qed.

      Definition exec_guest_store0 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) 
                 (rs: regset) (rd: preg) (destroyed: list preg) :=
        let ofs := (Int.unsigned adr) in 
        match (Genv.find_symbol ge NPT_LOC) with
          | Some b => 
            match Mem.loadv Mint32 m (Vptr b (Int.repr ((PDX ofs) * 4))) with
              | Some (Vptr b1 ofs1) =>
                match Mem.loadv Mint32 m (Vptr b1 (Int.repr (((Int.unsigned ofs1)/PgSize)*PgSize + (PTX ofs) *4))) with
                  | Some (Vint n) => 
                    let adr' := (Int.repr (PTADDR ((Int.unsigned n)/PgSize) ofs)) in
                    Asm.exec_store ge chunk m (Addrmode None None (inr (FlatMem_LOC, adr'))) rs rd destroyed
                  | _ => Stuck
                end
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_guest_store0_high_level_invariant:
        forall adr chunk m rs rd rs' ds m',
          exec_guest_store0 adr chunk m rs rd ds = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_guest_store0. intros until m'.
        destruct (Genv.find_symbol ge NPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b (Int.repr (PDX (Int.unsigned adr) * 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        unfold Asm.exec_store.
        destruct (Mem.storev chunk m
                             (eval_addrmode ge
                                            (Addrmode None None
                                                      (inr (FlatMem_LOC,
                                                            Int.repr (PTADDR (Int.unsigned i0 / 4096) (Int.unsigned adr))))) rs)
                             (rs rd)) eqn:Heqo; try discriminate.
        destruct (eval_addrmode ge
                                (Addrmode None None
                                          (inr (FlatMem_LOC,
                                                Int.repr (PTADDR (Int.unsigned i0 / 4096) (Int.unsigned adr)))))
                                rs); try discriminate.
        lift_unfold.
        destruct Heqo as [? DATA].
        unfold π_data in DATA. simpl in * |- *. congruence.
      Qed.

      Lemma exec_guest_store0_asm_invariant:
        forall chunk rd,
        forall adr m rs rs' ds m',
          exec_guest_store0 adr chunk m rs rd ds = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_guest_store0. intros until m'.
        destruct (Genv.find_symbol ge NPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b (Int.repr (PDX (Int.unsigned adr) * 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4))));
          try discriminate.
        destruct v; try discriminate.
        intros; eapply exec_store_invariant; try eassumption.
      Qed.

      Lemma exec_guest_store0_low_level_invariant:
        forall adr chunk m rs rd rs' ds m',
          exec_guest_store0 adr chunk m rs rd ds = Next rs' m' ->
          CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
          CompatData.low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_guest_store0. intros until m'.
        destruct (Genv.find_symbol ge NPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b (Int.repr (PDX (Int.unsigned adr) * 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        unfold Asm.exec_store.
        destruct (Mem.storev chunk m
                             (eval_addrmode ge
                                            (Addrmode None None
                                                      (inr (FlatMem_LOC,
                                                            Int.repr (PTADDR (Int.unsigned i0 / 4096) (Int.unsigned adr))))) rs)
                             (rs rd)) eqn:Heqo; try discriminate.
        destruct (eval_addrmode ge
                                (Addrmode None None
                                          (inr (FlatMem_LOC,
                                                Int.repr (PTADDR (Int.unsigned i0 / 4096) (Int.unsigned adr)))))
                                rs); try discriminate.
        lift_unfold.
        destruct Heqo as [? DATA].
        unfold π_data in DATA. simpl in * |- *. 
        injection 1; intros; subst.
        erewrite Mem.nextblock_store; eauto.
        congruence.
      Qed.      

  End GE.      

End Load_Store.