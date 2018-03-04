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

Require Export LoadStoreSem1.
(*
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

(*Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Clight.*)
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.ClightModules.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatClightSem.

(*Require Import LayerDefinition.
Require Import LayerTemplate.*)

Section Load_Store.

  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.
  Context {RData} `{HD: CompatData RData}.

  Context `{HP: RData -> flatmem}.
  Context `{CR3: RData -> globalpointer}.
  Context `{ikern: RData -> bool}.
  Context `{ihost: RData -> bool}.
  Context `{pe: RData -> bool}.
  Context `{PT: RData -> Z}.
  Context `{ptpool: RData -> PTPool}.

  Context `{npt: RData -> NPT}.

  Context `{flatmem_store: RData -> memory_chunk -> Z -> val -> (cdata RData)}.
  Context `{trapinfo_set: RData -> int -> val -> (cdata RData)}.
  
  Definition exec_flatmem_load (chunk: memory_chunk) (m: mwd (cdata RData))
             (adr: Z) (rs: regset) (rd: preg) :=
    let h:= (HP (snd m)) in
    Next (nextinstr_nf (rs#rd <- (FlatMem.load chunk h adr))) m.

  Lemma exec_flatmem_load_mem:
    forall chunk m adr rs rd rs' m',
      exec_flatmem_load chunk m adr rs rd = Next rs' m' ->
      m' = m.
  Proof.
    unfold exec_flatmem_load; simpl; intros; congruence.
  Qed.

  Lemma exec_flatmem_load_asm_invariant:
    forall chunk rd,
    forall TYP: subtype (type_of_chunk chunk) (typ_of_preg rd) = true,
    forall m adr rs rs' m',
      exec_flatmem_load chunk m adr rs rd = Next rs' m' ->
      forall {F V} (ge: _ F V),
        AsmX.asm_invariant ge rs m ->
        AsmX.asm_invariant ge rs' m'.
  Proof.
    unfold exec_flatmem_load; simpl.
    inversion 2; subst.
    inversion 1; subst.
    inversion inv_inject_neutral; subst.
    constructor.
    constructor; auto.
    apply nextinstr_nf_inject.
    apply set_reg_inject; auto.
    generalize (Mem.flat_inj (Mem.nextblock m')).
    generalize (HP (@snd mem RData m')).
    clear.
    intros.
    destruct (FlatMem.load chunk f adr) eqn:?; try constructor.
    edestruct FlatMem.load_valid; eauto.
    apply nextinstr_nf_wt; auto.
    apply set_reg_wt; auto.
    eapply Val.has_subtype.
    eassumption.
    eapply FlatMem.load_type; auto.
  Qed.

  Definition exec_flatmem_store (chunk: memory_chunk) (m: mwd (cdata RData))
             (adr: Z)  (rs: regset) (r1: preg) :=
    let abd := (snd m) in
    let abd' := flatmem_store abd chunk adr (rs r1) in
    Next (nextinstr_nf (if preg_eq r1 ST0 then rs#ST0 <- Vundef else rs)) (fst m, abd').

  Lemma exec_flatmem_store_fst_mem:
    forall chunk m adr rs r1 rs' m',
      exec_flatmem_store chunk m adr rs r1 = Next rs' m' ->
      fst m' = fst m.
  Proof.
    unfold exec_flatmem_store; simpl; intros.
    inv H; reflexivity.
  Qed.

  Lemma exec_flatmem_store_asm_invariant:
    forall chunk m adr rs r1 rs' m',
      exec_flatmem_store chunk m adr rs r1 = Next rs' m' ->
      forall {F V} (ge: _ F V),
        AsmX.asm_invariant ge rs m ->
        AsmX.asm_invariant ge rs' m'.
  Proof.
    unfold exec_flatmem_store; simpl; intros.
    inv H.
    inv H0.
    inv inv_inject_neutral.
    constructor.
    constructor; auto.
    apply nextinstr_nf_inject; auto.
    destruct (preg_eq r1 ST0); auto.
    apply undef_reg_inject; auto.
    apply nextinstr_nf_wt; auto.
    destruct (preg_eq r1 ST0); auto.
    apply undef_reg_wt; auto.
  Qed.

  Class FlatmemStoreInvariant: Prop :=
    {
      flatmem_store_low_level_invariant:
        forall abd n,
          low_level_invariant n abd ->
          forall chunk adr v,
            low_level_invariant n (flatmem_store abd chunk adr v)
      ;

      flatmem_store_high_level_invariant:
        forall abd,
          high_level_invariant abd ->
          forall chunk adr v,
            high_level_invariant (flatmem_store abd chunk adr v)
    }.

  Lemma exec_flatmem_store_low_level_invariant' `{FlatmemStoreInvariant}:
    forall chunk m adr rs r1 rs' m',
      exec_flatmem_store chunk m adr rs r1 = Next rs' m' ->
      forall n,
        low_level_invariant n (snd m) ->
        low_level_invariant n (snd m').
  Proof.
    unfold exec_flatmem_store; simpl; intros.
    inv H0.
    simpl.
    apply flatmem_store_low_level_invariant; auto.
  Qed.

  Lemma exec_flatmem_store_low_level_invariant `{FlatmemStoreInvariant}:
    forall chunk m adr rs r1 rs' m',
      exec_flatmem_store chunk m adr rs r1 = Next rs' m' ->
      low_level_invariant (Mem.nextblock m) (snd m) ->
      low_level_invariant (Mem.nextblock m') (snd m').
  Proof.
    intros until 1.
    replace (Mem.nextblock m') with (Mem.nextblock m).
    eapply exec_flatmem_store_low_level_invariant'; eauto.
    exploit exec_flatmem_store_fst_mem; eauto.
    clear. lift_unfold. congruence.
  Qed.

  Lemma exec_flatmem_store_high_level_invariant `{FlatmemStoreInvariant}:
    forall chunk m adr rs r1 rs' m',
      exec_flatmem_store chunk m adr rs r1 = Next rs' m' ->
      high_level_invariant (snd m) ->
      high_level_invariant (snd m').
  Proof.
    unfold exec_flatmem_store; simpl; intros.
    inv H0.
    simpl.
    apply flatmem_store_high_level_invariant; auto.
  Qed.

  Class TrapinfoSetInvariant: Prop :=
    {
      trapinfo_set_high_level_invariant:
        forall abd,
          high_level_invariant abd ->
          forall adr v,
            high_level_invariant (trapinfo_set abd adr v)
      ;

      trapinfo_set_low_level_invariant:
        forall n abd,
          low_level_invariant n abd ->
          forall v,
            Val.has_type v AST.Tint ->
            val_inject (Mem.flat_inj n) v v ->
            forall adr,
              low_level_invariant n (trapinfo_set abd adr v)
    }.
  
  Section GE.
    
    Context {F V} (ge: Genv.t F V).

    Definition exec_pagefault (m: mwd (cdata RData)) (adr: int) (rs: regset)
      (* HERE do not forget to mention this type, otherwise `match' does not type check *) 
      := let abd := (snd m) in
         let abd' := trapinfo_set abd adr (rs RA) in
         match Genv.find_symbol ge pgf_handler with
           | Some b => Next (rs#RA <- (rs#PC)#PC <- (Vptr b Int.zero)) (fst m, abd')
           | _ => Stuck
         end.

    Lemma exec_pagefault_fst_mem:
      forall m adr rs rs' m',
        exec_pagefault m adr rs = Next rs' m' ->
        fst m' = fst m.
    Proof.
      unfold exec_pagefault.
      destruct (Genv.find_symbol ge pgf_handler); try discriminate.
      injection 1; intros; subst; reflexivity.
    Qed.

    Lemma exec_pagefault_asm_invariant:
      forall m adr rs rs' m',
        exec_pagefault m adr rs = Next rs' m' ->
        AsmX.asm_invariant ge rs m ->
        AsmX.asm_invariant ge rs' m'.
    Proof.
      unfold exec_pagefault. intros.
      destruct (Genv.find_symbol ge pgf_handler) eqn:?; try discriminate.
      inv H.
      inversion H0; subst.
      inversion inv_inject_neutral; subst.
      constructor.
      constructor; auto.
      apply set_reg_inject; auto.
      lift_unfold.
      econstructor.
      unfold Mem.flat_inj.
      destruct (plt b (Mem.nextblock (fst m))) eqn:HLT; simpl in *; rewrite HLT.
      reflexivity.
      exploit Genv.genv_symb_range; eauto.
      xomega.
      reflexivity.
      apply set_reg_inject; auto.
      apply set_reg_wt; auto.
      constructor.
      apply set_reg_wt; auto.
      change (typ_of_preg RA) with (typ_of_preg PC); auto.
    Qed.

    Lemma exec_pagefault_low_level_invariant `{TrapinfoSetInvariant}:
      forall m adr rs rs' m',
        exec_pagefault m adr rs = Next rs' m' ->
        AsmX.asm_invariant ge rs m ->
        low_level_invariant (Mem.nextblock m) (snd m) ->
        low_level_invariant (Mem.nextblock m') (snd m').
    Proof.
      unfold exec_pagefault.
      destruct (Genv.find_symbol ge pgf_handler); try discriminate.
      injection 1; intros; subst; simpl.
      inv H3. inv inv_inject_neutral.
      apply trapinfo_set_low_level_invariant; auto.
      apply inv_reg_wt.
    Qed.

    Lemma exec_pagefault_high_level_invariant `{TrapinfoSetInvariant}:
      forall m adr rs rs' m',
        exec_pagefault m adr rs = Next rs' m' ->
        high_level_invariant (snd m) ->
        high_level_invariant (snd m').
    Proof.
      unfold exec_pagefault.
      destruct (Genv.find_symbol ge pgf_handler); try discriminate.
      injection 1; intros; subst; simpl.
      apply trapinfo_set_high_level_invariant; auto.
    Qed.

    Section Load_Store1.

      Definition exec_host_load1 (adr: int) (chunk: memory_chunk) (m: mwd (cdata RData)) (rs: regset) (rd: preg) :=
        let adt:= (snd m) in
        let ofs := (Int.unsigned adr) in 
        match (CR3 adt) with
          | GLOBP idpt ofs' =>
            match Genv.find_symbol ge idpt with
              | Some b =>
                match Mem.loadv Mint32 m (Vptr b (Int.repr ((Int.unsigned ofs') + (PDX ofs) * 4))) with
                  | Some (Vptr b1 ofs1) =>
                    match Mem.loadv Mint32 m (Vptr b1 (Int.repr (((Int.unsigned ofs1)/PgSize)*PgSize + (PTX ofs) *4))) with
                      | Some (Vint n) => 
                        let pz:= (Int.unsigned n) mod PgSize in
                        if zeq pz PT_PERM_P then
                          exec_flatmem_load chunk m (PTADDR ((Int.unsigned n)/PgSize) ofs) rs rd
                        else 
                          if zeq pz PT_PERM_PTU then
                            exec_flatmem_load chunk m (PTADDR ((Int.unsigned n)/PgSize) ofs) rs rd
                          else
                            if zeq pz PT_PERM_UP then
                              exec_pagefault m adr rs
                            else
                              Stuck
                      | _ => Stuck
                    end
                  | _ => Stuck
                end
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_host_load1_high_level_invariant `{TrapinfoSetInvariant}:
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
        destruct (Mem.loadv Mint32 m (Vptr b1 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4))));
          try discriminate.
        destruct v; try discriminate.
        destruct (zeq (Int.unsigned i0 mod 4096) 1); try discriminate.
        * intros. exploit exec_flatmem_load_mem; eauto. congruence.
        * destruct (zeq (Int.unsigned i0 mod 4096) 7).
        + intros. exploit exec_flatmem_load_mem; eauto. congruence.
        + destruct (zeq (Int.unsigned i0 mod 4096) 0); try discriminate.
          eapply exec_pagefault_high_level_invariant.
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
        destruct (Mem.loadv Mint32 m (Vptr b1 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (zeq (Int.unsigned i0 mod 4096) 1); try discriminate.
        * intros; eapply exec_flatmem_load_asm_invariant; eauto.
        * destruct (zeq (Int.unsigned i0 mod 4096) 7).
        + intros; eapply exec_flatmem_load_asm_invariant; eauto.
        + destruct (zeq (Int.unsigned i0 mod 4096) 0); try discriminate.
          intros; eapply exec_pagefault_asm_invariant; eauto.
      Qed.

      Lemma exec_host_load1_low_level_invariant `{TrapinfoSetInvariant}:
        forall adr chunk m rs rd rs' m',
          exec_host_load1 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          low_level_invariant (Mem.nextblock m) (snd m) ->
          low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_host_load1. intros until m'.
        destruct (CR3 (snd m)); try discriminate.
        destruct (Genv.find_symbol ge b); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned ofs + PDX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b1 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (zeq (Int.unsigned i0 mod 4096) 1); try discriminate.
        * intros. exploit exec_flatmem_load_mem; eauto. congruence.
        * destruct (zeq (Int.unsigned i0 mod 4096) 7).
        + intros. exploit exec_flatmem_load_mem; eauto. congruence.
        + destruct (zeq (Int.unsigned i0 mod 4096) 0); try discriminate.
          eapply exec_pagefault_low_level_invariant.
      Qed.

      Definition exec_host_store1 (adr: int) (chunk: memory_chunk) (m: mwd (cdata RData)) (rs: regset) (rd: preg) :=
        let adt:= (snd m) in
        let ofs := (Int.unsigned adr) in 
        match (CR3 adt) with
          | GLOBP idpt ofs' =>
            match Genv.find_symbol ge idpt with
              | Some b =>
                match Mem.loadv Mint32 m (Vptr b (Int.repr ((Int.unsigned ofs') + (PDX ofs) * 4))) with
                  | Some (Vptr b1 ofs1) =>
                    match Mem.loadv Mint32 m (Vptr b1 (Int.repr (((Int.unsigned ofs1)/PgSize)*PgSize + (PTX ofs) *4))) with
                      | Some (Vint n) => 
                        let pz:= (Int.unsigned n) mod PgSize in
                        if zeq pz PT_PERM_P then
                          exec_flatmem_store chunk m (PTADDR ((Int.unsigned n)/PgSize) ofs) rs rd
                        else 
                          if zeq pz PT_PERM_PTU then
                            exec_flatmem_store chunk m (PTADDR ((Int.unsigned n)/PgSize) ofs) rs rd
                          else
                            if zeq pz PT_PERM_UP then
                              exec_pagefault m adr rs
                            else
                              Stuck
                      | _ => Stuck
                    end
                  | _ => Stuck
                end
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_host_store1_high_level_invariant `{FlatmemStoreInvariant} `{TrapinfoSetInvariant}:
        forall adr chunk m rs rd rs' m',
          exec_host_store1 adr chunk m rs rd = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_host_store1. intros until m'.
        destruct (CR3 (snd m)); try discriminate.
        destruct (Genv.find_symbol ge b); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned ofs + PDX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b1 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (zeq (Int.unsigned i0 mod 4096) 1); try discriminate.
        * intros; eapply exec_flatmem_store_high_level_invariant; eauto.
        * destruct (zeq (Int.unsigned i0 mod 4096) 7).
        + intros; eapply exec_flatmem_store_high_level_invariant; eauto.
        + destruct (zeq (Int.unsigned i0 mod 4096) 0); try discriminate.
          eapply exec_pagefault_high_level_invariant.
      Qed.

      Lemma exec_host_store1_asm_invariant:
        forall chunk rd,
        forall adr m rs rs' m',
          exec_host_store1 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_host_store1. intros until m'.
        destruct (CR3 (snd m)); try discriminate.
        destruct (Genv.find_symbol ge b); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned ofs + PDX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b1 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (zeq (Int.unsigned i0 mod 4096) 1); try discriminate.
        * intros; eapply exec_flatmem_store_asm_invariant; eauto.
        * destruct (zeq (Int.unsigned i0 mod 4096) 7).
        + intros; eapply exec_flatmem_store_asm_invariant; eauto.
        + destruct (zeq (Int.unsigned i0 mod 4096) 0); try discriminate.
          intros; eapply exec_pagefault_asm_invariant; eauto.
      Qed.

      Lemma exec_host_store1_low_level_invariant `{FlatmemStoreInvariant}  `{TrapinfoSetInvariant}:
        forall adr chunk m rs rd rs' m',
          exec_host_store1 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          low_level_invariant (Mem.nextblock m) (snd m) ->
          low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_host_store1. intros until m'.
        destruct (CR3 (snd m)); try discriminate.
        destruct (Genv.find_symbol ge b); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned ofs + PDX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b1 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        destruct (zeq (Int.unsigned i0 mod 4096) 1); try discriminate.
        * intros; eapply exec_flatmem_store_low_level_invariant; eauto.
        * destruct (zeq (Int.unsigned i0 mod 4096) 7).
        + intros; eapply exec_flatmem_store_low_level_invariant; eauto.
        + destruct (zeq (Int.unsigned i0 mod 4096) 0); try discriminate.
          eapply exec_pagefault_low_level_invariant.
      Qed.

      Definition exec_guest_load1 (adr: int) (chunk: memory_chunk) (m: mwd (cdata RData)) (rs: regset) (rd: preg) :=
        let ofs := (Int.unsigned adr) in 
        match (Genv.find_symbol ge NPT_LOC) with
          | Some b => 
            match Mem.loadv Mint32 m (Vptr b (Int.repr ((PDX ofs) * 4))) with
              | Some (Vptr b1 ofs1) =>
                match Mem.loadv Mint32 m (Vptr b1 (Int.repr (((Int.unsigned ofs1)/PgSize)*PgSize + (PTX ofs) *4))) with
                  | Some (Vint n) => exec_flatmem_load chunk m (PTADDR ((Int.unsigned n)/PgSize) ofs) rs rd
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
        intros; eapply exec_flatmem_load_asm_invariant; eauto.
      Qed.

      Lemma exec_guest_load1_low_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_guest_load1 adr chunk m rs rd = Next rs' m' ->
          low_level_invariant (Mem.nextblock m) (snd m) ->
          low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_guest_load1. intros until m'.
        destruct (Genv.find_symbol ge NPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b (Int.repr (PDX (Int.unsigned adr) * 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        intros. exploit exec_flatmem_load_mem; eauto. congruence.
      Qed.

      Definition exec_guest_store1 (adr: int) (chunk: memory_chunk) (m: mwd (cdata RData)) (rs: regset) (rd: preg) :=
        let ofs := (Int.unsigned adr) in 
        match (Genv.find_symbol ge NPT_LOC) with
          | Some b => 
            match Mem.loadv Mint32 m (Vptr b (Int.repr ((PDX ofs) * 4))) with
              | Some (Vptr b1 ofs1) =>
                match Mem.loadv Mint32 m (Vptr b1 (Int.repr (((Int.unsigned ofs1)/PgSize)*PgSize + (PTX ofs) *4))) with
                  | Some (Vint n) => exec_flatmem_store chunk m (PTADDR ((Int.unsigned n)/PgSize) ofs) rs rd
                  | _ => Stuck
                end
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_guest_store1_high_level_invariant `{FlatmemStoreInvariant}:
        forall adr chunk m rs rd rs' m',
          exec_guest_store1 adr chunk m rs rd = Next rs' m' ->
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
        eapply exec_flatmem_store_high_level_invariant.
      Qed.

      Lemma exec_guest_store1_asm_invariant:
        forall chunk rd,
        forall adr m rs rs' m',
          exec_guest_store1 adr chunk m rs rd = Next rs' m' ->
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
        intros; eapply exec_flatmem_store_asm_invariant; eauto.
      Qed.

      Lemma exec_guest_store1_low_level_invariant `{FlatmemStoreInvariant}:
        forall adr chunk m rs rd rs' m',
          exec_guest_store1 adr chunk m rs rd = Next rs' m' ->
          low_level_invariant (Mem.nextblock m) (snd m) ->
          low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_guest_store1. intros until m'.
        destruct (Genv.find_symbol ge NPT_LOC); try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b (Int.repr (PDX (Int.unsigned adr) * 4)))); try discriminate.
        destruct v; try discriminate.
        destruct (Mem.loadv Mint32 m (Vptr b0 (Int.repr (Int.unsigned i / 4096 * 4096 + PTX (Int.unsigned adr) * 4)))); 
          try discriminate.
        destruct v; try discriminate.
        eapply exec_flatmem_store_low_level_invariant.
      Qed.
      
      Definition exec_loadex1 (chunk: memory_chunk) (m: mwd (cdata RData))
                 (a: addrmode) (rs: regset) (rd: preg) := 
        let adt:= (snd m) in
        match (eval_addrmode ge a rs) with
          | Vptr b ofs => 
            match (ikern adt, ihost adt) with
              | (true, true) => Asm.exec_load ge chunk m a rs rd
              | _ => Stuck     
            end
          | Vint adr => 
            let ofs := (Int.unsigned adr) in 
            match (pe adt, ihost adt) with
              | (true, true) => exec_host_load1 adr chunk m rs rd
              | (true, false) => exec_guest_load1 adr chunk m rs rd                                         
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_loadex1_high_level_invariant `{TrapinfoSetInvariant}:
        forall adr chunk m rs rd rs' m',
          exec_loadex1 chunk m adr rs rd = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_loadex1. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_load1_high_level_invariant; eauto.
        + eapply exec_guest_load1_high_level_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            unfold Asm.exec_load. 
            destruct (Mem.loadv chunk m (eval_addrmode ge adr rs)); 
              try discriminate. congruence.
      Qed.

      Local Existing Instance Asm.mem_accessors_default.
      Local Existing Instance AsmX.mem_accessors_default_invariant.

      Lemma exec_loadex1_asm_invariant:
        forall chunk rd,
        forall TYP: subtype (type_of_chunk chunk) (typ_of_preg rd) = true,
        forall adr m rs rs' m',
          exec_loadex1 chunk m adr rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_loadex1. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_load1_asm_invariant; eauto.
        + intros; eapply exec_guest_load1_asm_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            intros; eapply exec_load_invariant; eauto.
      Qed.

      Lemma exec_loadex1_low_level_invariant `{TrapinfoSetInvariant}:
        forall adr chunk m rs rd rs' m',
          exec_loadex1 chunk m adr rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          low_level_invariant (Mem.nextblock m) (snd m) ->
          low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_loadex1. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_load1_low_level_invariant; eauto.
        + intros; eapply exec_guest_load1_low_level_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            unfold Asm.exec_load. 
            destruct (Mem.loadv chunk m (eval_addrmode ge adr rs)); try discriminate.
            congruence.
      Qed.

      Definition exec_storeex1 (chunk: memory_chunk) (m: mwd (cdata RData))
                 (a: addrmode) (rs: regset) (rd: preg) (destroyed: list preg) := 
        let adt:= (snd m) in
        match  (eval_addrmode ge a rs) with
          | Vptr b ofs => 
            match (ikern adt, ihost adt) with
              | (true, true) => Asm.exec_store ge chunk m a rs rd destroyed
              | _ => Stuck     
            end
          | Vint adr => 
            let ofs := (Int.unsigned adr) in 
            match (pe adt, ihost adt) with
              | (true, true) => exec_host_store1 adr chunk m rs rd
              | (true, false)  => exec_guest_store1 adr chunk m rs rd
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_storeex1_high_level_invariant `{TrapinfoSetInvariant} `{FlatmemStoreInvariant}:
        forall adr chunk m rs rd des rs' m',
          exec_storeex1 chunk m adr rs rd des = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_storeex1. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_store1_high_level_invariant; eauto.
        + eapply exec_guest_store1_high_level_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            unfold Asm.exec_store. 
            destruct (Mem.storev chunk m (eval_addrmode ge adr rs) (rs rd)) eqn:Heqo; 
              try discriminate.
            destruct (eval_addrmode ge adr rs); try discriminate.
            lift_unfold.
            destruct Heqo as [? DATA].
            unfold π_data in DATA. simpl in * |- *. congruence.
      Qed.

      Lemma exec_storeex1_asm_invariant:
        forall chunk rd,
        forall adr m des rs rs' m',
          exec_storeex1 chunk m adr rs rd des = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_storeex1. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_store1_asm_invariant; eauto.
        + intros; eapply exec_guest_store1_asm_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            intros; eapply exec_store_invariant; eauto.
      Qed.

      Lemma exec_storeex1_low_level_invariant `{TrapinfoSetInvariant} `{FlatmemStoreInvariant}:
        forall adr chunk m rs rd des rs' m',
          exec_storeex1 chunk m adr rs rd des = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          low_level_invariant (Mem.nextblock m) (snd m) ->
          low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_storeex1. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_store1_low_level_invariant; eauto.
        + intros; eapply exec_guest_store1_low_level_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
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

    End Load_Store1.

    Section Load_Store2.

      Definition exec_host_load2 (adr: int) (chunk: memory_chunk) (m: mwd (cdata RData)) (rs: regset) (rd: preg) :=
        let adt:= (snd m) in
        let ofs := (Int.unsigned adr) in 
        match ZMap.get (PDX ofs) (ZMap.get (PT adt) (ptpool adt))with
          | PDTValid pte => 
            match ZMap.get (PTX ofs) pte with 
              | PTValid v p => 
                match p with
                  | PTK _=> Stuck
                  | _ => exec_flatmem_load chunk m (PTADDR (v/PgSize) ofs) rs rd     
                end
              | PTUnPresent => exec_pagefault m adr rs
              |_ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_host_load2_high_level_invariant `{TrapinfoSetInvariant}:
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
        destruct (ZMap.get (PTX (Int.unsigned adr)) pte); try discriminate.
        destruct p; try discriminate.
        * intros. exploit exec_flatmem_load_mem; eauto. congruence.
        * intros. exploit exec_flatmem_load_mem; eauto. congruence.
        * eapply exec_pagefault_high_level_invariant.
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
        destruct (ZMap.get (PTX (Int.unsigned adr)) pte); try discriminate.
        destruct p; try discriminate.
        * intros; eapply exec_flatmem_load_asm_invariant; eauto.
        * intros; eapply exec_flatmem_load_asm_invariant; eauto.
        * intros; eapply exec_pagefault_asm_invariant; eauto.
      Qed.

      Lemma exec_host_load2_low_level_invariant `{TrapinfoSetInvariant}:
        forall adr chunk m rs rd rs' m',
          exec_host_load2 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          low_level_invariant (Mem.nextblock m) (snd m) ->
          low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_host_load2. intros until m'.
        destruct (
            ZMap.get (PDX (Int.unsigned adr))
                     (ZMap.get (PT (snd m)) (ptpool (snd m)))
          ); try discriminate.
        destruct (ZMap.get (PTX (Int.unsigned adr)) pte); try discriminate.
        destruct p; try discriminate.
        * intros. exploit exec_flatmem_load_mem; eauto. congruence.
        * intros. exploit exec_flatmem_load_mem; eauto. congruence.
        * eapply exec_pagefault_low_level_invariant.
      Qed.

      Definition exec_host_store2 (adr: int) (chunk: memory_chunk) (m: mwd (cdata RData)) (rs: regset) (rd: preg) :=
        let adt:= (snd m) in
        let ofs := (Int.unsigned adr) in 
        match ZMap.get (PDX ofs) (ZMap.get (PT adt) (ptpool adt)) with
          | PDTValid pte => 
            match ZMap.get (PTX ofs) pte with 
              | PTValid v p => 
                match p with
                  | PTK _=> Stuck
                  | _ => exec_flatmem_store chunk m (PTADDR (v/PgSize) ofs)  rs rd
                end
              | PTUnPresent => exec_pagefault m adr rs
              |_ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_host_store2_high_level_invariant `{TrapinfoSetInvariant} `{FlatmemStoreInvariant}:
        forall adr chunk m rs rd rs' m',
          exec_host_store2 adr chunk m rs rd = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_host_store2. intros until m'.
        destruct (
            ZMap.get (PDX (Int.unsigned adr))
                     (ZMap.get (PT (snd m)) (ptpool (snd m)))
          ); try discriminate.
        destruct (ZMap.get (PTX (Int.unsigned adr)) pte); try discriminate.
        destruct p; try discriminate.
        * intros; eapply exec_flatmem_store_high_level_invariant; eauto.
        * intros; eapply exec_flatmem_store_high_level_invariant; eauto.
        * eapply exec_pagefault_high_level_invariant.
      Qed.

      Lemma exec_host_store2_asm_invariant:
        forall chunk rd,
        forall adr m rs rs' m',
          exec_host_store2 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_host_store2. intros until m'.
        destruct (
            ZMap.get (PDX (Int.unsigned adr))
                     (ZMap.get (PT (snd m)) (ptpool (snd m)))
          ); try discriminate.
        destruct (ZMap.get (PTX (Int.unsigned adr)) pte); try discriminate.
        destruct p; try discriminate.
        * intros; eapply exec_flatmem_store_asm_invariant; eauto.
        * intros; eapply exec_flatmem_store_asm_invariant; eauto.
        * intros; eapply exec_pagefault_asm_invariant; eauto.
      Qed.

      Lemma exec_host_store2_low_level_invariant `{TrapinfoSetInvariant} `{FlatmemStoreInvariant}:
        forall adr chunk m rs rd rs' m',
          exec_host_store2 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          low_level_invariant (Mem.nextblock m) (snd m) ->
          low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_host_store2. intros until m'.
        destruct (
            ZMap.get (PDX (Int.unsigned adr))
                     (ZMap.get (PT (snd m)) (ptpool (snd m)))
          ); try discriminate.
        destruct (ZMap.get (PTX (Int.unsigned adr)) pte); try discriminate.
        destruct p; try discriminate.
        * intros; eapply exec_flatmem_store_low_level_invariant; eauto.
        * intros; eapply exec_flatmem_store_low_level_invariant; eauto.
        * eapply exec_pagefault_low_level_invariant.
      Qed.

      Definition exec_loadex2 (chunk: memory_chunk) (m: mwd (cdata RData))
                 (a: addrmode) (rs: regset) (rd: preg) := 
        let adt:= (snd m) in
        match (eval_addrmode ge a rs) with
          | Vptr b ofs => 
            match (ikern adt, ihost adt) with
              | (true, true) => Asm.exec_load ge chunk m a rs rd
              | _ => Stuck     
            end
          | Vint adr => 
            let ofs := (Int.unsigned adr) in 
            match (pe adt, ihost adt) with
              | (true, true) => exec_host_load2 adr chunk m rs rd
              | (true, false) => exec_guest_load1 adr chunk m rs rd                                         
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_loadex2_high_level_invariant `{TrapinfoSetInvariant}:
        forall adr chunk m rs rd rs' m',
          exec_loadex2 chunk m adr rs rd = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_loadex2. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_load2_high_level_invariant; eauto.
        + eapply exec_guest_load1_high_level_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            unfold Asm.exec_load. destruct (Mem.loadv chunk m (eval_addrmode ge adr rs)); try discriminate.
            congruence.
      Qed.

      Local Existing Instance Asm.mem_accessors_default.
      Local Existing Instance AsmX.mem_accessors_default_invariant.

      Lemma exec_loadex2_asm_invariant:
        forall chunk rd,
        forall TYP: subtype (type_of_chunk chunk) (typ_of_preg rd) = true,
        forall adr m rs rs' m',
          exec_loadex2 chunk m adr rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_loadex2. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_load2_asm_invariant; eauto.
        + intros; eapply exec_guest_load1_asm_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            intros; eapply exec_load_invariant; eauto.
      Qed.

      Lemma exec_loadex2_low_level_invariant `{TrapinfoSetInvariant}:
        forall adr chunk m rs rd rs' m',
          exec_loadex2 chunk m adr rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          low_level_invariant (Mem.nextblock m) (snd m) ->
          low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_loadex2. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_load2_low_level_invariant; eauto.
        + intros; eapply exec_guest_load1_low_level_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            unfold Asm.exec_load. destruct (Mem.loadv chunk m (eval_addrmode ge adr rs)); try discriminate.
            congruence.
      Qed.

      Definition exec_storeex2 (chunk: memory_chunk) (m: mwd (cdata RData))
                 (a: addrmode) (rs: regset) (rd: preg) (destroyed: list preg) := 
        let adt:= (snd m) in
        match  (eval_addrmode ge a rs) with
          | Vptr b ofs => 
            match (ikern adt, ihost adt) with
              | (true, true) => Asm.exec_store ge chunk m a rs rd destroyed
              | _ => Stuck     
            end
          | Vint adr => 
            let ofs := (Int.unsigned adr) in 
            match (pe adt, ihost adt) with
              | (true, true) => exec_host_store2 adr chunk m rs rd
              | (true, false)  => exec_guest_store1 adr chunk m rs rd
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_storeex2_high_level_invariant `{TrapinfoSetInvariant} `{FlatmemStoreInvariant}:
        forall adr chunk m rs rd des rs' m',
          exec_storeex2 chunk m adr rs rd des = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_storeex2. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_store2_high_level_invariant; eauto.
        + eapply exec_guest_store1_high_level_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            unfold Asm.exec_store. destruct (Mem.storev chunk m (eval_addrmode ge adr rs) (rs rd)) eqn:Heqo; try discriminate.
            destruct (eval_addrmode ge adr rs); try discriminate.
            lift_unfold.
            destruct Heqo as [? DATA].
            unfold π_data in DATA. simpl in * |- *. congruence.
      Qed.

      Lemma exec_storeex2_asm_invariant:
        forall chunk rd,
        forall adr m des rs rs' m',
          exec_storeex2 chunk m adr rs rd des = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_storeex2. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_store2_asm_invariant; eauto.
        + intros; eapply exec_guest_store1_asm_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            intros; eapply exec_store_invariant; eauto.
      Qed.

      Lemma exec_storeex2_low_level_invariant `{TrapinfoSetInvariant} `{FlatmemStoreInvariant}:
        forall adr chunk m rs rd des rs' m',
          exec_storeex2 chunk m adr rs rd des = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          low_level_invariant (Mem.nextblock m) (snd m) ->
          low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_storeex2. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_store2_low_level_invariant; eauto.
        + intros; eapply exec_guest_store1_low_level_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            unfold Asm.exec_store. destruct (Mem.storev chunk m (eval_addrmode ge adr rs) (rs rd)) eqn:Heqo; try discriminate.
            destruct (eval_addrmode ge adr rs); try discriminate.
            lift_unfold.
            destruct Heqo as [? DATA].
            unfold π_data in DATA. simpl in * |- *.
            injection 1; intros; subst.
            erewrite Mem.nextblock_store; eauto.
            congruence.
      Qed.

    End Load_Store2.

    Section Load_Store3.

      Definition exec_guest_load2 (adr: int) (chunk: memory_chunk) (m: mwd (cdata RData)) (rs: regset) (rd: preg) :=
        let adt:= (snd m) in
        let ofs := (Int.unsigned adr) in 
        match ZMap.get (PDX ofs) (npt adt) with
          | NPDEValid npte =>
            match ZMap.get (PTX ofs) npte with
              | NPTEValid v =>
                exec_flatmem_load chunk m (PTADDR (v/PgSize) ofs) rs rd
              |_ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_guest_load2_high_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_guest_load2 adr chunk m rs rd = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_guest_load2. intros until m'.
        destruct (ZMap.get (PDX (Int.unsigned adr)) (npt (snd m))); try discriminate.
        destruct (ZMap.get (PTX (Int.unsigned adr)) nptab); try discriminate.
        intros. exploit exec_flatmem_load_mem; eauto. congruence.
      Qed.

      Lemma exec_guest_load2_asm_invariant:
        forall chunk rd,
        forall TYP: subtype (type_of_chunk chunk) (typ_of_preg rd) = true,
        forall adr m rs rs' m',
          exec_guest_load2 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_guest_load2. intros until m'.
        destruct (ZMap.get (PDX (Int.unsigned adr)) (npt (snd m))); try discriminate.
        destruct (ZMap.get (PTX (Int.unsigned adr)) nptab); try discriminate.
        intros; eapply exec_flatmem_load_asm_invariant; eauto.
      Qed.

      Lemma exec_guest_load2_low_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_guest_load2 adr chunk m rs rd = Next rs' m' ->
          low_level_invariant (Mem.nextblock m) (snd m) ->
          low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_guest_load2. intros until m'.
        destruct (ZMap.get (PDX (Int.unsigned adr)) (npt (snd m))); try discriminate.
        destruct (ZMap.get (PTX (Int.unsigned adr)) nptab); try discriminate.
        intros. exploit exec_flatmem_load_mem; eauto. congruence.
      Qed.

      Definition exec_guest_store2 (adr: int) (chunk: memory_chunk) (m: mwd (cdata RData)) (rs: regset) (rd: preg) :=
        let adt:= (snd m) in
        let ofs := (Int.unsigned adr) in 
        let ofs := (Int.unsigned adr) in 
        match ZMap.get (PDX ofs) (npt adt) with
          | NPDEValid npte =>
            match ZMap.get (PTX ofs) npte with
              | NPTEValid v =>
                exec_flatmem_store chunk m (PTADDR (v/PgSize) ofs) rs rd
              |_ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_guest_store2_high_level_invariant `{FlatmemStoreInvariant}:
        forall adr chunk m rs rd rs' m',
          exec_guest_store2 adr chunk m rs rd = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_guest_store2. intros until m'.
        destruct (ZMap.get (PDX (Int.unsigned adr)) (npt (snd m))); try discriminate.
        destruct (ZMap.get (PTX (Int.unsigned adr)) nptab); try discriminate.
        eapply exec_flatmem_store_high_level_invariant.
      Qed.

      Lemma exec_guest_store2_asm_invariant:
        forall chunk rd,
        forall adr m rs rs' m',
          exec_guest_store2 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_guest_store2. intros until m'.
        destruct (ZMap.get (PDX (Int.unsigned adr)) (npt (snd m))); try discriminate.
        destruct (ZMap.get (PTX (Int.unsigned adr)) nptab); try discriminate.
        intros; eapply exec_flatmem_store_asm_invariant; eauto.
      Qed.

      Lemma exec_guest_store2_low_level_invariant `{FlatmemStoreInvariant}:
        forall adr chunk m rs rd rs' m',
          exec_guest_store2 adr chunk m rs rd = Next rs' m' ->
          low_level_invariant (Mem.nextblock m) (snd m) ->
          low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_guest_store2. intros until m'.
        destruct (ZMap.get (PDX (Int.unsigned adr)) (npt (snd m))); try discriminate.
        destruct (ZMap.get (PTX (Int.unsigned adr)) nptab); try discriminate.
        eapply exec_flatmem_store_low_level_invariant.
      Qed.

      Definition exec_loadex3 (chunk: memory_chunk) (m: mwd (cdata RData))
                 (a: addrmode) (rs: regset) (rd: preg) := 
        let adt:= (snd m) in
        match (eval_addrmode ge a rs) with
          | Vptr b ofs => 
            match (ikern adt, ihost adt) with
              | (true, true) => Asm.exec_load ge chunk m a rs rd
              | _ => Stuck     
            end
          | Vint adr => 
            let ofs := (Int.unsigned adr) in 
            match (pe adt, ihost adt) with
              | (true, true) => exec_host_load2 adr chunk m rs rd
              | (true, false) => exec_guest_load2 adr chunk m rs rd                                         
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_loadex3_high_level_invariant `{TrapinfoSetInvariant}:
        forall adr chunk m rs rd rs' m',
          exec_loadex3 chunk m adr rs rd = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_loadex3. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_load2_high_level_invariant; eauto.
        + eapply exec_guest_load2_high_level_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            unfold Asm.exec_load. destruct (Mem.loadv chunk m (eval_addrmode ge adr rs)); try discriminate.
            congruence.
      Qed.

      Local Existing Instance Asm.mem_accessors_default.
      Local Existing Instance AsmX.mem_accessors_default_invariant.

      Lemma exec_loadex3_asm_invariant:
        forall chunk rd,
        forall TYP: subtype (type_of_chunk chunk) (typ_of_preg rd) = true,
        forall adr m rs rs' m',
          exec_loadex3 chunk m adr rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_loadex3. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_load2_asm_invariant; eauto.
        + intros; eapply exec_guest_load2_asm_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            intros; eapply exec_load_invariant; eauto.
      Qed.

      Lemma exec_loadex3_low_level_invariant `{TrapinfoSetInvariant}:
        forall adr chunk m rs rd rs' m',
          exec_loadex3 chunk m adr rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          low_level_invariant (Mem.nextblock m) (snd m) ->
          low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_loadex3. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_load2_low_level_invariant; eauto.
        + intros; eapply exec_guest_load2_low_level_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            unfold Asm.exec_load. destruct (Mem.loadv chunk m (eval_addrmode ge adr rs)); try discriminate.
            congruence.
      Qed.

      Definition exec_storeex3 (chunk: memory_chunk) (m: mwd (cdata RData))
                 (a: addrmode) (rs: regset) (rd: preg) (destroyed: list preg) := 
        let adt:= (snd m) in
        match  (eval_addrmode ge a rs) with
          | Vptr b ofs => 
            match (ikern adt, ihost adt) with
              | (true, true) => Asm.exec_store ge chunk m a rs rd destroyed
              | _ => Stuck     
            end
          | Vint adr => 
            let ofs := (Int.unsigned adr) in 
            match (pe adt, ihost adt) with
              | (true, true) => exec_host_store2 adr chunk m rs rd
              | (true, false)  => exec_guest_store2 adr chunk m rs rd
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_storeex3_high_level_invariant `{TrapinfoSetInvariant} `{FlatmemStoreInvariant}:
        forall adr chunk m rs rd des rs' m',
          exec_storeex3 chunk m adr rs rd des = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_storeex3. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_store2_high_level_invariant; eauto.
        + eapply exec_guest_store2_high_level_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            unfold Asm.exec_store. destruct (Mem.storev chunk m (eval_addrmode ge adr rs) (rs rd)) eqn:Heqo; try discriminate.
            destruct (eval_addrmode ge adr rs); try discriminate.
            lift_unfold.
            destruct Heqo as [? DATA].
            unfold π_data in DATA. simpl in * |- *. congruence.
      Qed.

      Lemma exec_storeex3_asm_invariant:
        forall chunk rd,
        forall adr m des rs rs' m',
          exec_storeex3 chunk m adr rs rd des = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_storeex3. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_store2_asm_invariant; eauto.
        + intros; eapply exec_guest_store2_asm_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            intros; eapply exec_store_invariant; eauto.
      Qed.

      Lemma exec_storeex3_low_level_invariant `{TrapinfoSetInvariant} `{FlatmemStoreInvariant}:
        forall adr chunk m rs rd des rs' m',
          exec_storeex3 chunk m adr rs rd des = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          low_level_invariant (Mem.nextblock m) (snd m) ->
          low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_storeex3. intros until m'.
        destruct (eval_addrmode ge adr rs); try discriminate.
        * destruct (pe (snd m)); try discriminate.
          destruct (ihost (snd m)).
        + eapply exec_host_store2_low_level_invariant; eauto.
        + intros; eapply exec_guest_store2_low_level_invariant; eauto.
          * destruct (ikern (snd m)); try discriminate.
            destruct (ihost (snd m)); try discriminate.
            unfold Asm.exec_store. destruct (Mem.storev chunk m (eval_addrmode ge adr rs) (rs rd)) eqn:Heqo; try discriminate.
            destruct (eval_addrmode ge adr rs); try discriminate.
            lift_unfold.
            destruct Heqo as [? DATA].
            unfold π_data in DATA. simpl in * |- *.
            injection 1; intros; subst.
            erewrite Mem.nextblock_store; eauto.
            congruence.
      Qed.

    End Load_Store3.

  End GE.      

  Class KernelModeImplies: Prop :=
    {
      kernel_mode_implies: forall adt, kernel_mode adt -> (ikern adt = true /\ ihost adt = true)
    }.

  Global Instance load_accessor_prf1 `{KernelModeImplies} 
         `{TrapinfoSetInvariant} `{FlatmemStoreInvariant}:
    LoadAccessor _ (@exec_loadex1).
  Proof.
    constructor.
    {
      unfold exec_loadex1.
      intros.
      erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
      destruct (eval_addrmode ge1 a rs); try reflexivity.
      * destruct (pe (snd m)); try reflexivity.
        destruct (ihost (snd m)).
      + unfold exec_host_load1.
        destruct (CR3 (snd m)); try reflexivity.
        unfold exec_pagefault. repeat rewrite SYMB. reflexivity.
      + unfold exec_guest_load1.
        rewrite SYMB.
        reflexivity.
        * unfold Asm.exec_load. erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
    }
    {
      intros.
      apply kernel_mode_implies in H3.
      destruct H3 as [IKERN IHOST].
      unfold exec_loadex1.
      unfold Asm.exec_load in H2 |- *.
      destruct (eval_addrmode ge a rs); try discriminate.
      unfold π_data in IKERN, IHOST.
      rewrite IKERN. rewrite IHOST.
      assumption.
    }
    {
      intros; eapply exec_loadex1_asm_invariant; eauto.
    }     
    {
      intros; eapply exec_loadex1_low_level_invariant; eauto.
    }
    {
      intros; eapply exec_loadex1_high_level_invariant; eauto.
    }
  Qed.

  Global Instance store_accessor_prf1 `{KernelModeImplies}
         `{TrapinfoSetInvariant} `{FlatmemStoreInvariant}:
    StoreAccessor _ (@exec_storeex1).
  Proof.
    constructor.
    {
      unfold exec_storeex1.
      intros.
      erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
      destruct (eval_addrmode ge1 a rs); try reflexivity.
      * destruct (pe (snd m)); try reflexivity.
        destruct (ihost (snd m)).
      + unfold exec_host_store1.
        destruct (CR3 (snd m)); try reflexivity.
        unfold exec_pagefault. repeat rewrite SYMB. reflexivity.
      + unfold exec_guest_store1.
        rewrite SYMB.
        reflexivity.
        * unfold Asm.exec_store. erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
    }
    {
      intros.
      apply kernel_mode_implies in H3.
      destruct H3 as [IKERN IHOST].
      unfold exec_storeex1.
      unfold Asm.exec_store in H2 |- *.
      destruct (eval_addrmode ge a rs); try discriminate.
      unfold π_data in IKERN, IHOST.
      rewrite IKERN. rewrite IHOST.
      assumption.
    }
    {
      intros; eapply exec_storeex1_asm_invariant; eauto.
    }     
    {
      intros; eapply exec_storeex1_low_level_invariant; eauto.
    }
    {
      intros; eapply exec_storeex1_high_level_invariant; eauto.
    }
  Qed.

  Global Instance load_accessor_prf2 `{KernelModeImplies}
         `{TrapinfoSetInvariant} `{FlatmemStoreInvariant}:
    LoadAccessor _ (@exec_loadex2).
  Proof.
    constructor.
    {
      unfold exec_loadex2.
      intros.
      erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
      destruct (eval_addrmode ge1 a rs); try reflexivity.
      * destruct (pe (snd m)); try reflexivity.
        destruct (ihost (snd m)).
      + unfold exec_host_load2.
        unfold exec_pagefault. rewrite SYMB. reflexivity.
      + unfold exec_guest_load1.
        rewrite SYMB.
        reflexivity.
        * unfold Asm.exec_load. erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
    }
    {
      intros.
      apply kernel_mode_implies in H3.
      destruct H3 as [IKERN IHOST].
      unfold exec_loadex2.
      unfold Asm.exec_load in H2 |- *.
      destruct (eval_addrmode ge a rs); try discriminate.
      unfold π_data in IKERN, IHOST.
      rewrite IKERN. rewrite IHOST.
      assumption.
    }
    {
      intros; eapply exec_loadex2_asm_invariant; eauto.
    }     
    {
      intros; eapply exec_loadex2_low_level_invariant; eauto.
    }
    {
      intros; eapply exec_loadex2_high_level_invariant; eauto.
    }
  Qed.

  Global Instance store_accessor_prf2 `{KernelModeImplies}
         `{TrapinfoSetInvariant} `{FlatmemStoreInvariant}:
    StoreAccessor _ (@exec_storeex2).
  Proof.
    constructor.
    {
      unfold exec_storeex2.
      intros.
      erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
      destruct (eval_addrmode ge1 a rs); try reflexivity.
      * destruct (pe (snd m)); try reflexivity.
        destruct (ihost (snd m)).
      + unfold exec_host_store2.
        unfold exec_pagefault. rewrite SYMB. reflexivity.
      + unfold exec_guest_store1.
        rewrite SYMB.
        reflexivity.
        * unfold Asm.exec_store. erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
    }
    {
      intros.
      apply kernel_mode_implies in H3.
      destruct H3 as [IKERN IHOST].
      unfold exec_storeex2.
      unfold Asm.exec_store in H2 |- *.
      destruct (eval_addrmode ge a rs); try discriminate.
      unfold π_data in IKERN, IHOST.
      rewrite IKERN. rewrite IHOST.
      assumption.
    }
    {
      intros; eapply exec_storeex2_asm_invariant; eauto.
    }     
    {
      intros; eapply exec_storeex2_low_level_invariant; eauto.
    }
    {
      intros; eapply exec_storeex2_high_level_invariant; eauto.
    }
  Qed.

  Global Instance load_accessor_prf3 `{KernelModeImplies}
         `{TrapinfoSetInvariant} `{FlatmemStoreInvariant}:
    LoadAccessor _ (@exec_loadex3).
  Proof.
    constructor.
    {
      unfold exec_loadex3.
      intros.
      erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
      destruct (eval_addrmode ge1 a rs); try reflexivity.
      * destruct (pe (snd m)); try reflexivity.
        destruct (ihost (snd m)).
      + unfold exec_host_load2.
        unfold exec_pagefault. rewrite SYMB. reflexivity.
      + unfold exec_guest_load2. reflexivity.
        * unfold Asm.exec_load. erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
    }
    {
      intros.
      apply kernel_mode_implies in H3.
      destruct H3 as [IKERN IHOST].
      unfold exec_loadex3.
      unfold Asm.exec_load in H2 |- *.
      destruct (eval_addrmode ge a rs); try discriminate.
      unfold π_data in IKERN, IHOST.
      rewrite IKERN. rewrite IHOST.
      assumption.
    }
    {
      intros; eapply exec_loadex3_asm_invariant; eauto.
    }     
    {
      intros; eapply exec_loadex3_low_level_invariant; eauto.
    }
    {
      intros; eapply exec_loadex3_high_level_invariant; eauto.
    }
  Qed.

  Global Instance store_accessor_prf3 `{KernelModeImplies}
         `{TrapinfoSetInvariant} `{FlatmemStoreInvariant}:
    StoreAccessor _ (@exec_storeex3).
  Proof.
    constructor.
    {
      unfold exec_storeex3.
      intros.
      erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
      destruct (eval_addrmode ge1 a rs); try reflexivity.
      * destruct (pe (snd m)); try reflexivity.
        destruct (ihost (snd m)).
      + unfold exec_host_store2.
        unfold exec_pagefault. rewrite SYMB. reflexivity.
      + unfold exec_guest_store2.
        reflexivity.
        * unfold Asm.exec_store. erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
    }
    {
      intros.
      apply kernel_mode_implies in H3.
      destruct H3 as [IKERN IHOST].
      unfold exec_storeex3.
      unfold Asm.exec_store in H2 |- *.
      destruct (eval_addrmode ge a rs); try discriminate.
      unfold π_data in IKERN, IHOST.
      rewrite IKERN. rewrite IHOST.
      assumption.
    }
    {
      intros; eapply exec_storeex3_asm_invariant; eauto.
    }     
    {
      intros; eapply exec_storeex3_low_level_invariant; eauto.
    }
    {
      intros; eapply exec_storeex3_high_level_invariant; eauto.
    }
  Qed.

End Load_Store.

Section Load_Store_Refinement.

  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.
  Context {HDATA} `{HD: CompatData HDATA}.
  Context {LDATA} `{LD: CompatData LDATA}.

  Notation HDATAOps := (cdata HDATA).
  Notation LDATAOps := (cdata LDATA).
  Context `{rel_prf: CompatRel (mem:=mem) (memory_model_ops:= memory_model_ops) (D1 := HDATAOps) (D2:=LDATAOps)}. 
  Context `{Hstencil: Stencil stencil (stencil_ops:= stencil_ops)}.

  Context `{hHP: HDATA -> flatmem}  `{hCR3: HDATA -> globalpointer}
          `{hikern: HDATA -> bool}  `{hihost: HDATA -> bool}  `{hpe: HDATA -> bool}.
  Context `{lHP: LDATA -> flatmem}  `{lCR3: LDATA -> globalpointer}
          `{likern: LDATA -> bool}  `{lihost: LDATA -> bool}  `{lpe: LDATA -> bool}.
  Context `{hPT: HDATA -> Z} `{lPT: LDATA -> Z}.
  Context `{hptpool: HDATA -> PTPool} `{lptpool: LDATA -> PTPool}.

  Context `{hnpt: HDATA -> NPT} `{lnpt: LDATA -> NPT}.

  Context `{hflatmem_store: HDATA -> memory_chunk -> Z -> val -> HDATA}
          `{htrapinfo_set: HDATA -> int -> val -> HDATA}.

  Context `{lflatmem_store: LDATA -> memory_chunk -> Z -> val -> LDATA}
          `{ltrapinfo_set: LDATA -> int -> val -> LDATA}.

  Context `{kernel_implies: KernelModeImplies (RData:= HDATA) (data_ops:= data_ops) (ikern:= hikern) (ihost:= hihost)}.
  Context `{trapinfo_inv: TrapinfoSetInvariant (mem:= mem) (memory_model_ops:= memory_model_ops)
                                               (RData:= HDATA) (data_ops:= data_ops)
                                               (trapinfo_set:= htrapinfo_set) (HD:= HD)}.
  Context `{flatmemstore_inv: FlatmemStoreInvariant (mem:= mem) (memory_model_ops:= memory_model_ops)
                                                    (RData:= HDATA) (data_ops:= data_ops)
                                                    (flatmem_store:= hflatmem_store) (HD:= HD)}.

  Notation hexec_flatmem_load := (exec_flatmem_load (HP:= hHP)).
  Notation lexec_flatmem_load := (exec_flatmem_load (HP:= lHP)).
  Notation hexec_flatmem_store := (exec_flatmem_store (flatmem_store:= hflatmem_store)).
  Notation lexec_flatmem_store := (exec_flatmem_store (flatmem_store:= lflatmem_store)).
  Notation hexec_pagefault := (exec_pagefault(trapinfo_set:=htrapinfo_set)).
  Notation lexec_pagefault := (exec_pagefault(trapinfo_set:=ltrapinfo_set)).

  Class LoadStoreProp:= 
    {
      trapinfo_set_relate:
        forall adt adt' f rs r0 addr s,
          relate_AbData s f adt adt'->
          (forall reg : PregEq.t,
             val_inject f (Pregmap.get reg rs) (Pregmap.get reg r0)) ->
          relate_AbData s f (htrapinfo_set adt addr (rs RA))
                        (ltrapinfo_set adt' addr (r0 RA));

      trapinfo_set_match:
        forall adt m0 f addr rs s,
          match_AbData s adt m0 f ->
          match_AbData s (htrapinfo_set adt addr (rs RA)) m0 f;

      flatmem_store_relate:
        forall adt adt' f (rs r0: regset) addr t rd s,
          relate_AbData s f adt adt'->
          (forall reg : PregEq.t,
             val_inject f (Pregmap.get reg rs) (Pregmap.get reg r0)) ->
          relate_AbData s f (hflatmem_store adt t addr (rs rd))
                        (lflatmem_store adt' t addr (r0 rd));

      flatmem_store_match:
        forall adt m0 f addr (rs r0: regset) t rd s,
          match_AbData s adt m0 f ->
          match_AbData s (hflatmem_store adt t addr (rs rd)) m0 f;

      flatmem_inj_relate:
        forall hadt ladt s f,
          relate_AbData s f hadt ladt ->
          FlatMem.flatmem_inj (hHP hadt) (lHP ladt)
          /\ (hihost hadt) = (lihost ladt)
          /\ (hikern hadt) = (likern ladt)
          /\ (hpe hadt) = (lpe ladt)
    }.

  Class LoadStoreProp1:= 
    {
      load_store_prop1:> LoadStoreProp;
      flatmem_inj_relate_CR3:
        forall hadt ladt s f,
          relate_AbData s f hadt ladt
          -> (hCR3 hadt) = (lCR3 ladt)
    }.

  Class LoadStoreProp2:= 
    {
      load_store_pro2:> LoadStoreProp;
      flatmem_inj_relate_PT:
        forall hadt ladt s f,
          relate_AbData s f hadt ladt
          -> (hPT hadt) = (lPT ladt)
             /\ (hptpool hadt) = (lptpool ladt)
    }.

  Class LoadStoreProp3:= 
    {
      load_store_pro3:> LoadStoreProp2;
      flatmem_inj_relate_npt:
        forall hadt ladt s f,
          relate_AbData s f hadt ladt
          -> (hnpt hadt) = (lnpt ladt)
    }.

  Section General.

    Context `{loadstoreprop: LoadStoreProp}.

    Lemma loadl_correct:
      forall {F V} (ge1 ge2: Genv.t F V) m1 m1' m2 (d1 d1': HDATAOps) (d2: LDATAOps) rs1 rs2 rs1' f s r chunk i delta a b2 b,
        Asm.exec_load ge1 chunk (m1, d1) a rs1 r = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATA LDATA) s f rs1 m1 d1 rs2 m2 d2
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> eval_addrmode ge1 a rs1 = Vptr b i
        -> f b = Some (b2, delta)
        -> Vptr b2 (Int.add i (Int.repr delta)) = eval_addrmode ge2 a rs2
        -> exists rs2' m2' d2',
             Asm.exec_load ge2 chunk (m2, d2) a rs2 r = Next rs2' (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATA LDATA) s f rs1' m1' d1' rs2' m2' d2'.
    Proof.
      intros. unfold Asm.exec_load in *.
      assert(HINJ: val_inject f (Vptr b i) (Vptr b2 (Int.add i (Int.repr delta)))).
      {
        apply val_inject_ptr with delta; trivial.
      }
      rewrite H3 in H. rewrite <- H5.
      lift_unfold.
      caseEq(Mem.loadv chunk m1 (Vptr b i)); intros; [| simpl in *; rewrite H6 in H; inv H].
      inv H0. pose proof match_extcall_states as Hmatch.
      inv match_extcall_states.
      exploit Mem.loadv_inject; eauto.
      intros [v0 [HLD HVAL]].
      simpl in *; setoid_rewrite HLD.
      rewrite H6 in H. inv H.
      exists ((nextinstr_nf rs2 # r <- v0)), m2, d2.
      split; trivial.
      constructor; eauto.
      eapply nextinstr_nf_inject'; eauto.
      Next_NF_Simpl.
      reg_destruct; eauto.
    Qed.

    Lemma storel_correct:
      forall {F V} (ge1 ge2: Genv.t F V) m1 m1' m2 (d1 d1': HDATAOps) (d2: LDATAOps) rs1 rs2 rs1' f s r chunk i delta a b2 b rd,
        Asm.exec_store ge1 chunk (m1, d1) a rs1 r rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATA LDATA) s f rs1 m1 d1 rs2 m2 d2
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> eval_addrmode ge1 a rs1 = Vptr b i
        -> f b = Some (b2, delta)
        -> Vptr b2 (Int.add i (Int.repr delta)) = eval_addrmode ge2 a rs2
        -> exists rs2' m2' d2',
             Asm.exec_store ge2 chunk (m2, d2) a rs2 r rd = Next rs2' (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATA LDATA) s f rs1' m1' d1' rs2' m2' d2'.
    Proof.
      intros. unfold Asm.exec_store in *.
      assert(HINJ: val_inject f (Vptr b i) (Vptr b2 (Int.add i (Int.repr delta)))).
      {
        apply val_inject_ptr with delta; trivial.
      }
      rewrite H3 in H. rewrite <- H5.
      lift_unfold.
      caseEq(Mem.store chunk m1 b (Int.unsigned i) (rs1 r)); intros; [| simpl in *; rewrite H6 in H; inv H].
      inv H0. pose proof match_extcall_states as Hmatch.
      inv match_extcall_states.
      generalize match_reg; intros HT.
      unfold Pregmap.get in *.
      specialize (HT r).
      assert (HST: Mem.storev chunk m1 (Vptr b i) (rs1 r) = Some m) by (simpl; trivial).
      exploit Mem.storev_mapped_inject; eauto.
      simpl in *.
      intros [m10 [HLD HVAL]].
      rewrite H6 in H. setoid_rewrite HLD. inv H.
      exists ((nextinstr_nf (undef_regs rd rs2))), m10, d2.
      split; trivial.
      constructor; eauto.
      constructor; eauto.
      assert(forall i b,
               In i new_glbl ->
               find_symbol s i = Some b -> b <> b2).
      {
        red; intros. subst.
        eapply inject_forward_equal in H4; eauto. inv H4.
        eapply (match_newglob_noperm _ _ _ Cur); eauto.
        eapply Mem.valid_access_perm.
        eapply Mem.store_valid_access_3; eauto.
      }
      eapply store_match_correct; eauto.
      erewrite Mem.nextblock_store; eauto.
      erewrite (Mem.nextblock_store _ _ _ _ _ _ HLD); eauto.

      red; intros. exploit match_newglob_noperm; eauto.
      eapply Mem.perm_store_2; eauto.

      intros. 
      erewrite (Mem.nextblock_store _ _ _ _ _ _ HST); eauto.

      eapply nextinstr_nf_inject; eauto.
      eapply undef_regs_inject; eauto.
    Qed.

    Lemma exec_flatmem_load_correct:
      forall t m1 m1' m2 d1 d2 d1' rs1 rd rs2 rs1' addr f s,
        hexec_flatmem_load t (m1, d1) addr rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATA LDATA) s f rs1 m1 d1 rs2 m2 d2
        -> exists r'0 m2' d2',
             lexec_flatmem_load t (m2, d2) addr rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATA LDATA) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros; unfold exec_flatmem_load in *.
      refine_split; eauto. inv H. simpl.
      inv H0. constructor; eauto. inv match_extcall_states.
      exploit flatmem_inj_relate; eauto.
      intros [Hflt _].
      specialize (FlatMem.load_inj _ _ t addr _ f Hflt refl_equal).
      intros [v0 [HLD HVL]]. rewrite HLD in *.
      set (v := (FlatMem.load t (hHP d1')) addr) in *.         
      Next_NF_Simpl.
      reg_destruct; trivial.
      assert (val_inject f (rs1 PC) (rs2 PC)) by eauto.
      destruct rd; simpl in *; trivial;
      repeat simpl_Pregmap; apply Val_add_simpl; trivial.
    Qed.

    Lemma exec_flatmem_store_correct:
      forall t m1 m1' m2 d1 d2 d1' rs1 rd rs2 rs1' addr f s,
        hexec_flatmem_store t (m1, d1) addr rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATA LDATA) s f rs1 m1 d1 rs2 m2 d2
        -> exists r'0 m2' d2',
             lexec_flatmem_store t (m2, d2) addr rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATA LDATA) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros; unfold exec_flatmem_store in *.
      refine_split; eauto. inv H. simpl.
      inv H0. inv match_extcall_states. constructor; eauto.
      constructor; eauto.
      eapply flatmem_store_relate; eauto.
      eapply flatmem_store_match; eauto.
      assert (val_inject f (rs1 PC) (rs2 PC)) by eauto.
      Next_NF_Simpl.
      destruct rd; simpl in *; trivial;
      repeat simpl_Pregmap; reg_destruct; trivial;
      try apply Val_add_simpl; trivial.
      repeat (rewrite Pregmap.gsspec; simpl).
      reg_destruct; eauto.
    Qed.

    Lemma pagefault_correct:
      forall {F V} (ge1 ge2: Genv.t F V) m1 m1' m2 d1 d2 d1' rs1 rs2 rs1' addr f s,
        hexec_pagefault ge1 (m1, d1) addr rs1 = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATA LDATA) s f rs1 m1 d1 rs2 m2 d2
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> exists r'0 m2' d2',
             lexec_pagefault ge2 (m2, d2) addr rs2 = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATA LDATA) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros. unfold exec_pagefault in *.
      pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H1 H2) as [Hpre _].            
      rewrite Hpre.
      caseEq (Genv.find_symbol ge1 pgf_handler); [intros b HSy| intros HSy]; rewrite HSy in H; contra_inv.
      refine_split; eauto. inv H. simpl.
      inv H0. constructor; eauto.
      inv match_extcall_states. constructor; eauto.
      eapply trapinfo_set_relate; eauto.
      eapply trapinfo_set_match; eauto.
      Next_NF_Simpl. 
      inv match_extcall_states.
      assert (HFB: f b = Some (b, 0%Z)).
      {
        eapply stencil_find_symbol_inject; eauto.
      }
      reg_destruct; eauto.
    Qed.

    Notation hexec_guest_load := (exec_guest_load1 (HP:= hHP)).
    Notation lexec_guest_load := (exec_guest_load1 (HP:= lHP)).
    Notation hexec_guest_store := (exec_guest_store1 (flatmem_store:= hflatmem_store)).
    Notation lexec_guest_store := (exec_guest_store1 (flatmem_store:= lflatmem_store)).

    Lemma guest_load_correct1:
      forall {F V} (ge1 ge2: Genv.t F V) m1 m1' m2 d1 d2 d1' rs1 rs2 rs1' f s rd t i,
        hexec_guest_load ge1 i t (m1, d1) rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATA LDATA) s f rs1 m1 d1 rs2 m2 d2
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> exists r'0 m2' d2',
             lexec_guest_load ge2 i t (m2, d2) rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATA LDATA) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros. unfold exec_guest_load1 in *.
      pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H1 H2) as [Hpre _].            
      rewrite Hpre.
      caseEq (Genv.find_symbol ge1 NPT_LOC);
        [| intro HLD; rewrite HLD in H; contra_inv].
      intros b0 HF. 
      exploit (stencil_find_symbol_inject (ge:= ge1)); eauto. intros HF0.
      rewrite HF in *. simpl in *.
      lift_unfold.
      caseEq(Mem.load Mint32 m1 b0 (Int.unsigned (Int.repr (PDX (Int.unsigned i) * 4))));
        [| intro HLD; rewrite HLD in H; contra_inv].
      intros v HLD.
      pose proof H0 as Hmatch.
      inv H0. inv match_extcall_states.
      exploit Mem.load_inject; eauto.
      rewrite Z.add_0_r; intros [v1[HLD1 HVAL]].
      rewrite HLD in H; rewrite HLD1.
      clear HLD HLD1.
      destruct v; contra_inv; inv_val_inject.
      caseEq (Mem.load Mint32 m1 b
                       (Int.unsigned (Int.repr (Int.unsigned i0 / 4096 * 4096 + PTX (Int.unsigned i) * 4))));
        [| intro HLD; rewrite HLD in H; contra_inv].
      intros v' HLD.
      specialize (proj1 (match_inject_forward _ _ _ H4)); intros HDZ.
      rewrite HDZ in *.
      exploit Mem.load_inject; eauto.
      repeat (rewrite Int.add_zero).
      rewrite Z.add_0_r.
      intros [v1'[HLD1 HVAL]].
      rewrite HLD in H; rewrite HLD1.
      destruct v'; contra_inv. inv_val_inject.
      subdestruct.
      eapply exec_flatmem_load_correct; eauto.
    Qed.

    Lemma guest_store_correct1:
      forall {F V} (ge1 ge2: Genv.t F V) m1 m1' m2 d1 d2 d1' rs1 rs2 rs1' f s rd t i,
        hexec_guest_store ge1 i t (m1, d1) rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATA LDATA) s f rs1 m1 d1 rs2 m2 d2
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> exists r'0 m2' d2',
             lexec_guest_store ge2 i t (m2, d2) rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATA LDATA) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros. unfold exec_guest_store1 in *.
      pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H1 H2) as [Hpre _].            
      rewrite Hpre.
      caseEq (Genv.find_symbol ge1 NPT_LOC);
        [| intro HLD; rewrite HLD in H; contra_inv].
      intros b0 HF. 
      exploit (stencil_find_symbol_inject (ge:= ge1)); eauto. intros HF0.
      rewrite HF in *. simpl in *.
      lift_unfold.
      caseEq(Mem.load Mint32 m1 b0 (Int.unsigned (Int.repr (PDX (Int.unsigned i) * 4))));
        [| intro HLD; rewrite HLD in H; contra_inv].
      intros v HLD.
      pose proof H0 as Hmatch.
      inv H0. inv match_extcall_states.
      exploit Mem.load_inject; eauto.
      rewrite Z.add_0_r; intros [v1[HLD1 HVAL]].
      rewrite HLD in H; rewrite HLD1.
      clear HLD HLD1.
      destruct v; contra_inv; inv_val_inject.
      caseEq (Mem.load Mint32 m1 b
                       (Int.unsigned (Int.repr (Int.unsigned i0 / 4096 * 4096 + PTX (Int.unsigned i) * 4))));
        [| intro HLD; rewrite HLD in H; contra_inv].
      intros v' HLD.
      specialize (proj1 (match_inject_forward _ _ _ H4)); intros HDZ.
      rewrite HDZ in *.
      exploit Mem.load_inject; eauto.
      repeat (rewrite Int.add_zero).
      rewrite Z.add_0_r.
      intros [v1'[HLD1 HVAL]].
      rewrite HLD in H; rewrite HLD1.
      destruct v'; contra_inv. inv_val_inject.
      subdestruct.
      eapply exec_flatmem_store_correct; eauto.
    Qed.

    Notation hexec_host_load := (exec_host_load2 (HP:= hHP) (PT:= hPT) (trapinfo_set:= htrapinfo_set)
                                                 (ptpool:= hptpool)).
    Notation lexec_host_load := (exec_host_load2 (HP:= lHP) (PT:= lPT) (trapinfo_set:= ltrapinfo_set)
                                                 (ptpool:= lptpool)).
    Notation hexec_host_store := (exec_host_store2 (PT:= hPT) (trapinfo_set:= htrapinfo_set)
                                                   (flatmem_store:= hflatmem_store) (ptpool:= hptpool)).
    Notation lexec_host_store := (exec_host_store2 (PT:= lPT) (trapinfo_set:= ltrapinfo_set)
                                                   (flatmem_store:= lflatmem_store) (ptpool:= lptpool)).
    Lemma host_load_correct2:
      forall {F V} (ge1 ge2: Genv.t F V) t m1 m1' m2 d1 d2 d1' rs1 rd rs2 rs1' f i s,
        hexec_host_load ge1 i t (m1, d1) rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATA LDATA) s f rs1 m1 d1 rs2 m2 d2
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> hPT d1 = lPT d2
        -> hptpool d1 = lptpool d2
        -> exists r'0 m2' d2',
             lexec_host_load ge2 i t (m2, d2) rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATA LDATA) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros. unfold exec_host_load2 in *; simpl in *.
      rewrite <- H3, <- H4. subdestruct.
      eapply exec_flatmem_load_correct; eauto.
      eapply exec_flatmem_load_correct; eauto.
      eapply pagefault_correct; eauto.
    Qed.

    Lemma host_store_correct2:
      forall {F V} (ge1 ge2: Genv.t F V) t m1 m1' m2 d1 d2 d1' rs1 rd rs2 rs1' f i s,
        hexec_host_store ge1 i t (m1, d1) rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATA LDATA) s f rs1 m1 d1 rs2 m2 d2
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> hPT d1 = lPT d2
        -> hptpool d1 = lptpool d2
        -> exists r'0 m2' d2',
             lexec_host_store ge2 i t (m2, d2) rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATA LDATA) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros. unfold exec_host_store2 in *; simpl in *.
      rewrite <- H3, <- H4. subdestruct.
      eapply exec_flatmem_store_correct; eauto.
      eapply exec_flatmem_store_correct; eauto.
      eapply pagefault_correct; eauto.
    Qed.

  End General.
  
  Section Load_Store1.

    Context `{loadstoreprop: LoadStoreProp1}.

    Notation hexec_host_load := (exec_host_load1 (HP:= hHP) (CR3:= hCR3) (trapinfo_set:= htrapinfo_set)).
    Notation lexec_host_load := (exec_host_load1 (HP:= lHP) (CR3:= lCR3) (trapinfo_set:= ltrapinfo_set)).
    Notation hexec_host_store := (exec_host_store1 (CR3:= hCR3) (trapinfo_set:= htrapinfo_set)
                                                   (flatmem_store:= hflatmem_store)).
    Notation lexec_host_store := (exec_host_store1 (CR3:= lCR3) (trapinfo_set:= ltrapinfo_set)
                                                   (flatmem_store:= lflatmem_store)).
    
    Notation hLoad := (fun F V => exec_loadex1 (HP:= hHP)(CR3:= hCR3) (trapinfo_set:= htrapinfo_set)
                                               (ikern:= hikern) (ihost:= hihost) (pe:= hpe) (F:=F) (V:=V)).
    Notation lLoad := (fun F V => exec_loadex1 (HP:= lHP)(CR3:= lCR3) (trapinfo_set:= ltrapinfo_set)
                                               (ikern:= likern) (ihost:= lihost) (pe:= lpe) (F:=F) (V:=V)).

    Notation hStore := (fun F V => exec_storeex1 (CR3:= hCR3) (trapinfo_set:= htrapinfo_set)
                                                 (ikern:= hikern) (ihost:= hihost) (pe:= hpe)
                                                 (flatmem_store := hflatmem_store) (F:=F) (V:=V)).
    Notation lStore := (fun F V => exec_storeex1 (CR3:= lCR3) (trapinfo_set:= ltrapinfo_set)
                                                 (ikern:= likern) (ihost:= lihost) (pe:= lpe)
                                                 (flatmem_store := lflatmem_store) (F:=F) (V:=V)).

    Lemma host_load_correct1:
      forall {F V} (ge1 ge2: Genv.t F V) t m1 m1' m2 d1 d2 d1' rs1 rd rs2 rs1' f i s,
        hexec_host_load ge1 i t (m1, d1) rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATA LDATA) s f rs1 m1 d1 rs2 m2 d2
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> hCR3 d1 = lCR3 d2
        -> exists r'0 m2' d2',
             lexec_host_load ge2 i t (m2, d2) rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATA LDATA) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros. unfold exec_host_load1 in *; simpl in *.
      rewrite <- H3.
      destruct (hCR3 d1); contra_inv.
      pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H1 H2) as [Hpre _].            
      rewrite Hpre.
      caseEq (Genv.find_symbol ge1 b);
        [| intro HLD; rewrite HLD in H; contra_inv].
      intros b0 HF. rewrite HF in *.
      lift_unfold.
      pose proof H0 as Hmatch.
      inv H0. inv match_extcall_states.
      exploit (stencil_find_symbol_inject (ge:= ge1)); eauto. intros HF0.
      caseEq(Mem.load Mint32 m1 b0 (Int.unsigned (Int.repr (Int.unsigned ofs + PDX (Int.unsigned i) * 4))));
        [| intro HLD; rewrite HLD in H; contra_inv].
      intros v HLD.
      exploit Mem.load_inject; eauto.
      rewrite Z.add_0_r; intros [v1[HLD1 HVAL]].
      rewrite HLD in H; rewrite HLD1.
      clear HLD HLD1.
      destruct v; contra_inv. inv_val_inject.
      caseEq (Mem.load Mint32 m1 b1
                       (Int.unsigned
                          (Int.repr (Int.unsigned i0 / PgSize * PgSize + PTX (Int.unsigned i) * 4))));
        [| intro HLD; rewrite HLD in H; contra_inv].
      intros v' HLD.
      specialize (proj1 (match_inject_forward _ _ _ H5)); intros HDZ.
      rewrite HDZ in *.
      exploit Mem.load_inject; eauto.
      repeat (rewrite Int.add_zero).
      rewrite Z.add_0_r.
      intros [v1'[HLD1 HVAL]].
      rewrite HLD in H; rewrite HLD1.
      destruct v'; contra_inv. inv_val_inject.
      subdestruct.
      eapply exec_flatmem_load_correct; eauto.
      eapply exec_flatmem_load_correct; eauto.
      eapply pagefault_correct; eauto.
    Qed.

    Lemma host_store_correct1:
      forall {F V} (ge1 ge2: Genv.t F V) t m1 m1' m2 d1 d2 d1' rs1 rd rs2 rs1' f i s,
        hexec_host_store ge1 i t (m1, d1) rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATA LDATA) s f rs1 m1 d1 rs2 m2 d2
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> hCR3 d1 = lCR3 d2
        -> exists r'0 m2' d2',
             lexec_host_store ge2 i t (m2, d2) rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATA LDATA) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros. unfold exec_host_store1 in *; simpl in *.
      rewrite <- H3.
      destruct (hCR3 d1); contra_inv.
      pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H1 H2) as [Hpre _].            
      rewrite Hpre.
      caseEq (Genv.find_symbol ge1 b);
        [| intro HLD; rewrite HLD in H; contra_inv].
      intros b0 HF. rewrite HF in *.
      lift_unfold.
      pose proof H0 as Hmatch.
      inv H0. inv match_extcall_states.
      exploit (stencil_find_symbol_inject (ge:= ge1)); eauto. intros HF0.
      caseEq(Mem.load Mint32 m1 b0 (Int.unsigned (Int.repr (Int.unsigned ofs + PDX (Int.unsigned i) * 4))));
        [| intro HLD; rewrite HLD in H; contra_inv].
      intros v HLD.
      exploit Mem.load_inject; eauto.
      rewrite Z.add_0_r; intros [v1[HLD1 HVAL]].
      rewrite HLD in H; rewrite HLD1.
      clear HLD HLD1.
      destruct v; contra_inv. inv_val_inject.
      caseEq (Mem.load Mint32 m1 b1
                       (Int.unsigned
                          (Int.repr (Int.unsigned i0 / PgSize * PgSize + PTX (Int.unsigned i) * 4))));
        [| intro HLD; rewrite HLD in H; contra_inv].
      intros v' HLD.
      specialize (proj1 (match_inject_forward _ _ _ H5)); intros HDZ.
      rewrite HDZ in *.
      exploit Mem.load_inject; eauto.
      repeat (rewrite Int.add_zero).
      rewrite Z.add_0_r.
      intros [v1'[HLD1 HVAL]].
      rewrite HLD in H; rewrite HLD1.
      destruct v'; contra_inv. inv_val_inject.
      subdestruct.
      eapply exec_flatmem_store_correct; eauto.
      eapply exec_flatmem_store_correct; eauto.
      eapply pagefault_correct; eauto.
    Qed.

    Lemma load_correct1:
      load_accessor_sim_def HDATAOps LDATAOps (one_crel HDATA LDATA) hLoad lLoad.
    Proof.
      unfold load_accessor_sim_def. intros.
      pose proof H2 as Hmatch.
      inv H2. inv match_extcall_states.
      exploit flatmem_inj_relate; eauto.
      intros [Hflt[Hhost[Hkern Hpe]]].
      exploit flatmem_inj_relate_CR3; eauto. intros HCR3.
      pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H0 H) as Hpre.            
      erewrite exec_load_symbols_preserved in H1; try eapply Hpre.
      unfold exec_loadex1 in *; simpl in *.
      rewrite <- Hhost, <- Hkern, <- Hpe.
      exploit (eval_addrmode_correct ge2 ge2 a); eauto. simpl; intros HW.
      caseEq(eval_addrmode ge2 a rs1); intros; rewrite H2 in *; contra_inv.
      inv HW.
      simpl in *; subdestruct.
      eapply host_load_correct1; eauto.
      eapply guest_load_correct1; eauto.

      inv HW; simpl in *.
      subdestruct.
      eapply loadl_correct; eauto.
    Qed.

    Lemma store_correct1:
      store_accessor_sim_def HDATAOps LDATAOps (one_crel HDATA LDATA) hStore lStore.
    Proof.
      unfold store_accessor_sim_def. intros.
      pose proof H2 as Hmatch.
      inv H2. inv match_extcall_states.
      exploit flatmem_inj_relate; eauto.
      intros [Hflt[Hhost[Hkern Hpe]]].
      exploit flatmem_inj_relate_CR3; eauto. intros HCR3.
      pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H0 H) as Hpre.
      unfold exec_storeex1 in *.
      simpl in *. rewrite <- Hhost, <- Hkern, <- Hpe.
      exploit (eval_addrmode_correct ge1 ge2 a); eauto. simpl; intros HW.
      caseEq(eval_addrmode ge1 a rs1); intros; rewrite H2 in *; contra_inv.
      inv HW.
      simpl in *; subdestruct.
      eapply host_store_correct1; eauto.
      eapply guest_store_correct1; eauto.

      inv HW; simpl in *.
      subdestruct.
      eapply storel_correct; eauto.
    Qed.

  End Load_Store1.

  Section Load_Store2.

    Context `{loadstoreprop: LoadStoreProp2}.
    
    Notation hLoad := (fun F V => exec_loadex2 (HP:= hHP) (PT:= hPT) (ptpool:= hptpool) (trapinfo_set:= htrapinfo_set)
                                               (ikern:= hikern) (ihost:= hihost) (pe:= hpe) (F:=F) (V:=V)).
    Notation lLoad := (fun F V => exec_loadex2 (HP:= lHP) (PT:= lPT) (ptpool:= lptpool) (trapinfo_set:= ltrapinfo_set)
                                               (ikern:= likern) (ihost:= lihost) (pe:= lpe) (F:=F) (V:=V)).

    Notation hStore := (fun F V => exec_storeex2 (PT:= hPT) (ptpool:= hptpool) (trapinfo_set:= htrapinfo_set)
                                                 (ikern:= hikern) (ihost:= hihost) (pe:= hpe)
                                                 (flatmem_store := hflatmem_store) (F:=F) (V:=V)).
    Notation lStore := (fun F V => exec_storeex2 (PT:= lPT) (ptpool:= lptpool) (trapinfo_set:= ltrapinfo_set)
                                                 (ikern:= likern) (ihost:= lihost) (pe:= lpe)
                                                 (flatmem_store := lflatmem_store) (F:=F) (V:=V)).

    Lemma load_correct2:
      load_accessor_sim_def HDATAOps LDATAOps (one_crel HDATA LDATA) hLoad lLoad.
    Proof.
      unfold load_accessor_sim_def. intros.
      pose proof H2 as Hmatch.
      inv H2. inv match_extcall_states.
      exploit flatmem_inj_relate; eauto.
      intros [Hflt[Hhost[Hkern Hpe]]].
      exploit flatmem_inj_relate_PT; eauto. intros [HPT Hptpool].
      pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H0 H) as Hpre.            
      erewrite exec_load_symbols_preserved in H1; try eapply Hpre.
      unfold exec_loadex2 in *; simpl in *.
      rewrite <- Hhost, <- Hkern, <- Hpe.
      exploit (eval_addrmode_correct ge2 ge2 a); eauto. simpl; intros HW.
      caseEq(eval_addrmode ge2 a rs1); intros; rewrite H2 in *; contra_inv.
      inv HW.
      simpl in *; subdestruct.
      eapply host_load_correct2; eauto.
      eapply guest_load_correct1; eauto.

      inv HW; simpl in *.
      subdestruct.
      eapply loadl_correct; eauto.
    Qed.

    Lemma store_correct2:
      store_accessor_sim_def HDATAOps LDATAOps (one_crel HDATA LDATA) hStore lStore.
    Proof.
      unfold store_accessor_sim_def. intros.
      pose proof H2 as Hmatch.
      inv H2. inv match_extcall_states.
      exploit flatmem_inj_relate; eauto.
      intros [Hflt[Hhost[Hkern Hpe]]].
      exploit flatmem_inj_relate_PT; eauto. intros [HPT Hptpool].
      pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H0 H) as Hpre.
      unfold exec_storeex2 in *.
      simpl in *. rewrite <- Hhost, <- Hkern, <- Hpe.
      exploit (eval_addrmode_correct ge1 ge2 a); eauto. simpl; intros HW.
      caseEq(eval_addrmode ge1 a rs1); intros; rewrite H2 in *; contra_inv.
      inv HW.
      simpl in *; subdestruct.
      eapply host_store_correct2; eauto.
      eapply guest_store_correct1; eauto.

      inv HW; simpl in *.
      subdestruct.
      eapply storel_correct; eauto.
    Qed.

  End Load_Store2.

  Section Load_Store3.

    Context `{loadstoreprop: LoadStoreProp3}.

    Notation hexec_guest_load := (exec_guest_load2 (HP:= hHP) (npt:= hnpt)).
    Notation lexec_guest_load := (exec_guest_load2 (HP:= lHP) (npt:= lnpt)).
    Notation hexec_guest_store := (exec_guest_store2 (flatmem_store:= hflatmem_store) (npt:= hnpt)).
    Notation lexec_guest_store := (exec_guest_store2 (flatmem_store:= lflatmem_store) (npt:= lnpt)).

    Lemma guest_load_correct2:
      forall m1 m1' m2 d1 d2 d1' rs1 rs2 rs1' f s rd t i,
        hexec_guest_load i t (m1, d1) rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATA LDATA) s f rs1 m1 d1 rs2 m2 d2
        -> hnpt d1 = lnpt d2
        -> exists r'0 m2' d2',
             lexec_guest_load i t (m2, d2) rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATA LDATA) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros. unfold exec_guest_load2 in *.
      lift_unfold.
      rewrite <- H1.
      destruct (ZMap.get (PDX (Int.unsigned i)) (hnpt d1)); contra_inv.
      destruct (ZMap.get (PTX (Int.unsigned i)) nptab); contra_inv.
      eapply exec_flatmem_load_correct; eauto.
    Qed.

    Lemma guest_store_correct2:
      forall m1 m1' m2 d1 d2 d1' rs1 rs2 rs1' f s rd t i,
        hexec_guest_store i t (m1, d1) rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATA LDATA) s f rs1 m1 d1 rs2 m2 d2
        -> hnpt d1 = lnpt d2
        -> exists r'0 m2' d2',
             lexec_guest_store i t (m2, d2) rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATA LDATA) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros. unfold exec_guest_store2 in *.
      lift_unfold.
      rewrite <- H1.
      destruct (ZMap.get (PDX (Int.unsigned i)) (hnpt d1)); contra_inv.
      destruct (ZMap.get (PTX (Int.unsigned i)) nptab); contra_inv.
      eapply exec_flatmem_store_correct; eauto.
    Qed.
    
    Notation hLoad := (fun F V => exec_loadex3 (HP:= hHP) (PT:= hPT) (ptpool:= hptpool) (trapinfo_set:= htrapinfo_set)
                                               (ikern:= hikern) (ihost:= hihost) (pe:= hpe) (npt:= hnpt) (F:=F) (V:=V)).
    Notation lLoad := (fun F V => exec_loadex3 (HP:= lHP) (PT:= lPT) (ptpool:= lptpool) (trapinfo_set:= ltrapinfo_set)
                                               (ikern:= likern) (ihost:= lihost) (pe:= lpe) (npt:= lnpt) (F:=F) (V:=V)).

    Notation hStore := (fun F V => exec_storeex3 (PT:= hPT) (ptpool:= hptpool) (trapinfo_set:= htrapinfo_set)
                                                 (ikern:= hikern) (ihost:= hihost) (pe:= hpe) (npt:= hnpt)
                                                 (flatmem_store := hflatmem_store) (F:=F) (V:=V)).
    Notation lStore := (fun F V => exec_storeex3 (PT:= lPT) (ptpool:= lptpool) (trapinfo_set:= ltrapinfo_set)
                                                 (ikern:= likern) (ihost:= lihost) (pe:= lpe) (npt:= lnpt)
                                                 (flatmem_store := lflatmem_store) (F:=F) (V:=V)).

    Lemma load_correct3:
      load_accessor_sim_def HDATAOps LDATAOps (one_crel HDATA LDATA) hLoad lLoad.
    Proof.
      unfold load_accessor_sim_def. intros.
      pose proof H2 as Hmatch.
      inv H2. inv match_extcall_states.
      exploit flatmem_inj_relate; eauto.
      intros [Hflt[Hhost[Hkern Hpe]]].
      exploit flatmem_inj_relate_PT; eauto. intros [HPT Hptpool].
      exploit flatmem_inj_relate_npt; eauto. intros Hnpt.
      pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H0 H) as Hpre.            
      erewrite exec_load_symbols_preserved in H1; try eapply Hpre.
      unfold exec_loadex3 in *; simpl in *.
      rewrite <- Hhost, <- Hkern, <- Hpe.
      exploit (eval_addrmode_correct ge2 ge2 a); eauto. simpl; intros HW.
      caseEq(eval_addrmode ge2 a rs1); intros; rewrite H2 in *; contra_inv.
      inv HW.
      simpl in *; subdestruct.
      eapply host_load_correct2; eauto.
      eapply guest_load_correct2; eauto.

      inv HW; simpl in *.
      subdestruct.
      eapply loadl_correct; eauto.
    Qed.

    Lemma store_correct3:
      store_accessor_sim_def HDATAOps LDATAOps (one_crel HDATA LDATA) hStore lStore.
    Proof.
      unfold store_accessor_sim_def. intros.
      pose proof H2 as Hmatch.
      inv H2. inv match_extcall_states.
      exploit flatmem_inj_relate; eauto.
      intros [Hflt[Hhost[Hkern Hpe]]].
      exploit flatmem_inj_relate_PT; eauto. intros [HPT Hptpool].
      exploit flatmem_inj_relate_npt; eauto. intros Hnpt.
      pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H0 H) as Hpre.
      unfold exec_storeex3 in *.
      simpl in *. rewrite <- Hhost, <- Hkern, <- Hpe.
      exploit (eval_addrmode_correct ge1 ge2 a); eauto. simpl; intros HW.
      caseEq(eval_addrmode ge1 a rs1); intros; rewrite H2 in *; contra_inv.
      inv HW.
      simpl in *; subdestruct.
      eapply host_store_correct2; eauto.
      eapply guest_store_correct2; eauto.

      inv HW; simpl in *.
      subdestruct.
      eapply storel_correct; eauto.
    Qed.

  End Load_Store3.

End Load_Store_Refinement.*)

Hint Extern 10 (KernelModeImplies (ikern := _) (ihost := _)) =>
(constructor; simpl; tauto):
  typeclass_instances.
