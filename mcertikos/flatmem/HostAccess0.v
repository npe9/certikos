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
Require Import Observation.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Import liblayers.compcertx.ClightModules.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatClightSem.
Require Import liblayers.compcertx.MemWithData.

Require Import AbstractDataType.
Require Export PageFault.
Require Import LoadStoreDef.

Section Load_Store.

  Context `{Hobs: Observation}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{HD: CompatData(Obs:=Obs) RData}.
  Context `{Hmwd: UseMemWithData mem}.

  Notation HDATAOps := (cdata (cdata_ops := data_ops) RData).

  Section GE.
    
    Context {F V} (ge: Genv.t F V).

    Definition exec_host_load_snd0 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) (rs: regset) (rd: preg) 
               (b1: block) (ofs1: int) (id: ident):=
      let ofs := (Int.unsigned adr) in
      match Mem.loadv Mint32 m (Vptr b1 (Int.repr (((Int.unsigned ofs1)/PgSize)*PgSize + (PTX ofs) *4))) with
        | Some (Vint n) => 
          let pz:= (Int.unsigned n) mod PgSize in
          (** try to access the memory that user level can access *)
          let adr' := (Int.repr (PTADDR ((Int.unsigned n)/PgSize) ofs)) in
          (** if the page map is valid *)
          if zeq pz PT_PERM_P then
            Asm.exec_load ge chunk m (Addrmode None None (inr (id, adr'))) rs rd
          else 
            if zeq pz PT_PERM_PTU then
              Asm.exec_load ge chunk m (Addrmode None None (inr (id, adr'))) rs rd
            (** if the page map is not valid *)
            else 
              if zeq pz PT_PERM_UP then
                exec_pagefault ge m adr rs
              else Stuck
        | _ => Stuck
      end.

    (** The memory accessors for the raw memory in the host mode *)
    Definition exec_host_load0 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) (rs: regset) (rd: preg) :=
      let adt:= (snd m) in
      let ofs := (Int.unsigned adr) in 
      (** CR3 register storing the starting address of page map*)
      match (CR3 adt) with
        | GLOBP idpt ofs' =>
          match Genv.find_symbol ge idpt with
            | Some b =>
              (** first level page map *)
              match Mem.loadv Mint32 m (Vptr b (Int.repr ((Int.unsigned ofs') + (PDX ofs) * 4))) with
                | Some (Vint ofs1) =>
                  match Genv.find_symbol ge FlatMem_LOC with
                    | Some b1 =>
                      exec_host_load_snd0 adr chunk m rs rd b1 ofs1 FlatMem_LOC
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

    Local Existing Instance Asm.mem_accessors_default.
    Local Existing Instance AsmX.mem_accessors_default_invariant.

    Context `{trap_inv: TrapinfoSetInvariant (Obs:=Obs) (data_ops := data_ops)}.

    Lemma exec_host_load_snd0_asm_invariant:
      forall chunk rd,
      forall TYP: subtype (type_of_chunk chunk) (typ_of_preg rd) = true,
      forall adr m rs b1 ofs1 rs' id m',
        exec_host_load_snd0 adr chunk m rs rd b1 ofs1 id = Next rs' m' ->
        AsmX.asm_invariant ge rs m ->
        AsmX.asm_invariant ge rs' m'.
    Proof.
      unfold exec_host_load_snd0. intros.
      subdestruct.
      - eapply exec_load_invariant; try eassumption.
      - eapply exec_load_invariant; try eassumption.
      - eapply exec_pagefault_asm_invariant; eauto.
    Qed.

    Lemma exec_host_load0_asm_invariant:
      forall chunk rd,
      forall TYP: subtype (type_of_chunk chunk) (typ_of_preg rd) = true,
      forall adr m rs rs' m',
        exec_host_load0 adr chunk m rs rd = Next rs' m' ->
        AsmX.asm_invariant ge rs m ->
        AsmX.asm_invariant ge rs' m'.
    Proof.
      unfold exec_host_load0. intros. subdestruct.
      eapply exec_host_load_snd0_asm_invariant; eassumption.
    Qed.

    Lemma exec_host_load_snd0_high_level_invariant :
      forall adr chunk m rs rd b1 ofs1 rs' id m',
        exec_host_load_snd0 adr chunk m rs rd b1 ofs1 id = Next rs' m' ->
        high_level_invariant (snd m) ->
        high_level_invariant (snd m').
    Proof.
      unfold exec_host_load_snd0, Asm.exec_load. intros. subdestruct; inv H; trivial.
      eapply exec_pagefault_high_level_invariant; eauto.
    Qed.

    Lemma exec_host_load0_high_level_invariant:
      forall adr chunk m rs rd rs' m',
        exec_host_load0 adr chunk m rs rd = Next rs' m' ->
        high_level_invariant (snd m) ->
        high_level_invariant (snd m').
    Proof.
      unfold exec_host_load0. intros. subdestruct.
      eapply exec_host_load_snd0_high_level_invariant; eauto.
    Qed.

    Lemma exec_host_load_snd0_low_level_invariant:
      forall adr chunk m rs rd b1 ofs1 id rs' m',
        exec_host_load_snd0 adr chunk m rs rd b1 ofs1 id = Next rs' m' ->
        AsmX.asm_invariant ge rs m ->
        CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
        CompatData.low_level_invariant (Mem.nextblock m') (snd m').
    Proof.
      unfold exec_host_load_snd0, Asm.exec_load. intros. 
      subdestruct; inv H; trivial.
      eapply exec_pagefault_low_level_invariant in H3; eauto.
    Qed.

    Lemma exec_host_load0_low_level_invariant:
      forall adr chunk m rs rd rs' m',
        exec_host_load0 adr chunk m rs rd = Next rs' m' ->
        AsmX.asm_invariant ge rs m ->
        CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
        CompatData.low_level_invariant (Mem.nextblock m') (snd m').
    Proof.
      unfold exec_host_load0. intros. subdestruct.
      eapply exec_host_load_snd0_low_level_invariant; eauto.
    (*- destruct (Genv.find_symbol ge IDPMap_LOC); try discriminate.
          destruct (Pos.eq_dec b1 b2); try discriminate.
          eapply exec_host_load_snd0_low_level_invariant.*)
    Qed.

    Definition exec_host_store_snd0 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) 
               (rs: regset) (rd: preg) (destroyed: list preg) (b1: block) (ofs1: int) (id: ident):=
      let ofs := (Int.unsigned adr) in 
      match Mem.loadv Mint32 m (Vptr b1 (Int.repr (((Int.unsigned ofs1)/PgSize)*PgSize + (PTX ofs) *4))) with
        | Some (Vint n) => 
          let pz:= (Int.unsigned n) mod PgSize in
          (** try to access the memory that user level can access *)
          let adr' := (Int.repr (PTADDR ((Int.unsigned n)/PgSize) ofs)) in
          (** if the page map is valid *)
          if zeq pz PT_PERM_P then
            Asm.exec_store ge chunk m (Addrmode None None (inr (id, adr'))) rs rd destroyed
          else 
            if zeq pz PT_PERM_PTU then
              Asm.exec_store ge chunk m (Addrmode None None (inr (id, adr'))) rs rd destroyed
            (** if the page map is not valid *)
            else 
              if zeq pz PT_PERM_UP then
                exec_pagefault ge m adr rs
              else Stuck
        | _ => Stuck
      end.

    (** The memory accessors for the raw memory in the host mode *)
    Definition exec_host_store0 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) 
               (rs: regset) (rd: preg) (destroyed: list preg):=
      let adt:= (snd m) in
      let ofs := (Int.unsigned adr) in 
      (** CR3 register storing the starting address of page map*)
      match (CR3 adt) with
        | GLOBP idpt ofs' =>
          match Genv.find_symbol ge idpt with
            | Some b =>
              (** first level page map *)
              match Mem.loadv Mint32 m (Vptr b (Int.repr ((Int.unsigned ofs') + (PDX ofs) * 4))) with
                | Some (Vint ofs1) =>
                  match Genv.find_symbol ge FlatMem_LOC with
                    | Some b1 => exec_host_store_snd0 adr chunk m rs rd destroyed b1 ofs1 FlatMem_LOC
                    (** second level page map *)
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

      Lemma exec_host_store_snd0_high_level_invariant:
        forall adr chunk m rs rd rs' des b1 ofs1 id m',
          exec_host_store_snd0 adr chunk m rs rd des b1 ofs1 id = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_host_store_snd0, Asm.exec_store. intros. subdestruct.
        - lift_unfold.
          destruct Hdestruct3 as [? DATA].
          unfold π_data in DATA. simpl in * |- *. congruence.
        - lift_unfold.
          destruct Hdestruct4 as [? DATA].
          unfold π_data in DATA. simpl in * |- *. congruence.
        - eapply exec_pagefault_high_level_invariant; eauto.
      Qed.

      Lemma exec_host_store0_high_level_invariant:
        forall adr chunk m rs rd rs' des m',
          exec_host_store0 adr chunk m rs rd des = Next rs' m' ->
          high_level_invariant (snd m) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_host_store0. intros. subdestruct.
        eapply exec_host_store_snd0_high_level_invariant; eauto.
        (*- destruct (Genv.find_symbol ge IDPMap_LOC); try discriminate.
          destruct (Pos.eq_dec b1 b2); try discriminate.
          eapply exec_host_store_snd0_high_level_invariant.*)
      Qed.

      Lemma exec_host_store_snd0_asm_invariant:
        forall chunk rd,
        forall adr m rs rs' ds b1 i id m',
          exec_host_store_snd0 adr chunk m rs rd ds b1 i id = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_host_store_snd0. intros. subdestruct.
        - eapply exec_store_invariant; eauto.
        - eapply exec_store_invariant; eauto.
        - eapply exec_pagefault_asm_invariant; eauto.
      Qed.

      Lemma exec_host_store0_asm_invariant:
        forall chunk rd,
        forall adr m rs rs' ds m',
          exec_host_store0 adr chunk m rs rd ds = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_host_store0. intros. subdestruct.
        eapply exec_host_store_snd0_asm_invariant; eauto.
        (*- destruct (Genv.find_symbol ge IDPMap_LOC); try discriminate.
          destruct (Pos.eq_dec b1 b2); try discriminate.
          eapply exec_host_store_snd0_asm_invariant.*)
      Qed.

      Lemma exec_host_store_snd0_low_level_invariant:
        forall adr chunk m rs rd rs' ds b1 i id m',
          exec_host_store_snd0 adr chunk m rs rd ds b1 i id = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
          CompatData.low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_host_store_snd0, Asm.exec_store. intros. subdestruct.
        - lift_unfold. inv H.
          destruct Hdestruct3 as [? DATA].
          unfold π_data in DATA. simpl in * |- *. 
          erewrite Mem.nextblock_store; eauto.
          congruence.
        - lift_unfold. inv H.
          destruct Hdestruct4 as [? DATA].
          unfold π_data in DATA. simpl in * |- *. 
          erewrite Mem.nextblock_store; eauto.
          congruence.
        - eapply exec_pagefault_low_level_invariant in H; eauto.
      Qed.

      Lemma exec_host_store0_low_level_invariant:
        forall adr chunk m rs rd rs' ds m',
          exec_host_store0 adr chunk m rs rd ds = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
          CompatData.low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_host_store0. intros. subdestruct.
        eapply exec_host_store_snd0_low_level_invariant; eauto.
        (*- destruct (Genv.find_symbol ge IDPMap_LOC); try discriminate.
          destruct (Pos.eq_dec b1 b2); try discriminate.
          eapply exec_host_store_snd0_low_level_invariant.*)
      Qed.

  End GE.

End Load_Store.