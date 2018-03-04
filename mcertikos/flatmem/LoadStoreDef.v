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
Require Import ObjCPU.

Section DEF.

  Context `{Hmem: Mem.MemoryModel}.
  Context `{HD: CompatData RData}.
  Context `{Hmwd: UseMemWithData mem}.

  Notation HDATAOps := (cdata (cdata_ops := data_ops) RData).
  
  Class KernelModeImplies: Prop :=
    {
      kernel_mode_implies: forall adt, kernel_mode adt -> (ikern adt = true /\ ihost adt = true)
    }.

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
          CompatData.low_level_invariant n abd ->
          forall v,
            Val.has_type v AST.Tint ->
            val_inject (Mem.flat_inj n) v v ->
            forall adr,
              CompatData.low_level_invariant n (trapinfo_set abd adr v)
    }.

  Context `{flatmem_store: RData -> memory_chunk -> Z -> val -> option (cdata RData)}.

  Class FlatmemStoreInvariant: Prop :=
    {
      flatmem_store_low_level_invariant:
        forall abd n,
          CompatData.low_level_invariant n abd ->
          forall chunk adr v abd',
            flatmem_store abd chunk adr v = Some abd' ->
            CompatData.low_level_invariant n abd'
      ;

      flatmem_store_high_level_invariant:
        forall abd,
          high_level_invariant abd ->
          forall chunk adr v abd',
            (adr mod PgSize <= PgSize - size_chunk chunk)%Z ->
            flatmem_store abd chunk adr v = Some abd' ->
            high_level_invariant abd'
    }.

  Lemma PTADDR_mod_lt:
    forall adr n,
      (adr mod PgSize <= PgSize - n)%Z ->
      forall i,
        (PTADDR i adr mod PgSize <= PgSize - n)%Z.
  Proof.
    unfold PTADDR. intros. rewrite Zplus_comm.          
    rewrite Z_mod_plus_full. rewrite Zmod_mod.
    assumption.
  Qed.  

End DEF.

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

  Context `{hflatmem_store: RData -> memory_chunk -> Z -> val -> option RData}.
  Context `{lflatmem_store: RData -> memory_chunk -> Z -> val -> option RData}.

  Class LoadStoreProp':= 
    {
      trapinfo_set_relate:
        forall adt adt' f rs r0 addr s,
          relate_AbData s f adt adt'->
          (forall reg : PregEq.t,
             val_inject f (Pregmap.get reg rs) (Pregmap.get reg r0)) ->
          relate_AbData s f (trapinfo_set adt addr (rs RA))
                        (trapinfo_set adt' addr (r0 RA));

      trapinfo_set_match:
        forall adt m0 f addr rs s,
          match_AbData s adt m0 f ->
          match_AbData s (trapinfo_set adt addr (rs RA)) m0 f
    }.

  Class LoadStoreProp:= 
    {
      load_store_prop':> LoadStoreProp';

      flatmem_store_relate:
        forall adt adt' f (rs r0: regset) m0 s,
          relate_AbData s f adt adt'->
          match_AbData s adt m0 f ->
          (forall reg : PregEq.t,
             val_inject f (Pregmap.get reg rs) (Pregmap.get reg r0)) ->
          forall hadt addr t rd,
            hflatmem_store adt t addr (rs rd) = Some hadt ->
            (addr mod PgSize <= PgSize - size_chunk t) % Z ->
            exists ladt, lflatmem_store adt' t addr (r0 rd) = Some ladt /\
                         relate_AbData s f hadt ladt;

      flatmem_store_match:
        forall adt m0 f addr (rs r0: regset) t rd s,
          match_AbData s adt m0 f ->
          forall adt',
            hflatmem_store adt t addr (rs rd) = Some adt' ->
            match_AbData s adt' m0 f

    }.

End Refinement.

Hint Extern 10 (KernelModeImplies) =>
(constructor; simpl; tauto):
  typeclass_instances.