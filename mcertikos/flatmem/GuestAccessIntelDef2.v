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

      Variable accessor: Z -> Z -> memory_chunk -> (mwd HDATAOps) -> regset -> preg -> Asm.outcome (mem:= mwd HDATAOps).

      Definition exec_guest_intel_accessor2 (adr: int) (chunk: memory_chunk) (m: mwd HDATAOps) (rs: regset) (rd: preg) :=
        let ofs := (Int.unsigned adr) in 
        let adt:= (snd m) in
        match ZMap.get (EPT_PML4_INDEX ofs) (ept adt) with
          | EPML4EValid epdpt =>
            match ZMap.get (EPT_PDPT_INDEX ofs) epdpt with
              | EPDPTEValid epdt =>
                match ZMap.get (EPT_PDIR_INDEX ofs) epdt with
                  | EPDTEValid eptab =>
                    match ZMap.get (EPT_PTAB_INDEX ofs) eptab with
                      | EPTEValid n =>
                        accessor n ofs chunk m rs rd
                      | _ => Stuck
                    end
                  | _ => Stuck
                end
              | _ => Stuck
            end
          | _ => Stuck
        end.

      Lemma exec_guest_intel_accessor2_high_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_guest_intel_accessor2 adr chunk m rs rd = Next rs' m' ->
          high_level_invariant (snd m) ->
          (forall i i',
             accessor i i' chunk m rs rd = Next rs' m' ->
             high_level_invariant (snd m')) ->
          high_level_invariant (snd m').
      Proof.
        unfold exec_guest_intel_accessor2. intros. subdestruct.
        intros. eauto.
      Qed.

      Lemma exec_guest_intel_accessor2_asm_invariant:
        forall chunk rd,
        forall adr m rs rs' m',
          exec_guest_intel_accessor2 adr chunk m rs rd = Next rs' m' ->
          AsmX.asm_invariant ge rs m ->
          (forall i i',
             accessor i i' chunk m rs rd = Next rs' m' ->
             AsmX.asm_invariant ge rs' m') ->
          AsmX.asm_invariant ge rs' m'.
      Proof.
        unfold exec_guest_intel_accessor2. intros. subdestruct.
        intros; eauto.
      Qed.

      Lemma exec_guest_intel_accessor2_low_level_invariant:
        forall adr chunk m rs rd rs' m',
          exec_guest_intel_accessor2 adr chunk m rs rd = Next rs' m' ->
          CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
          (forall i i',
             accessor i i' chunk m rs rd = Next rs' m' ->
             CompatData.low_level_invariant (Mem.nextblock m') (snd m')) ->
          CompatData.low_level_invariant (Mem.nextblock m') (snd m').
      Proof.
        unfold exec_guest_intel_accessor2. intros. subdestruct.
        intros; eauto.
      Qed.

    End Accessor.

  End GE.

  (*Section EQ.

    Context `{accessor1: Z -> Z -> memory_chunk -> (mwd HDATAOps) -> regset -> preg -> Asm.outcome (mem:= mwd HDATAOps)}.
    Context `{accessor2: Z -> Z -> memory_chunk -> (mwd HDATAOps) -> regset -> preg -> Asm.outcome (mem:= mwd HDATAOps)}.
 
    Lemma exec_guest_intel_accessor2_eq:
      forall {F V} (ge1 ge2: Genv.t F V) i chunk m rs r
             (ACC: (forall i1 i2 , accessor2 i1 i2 chunk m rs r = accessor1 i1 i2 chunk m rs r)),
        exec_guest_intel_accessor2 accessor2 i chunk m rs r =
        exec_guest_intel_accessor2 accessor1 i chunk m rs r.
    Proof.
      intros. unfold exec_guest_intel_accessor2.
      destruct (ZMap.get (EPT_PML4_INDEX (Int.unsigned i)) (ept (snd m))); try reflexivity.
      destruct (ZMap.get (EPT_PDPT_INDEX (Int.unsigned i)) epdpt); try reflexivity.
      destruct (ZMap.get (EPT_PDIR_INDEX (Int.unsigned i)) epdt); try reflexivity.
      destruct (ZMap.get (EPT_PTAB_INDEX (Int.unsigned i)) eptab); try reflexivity.
      erewrite ACC; trivial.
    Qed.

  End EQ.*)

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

  Context `{haccessor: Z -> Z -> memory_chunk -> (mwd HDATAOps) -> regset -> preg -> Asm.outcome (mem:= mwd HDATAOps)}.
  Context `{laccessor: Z -> Z -> memory_chunk -> (mwd LDATAOps) -> regset -> preg -> Asm.outcome (mem:= mwd LDATAOps)}.

  Section General.

    Opaque align_chunk Z.mul Z.div Z.sub. 

    Context {inv: relate_impl_ept}.

    Lemma guest_intel_correct2:
      forall m1 m1' m2 d1 d2 d1' rs1 rs2 rs1' f s rd t i,
        exec_guest_intel_accessor2 haccessor i t (m1, d1) rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1 m1 d1 rs2 m2 d2
        -> forall ACCESSOR_CORRECT:
                    (forall i i', haccessor i i' t (m1, d1) rs1 rd = Next rs1' (m1', d1') ->
                                  exists r'0 m2' d2',
                                    laccessor i i' t (m2, d2) rs2 rd = Next r'0 (m2', d2') /\
                                    MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' r'0 m2' d2'),
           exists r'0 m2' d2',
             exec_guest_intel_accessor2 laccessor i t (m2, d2) rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      unfold exec_guest_intel_accessor2; simpl. intros.
      pose proof H0 as Hmatch.
      inv H0. inv match_extcall_states.
      erewrite <- relate_impl_ept_eq; eauto. 
      subdestruct. eauto.
    Qed.

  End General.

End Refinement.