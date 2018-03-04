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
Require Import LoadStoreDef.
Require Import GuestAccessIntelDef0.

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

  Context `{haccessor: int64 -> Z -> memory_chunk -> (mwd HDATAOps) -> regset -> preg -> Asm.outcome (mem:= mwd HDATAOps)}.
  Context `{laccessor: int64 -> Z -> memory_chunk -> (mwd LDATAOps) -> regset -> preg -> Asm.outcome (mem:= mwd LDATAOps)}.

  Section General.

    Opaque align_chunk Z.mul Z.div Z.sub. 

    Lemma guest_intel_correct1:
      forall {F V} (ge1 ge2: Genv.t F V) m1 m1' m2 d1 d2 d1' rs1 rs2 rs1' f s rd t i,
        exec_guest_intel_accessor1 ge1 haccessor i t (m1, d1) rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1 m1 d1 rs2 m2 d2
        -> stencil_matches s ge1
        -> stencil_matches s ge2
        -> forall ACCESSOR_CORRECT:
                    (forall i i1, haccessor i i1 t (m1, d1) rs1 rd = Next rs1' (m1', d1') ->
                                  exists r'0 m2' d2',
                                    laccessor i i1 t (m2, d2) rs2 rd = Next r'0 (m2', d2') /\
                                    MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' r'0 m2' d2'),
           exists r'0 m2' d2',
             exec_guest_intel_accessor1 ge2 laccessor i t (m2, d2) rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros. unfold exec_guest_intel_accessor1 in *.
      pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H1 H2) as [Hpre _].            
      rewrite Hpre.
      destruct (Genv.find_symbol ge1 EPT_LOC) eqn: HF; contra_inv.
      exploit (stencil_find_symbol_inject (ge:= ge1)); eauto. intros HF0.
      revert H; simpl; lift_trivial; intros H.
      destruct (Mem.load Mint32 m1 b
                         (Int.unsigned (Int.repr (EPT_PML4_INDEX (Int.unsigned i) * 8 + 4)))) eqn: HLD; contra_inv.
      pose proof H0 as Hmatch.
      inv H0. inv match_extcall_states.
      exploit Mem.load_inject; eauto.
      rewrite Z.add_0_r; intros [v1[HLD1 HVAL]].
      rewrite HLD1.
      clear HLD HLD1.
      destruct v; contra_inv; inv HVAL.
      destruct (peq b0 b); contra_inv; subst.
      assert (HFB: f b = Some (b, 0%Z)).
      {
        eapply match_inject_flat. trivial.
      }
      rewrite HFB in H4. inv H4. rewrite peq_true.
      rewrite Int.add_zero.

      destruct (Mem.load Mint32 m1 b2
                         (Int.unsigned
                            (Int.repr
                               (Int.unsigned i0 / PgSize * PgSize + 4 + EPT_PDPT_INDEX (Int.unsigned i) * 8)))) eqn: HLD; contra_inv.
      exploit Mem.load_inject; eauto.
      rewrite Z.add_0_r; intros [v1[HLD1 HVAL]].
      rewrite HLD1.
      clear HLD HLD1.
      destruct v; contra_inv; inv HVAL.
      destruct (peq b b2); contra_inv; subst.
      rewrite HFB in H4. inv H4. rewrite peq_true.
      rewrite Int.add_zero.

      destruct (Mem.load Mint32 m1 b0
                         (Int.unsigned
                            (Int.repr
                               (Int.unsigned i1 / PgSize * PgSize + 4 + EPT_PDIR_INDEX (Int.unsigned i) * 8)))) eqn: HLD; contra_inv.
      exploit Mem.load_inject; eauto.
      rewrite Z.add_0_r; intros [v1[HLD1 HVAL]].
      rewrite HLD1.
      clear HLD HLD1.
      destruct v; contra_inv; inv HVAL.
      destruct (peq b b0); contra_inv; subst.
      rewrite HFB in H4. inv H4. rewrite peq_true.
      rewrite Int.add_zero.

      destruct (Mem.load Mint64 m1 b2
                         (Int.unsigned
                            (Int.repr
                               (Int.unsigned i2 / PgSize * PgSize + EPT_PTAB_INDEX (Int.unsigned i) * 8)))) eqn: HLD; contra_inv.
      exploit Mem.load_inject; eauto.
      rewrite Z.add_0_r; intros [v1[HLD1 HVAL]].
      rewrite HLD1.
      clear HLD HLD1.
      destruct v; contra_inv; inv HVAL. eauto.
    Qed.

  End General.

End Refinement.