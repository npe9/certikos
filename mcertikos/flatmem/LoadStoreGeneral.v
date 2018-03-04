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

  Lemma loadl_correct:
    forall {F V} (ge1 ge2: Genv.t F V) m1 m1' m2 (d1 d1': HDATAOps) (d2: LDATAOps) rs1 rs2 rs1' f s r chunk i delta a b2 b,
      Asm.exec_load ge1 chunk (m1, d1) a rs1 r = Next rs1' (m1', d1')
      -> MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1 m1 d1 rs2 m2 d2
      -> stencil_matches s ge1
      -> stencil_matches s ge2
      -> eval_addrmode ge1 a rs1 = Vptr b i
      -> f b = Some (b2, delta)
      -> Vptr b2 (Int.add i (Int.repr delta)) = eval_addrmode ge2 a rs2
      -> exists rs2' m2' d2',
           Asm.exec_load ge2 chunk (m2, d2) a rs2 r = Next rs2' (m2', d2')
           /\ MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' rs2' m2' d2'.
  Proof.
    intros. unfold Asm.exec_load in *.
    assert(HINJ: val_inject f (Vptr b i) (Vptr b2 (Int.add i (Int.repr delta)))).
    {
      apply val_inject_ptr with delta; trivial.
    }
    rewrite H3 in H. rewrite <- H5.
    revert H; simpl; lift_trivial; intros H.
    destruct(Mem.loadv chunk m1 (Vptr b i)) eqn: HLD; [| simpl in HLD; rewrite HLD in H; inv H].
    inv H0. pose proof match_extcall_states as Hmatch.
    inv match_extcall_states.
    exploit Mem.loadv_inject; eauto.
    intros [v0 [HLD' HVAL]].
    simpl in *; setoid_rewrite HLD'.
    rewrite HLD in H. inv H.
    exists ((nextinstr_nf rs2 # r <- v0)), m2, d2.
    split; trivial.
    constructor; eauto.
    eapply nextinstr_nf_inject'; eauto.
    val_inject_simpl.
  Qed.

  Lemma storel_correct:
    forall {F V} (ge1 ge2: Genv.t F V) m1 m1' m2 (d1 d1': HDATAOps) (d2: LDATAOps) rs1 rs2 rs1' f s r chunk i delta a b2 b rd,
      Asm.exec_store ge1 chunk (m1, d1) a rs1 r rd = Next rs1' (m1', d1')
      -> MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1 m1 d1 rs2 m2 d2
      -> stencil_matches s ge1
      -> stencil_matches s ge2
      -> eval_addrmode ge1 a rs1 = Vptr b i
      -> f b = Some (b2, delta)
      -> Vptr b2 (Int.add i (Int.repr delta)) = eval_addrmode ge2 a rs2
      -> exists rs2' m2' d2',
           Asm.exec_store ge2 chunk (m2, d2) a rs2 r rd = Next rs2' (m2', d2')
           /\ MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' rs2' m2' d2'.
  Proof.
    intros. unfold Asm.exec_store in *.
    assert(HINJ: val_inject f (Vptr b i) (Vptr b2 (Int.add i (Int.repr delta)))).
    {
      apply val_inject_ptr with delta; trivial.
    }
    rewrite H3 in H. rewrite <- H5.
    revert H; simpl; lift_trivial; intros H.
    destruct (Mem.store chunk m1 b (Int.unsigned i) (rs1 r)) eqn: HST; contra_inv.
    inv H0. pose proof match_extcall_states as Hmatch.
    inv match_extcall_states.
    generalize match_reg; intros HT.
    unfold Pregmap.get in *.
    specialize (HT r). 
    assert (HST': Mem.storev chunk m1 (Vptr b i) (rs1 r) = Some m) by (simpl; trivial).
    exploit Mem.storev_mapped_inject; eauto.
    simpl in *.
    intros [m10 [HLD HVAL]].
    setoid_rewrite HLD. inv H.
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
    erewrite (Mem.nextblock_store _ _ _ _ _ _ HST'); eauto.
    val_inject_simpl.
  Qed.

End Refinement.