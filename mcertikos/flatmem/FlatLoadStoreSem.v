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

Section Load_Store.

  Context `{Hobs: Observation}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{HD: CompatData RData}.
  Context `{Hmwd: UseMemWithData mem}.

  Notation HDATAOps := (cdata (cdata_ops := data_ops) RData).

  Context `{flatmem_store: RData -> memory_chunk -> Z -> val -> option (cdata RData)}.
    
  Definition exec_flatmem_load (chunk: memory_chunk) (m: mwd HDATAOps)
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

  Definition exec_flatmem_store (chunk: memory_chunk) (m: mwd HDATAOps)
             (adr: Z)  (rs: regset) (r1: preg) (destroyed: list preg) : Asm.outcome (mem:= mwd HDATAOps):=
    let abd := snd m in
    match flatmem_store abd chunk adr (rs r1) with
      | Some abd' => Next (nextinstr_nf (undef_regs destroyed rs)) (fst m, abd')
      | _ => Stuck
    end.

  Lemma exec_flatmem_store_fst_mem:
    forall chunk m adr rs r1 rs' ds m',
      exec_flatmem_store chunk m adr rs r1 ds = Next rs' m' ->
      fst m' = fst m.
  Proof.
    unfold exec_flatmem_store; intros.
    destruct (flatmem_store ((snd m): RData) chunk adr (rs r1)); contra_inv.
    inv H; reflexivity.
  Qed.

  Lemma exec_flatmem_store_asm_invariant:
    forall chunk m adr rs r1 rs' ds m',
      exec_flatmem_store chunk m adr rs r1 ds = Next rs' m' ->
      forall {F V} (ge: _ F V),
        AsmX.asm_invariant ge rs m ->
        AsmX.asm_invariant ge rs' m'.
  Proof.
    unfold exec_flatmem_store; intros.
    destruct (flatmem_store ((snd m): RData) chunk adr (rs r1)); contra_inv.
    inv H.
    inv H0.
    inv inv_inject_neutral.
    constructor.
    constructor; auto.
    apply nextinstr_nf_inject; auto.
    val_inject_simpl.
    apply nextinstr_nf_wt; auto.
    apply undef_regs_wt; auto.
  Qed.

  Context {flat_inv: FlatmemStoreInvariant (flatmem_store:= flatmem_store)}.

  Lemma exec_flatmem_store_low_level_invariant':
    forall chunk m adr rs r1 rs' ds m',
      exec_flatmem_store chunk m adr rs r1 ds = Next rs' m' ->
      forall n,
        CompatData.low_level_invariant n (snd m) ->
        CompatData.low_level_invariant n (snd m').
  Proof.
    unfold exec_flatmem_store; intros.
    destruct (flatmem_store ((snd m): RData) chunk adr (rs r1)) eqn: HST; contra_inv.    
    inv H; simpl.
    eapply flatmem_store_low_level_invariant; eauto.
  Qed.

  Lemma exec_flatmem_store_low_level_invariant:
    forall chunk m adr rs r1 rs' ds m',
      exec_flatmem_store chunk m adr rs r1 ds = Next rs' m' ->
      CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
      CompatData.low_level_invariant (Mem.nextblock m') (snd m').
  Proof.
    intros until 1.
    replace (Mem.nextblock m') with (Mem.nextblock m).
    eapply exec_flatmem_store_low_level_invariant'; eauto.
    exploit exec_flatmem_store_fst_mem; eauto.
    clear. simpl; lift_trivial. congruence.
  Qed.

  Lemma exec_flatmem_store_high_level_invariant:
    forall chunk m adr rs r1 rs' ds m',
      exec_flatmem_store chunk m adr rs r1 ds = Next rs' m' ->
      (adr mod PgSize <= PgSize - size_chunk chunk)%Z ->
      high_level_invariant (snd m) ->
      high_level_invariant (snd m').
  Proof.
    unfold exec_flatmem_store; intros.
    destruct (flatmem_store ((snd m): RData) chunk adr (rs r1)) eqn: HST; contra_inv.    
    inv H. simpl.
    eapply flatmem_store_high_level_invariant; eauto.
  Qed.

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

  Context `{hflatmem_store: RData -> memory_chunk -> Z -> val -> option RData}.
  Context `{lflatmem_store: RData -> memory_chunk -> Z -> val -> option RData}.

  Notation hexec_flatmem_store := (exec_flatmem_store (flatmem_store:= hflatmem_store)).
  Notation lexec_flatmem_store := (exec_flatmem_store (flatmem_store:= lflatmem_store)).

  Section General.

    Context {loadstoreprop: LoadStoreProp (hflatmem_store:= hflatmem_store) (lflatmem_store:= lflatmem_store)}.
    Context {re1: relate_impl_HP'}.

    Lemma exec_flatmem_load_correct:
      forall t m1 m1' m2 d1 d2 d1' rs1 rd rs2 rs1' addr f s,
        exec_flatmem_load t (m1, d1) addr rs1 rd = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1 m1 d1 rs2 m2 d2
        -> exists r'0 m2' d2',
             exec_flatmem_load t (m2, d2) addr rs2 rd = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros; unfold exec_flatmem_load in *.
      refine_split; eauto. inv H. simpl.
      inv H0. constructor; eauto. inv match_extcall_states.
      pose match_related as Hflt.
      eapply relate_impl_HP'_eq in Hflt; eauto.
      specialize (FlatMem.load_inj _ _ t addr _ f Hflt refl_equal).
      intros [v0 [HLD HVL]]. rewrite HLD in *.      
      set (v := (FlatMem.load t (HP d1')) addr) in *.         
      val_inject_simpl.
    Qed.

    Context {flatmemstore_inv: FlatmemStoreInvariant (data_ops:= data_ops) (flatmem_store:= hflatmem_store)}.

    Lemma exec_flatmem_store_correct:
      forall t m1 m1' m2 d1 d2 d1' rs1 rd rs2 rs1' addr f s ds,
        hexec_flatmem_store t (m1, d1) addr rs1 rd ds = Next rs1' (m1', d1')
        -> MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1 m1 d1 rs2 m2 d2
        -> (addr mod PgSize <= PgSize - size_chunk t)%Z
        -> exists r'0 m2' d2',
             lexec_flatmem_store t (m2, d2) addr rs2 rd ds = Next r'0 (m2', d2')
             /\ MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' r'0 m2' d2'.
    Proof.
      intros; unfold exec_flatmem_store in *.
      destruct (hflatmem_store (snd (m1, d1)) t addr (rs1 rd)) eqn: HST; contra_inv.
      inv H. inv H0. inv match_extcall_states. 
      exploit flatmem_store_relate; eauto.
      intros (ladt & HST' & Hre).
      simpl. rewrite HST'.
      refine_split; eauto. 
      constructor; eauto.
      constructor; eauto.
      eapply flatmem_store_match; eauto.
      val_inject_simpl.
    Qed.

  End General.
  
End Refinement.