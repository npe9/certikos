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
Require Import LoadStoreDef.

Section PAGE_FAULT.

  Context `{Hobs: Observation}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{HD: CompatData RData}.
  Context `{Hmwd: UseMemWithData mem}.

  Notation HDATAOps := (cdata (cdata_ops := data_ops) RData).

  Section GE.
    
    Context {F V} (ge: Genv.t F V).

    Definition exec_pagefault (m: mwd HDATAOps) (adr: int) (rs: regset): Asm.outcome (mem:= mwd HDATAOps)
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
        CompatData.low_level_invariant (Mem.nextblock m) (snd m) ->
        CompatData.low_level_invariant (Mem.nextblock m') (snd m').
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

  End GE.

End PAGE_FAULT.

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

  Context {loadstoreprop: LoadStoreProp'}.

  Lemma pagefault_correct:
    forall {F V} (ge1 ge2: Genv.t F V) m1 m1' m2 d1 d2 d1' rs1 rs2 rs1' addr f s,
      exec_pagefault ge1 (m1, d1) addr rs1 = Next rs1' (m1', d1')
      -> MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1 m1 d1 rs2 m2 d2
      -> stencil_matches s ge1
      -> stencil_matches s ge2
      -> exists r'0 m2' d2',
           exec_pagefault ge2 (m2, d2) addr rs2 = Next r'0 (m2', d2')
           /\ MatchPrimcallStates (one_crel HDATAOps LDATAOps) s f rs1' m1' d1' r'0 m2' d2'.
  Proof.
    intros. unfold exec_pagefault in *.
    pose proof (stencil_matches_preserves_trans _ _ _ _ _ _ _ H1 H2) as [Hpre _].            
    rewrite Hpre.
    destruct (Genv.find_symbol ge1 pgf_handler) eqn: Hsy; contra_inv.
    refine_split; eauto. inv H. simpl.
    inv H0. constructor; eauto.
    inv match_extcall_states. constructor; eauto.
    eapply trapinfo_set_relate; eauto.
    eapply trapinfo_set_match; eauto.
    val_inject_simpl.
    inv match_extcall_states.
    assert (HFB: f b = Some (b, 0%Z)).
    {
      eapply stencil_find_symbol_inject; eauto.
    }
    val_inject_simpl.
  Qed.

End Refinement.