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
(*              Lemmas for invariants                                  *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Maps.
Require Import AuxStateDataType.
Require Import Constant.
Require Import GlobIdent.
Require Import FlatMemory.
Require Import CommonTactic.
Require Import AuxLemma.

Require Import Values.
Require Import AsmX.
Require Import Integers.
Require Import liblayers.compat.CompatLayers.

Section SYNCCHAN_INV.

  Lemma SyncChanPool_Valid_gss:
    forall syncch,
      SyncChanPool_Valid syncch ->
      forall i to skpa count,
        SyncChanPool_Valid (ZMap.set i (SyncChanValid to skpa count) syncch).
  Proof.
    unfold SyncChanPool_Valid, SyncChannel_Valid; intros.
    destruct (zeq i0 i); subst.
    - rewrite ZMap.gss. eauto.
    - rewrite ZMap.gso; eauto.
  Qed.

End SYNCCHAN_INV.

(*Section CHAN_INV.

  Lemma ChanPool_Valid_gss:
    forall ch,
      ChanPool_Valid ch ->
      forall i s t,
        ChanPool_Valid (ZMap.set i (ChanValid s t) ch).
  Proof.
    unfold ChanPool_Valid, Channel_Valid; intros.
    destruct (zeq i0 i); subst.
    - rewrite ZMap.gss. eauto.
    - rewrite ZMap.gso; eauto.
  Qed.

End CHAN_INV.*)

Section UCTXT_INV.

  Local Open Scope Z_scope.

  Lemma uctxt_inject_neutral_gss:
    forall up n,
      uctxt_inject_neutral up n ->
      forall i u,
        (forall ii,
           0 <= ii < UCTXT_SIZE ->
           Val.has_type (ZMap.get ii u) AST.Tint /\
           val_inject (Mem.flat_inj n) (ZMap.get ii u) (ZMap.get ii u)) ->
        uctxt_inject_neutral (ZMap.set i u up) n.
  Proof.
    unfold uctxt_inject_neutral. intros.
    destruct (zeq i ii); subst.
    - rewrite ZMap.gss; eauto.
    - rewrite ZMap.gso; eauto.
  Qed.

  Lemma uctxt_inject_neutral0_gss:
    forall u n,
      (forall ii,
         0 <= ii < UCTXT_SIZE ->
         Val.has_type (ZMap.get ii u) AST.Tint /\
         val_inject (Mem.flat_inj n) (ZMap.get ii u) (ZMap.get ii u)) ->
      forall v,
        (Val.has_type v AST.Tint
         /\ val_inject (Mem.flat_inj n) v v) ->
        forall i,
          (forall ii,
             0 <= ii < UCTXT_SIZE ->
             Val.has_type (ZMap.get ii (ZMap.set i v u)) AST.Tint /\
             val_inject (Mem.flat_inj n) (ZMap.get ii (ZMap.set i v u))
                        (ZMap.get ii (ZMap.set i v u))).
  Proof.
    intros. destruct (zeq ii i); subst.
    - rewrite ZMap.gss; eauto.
    - rewrite ZMap.gso; eauto.
  Qed.

  Lemma uctxt_inject_neutral0_Vint:
    forall n v,
      (Val.has_type (Vint v) AST.Tint
       /\ val_inject (Mem.flat_inj n) (Vint v) (Vint v)).
  Proof.
    split; constructor.
  Qed.

  Lemma uctxt_inject_neutral0_init:
    forall n ii,
      0 <= ii < UCTXT_SIZE ->
      Val.has_type (ZMap.get ii (ZMap.init Vundef)) AST.Tint /\
      val_inject (Mem.flat_inj n) (ZMap.get ii (ZMap.init Vundef)) (ZMap.get ii (ZMap.init Vundef)).
  Proof.
    intros. rewrite ZMap.gi. split; constructor.
  Qed.

  Lemma uctxt_inject_neutral0_Vptr_flat:
    forall n b ofs,
      (Mem.flat_inj n) b = Some (b, 0) ->
      (Val.has_type (Vptr b ofs) AST.Tint
       /\ val_inject (Mem.flat_inj n) (Vptr b ofs) (Vptr b ofs)).
  Proof.
    split; try constructor.
    econstructor; eauto.
    rewrite Int.add_zero; trivial.
  Qed.

  Lemma uctxt_inject_neutral_impl:
    forall up n,
      uctxt_inject_neutral up n ->
      forall i,
        0 <= i < num_proc ->
        forall ii,
          0 <= ii < UCTXT_SIZE ->
          let u := ZMap.get i up in
          Val.has_type (ZMap.get ii u) AST.Tint /\
          val_inject (Mem.flat_inj n) (ZMap.get ii u) (ZMap.get ii u).
  Proof.
    unfold uctxt_inject_neutral; intros.
    eapply H; eauto.
  Qed.

  Section WITHSTENCIL.

    Context `{Hstencil: Stencil}.

    Lemma uctxt_inject_neutral0_Vptr:
      forall s n fun_id b ofs,
        find_symbol s fun_id = Some b ->
        (genv_next s <= n) % positive ->
        (Val.has_type (Vptr b ofs) AST.Tint
         /\ val_inject (Mem.flat_inj n) (Vptr b ofs) (Vptr b ofs)).
    Proof.
      intros. eapply uctxt_inject_neutral0_Vptr_flat; eauto.
      eapply stencil_find_symbol_inject'; eauto.
      apply flat_inj_inject_incr; trivial.
    Qed.

    Lemma uctxt_inject_neutral0_Vptr':
      forall s n b ofs,
        (exists fun_id, find_symbol s fun_id = Some b) ->
        (genv_next s <= n) % positive ->
        (Val.has_type (Vptr b ofs) AST.Tint
         /\ val_inject (Mem.flat_inj n) (Vptr b ofs) (Vptr b ofs)).
    Proof.
      intros. destruct H as (? & ?).
      eapply uctxt_inject_neutral0_Vptr; eauto.
    Qed.

  End WITHSTENCIL.

End UCTXT_INV.