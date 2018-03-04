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
Require Export AuxStateDataType.
Require Import Constant.
Require Import RealParams.
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import XOmega.
Require Import CLemmas.

Section INITZMAP.

  (* Initialize elements [0..n) of a ZMap to a constant value *)
  Fixpoint init_zmap_nat {A} (n: nat) (x: A) (f: ZMap.t A): ZMap.t A :=
    match n with
      | O => f
      | S i => ZMap.set (Z.of_nat i) x (init_zmap_nat i x f)
    end.

  Lemma init_zmap_nat_inside {A} (n: nat) (x: A) (f: ZMap.t A) (i: Z):
    0 <= i < (Z.of_nat n) ->
    ZMap.get i (init_zmap_nat n x f) = x.
  Proof.
    induction n; intros.
    * rewrite Nat2Z.inj_0 in H.
      omega.
    * simpl.
      destruct (Z.eq_dec i (Z.of_nat n)) as [Hi | Hi].
      + rewrite <- Hi.
        rewrite ZMap.gss.
        reflexivity.
      + rewrite ZMap.gso.
        - apply IHn.
          rewrite Nat2Z.inj_succ in H.
          omega.
        - assumption.
  Qed.

  (* This version has (n: Z) instead of (n: nat) *)
  Definition init_zmap {A} (n: Z): A -> ZMap.t A -> ZMap.t A :=
    init_zmap_nat (Z.to_nat n).

  Lemma init_zmap_inside {A} (n: Z) (x: A) (f: ZMap.t A) (i: Z):
    0 <= i < n ->
    ZMap.get i (init_zmap n x f) = x.
  Proof.
    intros H.
    unfold init_zmap.
    apply init_zmap_nat_inside.
    rewrite Z2Nat.id; omega.
  Qed.

  Lemma init_zmap_eq {A} (i: Z) (x: A) (f: ZMap.t A):
    0 <= i ->
    init_zmap (i+1) x f = ZMap.set i x (init_zmap i x f).
  Proof.
    intro Hi.
    unfold init_zmap.
    change (i + 1) with (Z.succ i).
    rewrite Z2Nat.inj_succ by assumption.
    simpl.
    rewrite Z2Nat.id by assumption.
    reflexivity.
  Qed.

End INITZMAP.

Section CInitSpecsPThreadIntro.

  Context `{real_params_ops : RealParamsOps}.

  Definition real_tcb: TCBPool -> TCBPool :=
    init_zmap num_proc (TCBValid DEAD num_proc num_proc).

  Lemma real_TCB_valid: forall tcb, TCBCorrect_range (real_tcb tcb).
  Proof.
    unfold TCBCorrect_range.
    unfold TCBCorrect.
    intros.
    unfold real_tcb.
    rewrite init_zmap_inside by assumption.
    exists DEAD.
    exists 64.
    exists 64.
    split.
    tauto.
    omega.
  Qed.

  (* FIXME: inconsistent naming *)
  Lemma real_TCB_init: forall tcb, TCBInit (real_tcb tcb).
  Proof.
    unfold TCBInit.
    intros.
    unfold real_tcb.
    rewrite init_zmap_inside by assumption.
    reflexivity.
  Qed.

End CInitSpecsPThreadIntro.

Section CInitSpecsPQueueIntro.

  Context `{real_params_ops : RealParamsOps}.

  Fixpoint Calculate_tdq (i: nat) (tdq: TDQueuePool) : TDQueuePool :=
    match i with 
      | O => ZMap.set 0 (TDQValid num_proc num_proc) tdq
      | S k => ZMap.set (Z.of_nat (S k)) (TDQValid num_proc num_proc) (Calculate_tdq k tdq)
    end.

  Definition real_tdq: TDQueuePool -> TDQueuePool :=
    init_zmap (num_chan + 1) (TDQValid num_proc num_proc).

  (* FIXME: inconsistent naming *)
  Lemma real_tdq_valid: forall tdq, TDQInit (real_tdq tdq).
  Proof.
    unfold TDQInit.
    intros.
    unfold real_tdq.
    rewrite init_zmap_inside by omega.
    reflexivity.
  Qed.

  Lemma real_TDQ_correct:
    forall t,
      TDQCorrect_range (real_tdq t).
  Proof.
    intros. specialize (real_tdq_valid t).
    unfold TDQInit, TDQCorrect_range, TDQCorrect.
    intros. specialize (H _ H0). 
    esplit; esplit. split; eauto.
    split; omega.
  Qed.

End CInitSpecsPQueueIntro.

(* Initialize a TCB pool *)
Section CInitSpecsAbPThreadIntro.

  Context `{real_params_ops : RealParamsOps}.

  Definition real_abtcb :=
    init_zmap num_proc (AbTCBValid DEAD (-1)).

  (* FIXME: inconsistent naming *)
  Lemma real_abtcb_init abtcb:
    AbTCBInit (real_abtcb abtcb).
  Proof.
    intros i.
    apply init_zmap_inside.
  Qed.

  Lemma real_abtcb_valid:
    forall tcbp i,
      0 <= i < num_proc ->
      AbTCBCorrect (ZMap.get i (real_abtcb tcbp)).
  Proof.
    intros; eapply AbTCBInit_valid; eauto.
    apply real_abtcb_init.
  Qed.

  Lemma real_abtcb_range:
    forall tcbp,
      AbTCBCorrect_range (real_abtcb tcbp).
  Proof.
    unfold AbTCBCorrect_range; intros.
    eapply real_abtcb_valid; eauto.
  Qed.

  Lemma real_abtcb_notInQ:
    forall tcbp i s b, 
      0 <= i < num_proc ->
      ZMap.get i (real_abtcb tcbp) = AbTCBValid s b ->
      b = -1.
  Proof.
    intros; eapply AbTCBInit_notInQ; eauto.
    apply real_abtcb_init.
  Qed.

  Lemma real_abtcb_pb_notInQ:
    forall tcbp pb,
      NotInQ pb (real_abtcb tcbp).
  Proof.
    unfold NotInQ; intros.
    eapply real_abtcb_notInQ; eauto.
  Qed.

  Lemma real_abtcb_valid':
    forall tcbp i,
      0 <= i < num_proc ->
      AbTCBCorrect (ZMap.get i (ZMap.set 0 (AbTCBValid RUN (-1)) (real_abtcb tcbp))).
  Proof.
    intros. destruct (zeq i 0); subst.
    +
      rewrite ZMap.gss. unfold AbTCBCorrect. 
      esplit. esplit. split; eauto. omega.
    +
      rewrite ZMap.gso; auto.
      eapply real_abtcb_valid; eauto.
  Qed.

  Lemma real_abtcb_range':
    forall tcbp,
      AbTCBCorrect_range (ZMap.set 0 (AbTCBValid RUN (-1)) (real_abtcb tcbp)).
  Proof.
    unfold AbTCBCorrect_range; intros.
    eapply real_abtcb_valid'; eauto.
  Qed.

  Lemma real_abtcb_notInQ':
    forall tcbp i s b, 
      0 <= i < num_proc ->
      ZMap.get i (ZMap.set 0 (AbTCBValid RUN (-1)) (real_abtcb tcbp)) = AbTCBValid s b ->
      b = -1.
  Proof.
    intros. destruct (zeq i 0); subst.
    +
      rewrite ZMap.gss in *. inv H0. trivial.
    +
      rewrite ZMap.gso in *; auto.
      eapply real_abtcb_notInQ; eauto.
  Qed.

  Lemma real_abtcb_pb_notInQ':
    forall tcbp pb,
      NotInQ pb (ZMap.set 0 (AbTCBValid RUN (-1)) (real_abtcb tcbp)).
  Proof.
    unfold NotInQ; intros.
    eapply real_abtcb_notInQ'; eauto.
  Qed.

  Lemma real_abtcb_notRun:
    forall tcbp i s b,
      0 <= i < num_proc ->
      i <> 0 ->
      ZMap.get i (ZMap.set 0 (AbTCBValid RUN (-1)) (real_abtcb tcbp)) = AbTCBValid s b ->
      s <> RUN.
  Proof.
    intros. rewrite ZMap.gso in *; auto.
    specialize (real_abtcb_init tcbp).
    unfold AbTCBInit. intros. specialize (H2 _ H).
    rewrite H1 in H2. inv H2. red; intros; inv H2.
  Qed.

  Lemma real_abtcb_SingleRun:
    forall tcbp,
      SingleRun 0 (ZMap.set 0 (AbTCBValid RUN (-1)) (real_abtcb tcbp)).
  Proof.
    unfold SingleRun; intros.
    eapply real_abtcb_notRun; eauto.
  Qed.

  Lemma real_abtcb_strong:
    forall tcbp i,
      0 <= i < num_proc ->
      AbTCBStrong (ZMap.get i (real_abtcb tcbp)).
  Proof.
    intros. specialize(real_abtcb_init tcbp).
    unfold AbTCBInit, AbTCBStrong; intros.
    specialize (H0 _ H). rewrite H0.
    esplit. esplit. split; eauto.
    split; trivial.
    split; intros HF; inv HF.
  Qed.

  Lemma real_abtcb_strong_range:
    forall tcbp,
      AbTCBStrong_range (real_abtcb tcbp).
  Proof.
    unfold AbTCBStrong_range. intros.
    eapply real_abtcb_strong; eauto.
  Qed.

  Lemma real_abtcb_strong':
    forall tcbp i,
      0 <= i < num_proc ->
      AbTCBStrong (ZMap.get i (ZMap.set 0 (AbTCBValid RUN (-1)) (real_abtcb tcbp))).
  Proof.
    intros. destruct (zeq i 0); subst.
    +
      rewrite ZMap.gss. unfold AbTCBStrong. 
      esplit. esplit. split; eauto. 
      split; trivial.
      split; intros HF; inv HF.
    +
      rewrite ZMap.gso; auto.
      eapply real_abtcb_strong; eauto.
  Qed.

  Lemma real_abtcb_strong_range':
    forall tcbp,
      AbTCBStrong_range (ZMap.set 0 (AbTCBValid RUN (-1)) (real_abtcb tcbp)).
  Proof.
    unfold AbTCBStrong_range. intros.
    eapply real_abtcb_strong'; eauto.
  Qed.

  Lemma real_abtcb_AC_CurIDValid:
    forall tcbp,
      CurIDValid 0 real_AC (ZMap.set 0 (AbTCBValid RUN (-1)) (real_abtcb tcbp)).
  Proof.
    unfold CurIDValid; intros; simpl; split; auto.
    rewrite ZMap.gss; auto.
  Qed.

End CInitSpecsAbPThreadIntro.

(* Initialize a pool of thread queues *)
Section CInitSpecsAbPQueueIntro.

  Definition real_abq :=
    init_zmap (num_chan + 1) (AbQValid nil).

  (* FIXME: inconsistent naming *)
  Lemma real_abq_init abq:
    AbQInit (real_abq abq).
  Proof.
    intros i Hi.
    apply init_zmap_inside.
    omega.
  Qed.

  Lemma real_abq_valid:
    forall tdqp i, 
      0 <= i <= num_proc ->
      AbQCorrect (ZMap.get i (real_abq tdqp)).
  Proof.
    intros; eapply AbTDQInit_valid; eauto.
    apply real_abq_init.
  Qed.

  Lemma real_abq_range:
    forall tdqp, 
      AbQCorrect_range (real_abq tdqp).
  Proof.
    unfold AbQCorrect_range; intros.
    eapply real_abq_valid; eauto.
  Qed.

  Lemma real_abq_contra:
    forall tdqp l i j,
      0 <= j <= num_proc ->                
      ZMap.get j (real_abq tdqp) = AbQValid l ->
      In i l -> 
      False.
  Proof.
    intros. specialize (real_abq_init tdqp).
    unfold AbQInit. intros HTDQ. specialize (HTDQ _ H).
    rewrite H0 in HTDQ; inv HTDQ. inv H1.
  Qed.

  Lemma real_abtcb_abq_valid:
    forall i j tcbp tdqp s,
      0 <= i < num_proc ->
      0 <= j <= num_proc ->
      ZMap.get i (real_abtcb tcbp) = AbTCBValid s j ->
      exists l, ZMap.get j (real_abq tdqp) = AbQValid l
                /\ count_occ zeq l i = 1%nat.
  Proof.
    intros. specialize (real_abtcb_init tcbp).
    unfold AbTCBInit. intros HTCB.
    specialize (HTCB _ H).
    rewrite H1 in HTCB. inv HTCB. omega.
  Qed.

  Lemma real_abtcb_abq_QCount:
    forall tcbp tdqp,
      QCount (real_abtcb tcbp) (real_abq tdqp).
  Proof.
    unfold QCount; intros.
    eapply real_abtcb_abq_valid; eauto.
  Qed.

  Lemma real_abtcb_abq_valid':
    forall i j tcbp tdqp s,
      0 <= i < num_proc ->
      0 <= j <= num_proc ->
      ZMap.get i (ZMap.set 0 (AbTCBValid RUN (-1)) (real_abtcb tcbp)) = AbTCBValid s j ->
      exists l, ZMap.get j (real_abq tdqp) = AbQValid l
                /\ count_occ zeq l i = 1%nat.
  Proof.
    intros. destruct (zeq i 0); subst.
    + rewrite ZMap.gss in *. inv H1. omega.
    + rewrite ZMap.gso in *; auto.
      eapply real_abtcb_abq_valid; eauto.
  Qed.

  Lemma real_abtcb_abq_QCount':
    forall tcbp tdqp,
      QCount (ZMap.set 0 (AbTCBValid RUN (-1)) (real_abtcb tcbp)) (real_abq tdqp).
  Proof.
    unfold QCount; intros.
    eapply real_abtcb_abq_valid'; eauto.
  Qed.

  Lemma real_abq_inQ:
    forall tdqp l i j tcbp,
      0 <= j <= num_proc ->                
      ZMap.get j (real_abq tdqp) = AbQValid l ->
      In i l -> 
      exists s, ZMap.get i tcbp = AbTCBValid s j.
  Proof.
    intros. exploit real_abq_contra; eauto.
    intros HF; inv HF.
  Qed.

  Lemma real_abq_tcb_inQ:
    forall tcbp tdqp,
      InQ tcbp (real_abq tdqp).
  Proof.
    unfold InQ; intros. 
    exploit real_abq_contra; eauto.
    intros HF; inv HF.
  Qed.

End CInitSpecsAbPQueueIntro.

Section CInitSpecsPIPCIntro.

  Context `{real_params_ops : RealParamsOps}.


  Definition real_syncchpool: SyncChanPool -> SyncChanPool :=
    init_zmap num_chan (SyncChanValid (Int.repr num_chan) Int.zero Int.zero).

  Lemma real_syncchpool_valid: 
    forall syncchpool, SyncChanPool_Init (real_syncchpool syncchpool).
  Proof.
    generalize max_unsigned_val; intros muval.
    unfold SyncChanPool_Init.
    unfold SyncChannel_Init.
    intros.
    unfold real_syncchpool.
    rewrite init_zmap_inside by omega.
    reflexivity.
  Qed.

  Lemma real_syncchpool_valid':
    forall syncchpool, SyncChanPool_Valid (real_syncchpool syncchpool).
  Proof.
    intros. apply SyncChannel_Init_Correct.
    apply real_syncchpool_valid.
  Qed.

(*

  (** proc_init *)
  Definition real_chpool: ChanPool -> ChanPool :=
    init_zmap num_chan (ChanValid Int.zero Int.zero).

  Lemma real_chpool_valid: forall chpool, ChanPool_Init (real_chpool chpool).
  Proof.
    generalize max_unsigned_val; intro muval.
    unfold ChanPool_Init.
    unfold Channel_Init.
    intros.
    unfold real_chpool.
    rewrite init_zmap_inside by omega.
    reflexivity.
  Qed.

  Lemma real_chpool_valid': forall chpool, ChanPool_Valid (real_chpool chpool).
  Proof.
    intros. apply ChanPool_Init_Correct.
    apply real_chpool_valid.
  Qed.*)

End CInitSpecsPIPCIntro.