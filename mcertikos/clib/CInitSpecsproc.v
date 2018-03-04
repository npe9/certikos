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
(*    Definitions used in verification of proc module initialization   *)
(*                                                                     *)
(*                       Xiongnan (Newman) Wu                          *)
(*                                                                     *)
(*                         Yale University                             *)
(*                                                                     *)
(* *********************************************************************)
Require Import Coqlib.
Require Import ZArith.Zwf.
Require Import DataType.
Require Import ProcDataType.
Require Import VirtDataType.
Require Import MemoryExtra.
Require Import Maps.
Require Import Integers.
Require Import CDataTypes.
Require Import LayerDefinition.
Require Import CInitSpecsMPTOp.
Require Import CInitSpecsMPTCommon.
Require Import CInitSpecsMPTBit.
Require Import PThreadIntro.
Require Import PQueueIntro.
Require Import PIPCIntro.
Require Import RealParams.

(** Perhaps this is useful elsewhere? *)
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

(* Initialize a TCB pool *)
Section CInitSpecsAbPThreadIntro.
  Definition real_abtcb :=
    init_zmap num_proc (AbTCBValid DEAD (-1)).

  (* FIXME: inconsistent naming *)
  Lemma real_abtcb_init abtcb:
    AbTCBInit (real_abtcb abtcb) 0 num_proc.
  Proof.
    intros i.
    apply init_zmap_inside.
  Qed.
End CInitSpecsAbPThreadIntro.

(* Initialize a pool of thread queues *)
Section CInitSpecsAbPQueueIntro.
  Definition real_abq :=
    init_zmap (num_chan + 1) (AbQValid nil).

  (* FIXME: inconsistent naming *)
  Lemma real_abq_init abq:
    AbQInit (real_abq abq) 0 num_chan.
  Proof.
    intros i Hi.
    apply init_zmap_inside.
    omega.
  Qed.
End CInitSpecsAbPQueueIntro.

Section CInitSpecsPThreadIntro.

  Context `{real_params_ops : RealParamsOps}.

  Notation DATA := (PTHREADINTRO.AbData (PgSize:= PgSize) (num_proc:= num_proc) (kern_high:= kern_high) (kern_low := kern_low) (maxpage:= maxpage)).

  Context {PTHREADINTRO_mem} 
              `{Hlmmh: !LayerMemoryModel DATA PTHREADINTRO_mem}.

  Instance pthread_intro_layer: LayerDefinition DATA PTHREADINTRO.primOp PTHREADINTRO_mem :=
        PTHREADINTRO.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (HPS4:= HPS4) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_ptb:= real_ptb) (Hnpc:= Hnpc) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC).

  (** thread_init *)

  Definition real_tcb: TCBPool -> TCBPool :=
    init_zmap num_proc (TCBValid DEAD num_proc num_proc).

  Lemma real_TCB_valid: forall tcb, TCBCorrect_range (real_tcb tcb) 0 num_proc.
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
  Lemma real_TCB_init: forall tcb, TCBInit (real_tcb tcb) 0 num_proc.
  Proof.
    unfold TCBInit.
    intros.
    unfold real_tcb.
    rewrite init_zmap_inside by assumption.
    reflexivity.
  Qed.

  Definition thread_init_madt (m: PTHREADINTRO_mem) := PTHREADINTRO.ADT (Mem.get_abstract_data m).

  Definition thread_init_mk_rdata (m: PTHREADINTRO_mem) (index: Z) :=
    let adt := (thread_init_madt m) in
      PTHREADINTRO.mkRData
        (PTHREADINTRO.HP adt)
        (PTHREADINTRO.AT adt)
        (PTHREADINTRO.nps adt)
        (PTHREADINTRO.ti adt)
        (PTHREADINTRO.PT adt)
        (PTHREADINTRO.ptpool adt)
        (PTHREADINTRO.pb adt)
        (PTHREADINTRO.kctxt adt)
        (init_zmap (index + 1) (TCBValid DEAD num_proc num_proc) (PTHREADINTRO.tcb adt))
        (PTHREADINTRO.pe adt)
        (PTHREADINTRO.ikern adt)
        (PTHREADINTRO.ipt adt)
        true.
    
  Lemma thread_init_mk_rinv  (m: PTHREADINTRO_mem) (index: Z):
    PTHREADINTRO.RInv  (kern_low:= kern_low) (kern_high:= kern_high) (maxpage:= maxpage) (num_proc:= num_proc) (PgSize:= PgSize) (thread_init_mk_rdata m index).
  Proof.
    unfold thread_init_mk_rdata.
    generalize (PTHREADINTRO.INV (Mem.get_abstract_data m)).
    intro HRINV.
    inv HRINV.
    unfold thread_init_madt.
    constructor; simpl; auto.
    intro contra; discriminate contra.
  Qed.
    
  Lemma thread_init_ABD_EX (m: PTHREADINTRO_mem) (index: Z):
    {abd | (PTHREADINTRO.ADT (kern_low:= kern_low) (kern_high:= kern_high) (maxpage:= maxpage) (num_proc:= num_proc) (PgSize:= PgSize)abd) = (thread_init_mk_rdata m index)}. 
  Proof.
    unfold thread_init_mk_rdata.
    exists (PTHREADINTRO.mkAbData (thread_init_mk_rdata m index) (thread_init_mk_rinv m index)).
    simpl.
    trivial.
  Qed.

  Definition thread_init_mk_abdata (m: PTHREADINTRO_mem) (index: Z) := match (thread_init_ABD_EX m index) with
    | exist a _ => a
  end. 

End CInitSpecsPThreadIntro.


Section CInitSpecsPQueueIntro.

  Context `{real_params_ops : RealParamsOps}.

  Notation DATA := (PQUEUEINTRO.AbData (PgSize:= PgSize) (num_proc:= num_proc) (kern_high:= kern_high) (kern_low := kern_low) (maxpage:= maxpage)).

  Context {PQUEUEINTRO_mem} 
              `{Hlmmh: !LayerMemoryModel DATA PQUEUEINTRO_mem}.

  Instance pqueue_intro_layer: LayerDefinition DATA PQUEUEINTRO.primOp PQUEUEINTRO_mem :=
        PQUEUEINTRO.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (HPS4:= HPS4) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_ptb:= real_ptb) (Hnpc:= Hnpc) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) (num_chan:= num_chan) (real_tcb:= real_tcb).

  (** tdqueue_init *)

  Fixpoint Calculate_tdq (i: nat) (tdq: TDQueuePool) : TDQueuePool :=
    match i with 
      | O => ZMap.set 0 (TDQValid num_proc num_proc) tdq
      | S k => ZMap.set (Z.of_nat (S k)) (TDQValid num_proc num_proc) (Calculate_tdq k tdq)
    end.

  Definition real_tdq: TDQueuePool -> TDQueuePool :=
    init_zmap (num_chan + 1) (TDQValid num_proc num_proc).

  (* FIXME: inconsistent naming *)
  Lemma real_tdq_valid: forall tdq, TDQInit (real_tdq tdq) 0 num_chan num_proc.
  Proof.
    unfold TDQInit.
    intros.
    unfold real_tdq.
    rewrite init_zmap_inside by omega.
    reflexivity.
  Qed.

  Definition tdqueue_init_madt (m: PQUEUEINTRO_mem) := PQUEUEINTRO.ADT (Mem.get_abstract_data m).

  Definition tdqueue_init_mk_rdata (m: PQUEUEINTRO_mem) (index: Z) := let adt := (tdqueue_init_madt m) in (PQUEUEINTRO.mkRData (PQUEUEINTRO.HP adt) (PQUEUEINTRO.AT adt) (PQUEUEINTRO.nps adt) (PQUEUEINTRO.ti adt) (PQUEUEINTRO.PT adt) (PQUEUEINTRO.ptpool adt) (PQUEUEINTRO.pb adt) (PQUEUEINTRO.kctxt adt) (PQUEUEINTRO.tcb adt) (Calculate_tdq (Z.to_nat index) (PQUEUEINTRO.tdq adt)) (PQUEUEINTRO.pe adt) (PQUEUEINTRO.ikern adt) (PQUEUEINTRO.ipt adt) true).
    
  Lemma tdqueue_init_mk_rinv  (m: PQUEUEINTRO_mem) (index: Z):
    PQUEUEINTRO.RInv  (kern_low:= kern_low) (kern_high:= kern_high) (maxpage:= maxpage) (num_proc:= num_proc) (PgSize:= PgSize) (tdqueue_init_mk_rdata m index).
  Proof.
    unfold tdqueue_init_mk_rdata.
    generalize (PQUEUEINTRO.INV (Mem.get_abstract_data m)).
    intro HRINV.
    inv HRINV.
    unfold tdqueue_init_madt.
    constructor; simpl; auto.
    intro contra; discriminate contra.
  Qed.
    
  Lemma tdqueue_init_ABD_EX (m: PQUEUEINTRO_mem) (index: Z):
    {abd | (PQUEUEINTRO.ADT (kern_low:= kern_low) (kern_high:= kern_high) (maxpage:= maxpage) (num_proc:= num_proc) (PgSize:= PgSize)abd) = (tdqueue_init_mk_rdata m index)}. 
  Proof.
    unfold tdqueue_init_mk_rdata.
    exists (PQUEUEINTRO.mkAbData (tdqueue_init_mk_rdata m index) (tdqueue_init_mk_rinv m index)).
    simpl.
    trivial.
  Qed.

  Definition tdqueue_init_mk_abdata (m: PQUEUEINTRO_mem) (index: Z) := match (tdqueue_init_ABD_EX m index) with
    | exist a _ => a
  end. 

End CInitSpecsPQueueIntro.


Section CInitSpecsPIPCIntro.

  Context `{real_params_ops : RealParamsOps}.

  Notation DATA := (PIPCINTRO.AbData (PgSize:= PgSize) (num_proc:= num_proc) (kern_high:= kern_high) (kern_low := kern_low) (maxpage:= maxpage) (num_chan:= num_chan)).

  Local Instance LdataOp:AbstractDataOps DATA:= (PIPCINTRO.abstract_data (Hnpc:= Hnpc)).

  Context {PIPCINTRO_mem} 
              `{Hlmmh: !LayerMemoryModel DATA PIPCINTRO_mem}.

  Instance pipc_intro_layer: LayerDefinition DATA PIPCINTRO.primOp PIPCINTRO_mem :=
        PIPCINTRO.layer_def (maxpage := maxpage) (real_nps:= real_nps) (real_AT:= real_AT) (HPS4:= HPS4) (Hlow:= Hlow) (Hhigh:= Hhigh) (real_ptp:= real_ptp) (real_pt:= real_pt) (real_ptb:= real_ptb) (Hnpc:= Hnpc) (real_free_pt:= real_free_pt) (STACK_LOC:= STACK_LOC) (num_chan:= num_chan) (real_abtcb:= real_abtcb) (real_abq:= real_abq) (Hnchan:= Hnchan).

  (** proc_init *)

  Definition real_chpool: ChanPool -> ChanPool :=
    init_zmap num_chan (ChanValid Int.zero Int.zero).

  Lemma real_chpool_valid: forall chpool, ChanPool_Init (real_chpool chpool) 0 num_chan.
  Proof.
    generalize max_unsigned_val; intro muval.
    unfold ChanPool_Init.
    unfold Channel_Init.
    intros.
    unfold real_chpool.
    rewrite init_zmap_inside by omega.
    reflexivity.
  Qed.

  Definition proc_init_madt (m: PIPCINTRO_mem) := PIPCINTRO.ADT (Mem.get_abstract_data m).

  Definition proc_init_mk_rdata (m: PIPCINTRO_mem) (index: Z) :=
    let adt := (proc_init_madt m) in
      PIPCINTRO.mkRData
        (PIPCINTRO.HP adt)
        (PIPCINTRO.AT adt)
        (PIPCINTRO.nps adt)
        (PIPCINTRO.ti adt)
        (PIPCINTRO.PT adt)
        (PIPCINTRO.ptpool adt)
        (PIPCINTRO.pb adt)
        (PIPCINTRO.kctxt adt)
        (PIPCINTRO.abtcb adt)
        (PIPCINTRO.abq adt)
        (PIPCINTRO.cid adt)
        (init_zmap (index + 1) (ChanValid Int.zero Int.zero) (PIPCINTRO.chpool adt))
        (PIPCINTRO.pe adt)
        (PIPCINTRO.ikern adt)
        (PIPCINTRO.ipt adt)
        true.

  Lemma proc_init_mk_rinv  (m: PIPCINTRO_mem) (index: Z):
    PIPCINTRO.RInv  (kern_low:= kern_low) (kern_high:= kern_high) (maxpage:= maxpage) (num_proc:= num_proc) (PgSize:= PgSize) (num_chan:= num_chan) (proc_init_mk_rdata m index).
  Proof.
    unfold proc_init_mk_rdata.
    generalize (PIPCINTRO.INV (Mem.get_abstract_data m)).
    intro HRINV.
    inv HRINV.
    unfold proc_init_madt.
    constructor; simpl; auto.
    intro contra; discriminate contra.
  Qed.

  Lemma proc_init_ABD_EX (m: PIPCINTRO_mem) (index: Z):
    {abd | (PIPCINTRO.ADT (kern_low:= kern_low) (kern_high:= kern_high) (maxpage:= maxpage) (num_proc:= num_proc) (PgSize:= PgSize) (num_chan:= num_chan) abd) = (proc_init_mk_rdata m index)}. 
  Proof.
    unfold proc_init_mk_rdata.
    exists (PIPCINTRO.mkAbData (proc_init_mk_rdata m index) (proc_init_mk_rinv m index)).
    simpl.
    trivial.
  Qed.

  Definition proc_init_mk_abdata (m: PIPCINTRO_mem) (index: Z) := match (proc_init_ABD_EX m index) with
    | exist a _ => a
  end. 

End CInitSpecsPIPCIntro.


