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
(*           Layers of Process Management                              *)
(*                                                                     *)
(*          Ronghui Gu <ronghui.gu@yale.edu>                           *)
(*                                                                     *)
(*          Yale Flint Group                                           *)
(*                                                                     *)
(* *********************************************************************)

(** This file provide some [data types] that will be used in the layer definitions and refinement proofs in PM*)
Require Import Coq.ZArith.BinInt.  
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import AsmExtra.
Require Import AST.
Require Import DataType.
Require Import LayerDefinition.


Notation U_EDI := 0.
Notation U_ESI := 1.
Notation U_EBP := 2.
Notation U_OESP := 3.
Notation U_EBX := 4.
Notation U_EDX := 5.
Notation U_ECX := 6.
Notation U_EAX := 7.
Notation U_ES := 8.
Notation U_DS := 9.
Notation U_TRAPNO := 10.
Notation U_ERR := 11.
Notation U_EIP := 12.
Notation U_CS := 13.
Notation U_EFLAGS := 14.
Notation U_ESP := 15.
Notation U_SS := 16.

Notation UCTXT_SIZE := 17.

Notation CPU_GDT_UDATA := (Vint (Int.repr 35)).
Notation CPU_GDT_UCODE := (Vint (Int.repr 27)).
Notation FL_IF := (Vint (Int.repr 512)).

Section ProcDataType.
  
  (** * Data types for pm *)
  Definition BitMap := PTBitMap.
  Definition KContext := regset.
  Definition KContextPool := ZMap.t KContext.

  Lemma register_type_load:
    forall (rs: regset)  r v f,
      Val.has_type (rs r) Tint
      -> val_inject f (Val.load_result Mint32 (rs r)) v
      -> val_inject f (rs r) v.
  Proof.
    intros.
    unfold Val.has_type in *.
    destruct (rs r); inv H; inv H0; try econstructor; eauto.
  Qed.
  
  Definition PregtoZ (r: preg) : option Z :=
    match r with 
      | ESP => Some 0
      | EDI => Some 1
      | ESI => Some 2
      | EBX => Some 3
      | EBP => Some 4
      | RA => Some 5
      | _ => None
    end.

  Definition ZtoPreg (i: Z) : option preg :=
    if zeq i 0 then
      Some (IR ESP)
    else 
      if zeq i 1 then
        Some (IR EDI)
      else 
        if zeq i 2 then
          Some (IR ESI)
        else 
          if zeq i 3 then
            Some (IR EBX) 
          else 
            if zeq i 4 then
              Some (IR EBP)
            else 
              if zeq i 5 then
                Some RA
              else None.
  
  Definition kctxt_inj (f:meminj) (range:Z) (kctxtp kctxtp': KContextPool) :=
    forall i n r,
      0<= n < range
      -> ZtoPreg i = Some r
      -> val_inject f (Pregmap.get r (ZMap.get n kctxtp)) (Pregmap.get r (ZMap.get n kctxtp')).
  
  Lemma PregToZ_correct:
    forall r i, PregtoZ r = Some i -> ZtoPreg i = Some r.
  Proof.      
    intros.
    induction r; inv H; auto.
    induction i0; inv H1; auto.
  Qed.

  Lemma ZtoPreg_correct:
    forall r i, ZtoPreg i = Some r -> PregtoZ r = Some i.
  Proof.
    intros.
    unfold ZtoPreg in H.
    destruct (zeq i 0).
    inv H; auto.
    destruct (zeq i 1).
    inv H; auto.
    destruct (zeq i 2).
    inv H; auto.
    destruct (zeq i 3).
    inv H; auto.
    destruct (zeq i 4).
    inv H; auto.
    destruct (zeq i 5).
    inv H; auto.
    inv H.
  Qed.

  Lemma ZtoPreg_range:
    forall n r, 
      ZtoPreg n = Some r -> 0<= n <= 5.
  Proof.
    unfold ZtoPreg.
    intros.
    destruct (zeq n 0). omega.
    destruct (zeq n 1). omega.
    destruct (zeq n 2). omega.
    destruct (zeq n 3). omega.
    destruct (zeq n 4). omega.
    destruct (zeq n 5). omega.    
    inv H.
  Qed.

  Lemma ZtoPreg_range_correct:
    forall n, 
      0<= n <= 5 -> exists r, ZtoPreg n = Some r.
  Proof.
    unfold ZtoPreg.
    intros.
    destruct (zeq n 0). eauto.
    destruct (zeq n 1). eauto.
    destruct (zeq n 2). eauto.
    destruct (zeq n 3). eauto.
    destruct (zeq n 4). eauto.
    destruct (zeq n 5). eauto.    
    omega.
  Qed.

  Lemma ZtoPreg_type:
    forall v r,
      ZtoPreg v = Some r -> Tint = typ_of_preg r.
  Proof.
    intros.
    unfold ZtoPreg in *.
    destruct (zeq v 0); [inv H; trivial |].
    destruct (zeq v 1); [inv H; trivial |].
    destruct (zeq v 2); [inv H; trivial |].
    destruct (zeq v 3); [inv H; trivial |].
    destruct (zeq v 4); [inv H; trivial |].
    destruct (zeq v 5); [inv H; trivial |].
    inv H.
  Qed.

  Definition is_valid_context_reg (v: val) :=
    match v with
      | Vfloat _ => false
      | _ => true
    end.
  
  Inductive ThreadState :=
  | READY
  | RUN
  | SLEEP
  | DEAD.

  Remark ThreadState_dec: forall ts ts': ThreadState, {ts = ts'} + {~ ts = ts'}.
  Proof.
    intros.
    decide equality.
  Qed.

  Definition ZtoThreadState (i:Z) :=
    if zeq i 0 then
      Some READY
    else 
      if zeq i 1 then
        Some RUN
      else 
        if zeq i 2 then
          Some SLEEP
        else 
          if zeq i 3 then
            Some DEAD
          else None.
  
  Definition ThreadStatetoZ (tds: ThreadState) :=
    match tds with
      | READY => 0
      | RUN => 1
      | SLEEP => 2
      | DEAP => 3
    end.

  Lemma ZtoThreadState_correct: 
    forall i tds, ZtoThreadState i = Some tds -> ThreadStatetoZ tds = i.
  Proof.  
    intros.
    unfold ZtoThreadState, ThreadStatetoZ in *.
    destruct (zeq i 0).
    inv H; trivial.
    destruct (zeq i 1).
    inv H; trivial.
    destruct (zeq i 2).
    inv H; trivial.
    destruct (zeq i 3).
    inv H; trivial.
    inv H.
  Qed.

  Lemma ThreadStatetoZ_correct: 
    forall tds, ZtoThreadState (ThreadStatetoZ tds) = Some tds.
  Proof.  
    intros.
    destruct tds; simpl; trivial.
  Qed.

  Lemma ZtoThreadState_range:
    forall i tds, ZtoThreadState i = Some tds -> 0 <= i <= 3.
  Proof.
    intros.
    unfold ZtoThreadState in *.
    destruct (zeq i 0).
    omega.
    destruct (zeq i 1).
    omega.
    destruct (zeq i 2).
    omega.
    destruct (zeq i 3).
    omega.
    inv H.
  Qed.

  Lemma ZtoThreadState_range_correct:
    forall i, 0<= i <= 3 -> exists tds, ZtoThreadState i = Some tds. 
  Proof.
    intros.
    unfold ZtoThreadState in *.
    destruct (zeq i 0).
    eauto.
    destruct (zeq i 1).
    eauto.
    destruct (zeq i 2).
    eauto.
    destruct (zeq i 3).
    eauto.
    omega.
  Qed.

  Inductive TCB :=
  | TCBUndef
  | TCBValid (tds: ThreadState) (prev: Z) (next: Z).

  Remark TCB_dec: forall tcb tcb': TCB, {tcb = tcb'} + {~ tcb = tcb'}.
  Proof.
    intros.
    decide equality.
    apply Z_eq_dec.
    apply Z_eq_dec.
    apply ThreadState_dec.
  Qed.
  
  Definition TCBPool := ZMap.t TCB.

  Definition TCBCorrect (tcb: TCB) (high:Z) :=
    exists s prev next, tcb = TCBValid s prev next /\ 0<= prev <= high /\ 0<= next <= high.
  
  Remark TCBCorrect_dec:
    forall tcb high, {TCBCorrect tcb high} + {~TCBCorrect tcb high}.
  Proof.
    intros.
    unfold TCBCorrect.
    destruct tcb.
    right.
    red; intros.
    destruct H as [s[p[n [HF _]]]].
    inv HF.
    destruct (zle 0 prev).
    destruct (zle prev high).
    destruct (zle 0 next).
    destruct (zle next high).
    left.
    exists tds, prev, next.
    split; eauto.
    right.
    red; intros [s[p[n[HF[Hr1 hr2]]]]].
    inv HF.
    omega.

    right.
    red; intros [s[p[n[HF[Hr1 hr2]]]]].
    inv HF.
    omega.

    right.
    red; intros [s[p[n[HF[Hr1 hr2]]]]].
    inv HF.
    omega.

    right.
    red; intros [s[p[n[HF[Hr1 hr2]]]]].
    inv HF.
    omega.
  Qed.

  Definition TCBCorrect_range' (tcb: TCBPool) (lo high num_proc: Z) :=
    forall i , lo <= i < high -> TCBCorrect (ZMap.get i tcb) num_proc. 
    
  Remark TCBCorrect_range_dec':
    forall tcb lo high num_proc, {TCBCorrect_range' tcb lo high num_proc} + {~TCBCorrect_range' tcb lo high num_proc}.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {TCBCorrect_range' tcb lo (lo+n) num_proc} + {~TCBCorrect_range' tcb lo (lo+n) num_proc}).
    apply natlike_rec2.
    left.
    red.
    intros.
    omegaContradiction.
    intros.
    destruct H0.
    
    destruct (TCBCorrect_dec (ZMap.get (lo+z) tcb) num_proc).
    left.
    unfold TCBCorrect_range' in *.
    intros.
    destruct (zeq i (lo + z)).
    subst i; trivial.
    apply t.
    omega.

    right; red; intro. 
    unfold TCBCorrect_range' in H0.
    elim n.
    apply H0.
    omega.

    right; red; intro. 
    elim n.
    unfold TCBCorrect_range' in *.
    intros.
    apply H0.
    omega.
    
    destruct (zlt lo high).
    replace high with (lo + (high - lo)) by omega. apply HP. omega.
    left; red; intros. omegaContradiction. 
  Qed.
  
  Definition TCBCorrect_range (tcb: TCBPool) (lo high: Z) :=
    forall i , lo <= i < high -> TCBCorrect (ZMap.get i tcb) high. 
    
  Remark TCBCorrect_range_dec:
    forall tcb lo high, {TCBCorrect_range tcb lo high} + {~TCBCorrect_range tcb lo high}.
  Proof.
    intros.
    unfold TCBCorrect_range.
    specialize (TCBCorrect_range_dec' tcb lo high high).
    unfold TCBCorrect_range'.
    trivial.
  Qed.

  Definition TCBInit' (tcb: TCBPool) (lo high num_proc: Z) :=
    forall i , lo <= i < high -> ZMap.get i tcb = TCBValid DEAD num_proc num_proc. 
    
  Remark TCBInit_dec':
    forall tcb lo high num_proc, {TCBInit' tcb lo high num_proc} + {~TCBInit' tcb lo high num_proc}.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {TCBInit' tcb lo (lo+n) num_proc} + {~TCBInit' tcb lo (lo+n) num_proc}).
    apply natlike_rec2.
    left.
    red.
    intros.
    omegaContradiction.
    intros.
    destruct H0.
    
    destruct (TCB_dec (ZMap.get (lo+z) tcb) (TCBValid DEAD num_proc num_proc)).
    left.
    unfold TCBInit' in *.
    intros.
    destruct (zeq i (lo + z)).
    subst i; trivial.
    apply t.
    omega.

    right; red; intro. 
    unfold TCBInit' in H0.
    elim n.
    apply H0.
    omega.

    right; red; intro. 
    elim n.
    unfold TCBInit' in *.
    intros.
    apply H0.
    omega.
    
    destruct (zlt lo high).
    replace high with (lo + (high - lo)) by omega. apply HP. omega.
    left; red; intros. omegaContradiction. 
  Qed.

  Definition TCBInit (tcb: TCBPool) (lo high: Z) :=
    forall i , lo <= i < high -> ZMap.get i tcb = TCBValid DEAD high high. 
    
  Remark TCBInit_dec:
    forall tcb lo high, {TCBInit tcb lo high} + {~TCBInit tcb lo high}.
  Proof.
    intros.
    specialize (TCBInit_dec' tcb lo high high).
    unfold TCBInit', TCBInit.
    trivial.
  Qed.

  Inductive TDQueue :=
  | TDQUndef
  | TDQValid (head tail: Z).

  Definition TDQueuePool := ZMap.t TDQueue.

  Remark TDQ_dec: forall tdq tdq': TDQueue, {tdq = tdq'} + {~ tdq = tdq'}.
  Proof.
    intros.
    decide equality.
    apply Z_eq_dec.
    apply Z_eq_dec.
  Qed.

  Definition TDQCorrect (tdq: TDQueue) (high:Z) :=
    exists head tail, tdq = TDQValid head tail /\ 0<= head <= high /\ 0<= tail <= high.
  
  Remark TDQCorrect_dec:
    forall tdq high, {TDQCorrect tdq high} + {~TDQCorrect tdq high}.
  Proof.
    intros.
    unfold TDQCorrect.
    destruct tdq.
    right.
    red; intros.
    destruct H as [p[n [HF _]]].
    inv HF.
    destruct (zle 0 head).
    destruct (zle head high).
    destruct (zle 0 tail).
    destruct (zle tail high).
    left.
    exists head, tail.
    split; eauto.
    right.
    red; intros [p[n[HF[Hr1 hr2]]]].
    inv HF.
    omega.
    
    right.
    red; intros [p[n[HF[Hr1 hr2]]]].
    inv HF.
    omega.

    right.
    red; intros [p[n[HF[Hr1 hr2]]]].
    inv HF.
    omega.

    right.
    red; intros [p[n[HF[Hr1 hr2]]]].
    inv HF.
    omega.
  Qed.

  Definition TDQCorrect_range (tdq: TDQueuePool) (lo high num_proc: Z) :=
    forall i , lo <= i <= high -> TDQCorrect (ZMap.get i tdq) num_proc. 
    
  Remark TDQCorrect_range_dec:
    forall tdq lo high num_proc, {TDQCorrect_range tdq lo high num_proc} + {~TDQCorrect_range tdq lo high num_proc}.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {TDQCorrect_range tdq lo (lo+n) num_proc} + {~TDQCorrect_range tdq lo (lo+n) num_proc}).
    apply natlike_rec2.
    destruct (TDQCorrect_dec (ZMap.get lo tdq) num_proc).
    left.
    unfold TDQCorrect_range.
    intros.
    replace i with lo by omega.
    trivial.
    right.
    red; intros.
    elim n.
    unfold TDQCorrect_range in *.
    apply H.
    omega.
    
    intros.
    destruct H0.
    destruct (TDQCorrect_dec (ZMap.get (lo + (Z.succ z)) tdq) num_proc).
    left.
    unfold TDQCorrect_range in *.
    intros.
    destruct (zeq i (lo + (Z.succ z))).
    subst i; trivial.
    apply t.
    omega.

    right; red; intro. 
    unfold TDQCorrect_range in H0.
    elim n.
    apply H0.
    omega.

    right; red; intro. 
    elim n.
    unfold TDQCorrect_range in *.
    intros.
    apply H0.
    omega.
    
    destruct (zle lo high).
    replace high with (lo + (high - lo)) by omega. apply HP. omega.
    left; red; intros. omegaContradiction. 
  Qed.
  
  Definition TDQInit (tdq: TDQueuePool) (lo high num_proc: Z) :=
    forall i , lo <= i <= high -> ZMap.get i tdq = TDQValid num_proc num_proc. 
    
  Remark TDQInit_dec:
    forall tdq lo high num_proc, {TDQInit tdq lo high num_proc} + {~TDQInit tdq lo high num_proc}.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {TDQInit tdq lo (lo+n) num_proc} + {~TDQInit tdq lo (lo+n) num_proc}).
    apply natlike_rec2.
    destruct (TDQ_dec (ZMap.get lo tdq) (TDQValid num_proc num_proc)).
    left.
    unfold TDQInit.
    intros.
    replace i with lo by omega.
    trivial.
    right.
    red; intros.
    elim n.
    unfold TDQInit in *.
    apply H.
    omega.

    intros.
    destruct H0.    
    destruct (TDQ_dec (ZMap.get (lo+ (Z.succ z)) tdq) (TDQValid num_proc num_proc)).
    left.
    unfold TDQInit in *.
    intros.
    destruct (zeq i (lo + (Z.succ z))).
    subst i; trivial.
    apply t.
    omega.

    right; red; intro. 
    unfold TDQInit in H0.
    elim n.
    apply H0.
    omega.

    right; red; intro. 
    elim n.
    unfold TDQInit in *.
    intros.
    apply H0.
    omega.
    
    destruct (zle lo high).
    replace high with (lo + (high - lo)) by omega. apply HP. omega.
    left; red; intros. omegaContradiction. 
  Qed.


  Inductive AbQueue :=
  | AbQUndef
  | AbQValid (l: list Z).

  Definition AbQueuePool := ZMap.t AbQueue.
  
  (* [inQ] below is the index of the queue the process is in:

      -1             no queue
      0..num_proc-1  the queue associated with thread n
      num_proc       the ready queue
   *)
  Inductive AbTCB :=
  | AbTCBUndef
  | AbTCBValid (tds: ThreadState) (inQ: Z).

  Definition AbTCBPool := ZMap.t AbTCB.

  Definition AbTCBCorrect (tcb: AbTCB) (num_chan:Z):=
    exists s b, tcb = AbTCBValid s b /\ (-1 <= b <= num_chan).
  
  Definition AbTCBStrong (tcb: AbTCB) (num_chan:Z):=
    exists s b, tcb = AbTCBValid s b /\ ((s = RUN \/ s = DEAD) -> b = -1) 
                /\ (s = SLEEP -> 0 <= b < num_chan)
                /\ (s = READY -> b = num_chan).

  Definition AbQCorrect (tdq: AbQueue) (high:Z) :=
    exists l, tdq = AbQValid l /\ (forall x, In x l -> 0<= x < high).

  Remark AbTCB_dec: forall tcb tcb': AbTCB, {tcb = tcb'} + {~ tcb = tcb'}.
  Proof.
    intros.
    decide equality.
    apply zeq.
    apply ThreadState_dec.
  Qed.

  Definition AbTCBInit (tcb: AbTCBPool) (lo high: Z) :=
    forall i , lo <= i < high -> ZMap.get i tcb = AbTCBValid DEAD (-1). 
    
  Remark AbTCBInit_dec:
    forall tcb lo high, {AbTCBInit tcb lo high} + {~AbTCBInit tcb lo high}.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {AbTCBInit tcb lo (lo+n)} + {~AbTCBInit tcb lo (lo+n)}).
    apply natlike_rec2.
    left.
    red.
    intros.
    omegaContradiction.
    intros.
    destruct H0.
    
    destruct (AbTCB_dec (ZMap.get (lo+z) tcb) (AbTCBValid DEAD (-1))).
    left.
    unfold AbTCBInit in *.
    intros.
    destruct (zeq i (lo + z)).
    subst i; trivial.
    apply a.
    omega.

    right; red; intro. 
    unfold AbTCBInit in H0.
    elim n.
    apply H0.
    omega.

    right; red; intro. 
    elim n.
    unfold AbTCBInit in *.
    intros.
    apply H0.
    omega.
    
    destruct (zlt lo high).
    replace high with (lo + (high - lo)) by omega. apply HP. omega.
    left; red; intros. omegaContradiction. 

  Qed.

  Remark AbQ_dec: forall tdq tdq': AbQueue, {tdq = tdq'} + {~ tdq = tdq'}.
  Proof.
    intros.
    decide equality.
    apply list_eq_dec.
    apply zeq.
  Qed.

  Definition AbQInit (tdq: AbQueuePool) (lo high: Z) :=
    forall i , lo <= i <= high -> ZMap.get i tdq = AbQValid nil. 
    
  Remark AbQInit_dec:
    forall tdq lo high, {AbQInit tdq lo high} + {~AbQInit tdq lo high}.
  Proof.
    intros.
    assert(HP: forall n, 0 <= n
                         -> {AbQInit tdq lo (lo+n)} + {~AbQInit tdq lo (lo+n)}).
    apply natlike_rec2.
    destruct (AbQ_dec (ZMap.get lo tdq) (AbQValid nil)).
    left.
    unfold AbQInit.
    intros.
    replace i with lo by omega.
    trivial.
    right.
    red; intros.
    elim n.
    unfold AbQInit in *.
    apply H.
    omega.

    intros.
    destruct H0.    
    destruct (AbQ_dec (ZMap.get (lo+ (Z.succ z)) tdq) (AbQValid nil)).
    left.
    unfold AbQInit in *.
    intros.
    destruct (zeq i (lo + (Z.succ z))).
    subst i; trivial.
    apply a.
    omega.

    right; red; intro. 
    unfold AbQInit in H0.
    elim n.
    apply H0.
    omega.

    right; red; intro. 
    elim n.
    unfold AbQInit in *.
    intros.
    apply H0.
    omega.
    
    destruct (zle lo high).
    replace high with (lo + (high - lo)) by omega. apply HP. omega.
    left; red; intros. omegaContradiction. 
  Qed.

  Section List_Lemma.

    Lemma removelast_incl:
      forall {A:Type} (l: list A), incl (removelast l) l.
    Proof.
      induction 0.
      simpl.
      apply incl_refl.
      
      simpl.
      destruct l.
      apply incl_tl. 
      apply incl_refl.
      apply incl_cons.
      simpl; eauto.
      apply incl_tl.
      trivial.
    Qed.

    Lemma remove_incl:
      forall (l: list Z) x, incl (remove zeq x l) l.
    Proof.
      intros.
      induction l.
      simpl.
      apply incl_refl.
      
      simpl.
      destruct (zeq x a).
      apply incl_tl. 
      trivial.
      apply incl_cons.
      simpl; eauto.
      apply incl_tl.
      trivial.
    Qed.

    Lemma remove_outside:
      forall (l: list Z) x y, y <> x -> In y l -> In y (remove zeq x l).
    Proof.
      intros.
      induction l.
      inv H0.
      
      simpl.
      destruct (zeq x a).
      inv H0.
      elim H; trivial.
      auto.

      inv H0.
      simpl.
      left; trivial.
      simpl.
      right.
      auto.
    Qed.

    Lemma remove_count_outside:
      forall (l: list Z) x y, y <> x -> count_occ zeq (remove zeq x l) y = count_occ zeq l y.
    Proof.
      intros.
      induction l.
      simpl.
      trivial.
      
      simpl.
      destruct (zeq x a).
      destruct (zeq a y).
      omega.
      trivial.

      destruct (zeq a y).
      subst.
      rewrite count_occ_cons_eq; trivial.
      rewrite IHl.
      trivial.
      rewrite count_occ_cons_neq; auto.

    Qed.

    Lemma last_correct:
      forall (l: list Z) x, x <> (last l x) -> In (last l x) l.
    Proof.
      intros.
      induction l.
      simpl in H.
      elim H.
      trivial.
      
      simpl in *.
      destruct l.
      left; trivial.
      right; auto.
    Qed.

  End List_Lemma.

  
  Definition UContext := ZMap.t val.
  
  Definition UContextPool := ZMap.t UContext.

(*
  typedef
    struct pushregs {
      uint32_t edi;
      uint32_t esi;
      uint32_t ebp;
      uint32_t oesp;		/* Useless */
      uint32_t ebx;
      uint32_t edx;
      uint32_t ecx;
      uint32_t eax;
    } pushregs;

    typedef
      struct tf_t {
	/* registers and other info we push manually in trapasm.S */
	                                                          pushregs regs;
	uint16_t es;		uint16_t padding_es;
	uint16_t ds;		uint16_t padding_ds;
	uint32_t trapno;

	/* format from here on determined by x86 hardware architecture */
	uint32_t err;
	uintptr_t eip;
	uint16_t cs;		uint16_t padding_cs;
	uint32_t eflags;

	/* rest included only when crossing rings, e.g., user to kernel */
	uintptr_t esp;
        uint16_t ss;		uint16_t padding_ss;
      } tf_t;
*)

  Function is_UCTXT_ptr (ofs : Z): bool :=
    match ofs with
      | U_EDI => false
      | U_ESI => false
      | U_EBX => false
      | U_EDX => false
      | U_ECX => false
      | U_EAX => false
      | U_ES => false
      | U_DS => false
      | U_ERR => false
      | U_TRAPNO => false
      | U_CS => false
      | U_EFLAGS => false
      | U_ESP => false
      | U_SS => false
      | _ => true
    end.


  Lemma is_UCTXT_ptr_range:
    forall i, is_UCTXT_ptr i = false -> 0<= i < UCTXT_SIZE.
  Proof.
    intros.
    functional inversion H; omega.
  Qed.

  Function UCtxt_Reg (r: preg) : bool :=
    match r with
      | IR _ => true
      | RA => true
      | _ => false
    end.

   Inductive Channel :=
    | ChanUndef
    | ChanValid (isbusy content: int).

    Definition ChanPool := ZMap.t Channel.
    
    Definition Channel_Valid  (ch: Channel) := 
      exists ib ct, ch = ChanValid ib ct.

    Remark Channel_valid_dec:
      forall ch, {Channel_Valid ch } + {~ Channel_Valid ch}.
    Proof.
      intros.
      unfold Channel_Valid.
      destruct ch.
      right. red; intros.
      destruct H as [ib[ct HF]].
      inv HF.
      left.
      eauto.
    Qed.
    
    Definition ChanPool_Valid (chp: ChanPool) (lo high: Z) :=
      forall i , lo <= i < high -> Channel_Valid (ZMap.get i chp).

    Remark ChanPool_valid_dec:
      forall chp lo high, {ChanPool_Valid chp lo high} + {~ ChanPool_Valid chp lo high}.
    Proof.
      intros.
      assert(HP: forall n, 0 <= n
                           -> {ChanPool_Valid chp lo (lo+n)} + {~ ChanPool_Valid chp lo (lo+n)}).
      apply natlike_rec2.
      left.
      red.
      intros.
      omegaContradiction.
      intros.
      destruct H0.
      unfold ChanPool_Valid in *.
      destruct (Channel_valid_dec (ZMap.get (lo+z) chp)).
      left.
      intros.
      destruct (zeq i (lo + z)).
      congruence.
      apply c.
      omega.
      right; red; intro.
      elim n.
      apply H0.
      omega.
      right; red; intro.
      elim n.
      red; intros.
      apply H0.
      omega.

      destruct (zlt lo high).
      replace high with (lo + (high - lo)) by omega. apply HP. omega.
      left; red; intros. omegaContradiction.

    Qed. 

    Definition Channel_Init  (ch: Channel) := 
      ch = ChanValid Int.zero Int.zero.

    Remark Channel_Init_dec:
      forall ch, {Channel_Init ch } + {~ Channel_Init ch}.
    Proof.
      intros.
      unfold Channel_Valid.
      destruct ch.
      right. red; intros.
      inv H.
      unfold Channel_Init.
      destruct (Int.eq_dec isbusy Int.zero).
      destruct (Int.eq_dec content Int.zero).
      subst.
      left; trivial.
      right; red; intros.
      inv H.
      elim n; trivial.

      right; red; intros.
      inv H.
      elim n; trivial.

    Qed.
    
    Definition ChanPool_Init (chp: ChanPool) (lo high: Z) :=
      forall i , lo <= i < high -> Channel_Init (ZMap.get i chp).

    Remark ChanPool_Init_dec:
      forall chp lo high, {ChanPool_Init chp lo high} + {~ ChanPool_Init chp lo high}.
    Proof.
      intros.
      assert(HP: forall n, 0 <= n
                           -> {ChanPool_Init chp lo (lo+n)} + {~ ChanPool_Init chp lo (lo+n)}).
      apply natlike_rec2.
      left.
      red.
      intros.
      omegaContradiction.
      intros.
      destruct H0.
      unfold ChanPool_Init in *.
      destruct (Channel_Init_dec (ZMap.get (lo+z) chp)).
      left.
      intros.
      destruct (zeq i (lo + z)).
      congruence.
      apply c.
      omega.
      right; red; intro.
      elim n.
      apply H0.
      omega.
      right; red; intro.
      elim n.
      red; intros.
      apply H0.
      omega.

      destruct (zlt lo high).
      replace high with (lo + (high - lo)) by omega. apply HP. omega.
      left; red; intros. omegaContradiction.

    Qed. 

    Lemma ChanPool_Init_Correct:
      forall chp lo hi,
        ChanPool_Init lo hi chp -> ChanPool_Valid lo hi chp.
    Proof.
      unfold ChanPool_Init, ChanPool_Valid.
      unfold Channel_Init, Channel_Valid.
      eauto.

    Qed.
  
End ProcDataType.

Ltac inv_uctx_primitive HVV:=
  repeat match goal with
           | [ |- context[Pregmap.elt_eq ?a ?b]] 
             => destruct (Pregmap.elt_eq a b);
               [try (eapply HVV; eauto; try omega; try (apply PregToZ_correct; compute;trivial))|]
         end.

Ltac inv_proc := 
  repeat match goal with
           | [ |- context[ZMap.get ?a (ZMap.set ?b _ _ )]] 
             => destruct (zeq a b);
               [subst; repeat rewrite ZMap.gss; eauto
               | 
               match goal with
                 | [ H0: a <> b |- _] =>
                   repeat (rewrite (ZMap.gso _ _ H0)); auto
               end]
         end.


Ltac reg_destruct_simpl :=
  repeat match goal with
           | [ |- context[Pregmap.elt_eq ?a ?b]] 
             => destruct (Pregmap.elt_eq a b); trivial; eauto; try constructor
         end.