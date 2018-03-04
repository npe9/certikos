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

Section KCTXT_INJECT_NEUTRAL_INV.

  Lemma kctxt_inject_neutral_gss:
    forall kp n (rs: regset),
      kctxt_inject_neutral kp n ->
      (forall r,
         val_inject (Mem.flat_inj n) (rs r) (rs r)) ->
      wt_regset rs ->
      forall i,
        kctxt_inject_neutral
          (ZMap.set i
                    (Pregmap.init Vundef) # ESP <- (rs ESP) 
                    # EDI <- (rs EDI) # ESI <- (rs ESI)
                    # EBX <- (rs EBX) # EBP <- (rs EBP) 
                    # RA <- (rs RA) kp) n.
  Proof.
    intros. intros until 2.
    destruct (zeq ofs i); subst.
    - rewrite ZMap.gss.
      repeat (rewrite Pregmap_Simpl).
      erewrite ZtoPreg_type; eauto.
      inv_uctx_primitive H; split; subst; auto.
      constructor.
    - rewrite ZMap.gso; eauto.
  Qed.

  Section WITHMEM.

    Context `{Hstencil: Stencil}.
    Context `{Hmem: Mem.MemoryModel}.

    Local Open Scope Z_scope.

    Lemma kctxt_inject_neutral_gss_flatinj':
      forall i k kp n,
        kctxt_inject_neutral (ZMap.set i k kp) n ->
        forall b,
          Mem.flat_inj n b = Some (b, 0) ->
          forall ofs r,
            kctxt_inject_neutral
              (ZMap.set i k # r <- (Vptr b ofs) kp) n.
    Proof.
      intros. intros until 2.
      destruct (zeq ofs0 i); subst; simpl.
      + specialize (H _ H1 _ _ H2).
        rewrite ZMap.gss in *.
        rewrite Pregmap_Simpl.
        destruct (Pregmap.elt_eq r0 r); trivial.
        split. constructor.
        econstructor; eauto.
        rewrite Int.add_zero; trivial.
      + specialize (H _ H1 _ _ H2).
        rewrite ZMap.gso in *; eauto.
    Qed.

    Lemma kctxt_inject_neutral_gss_flatinj:
      forall kp n,
        kctxt_inject_neutral kp n ->
        forall b,
          Mem.flat_inj n b = Some (b, 0) ->
          forall i ofs r,
            kctxt_inject_neutral
              (ZMap.set i (ZMap.get i kp) # r <- (Vptr b ofs) kp) n.
    Proof.
      intros. intros until 2.
      destruct (zeq ofs0 i); subst; simpl.
      + rewrite ZMap.gss.
        specialize (H _ H1 _ _ H2).
        rewrite Pregmap_Simpl.
        destruct (Pregmap.elt_eq r0 r); trivial.
        split. constructor.
        econstructor; eauto.
        rewrite Int.add_zero; trivial.
      + rewrite ZMap.gso; eauto.
    Qed.

    Lemma kctxt_inject_neutral_gss_ptr:
      forall kp n,
        kctxt_inject_neutral kp n ->
        forall s b,
          (exists fun_id, find_symbol s fun_id = Some b) ->
          (genv_next s <= n)%positive ->
          forall i ofs r,
            kctxt_inject_neutral
              (ZMap.set i (ZMap.get i kp) # r <- (Vptr b ofs) kp) n.
    Proof.
      intros. 
      eapply kctxt_inject_neutral_gss_flatinj; eauto.
      destruct H0 as [fun_id HSy].
      eapply stencil_find_symbol_inject'; eauto.
      eapply flat_inj_inject_incr; assumption.
    Qed.

    Lemma kctxt_inject_neutral_gss_mem:
      forall s kp m (rs: regset),
        kctxt_inject_neutral kp (Mem.nextblock m) ->
        asm_invariant s rs m ->
        forall i,
          kctxt_inject_neutral
            (ZMap.set i
                      (Pregmap.init Vundef) # ESP <- (rs ESP) 
                      # EDI <- (rs EDI) # ESI <- (rs ESI)
                      # EBX <- (rs EBX) # EBP <- (rs EBP) 
                      # RA <- (rs RA) kp) (Mem.nextblock m).
    Proof.
      intros. inv H0. inv inv_inject_neutral.
      eapply kctxt_inject_neutral_gss; eauto.
    Qed.

  End WITHMEM.

End KCTXT_INJECT_NEUTRAL_INV.

Section TCB_INV.

  Local Open Scope Z_scope.

  Lemma TCBCorrect_range_gss:
    forall t,
      TCBCorrect_range t ->
      forall i,
        0 <= i < num_proc ->
        forall s' n' p',
          0 <= n' <= num_proc ->
          0 <= p' <= num_proc ->
          TCBCorrect_range
            (ZMap.set i (TCBValid s' p' n') t).
  Proof.
    unfold TCBCorrect_range; intros.
    destruct (zeq i i0); subst.
    - rewrite ZMap.gss.
      specialize (H _ H0). unfold TCBCorrect in *. eauto 6.
    - rewrite ZMap.gso; auto.
  Qed.      

  Lemma TCBCorrect_range_gss_64:
    forall t,
      TCBCorrect_range t ->
      forall i,
        0 <= i < num_proc ->
        forall s',
          TCBCorrect_range
            (ZMap.set i (TCBValid s' num_proc num_proc) t).
  Proof.
    intros. eapply TCBCorrect_range_gss; eauto; omega.
  Qed.      

  Lemma TCBCorrect_range_valid_prev:
    forall q,
      TCBCorrect_range q ->
      forall i s n p,
        ZMap.get i q = TCBValid s n p ->
        0 <= i < num_proc ->
        0 <= n <= num_proc.
  Proof.
    unfold TCBCorrect_range, TCBCorrect. intros.
    specialize (H _ H1). rewrite H0 in H.
    destruct H as (st & next & prev & He & Hr & Hr').
    inv He. assumption.
  Qed.      

  Lemma TCBCorrect_range_valid_next:
    forall q,
      TCBCorrect_range q ->
      forall i s n p,
        ZMap.get i q = TCBValid s n p ->
        0 <= i < num_proc ->
        0 <= p <= num_proc.
  Proof.
    unfold TCBCorrect_range, TCBCorrect. intros.
    specialize (H _ H1). rewrite H0 in H.
    destruct H as (st & next & prev & He & Hr & Hr').
    inv He. assumption.
  Qed.      

  Lemma TCBCorrect_range_gso:
    forall t,
      TCBCorrect_range t ->
      forall i,
        0 <= i < num_proc ->
        forall p n s,
          ZMap.get i t = TCBValid s p n ->
          forall s',
            TCBCorrect_range
              (ZMap.set i (TCBValid s' p n) t).
  Proof.
    intros. eapply TCBCorrect_range_gss; eauto.
    - eapply TCBCorrect_range_valid_next; eauto.
    - eapply TCBCorrect_range_valid_prev; eauto.
  Qed.      

  Lemma TCBCorrect_range_gss_prev:
    forall t,
      TCBCorrect_range t ->
      forall i,
        0 <= i < num_proc ->
        forall p n s,
          ZMap.get i t = TCBValid s p n ->
          forall s' p',
            0 <= p' <= num_proc ->
            TCBCorrect_range
              (ZMap.set i (TCBValid s' p' n) t).
  Proof.
    intros. eapply TCBCorrect_range_gss; eauto.
    eapply TCBCorrect_range_valid_next; eauto.
  Qed.      

  Lemma TCBCorrect_range_gss_next:
    forall t,
      TCBCorrect_range t ->
      forall i,
        0 <= i < num_proc ->
        forall p n s,
          ZMap.get i t = TCBValid s p n ->
          forall s' n',
            0 <= n' <= num_proc ->
            TCBCorrect_range
              (ZMap.set i (TCBValid s' p n') t).
  Proof.
    intros. eapply TCBCorrect_range_gss; eauto.
    eapply TCBCorrect_range_valid_prev; eauto.
  Qed.      

End TCB_INV.

Section TDQ_INV.

  Local Open Scope Z_scope.

  Lemma TDQCorrect_range_gss:
    forall q,
      TDQCorrect_range q ->
      forall i,
        0 <= i <= num_proc ->
        forall h t,
          0 <= h <= num_proc ->
          0 <= t <= num_proc ->
          TDQCorrect_range
            (ZMap.set i (TDQValid h t) q).
  Proof.
    unfold TDQCorrect_range. intros.
    destruct (zeq i i0); subst.
    - rewrite ZMap.gss. unfold TDQCorrect.
      esplit; esplit. split; trivial.
      split; assumption.
    - rewrite ZMap.gso; auto 2.
  Qed.      

  Lemma TDQCorrect_range_gss_64:
    forall q,
      TDQCorrect_range q ->
      forall i,
        0 <= i <= num_proc ->
        TDQCorrect_range
          (ZMap.set i (TDQValid num_proc num_proc) q).
  Proof.
    intros. eapply TDQCorrect_range_gss; eauto; omega.
  Qed.      

  Lemma TDQCorrect_range_valid_head:
    forall q,
      TDQCorrect_range q ->
      forall i h t,
        ZMap.get i q = TDQValid h t ->
        0 <= i <= num_proc ->
        0 <= h <= num_proc.
  Proof.
    unfold TDQCorrect_range, TDQCorrect. intros.
    specialize (H _ H1). rewrite H0 in H.
    destruct H as (head & tail & He & Hr & Hr').
    inv He. assumption.
  Qed.      

  Lemma TDQCorrect_range_valid_tail:
    forall q,
      TDQCorrect_range q ->
      forall i h t,
        ZMap.get i q = TDQValid h t ->
        0 <= i <= num_proc ->
        0 <= t <= num_proc.
  Proof.
    unfold TDQCorrect_range, TDQCorrect. intros.
    specialize (H _ H1). rewrite H0 in H.
    destruct H as (head & tail & He & Hr & Hr').
    inv He. assumption.
  Qed.      

  Lemma TDQCorrect_range_gss_tail:
    forall q,
      TDQCorrect_range q ->
      forall i h t,
        0 <= i <= num_proc ->
        ZMap.get i q = TDQValid h t ->
        forall t',
          0 <= t' <= num_proc ->
          TDQCorrect_range
            (ZMap.set i (TDQValid h t') q).
  Proof.
    intros. eapply TDQCorrect_range_gss; eauto.
    eapply TDQCorrect_range_valid_head; eauto.
  Qed.      

End TDQ_INV.

Section AbTCB_INV.

  Local Open Scope Z_scope.

  Lemma AbTCBCorrect_range_gss:
    forall t,
      AbTCBCorrect_range t ->
      forall i s b,
        -1 <= b <= num_chan ->
        AbTCBCorrect_range (ZMap.set i (AbTCBValid s b) t).
  Proof.
    unfold AbTCBCorrect_range; intros.
    destruct (zeq i0 i); subst.
    - rewrite ZMap.gss. unfold AbTCBCorrect.
      esplit; esplit. split; trivial.
    - rewrite ZMap.gso; eauto.
  Qed.

  Lemma AbTCBCorrect_range_valid_b:
    forall t,
      AbTCBCorrect_range t ->
      forall i,
        0 <= i < num_proc ->
        forall s b,
          ZMap.get i t = AbTCBValid s b ->
          -1 <= b <= num_chan.
  Proof.
    unfold AbTCBCorrect_range, AbTCBCorrect; intros.
    specialize (H _ H0). rewrite H1 in H.
    destruct H as (? & ? & He & Hr). inv He. assumption.
  Qed.

  Lemma AbQCorrect_range_gss_enqueue:
    forall q,
      AbQCorrect_range q ->
      forall i l,
        ZMap.get i q = AbQValid l ->
        forall a,
          0 <= a < num_proc ->
          AbQCorrect_range
            (ZMap.set i (AbQValid (a :: l)) q).
  Proof.
    unfold AbQCorrect_range, AbQCorrect. intros.
    destruct (zeq i0 i); subst.
    - rewrite ZMap.gss. exploit H; eauto. rewrite H0.
      intros (l0 & He & Hr). inv He.
      refine_split'; trivial.
      intros. inv H3; eauto.
    - rewrite ZMap.gso; eauto.
  Qed.

  Lemma AbTCBStrong_range_gss_READY:
    forall t,
      AbTCBStrong_range t ->
      forall i,
        AbTCBStrong_range (ZMap.set i (AbTCBValid READY num_proc) t).
  Proof.
    unfold AbTCBStrong_range; intros.
    destruct (zeq i0 i); subst.
    - rewrite ZMap.gss. unfold AbTCBStrong.
      refine_split'; eauto; intros.
      + inv H1; congruence.
      + congruence.
    - rewrite ZMap.gso; eauto.
  Qed.

  Lemma AbTCBStrong_range_gss_SLEEP:
    forall t,
      AbTCBStrong_range t ->
      forall i n,
        0 <= n < num_proc ->
        AbTCBStrong_range (ZMap.set i (AbTCBValid SLEEP n) t).
  Proof.
    unfold AbTCBStrong_range; intros.
    destruct (zeq i0 i); subst.
    - rewrite ZMap.gss. unfold AbTCBStrong.
      refine_split'; eauto; intros; inv H2; congruence.
    - rewrite ZMap.gso; eauto.
  Qed.

  Lemma AbTCBStrong_range_gss_RUN:
    forall t,
      AbTCBStrong_range t ->
      forall i,
        AbTCBStrong_range (ZMap.set i (AbTCBValid RUN (-1)) t).
  Proof.
    unfold AbTCBStrong_range; intros.
    destruct (zeq i0 i); subst.
    - rewrite ZMap.gss. unfold AbTCBStrong.
      refine_split'; eauto; intros;inv H1.
    - rewrite ZMap.gso; eauto.
  Qed.

  Lemma AbTCBStrong_range_impl:
    forall t,
      AbTCBStrong_range t ->
      AbTCBCorrect_range t.
  Proof.
    unfold AbTCBStrong_range, AbTCBCorrect_range, AbTCBStrong, AbTCBCorrect. intros.
    exploit H; eauto. intros (? & ? & Hr1 & Hr2 & Hr3 & Hr4).
    rewrite Hr1. esplit; esplit. split; trivial.
    destruct x.
    - exploit Hr4; trivial. omega.
    - exploit Hr2; auto. omega.
    - exploit Hr3; trivial. omega.
    - exploit Hr2; auto. omega.
  Qed.

End AbTCB_INV.

Section AbQ_INV.

  Local Open Scope Z_scope.


  Lemma AbQCorrect_range_gss:
    forall q,
      AbQCorrect_range q ->
      forall l,
        (forall x, In x l -> 0 <= x < num_proc) ->
        forall i,
          AbQCorrect_range
            (ZMap.set i (AbQValid l) q).
  Proof.
    unfold AbQCorrect_range, AbQCorrect. intros.
    destruct (zeq i0 i); subst.
    - rewrite ZMap.gss. 
      refine_split'; trivial.
    - rewrite ZMap.gso; eauto.
  Qed.

  Lemma remove_property:
    forall l P,
      (forall x, In x l -> P x) ->
      forall a,
        (forall x, In x (remove zeq a l) -> P x).
  Proof.
    intros. eapply X.
    specialize (remove_incl l a). intros Hcl.
    apply Hcl in H. auto.
  Qed.

  Lemma AbQCorrect_range_gss_remove':
    forall q,
      AbQCorrect_range q ->
      forall l,
        (forall x, In x l -> 0 <= x < num_proc) ->
        forall i a,
          AbQCorrect_range
            (ZMap.set i (AbQValid (remove zeq a l)) q).
  Proof.
    intros. eapply AbQCorrect_range_gss; eauto.
    eapply remove_property; eauto.
  Qed.

  Lemma list_range_enqueue:
    forall l,
      (forall x, In x l -> 0 <= x < num_proc) ->
      forall a,
        0 <= a < num_proc ->
        (forall x, In x (a::l) -> 0 <= x < num_proc).
  Proof.
    intros. inv H1; eauto.
  Qed.

  Lemma AbQCorrect_range_gss_enqueue':
    forall q,
      AbQCorrect_range q ->
      forall l,
        (forall x, In x l -> 0 <= x < num_proc) ->
        forall a,
          0 <= a < num_proc ->
          forall i,
            AbQCorrect_range
              (ZMap.set i (AbQValid (a::l)) q).
  Proof.
    intros. eapply AbQCorrect_range_gss; eauto.
    eapply list_range_enqueue; eauto.
  Qed.

  Lemma AbQCorrect_range_impl:
    forall q,
      AbQCorrect_range q ->
      forall i l,
        0 <= i <= num_proc ->
        ZMap.get i q = AbQValid l ->
        (forall x, In x l -> 0 <= x < num_proc).
  Proof.
    unfold AbQCorrect_range, AbQCorrect. intros.
    exploit H; eauto. rewrite H1.
    intros (? & He & Hr). inv He. eauto.
  Qed.

  Lemma AbQCorrect_range_gss_remove:
    forall q,
      AbQCorrect_range q ->
      forall i l,
        ZMap.get i q = AbQValid l ->
        forall a,
          AbQCorrect_range
            (ZMap.set i (AbQValid (remove zeq a l)) q).
  Proof.
    unfold AbQCorrect_range, AbQCorrect. intros.
    destruct (zeq i0 i); subst.
    - rewrite ZMap.gss. exploit H; eauto. rewrite H0.
      intros (l0 & He & Hr). inv He.
      refine_split'; trivial.
      intros. specialize (remove_incl l0 a). intros Hincl.
      specialize (Hincl _ H2). exploit H; eauto. 
    - rewrite ZMap.gso; eauto.
  Qed.

  Lemma last_range_AbQ:
    forall q,
      AbQCorrect_range q ->
      forall i,
        0 <= i <= num_proc ->
        forall l,
          ZMap.get i q = AbQValid l ->
          last l num_proc <> num_proc ->
          0 <= last l num_proc < num_proc.
  Proof.
    unfold AbQCorrect_range, AbQCorrect; intros.
    exploit H; eauto. rewrite H1.
    intros (? & He & Hr). inv He.
    eapply Hr. apply last_correct; auto.
  Qed.

  Lemma AbQCorrect_range_gss_enqueue_rmv:
    forall q,
      AbQCorrect_range q ->
      forall i l,
        ZMap.get i q = AbQValid l ->
        forall i' l',
          ZMap.get i' q = AbQValid l' ->
          i' <> i ->
          forall a,
            0 <= a < num_proc ->
            AbQCorrect_range
              (ZMap.set i (AbQValid (a :: l)) 
                        (ZMap.set i' (AbQValid (remove zeq a l')) q)).
  Proof.
    intros. eapply AbQCorrect_range_gss_enqueue; eauto.
    - eapply AbQCorrect_range_gss_remove; eauto.
    - rewrite ZMap.gso; eauto.
  Qed.

  Lemma AbQCorrect_range_gss_wakeup':
    forall q,
      AbQCorrect_range q ->
      forall l,
        ZMap.get num_proc q = AbQValid l ->
        forall i' l',
          ZMap.get i' q = AbQValid l' ->
          0 <= i' < num_proc ->
          forall a,
            0 <= a < num_proc ->
            AbQCorrect_range
              (ZMap.set num_proc (AbQValid (a :: l)) 
                        (ZMap.set i' (AbQValid (remove zeq a l')) q)).
  Proof.
    intros. eapply AbQCorrect_range_gss_enqueue_rmv; eauto.
    red; intros. subst. omega.
  Qed.

  Lemma AbQCorrect_range_gss_wakeup:
    forall q,
      AbQCorrect_range q ->
      forall l,
        ZMap.get num_proc q = AbQValid l ->
        forall i' l',
          ZMap.get i' q = AbQValid l' ->
          0 <= i' < num_proc ->
          last l' num_proc <> num_proc ->
          AbQCorrect_range
            (ZMap.set num_proc (AbQValid (last l' num_proc :: l)) 
                      (ZMap.set i' (AbQValid (remove zeq (last l' num_proc) l')) q)).
  Proof.
    intros. eapply AbQCorrect_range_gss_wakeup'; eauto.
    eapply last_range_AbQ; eauto. omega.
  Qed.

End AbQ_INV.

Section THREAD_INV.

  Local Open Scope Z_scope.

  Section NOTINQ_INV.

    Lemma NotInQ_gso_true:
      forall ac t,
        NotInQ ac t ->
        forall i c,
          cused c = true ->
          NotInQ (ZMap.set i c ac) t.
    Proof.
      unfold NotInQ; intros.
      destruct (zeq i0 i); subst.
      - rewrite ZMap.gss in H2. congruence.
      - rewrite ZMap.gso in H2; eauto.
    Qed.

    Lemma NotInQ_gso_state:
      forall ac t,
        NotInQ ac t ->
        forall i,
          0 <= i < num_proc ->
          forall s b,
            ZMap.get i t = AbTCBValid s b ->
            forall s',
              NotInQ ac (ZMap.set i (AbTCBValid s' b) t).
    Proof.
      unfold NotInQ; intros.
      destruct (zeq i0 i); subst.
      - rewrite ZMap.gss in H4. inv H4. eauto.
      - rewrite ZMap.gso in *; eauto.
    Qed.

    Lemma NotInQ_gso_ac:
      forall ac t,
        NotInQ ac t ->
        forall i,
          cused (ZMap.get i ac) = true ->
          forall s,
            NotInQ ac (ZMap.set i s t).
    Proof.
      unfold NotInQ; intros.
      destruct (zeq i0 i); subst.
      - rewrite ZMap.gss in H3. inv H3. congruence.
      - rewrite ZMap.gso in *; eauto.
    Qed.

    Lemma NotInQ_gso_ac_true:
      forall ac t,
        NotInQ ac t ->
        forall i c s,
          cused c = true ->
          NotInQ (ZMap.set i c ac) (ZMap.set i s t).
    Proof.
      intros; eapply NotInQ_gso_ac; eauto.
      - eapply NotInQ_gso_true; eauto.
      - rewrite ZMap.gss; eauto.
    Qed.

    Lemma NotInQ_gso_neg:
      forall ac t,
        NotInQ ac t ->
        forall i s,
          NotInQ ac (ZMap.set i (AbTCBValid s (-1)) t).
    Proof.
      unfold NotInQ; intros.
      destruct (zeq i0 i); subst.
      - rewrite ZMap.gss in H2. inv H2. trivial.
      - rewrite ZMap.gso in *; eauto.
    Qed.

    Lemma NotInQ_InQ_gss_wakeup':
      forall ac t q,
        NotInQ ac t ->
        InQ t q ->
        forall i,
          0 <= i < num_proc ->
          forall l,
            ZMap.get i q = AbQValid l ->
            forall i',
              0 <= i' < num_proc ->
              In i' l ->
              forall s b,
                NotInQ ac (ZMap.set i' (AbTCBValid s b) t).
    Proof.
      unfold NotInQ, InQ; intros.
      destruct (zeq i0 i'); subst.
      - rewrite ZMap.gss in H7. inv H7.
        exploit H0; eauto. omega.
        intros (? & He). exploit H; eauto. omega.
      - rewrite ZMap.gso in *; eauto.
    Qed.

    Lemma NotInQ_InQ_gss_wakeup:
      forall ac t q,
        NotInQ ac t ->
        InQ t q ->
        AbQCorrect_range q ->
        forall i,
          0 <= i < num_proc ->
          forall l,
            ZMap.get i q = AbQValid l ->
            last l num_proc <> num_proc ->
            forall s b,
              NotInQ ac (ZMap.set (last l num_proc) (AbTCBValid s b) t).
    Proof.
      intros. eapply NotInQ_InQ_gss_wakeup'; eauto.
      - eapply last_range_AbQ; eauto. omega.
      - apply last_correct; auto.
    Qed.

  End NOTINQ_INV.

  Section QCOUNT_INV.

    Lemma QCount_gso_state:
      forall t q,
        QCount t q ->
        forall i,
          0 <= i < num_proc ->
          forall s b,
            ZMap.get i t = AbTCBValid s b ->
            forall s',
              QCount (ZMap.set i (AbTCBValid s' b) t) q.
    Proof.
      unfold QCount; intros.
      destruct (zeq i0 i); subst.
      - rewrite ZMap.gss in H3. inv H3. eauto.
      - rewrite ZMap.gso in *; eauto.
    Qed.

    Lemma QCount_gss_enqueue:
      forall t q,
        QCount t q ->
        InQ t q ->
        forall i,
          0 <= i < num_proc ->
          forall s',
            ZMap.get i t = AbTCBValid s' (-1) ->
            forall i',
              0 <= i' <= num_proc ->
              forall l,
                ZMap.get i' q = AbQValid l ->
                forall s,
                  QCount (ZMap.set i (AbTCBValid s i') t) 
                         (ZMap.set i' (AbQValid (i::l)) q).
    Proof.
      unfold QCount, InQ; intros.
      destruct (zeq i0 i); subst.
      - rewrite ZMap.gss in *. inv H6. rewrite ZMap.gss.
        refine_split'; eauto.
        rewrite count_occ_cons_eq; eauto.
        assert (HW: count_occ zeq l i = 0%nat).
        {
          caseEq (count_occ zeq l i); trivial.
          intros. 
          assert (HR: (count_occ zeq l i > 0)%nat) by omega.
          eapply count_occ_In in HR.
          exploit (H0 i b); eauto. 
          rewrite H2. intros (? & He). inv He. omega.
        }
        rewrite HW; auto. 
      - rewrite ZMap.gso in H6; auto.
        destruct (zeq b i'); subst.
        + rewrite ZMap.gss.
          exploit H; eauto. rewrite H4.
          intros (? & He & Hr). inv He.
          refine_split'; trivial.
          rewrite count_occ_cons_neq; auto.
        + rewrite ZMap.gso; eauto.
    Qed.

    Lemma QCount_gss_remove:
      forall t q,
        QCount t q ->
        (*InQ t q ->*)
        forall i,
          0 <= i < num_proc ->
          (*forall s',
            ZMap.get i t = AbTCBValid s' (-1) ->*)
          forall i',
            0 <= i' <= num_proc ->
            forall l,
              ZMap.get i' q = AbQValid l ->
              (*In i l ->*)
              forall s,
                QCount (ZMap.set i (AbTCBValid s (-1)) t) 
                       (ZMap.set i' (AbQValid (remove zeq i l)) q).
    Proof.
      unfold QCount, InQ; intros. 
      destruct (zeq b i'); subst.
      - rewrite ZMap.gss. 
        destruct (zeq i0 i); subst.
        + rewrite ZMap.gss in *. inv H4. omega.
        + rewrite ZMap.gso in *; eauto. 
          refine_split'; eauto.
          exploit H; eauto.
          rewrite H2. intros (? & He & Hr). inv He.
          rewrite remove_count_outside; auto.
      - rewrite ZMap.gso; eauto.
        destruct (zeq i0 i); subst.
        + rewrite ZMap.gss in *. inv H4. omega.
        + rewrite ZMap.gso in *; eauto. 
    Qed.

    Lemma QCount_valid:
      forall t q,
        QCount t q ->
        forall i i' s' l,
          0 <= i < num_proc ->
          0 <= i' <= num_proc ->
          ZMap.get i t = AbTCBValid s' i' ->
          ZMap.get i' q = AbQValid l ->
          In i l.
    Proof.
      unfold QCount; intros.
      exploit H; eauto. rewrite H3.
      intros (? & He & Hr). inv He.
      assert (Hl: (count_occ zeq x i > 0) % nat) by omega.
      eapply count_occ_In in Hl; eauto.
    Qed.

    Lemma QCount_gss_wakeup':
      forall t q,
        QCount t q ->
        InQ t q ->
        forall i,
          0 <= i < num_proc ->
          forall i',
            0 <= i' <= num_proc ->
            forall l,
              ZMap.get i' q = AbQValid l ->
              forall i'',
                0 <= i'' < num_proc ->
                i' <> i'' ->
                forall l',
                  ZMap.get i'' q = AbQValid l' ->
                  In i l' ->
                  forall s,
                    QCount (ZMap.set i (AbTCBValid s i') t) 
                           (ZMap.set i' (AbQValid (i::l)) 
                                     (ZMap.set i'' (AbQValid (remove zeq i l')) q)).
    Proof.
      unfold QCount, InQ; intros.
      destruct (zeq i0 i); subst.
      - rewrite ZMap.gss in *. inv H9. rewrite ZMap.gss.
        refine_split'; eauto.
        rewrite count_occ_cons_eq; eauto.
        assert (HW: count_occ zeq l i = 0%nat).
        {
          assert (HW: ~ In i l).
          {
            exploit (H0 i i''); eauto. omega. intros (? & Hr).
            exploit H; eauto. omega. rewrite H6. intros (? & He & Hr'). inv He.
            red; intros.
            exploit (H0 i b); eauto. rewrite Hr. intros (? & He). inv He.
            congruence.
          }
          destruct (count_occ_In zeq l i) as [HP1 HP2].
          destruct (count_occ zeq l i). trivial.
          elim HW. apply HP2. omega.
        }
        rewrite HW. trivial.
      - rewrite ZMap.gso in H9; auto.
        destruct (zeq b i'); subst.
        + rewrite ZMap.gss.
          refine_split'; trivial.
          exploit H; eauto. rewrite H3.
          intros (? & He & Hr). inv He.
          rewrite count_occ_cons_neq; auto.
        + rewrite ZMap.gso; eauto.
          destruct (zeq b i''); subst.
          * rewrite ZMap.gss. refine_split'; eauto.
            exploit H; eauto. rewrite H6.
            intros (? & He & Hr). inv He.
            rewrite remove_count_outside; auto.
          * rewrite ZMap.gso; eauto.
    Qed.

    Lemma QCount_gss_wakeup:
      forall t q,
        QCount t q ->
        InQ t q ->
        AbQCorrect_range q ->
        forall l,
          ZMap.get num_proc q = AbQValid l ->
          forall i,
            0 <= i < num_proc ->
            forall l',
              ZMap.get i q = AbQValid l' ->
              last l' num_proc <> num_proc ->
              forall s,
                QCount (ZMap.set (last l' num_proc) (AbTCBValid s num_proc) t) 
                       (ZMap.set num_proc (AbQValid (last l' num_proc :: l)) 
                                 (ZMap.set i (AbQValid (remove zeq (last l' num_proc) l')) q)).
    Proof.
      intros. eapply QCount_gss_wakeup'; eauto; try omega.
      - eapply last_range_AbQ; eauto. omega.
      - apply last_correct; auto.
    Qed.

    Lemma QCount_tcb_gss_enqueue:
      forall t q ac,
        QCount t q ->
        InQ t q ->
        AbTCBCorrect_range t ->
        NotInQ ac t ->
        forall i,
          0 <= i < num_proc ->
          cused (ZMap.get i ac) = false ->
          forall i',
            0 <= i' <= num_proc ->
            forall l,
              ZMap.get i' q = AbQValid l ->
              forall s,
                QCount (ZMap.set i (AbTCBValid s i') t) 
                       (ZMap.set i' (AbQValid (i::l)) q).
    Proof.
      unfold NotInQ, AbTCBCorrect_range, AbTCBCorrect. intros.      
      exploit H1; eauto. intros (? & ? & Hr & Hr').
      specialize (H2 _ _ _ H3 H4 Hr); subst.
      eapply QCount_gss_enqueue; eauto.
    Qed.

    Lemma QCount_gss_spawn:
      forall t q ac,
        QCount t q ->
        InQ t q ->
        AbTCBCorrect_range t ->
        NotInQ ac t ->
        forall i P,
          (0 < i < num_proc
           /\ cused (ZMap.get i ac) = false
           /\ P) ->
          forall l,
            ZMap.get num_proc q = AbQValid l ->
            forall s,
              QCount (ZMap.set i (AbTCBValid s num_proc) t) 
                     (ZMap.set num_proc (AbQValid (i::l)) q).
    Proof.
      intros. destruct H3 as (HP1 & HP2 & _).
      eapply QCount_tcb_gss_enqueue; eauto; omega.
    Qed.

    Lemma QCount_gss_yield':
      forall t q,
        QCount t q ->
        InQ t q ->
        forall i,
          0 <= i <= num_proc ->
          forall l,
            ZMap.get i q = AbQValid l ->
            forall i',
              0 <= i' < num_proc ->
              In i' l ->
              forall c s1,
                0 <= c < num_proc ->
                ZMap.get c t = AbTCBValid s1 (-1) ->
                c <> i' ->
                forall s s',
                  QCount (ZMap.set i' (AbTCBValid s (-1)) 
                                   (ZMap.set c (AbTCBValid s' i) t)) 
                         (ZMap.set i (AbQValid (remove zeq i' (c :: l))) q).
    Proof.
      unfold QCount, InQ; intros.
      destruct (zeq i0 i'); subst.
      - rewrite ZMap.gss in *. inv H9. omega.
      - rewrite ZMap.gso in H9; eauto.
        destruct (zeq i0 c); subst.
        + rewrite ZMap.gss in *. inv H9.
          rewrite ZMap.gss.
          refine_split'; eauto.
          rewrite remove_count_outside; auto.
          rewrite count_occ_cons_eq; eauto.
          assert (HW: count_occ zeq l c = 0%nat).
          {
            assert (HW: ~ In c l).
            {
              red; intros. exploit H0; eauto.
              rewrite H6. intros (? & He). inv He. omega.
            }
            destruct (count_occ_In zeq l c) as [HP1 HP2].
            destruct (count_occ zeq l c). trivial.
            elim HW. apply HP2. omega.
          }
          rewrite HW. trivial.
        + rewrite ZMap.gso in H9; auto.
          destruct (zeq b i); subst.
          * rewrite ZMap.gss.
            refine_split'; trivial.
            exploit H; eauto. rewrite H2.
            intros (? & He & Hr). inv He.
            rewrite remove_count_outside; auto.
            rewrite count_occ_cons_neq; auto.
          * rewrite ZMap.gso; eauto.
    Qed.

    Lemma last_neq_cid:
      forall t q c p,
        InQ t q ->
        AbQCorrect_range q ->
        CurIDValid c p t ->
        forall i l,
          0 <= i <= num_chan ->
          ZMap.get i q = AbQValid l ->
          last l num_proc <> num_proc ->
          c <> last l num_proc.
    Proof.
      intros. 
      assert(HIn: In (last l num_proc) l).
      {
        apply last_correct; auto.
      }
      assert (Hrange: 0 <= (last l num_proc) < num_proc).      
      {
        eapply last_range_AbQ; eauto.
      }
      unfold InQ, AbQCorrect_range, AbQCorrect, CurIDValid in *. 
      red; intros; subst. destruct H1 as (_ & Hr).
      exploit H; eauto. rewrite Hr.
      intros (? & He). inv He. omega.
    Qed.

    Lemma QCount_gss_yield:
      forall c t q p,
        QCount t q ->
        InQ t q ->
        AbQCorrect_range q ->
        CurIDValid c p t ->
        forall l,
          ZMap.get num_proc q = AbQValid l ->
          0 <= c < num_proc ->
          0 <= last l num_proc < num_proc ->
          forall s s',
            QCount (ZMap.set (last l num_proc) (AbTCBValid s (-1)) 
                             (ZMap.set c (AbTCBValid s' num_proc) t)) 
                   (ZMap.set num_proc (AbQValid (remove zeq (last l num_proc) (c :: l))) q).
    Proof.
      intros. eapply QCount_gss_yield'; eauto.
      - omega.
      - apply last_correct; eauto. omega.
      - eapply H2.
      - eapply last_neq_cid; eauto; omega.
    Qed.

  End QCOUNT_INV.

  Section INQ_INV.

    Lemma InQ_gso_state:
      forall t q,
        InQ t q ->
        forall i,
          0 <= i < num_proc ->
          forall s b,
            ZMap.get i t = AbTCBValid s b ->
            forall s',
              InQ (ZMap.set i (AbTCBValid s' b) t) q.
    Proof.
      unfold InQ; intros.
      destruct (zeq i0 i); subst.
      - rewrite ZMap.gss. exploit H; eauto. rewrite H1.
        intros (? & He). inv He. eauto.
      - rewrite ZMap.gso; eauto.
    Qed.

    Lemma InQ_gss_enqueue:
      forall t q,
        InQ t q ->
        forall i,
          0 <= i < num_proc ->
          forall s',
            ZMap.get i t = AbTCBValid s' (-1) ->
            forall i',
              0 <= i' <= num_proc ->
              forall l,
                ZMap.get i' q = AbQValid l ->
                forall s,
                  InQ (ZMap.set i (AbTCBValid s i') t) 
                      (ZMap.set i' (AbQValid (i::l)) q).
    Proof.
      unfold InQ; intros.
      destruct (zeq j i'); subst.
      - rewrite ZMap.gss in *. inv H6. 
        destruct (zeq i0 i); subst.
        + rewrite ZMap.gss.
          refine_split'; eauto.
        + rewrite ZMap.gso; auto. inv H7.
          * congruence.
          * eauto.
      - rewrite ZMap.gso in H6; eauto.
        destruct (zeq i0 i); subst.
        + rewrite ZMap.gss. exploit H; eauto.
          rewrite H1. intros (? & He).
          inv He. omega.
        + rewrite ZMap.gso; eauto. 
    Qed.

    Lemma InQ_gss_remove:
      forall t q,
        InQ t q ->
        QCount t q ->
        forall i,
          0 <= i < num_proc ->
          (*forall s',
            ZMap.get i t = AbTCBValid s' (-1) ->*)
          forall i',
            0 <= i' <= num_proc ->
            forall l,
              ZMap.get i' q = AbQValid l ->
              In i l ->
              forall s,
                InQ (ZMap.set i (AbTCBValid s (-1)) t) 
                    (ZMap.set i' (AbQValid (remove zeq i l)) q).
    Proof.
      unfold InQ, QCount; intros.
      destruct (zeq j i'); subst.
      - rewrite ZMap.gss in *. inv H7. 
        destruct (zeq i0 i); subst.
        + rewrite ZMap.gss.
          contradict H8. apply remove_In.
        + rewrite ZMap.gso; auto.
          specialize (remove_incl _ _ _ H8); intros Hincl; eauto.
      - rewrite ZMap.gso in H7; eauto.
        destruct (zeq i0 i); subst.
        + exploit H; eauto. intros (? & Hr).
          exploit (H i i'); eauto. rewrite Hr.
          intros (? & He). inv He. congruence.
        + rewrite ZMap.gso; eauto. 
    Qed.

    Lemma InQ_gss_wakeup':
      forall t q,
        InQ t q ->
        QCount t q ->
        forall i,
          0 <= i < num_proc ->
          forall i',
            0 <= i' <= num_proc ->
            forall l,
              ZMap.get i' q = AbQValid l ->
              forall i'',
                0 <= i'' < num_proc ->
                i' <> i'' ->
                forall l',
                  ZMap.get i'' q = AbQValid l' ->
                  In i l' ->
                  forall s,
                    InQ (ZMap.set i (AbTCBValid s i') t) 
                        (ZMap.set i' (AbQValid (i::l)) 
                                  (ZMap.set i'' (AbQValid (remove zeq i l')) q)).
    Proof.
      unfold QCount, InQ; intros.
      destruct (zeq j i'); subst.
      - rewrite ZMap.gss in *. inv H10.
        destruct (zeq i0 i); subst.
        + rewrite ZMap.gss. eauto.
        + rewrite ZMap.gso; auto. destruct H11 as [HP | HP ].
          congruence. eauto.
      - rewrite ZMap.gso in H10; auto.
        destruct (zeq j i''); subst.
        + rewrite ZMap.gss in *. inv H10.
          destruct (zeq i0 i); subst.
          * rewrite ZMap.gss. contradict H11.
            apply remove_In.
          * rewrite ZMap.gso; auto.
            specialize (remove_incl _ _ _ H11).
            intros Hincl. eauto.
        + rewrite ZMap.gso in H10; auto.
          destruct (zeq i0 i); subst.
          * rewrite ZMap.gss.
            exploit (H i i''); eauto. omega. intros (? & Hr).
            exploit (H i j); eauto. rewrite Hr. intros (? & He).
            inv He. omega.
          * rewrite ZMap.gso; eauto.
    Qed.

    Lemma InQ_gss_wakeup:
      forall t q,
        InQ t q ->
        QCount t q ->
        AbQCorrect_range q ->
        forall l,
          ZMap.get num_proc q = AbQValid l ->
          forall i,
            0 <= i < num_proc ->
            forall l',
              ZMap.get i q = AbQValid l' ->
              last l' num_proc <> num_proc ->
              forall s,
                InQ (ZMap.set (last l' num_proc) (AbTCBValid s num_proc) t) 
                    (ZMap.set num_proc (AbQValid (last l' num_proc :: l)) 
                              (ZMap.set i (AbQValid (remove zeq (last l' num_proc) l')) q)).
    Proof.
      intros. eapply InQ_gss_wakeup'; eauto; try omega.
      - eapply last_range_AbQ; eauto. omega.
      - apply last_correct; auto.
    Qed.

    Lemma InQ_tcb_gss_enqueue:
      forall t q ac,
        InQ t q ->
        QCount t q ->
        AbTCBCorrect_range t ->
        NotInQ ac t ->
        forall i,
          0 <= i < num_proc ->
          cused (ZMap.get i ac) = false ->
          forall i',
            0 <= i' <= num_proc ->
            forall l,
              ZMap.get i' q = AbQValid l ->
              forall s,
                InQ (ZMap.set i (AbTCBValid s i') t) 
                    (ZMap.set i' (AbQValid (i::l)) q).
    Proof.
      unfold NotInQ, AbTCBCorrect_range, AbTCBCorrect. intros.
      exploit H1; eauto. intros (? & ? & Hr & Hr').
      specialize (H2 _ _ _ H3 H4 Hr); subst.
      eapply InQ_gss_enqueue; eauto.
    Qed.

    Lemma InQ_gss_spawn:
      forall t q ac,
        InQ t q ->
        QCount t q ->
        AbTCBCorrect_range t ->
        NotInQ ac t ->
        forall i P,
          (0 < i < num_proc
           /\ cused (ZMap.get i ac) = false
           /\ P) ->
          forall l,
            ZMap.get num_proc q = AbQValid l ->
            forall s,
              InQ (ZMap.set i (AbTCBValid s num_proc) t) 
                  (ZMap.set num_proc (AbQValid (i::l)) q).
    Proof.
      intros. destruct H3 as (HP1 & HP2 & _).
      eapply InQ_tcb_gss_enqueue; eauto; omega.
    Qed.

    Local Opaque remove.

    Lemma InQ_gss_yield':
      forall t q,
        QCount t q ->
        InQ t q ->
        forall i,
          0 <= i <= num_proc ->
          forall l,
            ZMap.get i q = AbQValid l ->
            forall i',
              0 <= i' < num_proc ->
              In i' l ->
              forall c s1,
                0 <= c < num_proc ->
                ZMap.get c t = AbTCBValid s1 (-1) ->
                c <> i' ->
                forall s s',
                  InQ (ZMap.set i' (AbTCBValid s (-1)) 
                                (ZMap.set c (AbTCBValid s' i) t)) 
                      (ZMap.set i (AbQValid (remove zeq i' (c :: l))) q).
    Proof.
      unfold QCount, InQ; intros.
      destruct (zeq j i); subst.
      - rewrite ZMap.gss in *. inv H10.
        destruct (zeq i0 i'); subst.
        + rewrite ZMap.gss. contradict H11.
          apply remove_In.
        + rewrite ZMap.gso; auto. 
          specialize (remove_incl _ _ _ H11).
          intros Hincl. destruct Hincl; subst.
          * rewrite ZMap.gss. eauto.
          * destruct (zeq i0 c); subst.
            rewrite ZMap.gss. eauto.
            rewrite ZMap.gso; eauto.
      - rewrite ZMap.gso in H10; auto.
        destruct (zeq i0 i'); subst.
        + exploit H0; eauto. intros (? & Hr).
          exploit (H0 i' i); eauto. rewrite Hr.
          intros (? & He). inv He. congruence.
        + rewrite ZMap.gso; auto.
          destruct (zeq i0 c); subst.
          * rewrite ZMap.gss.
            exploit H0; eauto. rewrite H6.
            intros (? & He). inv He. omega.
          * rewrite ZMap.gso; eauto.
    Qed.

    Lemma InQ_gss_yield:
      forall c t q p,
        QCount t q ->
        InQ t q ->
        AbQCorrect_range q ->
        CurIDValid c p t ->
        forall l,
          ZMap.get num_proc q = AbQValid l ->
          0 <= c < num_proc ->
          0 <= last l num_proc < num_proc ->
          forall s s',
            InQ (ZMap.set (last l num_proc) (AbTCBValid s (-1)) 
                          (ZMap.set c (AbTCBValid s' num_proc) t)) 
                (ZMap.set num_proc (AbQValid (remove zeq (last l num_proc) (c :: l))) q).
    Proof.
      intros. eapply InQ_gss_yield'; eauto.
      - omega.
      - apply last_correct; eauto. omega.
      - eapply H2.
      - eapply last_neq_cid; eauto; omega.
    Qed.

  End INQ_INV.

End THREAD_INV.

Section CID_INV.

  Local Open Scope Z_scope.

  Lemma SingleRun_gss_state:
    forall c t,
      SingleRun c t ->
      forall i st b,
        0 <= i < num_proc ->
        ZMap.get i t = AbTCBValid st b ->
        forall b',
          SingleRun c (ZMap.set i (AbTCBValid st b') t).
  Proof.
    unfold SingleRun; intros.
    destruct (zeq i i0); subst.
    - rewrite ZMap.gss in *. inv H4.
      eapply H; eauto.
    - rewrite ZMap.gso in H4; eauto.
  Qed.

  Lemma SingleRun_gso_state:
    forall c t,
      SingleRun c t ->
      forall i st b,
        st <> RUN ->
        SingleRun c (ZMap.set i (AbTCBValid st b) t).
  Proof.
    unfold SingleRun; intros.
    destruct (zeq i i0); subst.
    - rewrite ZMap.gss in *. inv H3. trivial.
    - rewrite ZMap.gso in H3; eauto.
  Qed.

  Lemma SingleRun_gso_state_READY:
    forall c t,
      SingleRun c t ->
      forall i b,
        SingleRun c (ZMap.set i (AbTCBValid READY b) t).
  Proof.
    intros. eapply SingleRun_gso_state; eauto.
    congruence.
  Qed.

  Lemma SingleRun_gso_cid:
    forall c t,
      SingleRun c t ->
      forall s b,
        ZMap.get c t = AbTCBValid s b ->
        s <> RUN ->
        forall b' c',
          SingleRun c' (ZMap.set c' b' t).
  Proof.
    unfold SingleRun; intros.
    rewrite ZMap.gso in H4; eauto.
    destruct (zeq i c); subst; eauto.
    rewrite H0 in H4. inv H4. trivial.
  Qed.

  Lemma SingleRun_gss_gso_cid:
    forall c t,
      SingleRun c t ->
      forall s,
        s <> RUN ->
        forall b b' c',
          SingleRun c' (ZMap.set c' b' (ZMap.set c (AbTCBValid s b) t)).
  Proof.
    unfold SingleRun; intros.
    rewrite ZMap.gso in H3; eauto.
    destruct (zeq i c); subst; eauto.
    - rewrite ZMap.gss in H3. inv H3. trivial.
    - rewrite ZMap.gso in H3; eauto.
  Qed.

  Lemma correct_curid_gss_true:
    forall c ac,
      cused (ZMap.get c ac) = true ->
      forall i C, cused C = true ->
        cused (ZMap.get c (ZMap.set i C ac)) = true.
  Proof.
    unfold update_cused; intros; zmap_solve.
  Qed.
  
  Lemma CurIDValid_gso_tcb:
    forall c ac t,
      CurIDValid c ac t ->
      forall i,
        c <> i ->
        forall s,
          CurIDValid c ac (ZMap.set i s t).
  Proof.
    unfold CurIDValid; intros; zmap_solve.
  Qed.

  Lemma CurIDValid_gso_ac:
    forall c ac t,
      CurIDValid c ac t ->
      forall i,
        c <> i -> 
        forall s,
          CurIDValid c (ZMap.set i s ac) t.
  Proof.
    unfold CurIDValid; intros; zmap_solve.
  Qed.

  Lemma CurIDValid_gss_ac:
    forall c ac t,
      CurIDValid c ac t ->
      forall i C,
        cused C = true -> CurIDValid c (ZMap.set i C ac) t.
  Proof.
    unfold CurIDValid; intros; zmap_solve; intuition.
  Qed.

  Lemma CurIDValid_gso_neq_true:
    forall c ac t,
      CurIDValid c ac t ->
      forall i,
        cused (ZMap.get i ac) = false ->
        forall s1 s2,
          CurIDValid c (ZMap.set i s1 ac) (ZMap.set i s2 t).
  Proof.
    unfold CurIDValid, update_cused; intros.
    assert (HN: c <> i).
    {
      red; intros; subst.
      destruct H as (H & _). congruence.
    }
    repeat rewrite ZMap.gso; eauto.
  Qed.

  Lemma CurIDValid_gss_In:
    forall ac t q,
      InQ t q ->
      NotInQ ac t ->
      forall i i' l t',
        ZMap.get i' q = AbQValid l ->
        0 <= i' <= num_proc ->
        In i l ->
        0 <= i < num_proc ->
        CurIDValid i ac (ZMap.set i (AbTCBValid RUN (-1)) t').
  Proof.
    unfold CurIDValid, InQ, NotInQ; intros.
    rewrite ZMap.gss. split; trivial.
    exploit H; eauto. intros (? & Hr).
    specialize (H0 _ x i' H4).
    destruct (cused (ZMap.get i ac)); trivial.
    exploit H0; eauto; intros. subst. omega.
  Qed.

  Lemma CurIDValid_gss_last:
    forall ac t q,
      InQ t q ->
      NotInQ ac t ->
      forall l t',
        ZMap.get num_proc q = AbQValid l ->
        0 <= last l num_proc < num_proc ->
        CurIDValid (last l num_proc) ac
                   (ZMap.set (last l num_proc) (AbTCBValid RUN (-1)) t').
  Proof.
    intros. eapply CurIDValid_gss_In; eauto.
    - omega.
    - apply last_correct; eauto. omega.
  Qed.

End CID_INV.