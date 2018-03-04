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
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import XOmega.
Require Import CLemmas.

Section Real_FreePT.

  Opaque Z.of_nat Z.to_nat.

  Function Calculate_free_pt_at_i (i: Z) (pt: PTable) : PTable :=
    match ZMap.get (PDX i) pt with
      | PDTValid pdt =>
          ZMap.set (PDX i) (PDTValid (ZMap.set (PTX i) PTUnPresent pdt)) pt
      | _ => pt (**r this case should never happen *)
    end.

  Fixpoint Calculate_free_pt (i: nat) (pt: PTable) : PTable :=
    match i with
      | O => Calculate_free_pt_at_i (kern_low * PgSize) pt
      | S k => Calculate_free_pt_at_i (Z.of_nat (S k) * PgSize + (kern_low * PgSize)) (Calculate_free_pt k pt)
    end.

  Definition real_free_pt (ptp: PTPool) (index: Z) := 
    Calculate_free_pt (Z.to_nat ((kern_high * PgSize - kern_low * PgSize - PgSize) / PgSize)) (ZMap.get index ptp).

  Lemma real_free_pt_unchange:
    forall i pt,
      0<= i < kern_low \/ kern_high <= i < maxpage ->
           forall a, 0<= Z.of_nat a <= (kern_high * PgSize - kern_low * PgSize - PgSize) / PgSize->
             ZMap.get (PDX (i * PgSize)) (Calculate_free_pt a pt) = ZMap.get (PDX (i * PgSize)) pt.
  Proof.
    intros until a.
    assert (HT: 0<= i / 1024 < 256 \/ 960 <= i /1024 < 1024) by xomega.
    clear H.
    induction a; simpl; intros;
    unfold Calculate_free_pt_at_i.
    +
      destruct (ZMap.get (PDX 1073741824) pt); trivial.
      rewrite ZMap.gso; trivial.
      unfold PDX.
      change (1073741824 / (4096 * 1024)) with 256.
      replace (i * 4096 / (4096 * 1024)) with (i/1024) by (clear; xomega).
      red; intros HF; rewrite HF in *.
      omega.
    +
      set (pt':=  (Calculate_free_pt a pt)) in *.
      destruct (ZMap.get (PDX (Z.of_nat (S a) * 4096 + 1073741824)) pt'); trivial.
      *
        rewrite ZMap.gso.
        apply IHa; simpl.
        rewrite Nat2Z.inj_succ in H; omega.
        unfold PDX.
        replace (i * 4096 / (4096 * 1024)) with (i/1024) by (clear; xomega).
        set (z:= Z.of_nat (S a)) in *.
        change (2952785920 / 4096) with 720895 in *.
        replace ((z * 4096 + 1073741824) / (4096 * 1024)) with ((z + 262144)/1024) by (clear; xomega).
        red; intros HF; rewrite HF in *; clear HF.
        inversion HT.
        assert ((z + 262144) / 1024 >= 256) by xomega.
        omega.
        assert ((z + 262144) / 1024 < 960) by xomega.
        omega.
      *
        apply IHa; simpl.
        rewrite Nat2Z.inj_succ in H; omega.
  Qed.

  Lemma real_free_pt_unchange_less:
    forall i pt a, 0<= Z.of_nat a <= (kern_high * PgSize - kern_low * PgSize - PgSize) / PgSize->
                   (exists pte, ZMap.get (PDX (i * PgSize)) pt = PDTValid pte) ->
                   (exists pte, ZMap.get (PDX (i * PgSize)) (Calculate_free_pt a pt) = PDTValid pte).
  Proof.
    intros until a.
    induction a; simpl; intros;
    unfold Calculate_free_pt_at_i.
    +
      destruct (ZMap.get (PDX 1073741824) pt); trivial.
      destruct (zeq (PDX (i * 4096)) (PDX 1073741824)).
      rewrite e.
      rewrite ZMap.gss. eauto.
      rewrite ZMap.gso; trivial.
    +
      set (pt':=  (Calculate_free_pt a pt)) in *.
      destruct (ZMap.get (PDX (Z.of_nat (S a) * 4096 + 1073741824)) pt'); eauto.
      destruct (zeq (PDX (i * 4096)) (PDX (Z.of_nat (S a) * 4096 + 1073741824))).
      rewrite e. rewrite ZMap.gss. esplit; eauto.
      rewrite ZMap.gso; auto.
      apply IHa; simpl; trivial.
      xomega.
      apply IHa; simpl; trivial.
      xomega.
  Qed.

  Lemma real_free_pt_change:
    forall i pt,
      kern_low <= i < kern_high ->
           forall a, 0<= Z.of_nat a <= (kern_high * PgSize - kern_low * PgSize - PgSize) / PgSize ->
                     (i - kern_low) <= Z.of_nat a ->
                     PDT_valid pt i ->
                     PT_unp (Calculate_free_pt a pt) i.
  Proof.
    intros until a.
    unfold PDT_valid, PT_unp.
    induction a; simpl; intros.    
    +
      assert (HT: i = 262144) by xomega.
      subst; trivial; simpl in *.
      unfold Calculate_free_pt_at_i.
      destruct H2 as [pte HPT].
      rewrite HPT. rewrite ZMap.gss.
      esplit; split; eauto.
      rewrite ZMap.gss; trivial.
    +
      destruct (zeq (i - 262144) (Z.of_nat (S a))).
      *
        rewrite <- e. clear IHa.
        replace ((i - 262144) * 4096 + 1073741824) with (i * 4096) by (clear; xomega).
        unfold Calculate_free_pt_at_i.
        apply (real_free_pt_unchange_less _ _ a) in H2.
        destruct H2 as [pte HPT].
        rewrite HPT. rewrite ZMap.gss.
        esplit; split; eauto.
        rewrite ZMap.gss; trivial.
        xomega.
      *
        assert (HT1: 0 <= Z.of_nat a <= (983040 * 4096 - 262144 * 4096 - 4096) / 4096).
        {
          simpl; xomega.
        }
        assert (HT2: i - 262144 <= Z.of_nat a) by xomega.
        specialize (IHa HT1 HT2 H2).
        clear HT1 HT2 H2.
        unfold Calculate_free_pt_at_i.
        destruct (zeq (PDX (i * 4096)) (PDX (Z.of_nat (S a) * 4096 + 1073741824))).
        rewrite e in *. 
        destruct IHa as [pte [HPT HPTE]].
        rewrite HPT.
        rewrite ZMap.gss. esplit; split; eauto.
        destruct (zeq (PTX (i * 4096)) (PTX (Z.of_nat (S a) * 4096 + 1073741824))).
        rewrite e0; rewrite ZMap.gss; trivial.
        rewrite ZMap.gso; auto.
        destruct (ZMap.get (PDX (Z.of_nat (S a) * 4096 + 1073741824))
                           (Calculate_free_pt a pt)).
        rewrite ZMap.gso; auto.
        trivial.
  Qed.

  Lemma real_free_pt_valid: 
    forall ptp n, PT_common (ZMap.get n ptp) -> 
                  PDT_usr (ZMap.get n ptp) ->  PT_init (real_free_pt ptp n).
  Proof.
    unfold PT_init, PT_common, PDT_usr.
    split; intros.
    +
      specialize (H _ H1).
      unfold real_free_pt, PT_pos in *.
      erewrite real_free_pt_unchange; trivial.
      simpl; clear; xomega.
    +
      unfold real_free_pt.
      apply real_free_pt_change; auto; simpl; xomega.
  Qed.

End Real_FreePT.
