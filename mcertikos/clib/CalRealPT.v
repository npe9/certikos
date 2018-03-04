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
Require Import CalRealPTPool.
Require Import CLemmas.

Section Real_PT.

  Function Calculate_pt_kern_at_i (i: Z) (ptp: PMapPool) : PMapPool :=
    (ZMap.set 0
              (ZMap.set i PDEID (ZMap.get 0 ptp)) ptp).

  Fixpoint Calculate_pt_kern (i: nat) (ptp: PMapPool) : PMapPool :=
    match i with
      | O => Calculate_pt_kern_at_i (kern_low / one_k) ptp
      | S k => Calculate_pt_kern_at_i (Z.of_nat (S k) + kern_low / one_k) (Calculate_pt_kern k ptp)
    end.

  Definition real_pt (ptp: PMapPool) := 
    (Calculate_pt_kern (Z.to_nat ((kern_high - kern_low) / one_k - 1)) (real_ptp ptp)).

  Lemma calculate_pt_kern_at_i_0_PDEID: forall i ptp,
    ZMap.get i (ZMap.get 0 (Calculate_pt_kern_at_i i ptp)) = PDEID.
  Proof.
    intros.
    unfold Calculate_pt_kern_at_i.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    reflexivity.
  Qed.

  Lemma calculate_pt_kern_at_i_0_local: forall i j ptp,
    j <> i ->   
      ZMap.get j (ZMap.get 0 (Calculate_pt_kern_at_i i ptp)) = 
      ZMap.get j (ZMap.get 0 ptp).
  Proof.
    intros.
    unfold Calculate_pt_kern_at_i.
    rewrite ZMap.gss.
    rewrite ZMap.gso.
    reflexivity.
    assumption.
  Qed.

  Lemma calculate_pt_kern_at_i_local: forall i j ptp,
    j <> 0 -> ZMap.get j (Calculate_pt_kern_at_i i ptp) = ZMap.get j ptp.
  Proof.
    intros. 
    unfold Calculate_pt_kern_at_i.
    rewrite ZMap.gso.
    reflexivity.
    assumption.
  Qed.

  Lemma calculate_pt_kern_0_PDEID: forall i j ptp,
    kern_low / one_k <= j <= Z.of_nat i + kern_low/one_k ->
      ZMap.get j (ZMap.get 0 (Calculate_pt_kern i ptp)) = PDEID.
  Proof.
    intros.
    induction i.
    {
      simpl.
      assert (j = (262144 / 1024)).
      xomega.
      rewrite H0.
      rewrite calculate_pt_kern_at_i_0_PDEID.
      reflexivity.
    }
    {
      simpl.
      assert ((Z.pos (Pos.of_succ_nat i + 256)) = Z.of_nat (S i) + kern_low / one_k).
      reflexivity.
      rewrite H0.
      destruct (Z.eq_dec j (Z.of_nat (S i) + kern_low / one_k)).
      rewrite <- e.
      rewrite calculate_pt_kern_at_i_0_PDEID.
      reflexivity.
      rewrite calculate_pt_kern_at_i_0_local.
      apply IHi.
      xomega.      
      assumption.
    }
  Qed.

  Lemma calculate_pt_kern_0_local: forall i j ptp,
    j < kern_low / one_k \/ j > Z.of_nat i + kern_low/one_k ->
      ZMap.get j (ZMap.get 0 (Calculate_pt_kern i ptp)) = ZMap.get j (ZMap.get 0 ptp).
  Proof.
    intros.
    induction i.
    {
      simpl.
      rewrite calculate_pt_kern_at_i_0_local.
      reflexivity.
      destruct (Z.eq_dec j (262144 / 1024)).
      rewrite <- e in H.
      destruct H; simpl in H; xomega.
      assumption.      
    }
    {
      simpl.
      replace (Z.pos (Pos.of_succ_nat i + 256)) with (Z.of_nat (S i) + kern_low / one_k).
      rewrite calculate_pt_kern_at_i_0_local.
      apply IHi.
      destruct H.
      left.      
      assumption.
      right.
      xomega.
      destruct (Z.eq_dec j (Z.of_nat (S i) + 262144 / 1024)).
      rewrite <- e in H.
      xomega.
      assumption.      
      reflexivity.
    }
  Qed.  

  Lemma calculate_pt_kern_local: forall i j ptp,
    j <> 0 -> ZMap.get j (Calculate_pt_kern i ptp) = ZMap.get j ptp. 
  Proof.
    intros.
    induction i.
    simpl.
    rewrite calculate_pt_kern_at_i_local.
    reflexivity.
    assumption.
    simpl.
    rewrite calculate_pt_kern_at_i_local.    
    assumption.
    assumption.
  Qed.

  Lemma real_pt_0_PDEID: forall i ptp,
    kern_low/one_k <= i < kern_high/one_k ->
      ZMap.get i (ZMap.get 0 (real_pt ptp)) = PDEID.
  Proof.
    intros.
    unfold real_pt.
    rewrite calculate_pt_kern_0_PDEID.
    reflexivity.
    xomega.
  Qed.

  Lemma real_pt_0_local: forall j ptp,
    j < kern_low / one_k \/ j >= kern_high/one_k ->
      ZMap.get j (ZMap.get 0 (real_pt ptp)) = ZMap.get j (ZMap.get 0 (real_ptp ptp)).
  Proof.
    intros.
    unfold real_pt.
    rewrite calculate_pt_kern_0_local.
    reflexivity.
    destruct H.
    left.
    assumption.
    right.
    xomega.
  Qed.

  Lemma real_pt_PMap_common_0: forall ptp,
     PMap_common (ZMap.get 0 ((real_pt) ptp)).
  Proof.
    intros.
    unfold PMap_common.
    unfold real_pt.
    intros.
    unfold PDE_kern.
    rewrite calculate_pt_kern_0_local.
    assert (tmp: PMap_common (ZMap.get 0 (real_ptp ptp))).
    apply real_ptp_PMap_common_nonkern.
    xomega.
    unfold PMap_common in tmp.
    unfold PDE_kern in tmp.
    apply tmp.
    assumption.
    unfold PDX.
    replace (i * 4096 / (4096 * 1024)) with (i / 1024).
    destruct H.
    left.
    xomega.    
    right.
    xomega.
    xomega.
  Qed.

  Lemma real_pt_nonkern_local: forall i ptp, i <> 0 ->
     ZMap.get i (real_pt ptp) = ZMap.get i (real_ptp ptp).
  Proof.
    intros.
    unfold real_pt.
    rewrite calculate_pt_kern_local.
    reflexivity.
    assumption.
  Qed.

  Lemma real_pt_PMap_common_local:
    forall ptp i,
      0 < i < 64 ->
      PMap_common (ZMap.get i (real_pt ptp)).
  Proof.
    intros.
    rewrite real_pt_nonkern_local.
    apply real_ptp_PMap_common_nonkern.
    xomega.
    xomega.
  Qed.

  (* Required by layer definition *)
  Lemma real_pt_PMap_valid:
    forall ptp i,
      0 <= i < 64 ->
      PMap_valid (ZMap.get i (real_pt ptp)).
  Proof.
    intros.
    unfold PMap_valid.
    split.

    { 
      destruct (Z.eq_dec i 0).
        rewrite e.
        apply real_pt_PMap_common_0.
        apply real_pt_PMap_common_local.
        xomega.
    }
    {
      destruct (Z.eq_dec i 0).
      {
        rewrite e.
        unfold PMap_usr.
        unfold PDE_usr.
        intros.
        right.
        left.
        rewrite real_pt_0_PDEID.
        reflexivity.
        unfold PDX.
        xomega.
      }
      {
        rewrite real_pt_nonkern_local.
        unfold PMap_usr.
        unfold PDE_usr.
        intros.
        assert (tmp: ZMap.get (PDX (i0 * 4096)) (ZMap.get i (real_ptp ptp)) = PDEUnPresent \/
   ZMap.get (PDX (i0 * 4096)) (ZMap.get i (real_ptp ptp)) = PDEID).
        apply real_ptp_usr.
        unfold PDX.
        xomega.
        assumption.
        destruct tmp.
        left.
        assumption.
        right.
        left.
        assumption.
        assumption.
      }      
    }
  Qed.

  (* Required by layer definition *)
  Lemma real_pt_PMap_kern:
    forall ptp,
      PMap_kern (ZMap.get 0 (real_pt ptp)).
  Proof.
    unfold PMap_kern.
    unfold PDE_kern.
    intros.
    apply real_pt_0_PDEID.
    unfold PDX.
    xomega.
  Qed.

  (* Required by layer definition *)
  Lemma real_pt_consistent_pmap:
    forall ptp p a n,
      consistent_pmap (real_pt ptp) p a n.
  Proof.
    intros.
    unfold consistent_pmap.
    intros.
    destruct (Z.eq_dec i 0).
    {
      rewrite e in *.
      destruct (zle_lt (kern_low/one_k) (PDX j) (kern_high/one_k)).
      rewrite real_pt_0_PDEID in H1.
      discriminate H1.
      assumption.
      assert (tmp : ZMap.get (PDX j) (ZMap.get 0 (real_ptp ptp)) = PDEUnPresent \/
        ZMap.get (PDX j) (ZMap.get 0 (real_ptp ptp)) = PDEID).
      apply real_ptp_usr.
      unfold PDX in *.
      xomega.
      xomega.
      rewrite real_pt_0_local in H1.
      destruct tmp; rewrite H2 in H1; discriminate H1.
      unfold PDX in *.
      destruct o.
      left.
      xomega.
      right.
      assumption.
    }
    {
      assert (ZMap.get (PDX j) (ZMap.get i (real_pt ptp)) = PDEUnPresent \/ 
        ZMap.get (PDX j) (ZMap.get i (real_pt ptp)) = PDEID).
      rewrite real_pt_nonkern_local.
      apply real_ptp_usr.
      unfold PDX.
      xomega.
      assumption.
      assumption.
      destruct H2; rewrite H2 in H1; discriminate H1.
    }
  Qed.

  (* Required by layer definition *)
  Lemma real_pt_consistent_pmap_domain:
    forall ptp p a n,
      consistent_pmap_domain (real_pt ptp) p a n.
  Proof.
    intros.
    unfold consistent_pmap_domain.
    intros.
    destruct (Z.eq_dec i 0).
    {
      rewrite e in *.
      destruct (zle_lt (kern_low/one_k) (PDX j) (kern_high/one_k)).
      rewrite real_pt_0_PDEID in H1.
      discriminate H1.
      assumption.
      assert (tmp : ZMap.get (PDX j) (ZMap.get 0 (real_ptp ptp)) = PDEUnPresent \/
        ZMap.get (PDX j) (ZMap.get 0 (real_ptp ptp)) = PDEID).
      apply real_ptp_usr.
      unfold PDX in *.
      xomega.
      xomega.
      rewrite real_pt_0_local in H1.
      destruct tmp; rewrite H3 in H1; discriminate H1.
      unfold PDX in *.
      destruct o.
      left.
      xomega.
      right.
      assumption.
    }
    {
      assert (ZMap.get (PDX j) (ZMap.get i (real_pt ptp)) = PDEUnPresent \/ 
        ZMap.get (PDX j) (ZMap.get i (real_pt ptp)) = PDEID).
      rewrite real_pt_nonkern_local.
      apply real_ptp_usr.
      unfold PDX.
      xomega.
      assumption.
      assumption.
      destruct H3; rewrite H3 in H1; discriminate H1.
    }
  Qed.

  (*Lemma original_valid: 
    forall i ptp, 0 <= i < kern_low \/ kern_high <= i < maxpage ->
                  exists pte : PTE,
                    ZMap.get (i / 1024)  (ZMap.get 0 (real_ptp ptp)) = PDTValid pte /\
                    ZMap.get (i * PgSize / PgSize mod 1024) pte = PTValid (i * 4096) (PTK true).
  Proof.
    intros i ptp irange.
    generalize (real_PTP_init_valid ptp); intro.
    unfold PTP_init, PT_init, PT_common, PT_pos in H.
    assert(tmp: 0 <= 0 < 64) by omega.
    generalize (H 0 tmp); intro.
    destruct H0.
    generalize (H0 i irange); intro.
    unfold PDX, PTX in H2.
    simpl in H2.
    change 4194304 with (4096 * one_k) in H2.
    rewrite <- Zdiv_Zdiv in H2; try omega.
    rewrite Z_div_mult_full in *; try omega.
    assumption.
  Qed.

  Lemma original_pdt_valid: 
    forall i ptp, 0 <= i < maxpage -> exists pdt, ZMap.get (PDX (i * PgSize)) (ZMap.get 0 (real_ptp ptp)) = PDTValid pdt.
  Proof.
    intros i ptp irange.
    generalize (real_PTP_init_valid ptp); intro.
    unfold PTP_init, PT_init, PT_common, PT_pos, PT_unp in H.
    assert(tmp: 0 <= 0 < 64) by omega.
    generalize (H 0 tmp); intro.
    destruct H0.
    assert(262144 <= i < 983040 \/ 0 <= i < 262144 \/ 983040 <= i < 1048576) by omega.
    Caseeq H2; intro.
    generalize (H1 i H2); intro.
    destruct H3.
    destruct H3.
    esplit; eassumption.
    generalize (H0 i H2); intro.
    destruct H3.
    destruct H3.
    esplit; eassumption.
  Qed.

  Lemma real_PT_common_valid: forall ptp, PT_common (real_pt ptp).
  Proof.
    generalize max_unsigned_val; intro muval.
    unfold PT_common, PT_pos, real_pt.
    intros; unfold PDX.
    replace (i * 4096 / (4096 * one_k)) with (i / one_k); [|xomega].
    assert(H1: 1073741824 / one_k > i / one_k \/ i / one_k > (720895 / 4096 + kern_low) / one_k) by (simpl; xomega).
    change (1073741824) with (4026527744 - 720895 * PgSize) in H1 at 1.
    assert(ub: 720895 <= 720895) by omega.
    change ((4026527744 - 262144 * 4096)/4096) with 720895.
    rewrite <- Z2Nat.id with 720895 in H1; try omega.
    rewrite <- Z2Nat.id in ub at 1; try omega.
    induction (Z.to_nat 720895).
    simpl in *.
    unfold Calculate_pt_kern_at_i.
    destruct (ZMap.get (PDX 1073741824) (ZMap.get 0 (real_ptp ptp))).
    rewrite ZMap.gss.
    unfold PDX, PTX; simpl.
    rewrite ZMap.gso.
    apply original_valid; assumption.
    change (1073741824 / 4194304) with 256.
    intro HT.
    Caseeq H; intro.
    assert(i / one_k <= 255) by xomega.
    rewrite HT in *; omega.
    assert(i / one_k >= 960) by xomega.
    rewrite HT in *; omega.

    apply original_valid; assumption.

    Opaque Z.of_nat.
    simpl.
    unfold Calculate_pt_kern_at_i.
    assert(tcase: i / one_k = PDX (Z.of_nat (S n) * 4096 + (kern_low * PgSize)) \/ i / one_k <> PDX (Z.of_nat (S n) * 4096 + (kern_low * PgSize))) by omega.
    Caseeq tcase; intro.
    assert(kern_low <= i < kern_high).
    {
      unfold PDX in H0.
      simpl in H0.
      assert(tmp: (Z.of_nat (S n) * 4096 + 1073741824) / 4194304 = (Z.of_nat (S n) + 262144) / one_k).
      {
        change 4194304 with (PgSize * one_k).
        rewrite <- Zdiv_Zdiv; try omega.
        change 1073741824 with (262144 * PgSize).
        rewrite Z_div_plus_full; try omega.
        rewrite Z_div_mult_full; try omega.
      }
      rewrite tmp in H0.
      split.
      assert((Z.of_nat (S n) + 262144) / one_k >= 262144 / one_k) by
          (apply Z_div_ge; omega).
      
      rewrite <- H0 in H2.
      assert(~ i <= kern_low - 1).
      {
        intro.
        assert(i / one_k <=  262143 / one_k) by
            (apply Z_div_le; omega).
        change (262143 / one_k) with 255 in H4.
        change (262144 / one_k) with 256 in H2.
        omega.
      }
      omega.
      assert((Z.of_nat (S n) + 262144) / one_k <= 983039 / one_k) by
          (apply Z_div_le; omega).
      rewrite <- H0 in H2.
      assert(~ i >= kern_high).
      {
        intro.
        assert(i / one_k >=  983040 / one_k) by
            (apply Z_div_ge; omega).
        change (983040 / one_k) with 960 in H4.
        change (983039 / one_k) with 959 in H2.
        omega.
      }
      omega.
    }
    Caseeq H; intro; omega.

    assert((4026527744 - (Z.of_nat n + 1) * 4096) / one_k <= (4026527744 - Z.of_nat n * 4096) / one_k) by
        (apply Z_div_le; omega).
    assert(((Z.of_nat n + 1)/PgSize + kern_low) / one_k >= ((Z.of_nat n)/PgSize + kern_low) / one_k).
    {
      apply Z_div_ge; try omega.
      assert ((Z.of_nat n + 1) / 4096 >= Z.of_nat n / 4096) by (apply Z_div_ge; omega).
      omega.
    }
    destruct(ZMap.get (PDX (Z.of_nat (S n) * 4096 + 1073741824)) (ZMap.get 0 (Calculate_pt_kern n (real_ptp ptp)))).
    rewrite ZMap.gss.
    rewrite ZMap.gso; try assumption.
    unfold PTX.
    apply IHn.
    rewrite Nat2Z.inj_succ in H1, ub, H0.
    unfold Z.succ, PDX in *.
    Caseeq H1; intro.
    left; omega.
    right; omega.
    rewrite Nat2Z.inj_succ in H1, ub, H0.
    unfold Z.succ in *.
    omega.
    apply IHn.
    rewrite Nat2Z.inj_succ in H1, ub, H0.
    unfold Z.succ in *.
    unfold PDX in *.
    Caseeq H1; intro.
    left; omega.
    right; omega.
    rewrite Nat2Z.inj_succ in H1, ub, H0.
    unfold Z.succ in *.
    omega.
  Qed.

  Lemma real_PT_kern_pdt_valid:
    forall i ptp n, 0 <= i < maxpage ->
                    exists pdt, ZMap.get (PDX (i * PgSize)) (ZMap.get 0 (Calculate_pt_kern n (real_ptp ptp))) = PDTValid pdt.
  Proof.
    induction n; intros; simpl.
    unfold Calculate_pt_kern_at_i.
    assert(0 <= 262144 < maxpage) by omega.
    change 1073741824 with (262144 * PgSize).
    destruct (original_pdt_valid 262144 ptp H0).
    rewrite H1.
    rewrite ZMap.gss.
    assert (icase: PDX (i * 4096) = PDX (262144 * 4096) \/ PDX (i * 4096) <> PDX (262144 * 4096)) by omega.
    Caseeq icase; intro.
    rewrite H2.
    rewrite ZMap.gss.
    esplit; reflexivity.
    rewrite ZMap.gso; try assumption.
    apply original_pdt_valid.
    omega.
    simpl.
    unfold Calculate_pt_kern_at_i.
    destruct (ZMap.get (PDX (Z.of_nat (S n) * 4096 + 1073741824))
                       (ZMap.get 0 (Calculate_pt_kern n (real_ptp ptp)))).
    rewrite ZMap.gss.
    assert(icase: PDX (i * 4096) = PDX (Z.of_nat (S n) * 4096 + 1073741824) 
                  \/ PDX (i * 4096) <> PDX (Z.of_nat (S n) * 4096 + 1073741824)) by omega.
    Caseeq icase; intro.
    rewrite H0.
    rewrite ZMap.gss.
    esplit; reflexivity.
    rewrite ZMap.gso; try assumption.
    apply IHn; omega.
    apply IHn; omega.
  Qed.

  Lemma real_PT_kern_valid: forall ptp, PT_kern (real_pt ptp).
  Proof.
    generalize max_unsigned_val; intro muval.
    unfold PT_kern, PT_pos, real_pt, PDX.
    intros.
    change ((4026527744 - 262144 * 4096) / 4096) with 720895.
    assert(ir: 262144 <= i <= 720895 + 262144) by omega.
    assert(ub: 720895 <= 720895) by omega.
    rewrite <- Z2Nat.id with 720895 in ir; try omega.
    rewrite <- Z2Nat.id in ub at 1; try omega.

    generalize i, H, ir, ub.
    clear i H ir ub.
    induction (Z.to_nat 720895).
    simpl.
    rewrite Nat2Z.inj_0.
    intros.
    replace i with 262144 by omega.
    unfold PTX; simpl.
    unfold Calculate_pt_kern_at_i.
    assert(0 <= 262144 < maxpage) by omega.
    change 1073741824 with (262144 * PgSize).
    destruct (original_pdt_valid 262144 ptp H0).
    rewrite H1.
    unfold PDX; simpl.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gss.
    reflexivity.

    Opaque Z.of_nat.
    intros.
    simpl.
    unfold Calculate_pt_kern_at_i.
    replace (Z.of_nat (S n) * 4096 + 1073741824) with ((Z.of_nat (S n) + 262144) * PgSize) by omega.
    assert(tcase: i = Z.of_nat (S n) + 262144 \/ i <> Z.of_nat (S n) + 262144) by omega.
    Caseeq tcase; intro.
    rewrite <- H0.
    assert(tmp: 0 <= i < maxpage) by omega.
    destruct (real_PT_kern_pdt_valid i ptp n tmp) as [pdt pdtvalid].
    rewrite pdtvalid.
    unfold PDX; simpl.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gss.
    reflexivity.

    rewrite Nat2Z.inj_succ in ir, ub, H0.
    rewrite Nat2Z.inj_succ.
    unfold Z.succ in *.
    assert(262144 <= i <= Z.of_nat n + 262144) by omega.
    assert(Z.of_nat n <= 720895) by omega.
    generalize (IHn i H H1 H2); intro.
    destruct H3 as [pdt pdtvalid].
    destruct pdtvalid as [pdtvalid ptevalid].
    unfold PDX; simpl in *.
    assert(tcase: i * 4096 / 4194304 = (Z.of_nat n + 1 + 262144) * 4096 / 4194304 
                  \/ i * 4096 / 4194304 <> (Z.of_nat n + 1 + 262144) * 4096 / 4194304) by omega.
    Caseeq tcase; intro.
    rewrite <- H3.
    rewrite pdtvalid.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    assert(tcase: PTX (i * 4096) = PTX ((Z.of_nat n + 1 + 262144) * 4096) \/ PTX (i * 4096) <> PTX ((Z.of_nat n + 1 + 262144) * 4096)) by omega.
    Caseeq tcase; intro.
    rewrite H4.
    rewrite ZMap.gss.
    unfold PTX in *.
    assert(Z.of_nat n + 1 + 262144 = i).
    {
      change 4194304 with (4096 * one_k) in *.
      rewrite <- Zdiv_Zdiv in H3; try omega.
      rewrite <- Zdiv_Zdiv in H3; try omega.
      rewrite Z_div_mult_full in *; try omega.
      rewrite Z_div_mult_full in *; try omega.
      rewrite Zmod_eq_full in H4; try omega.
      rewrite Zmod_eq_full in H4; try omega.
    }
    rewrite H5; trivial.
    rewrite ZMap.gso; try assumption.
    
    destruct (ZMap.get ((Z.of_nat n + 1 + 262144) * 4096 / 4194304)
                       (ZMap.get 0 (Calculate_pt_kern n (real_ptp ptp)))).
    rewrite ZMap.gss.
    rewrite ZMap.gso; try assumption.
    apply IHn; omega.
    apply IHn; omega.
  Qed.*)

End Real_PT.
