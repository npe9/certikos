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

Section Real_PTP.

  Opaque Z.of_nat Z.to_nat.

  Function Calculate_PDE_at_i (i: Z) (index: Z) (ptp: PMapPool) : PMapPool := 
    if zle (kern_low / one_k) i then
      if zlt i (kern_high / one_k) then 
        (ZMap.set index (ZMap.set i PDEUnPresent (ZMap.get index ptp)) ptp)
      else (ZMap.set index (ZMap.set i PDEID (ZMap.get index ptp)) ptp)
    else (ZMap.set index (ZMap.set i PDEID (ZMap.get index ptp)) ptp).

  Fixpoint Calculate_PDE (i: nat) (index: Z) (ptp: PMapPool) : PMapPool :=
    match i with
      | O => Calculate_PDE_at_i 0 index ptp
      | S k => Calculate_PDE_at_i (Z.of_nat (S k)) index (Calculate_PDE k index ptp)
    end.

  Function Calculate_pt_comm_at_i (i: Z) (ptp: PMapPool) : PMapPool :=
    (Calculate_PDE (Z.to_nat (maxpage / one_k) - 1) i ptp).

  Fixpoint Calculate_pt_comm (i: nat) (ptp: PMapPool) : PMapPool := 
    match i with
      | O => Calculate_pt_comm_at_i 0 ptp
      | S k => Calculate_pt_comm_at_i (Z.of_nat (S k)) (Calculate_pt_comm k ptp)
    end.

  Definition real_ptp (ptp: PMapPool) := Calculate_pt_comm (Z.to_nat (num_proc - 1)) ptp.

  Lemma calculate_PDE_at_i_local: forall i index ptp j,
    i <> j ->
      ZMap.get i
        (ZMap.get index (Calculate_PDE_at_i j index ptp)) = 
      ZMap.get i (ZMap.get index ptp).
  Proof.
    intros.
    unfold Calculate_PDE_at_i.      
    destruct (zle (262144 / 1024) j).
    destruct (zlt j (983040/1024)).
    {
      rewrite ZMap.gss.
      rewrite ZMap.gso.
      reflexivity.
      assumption.
    }
    {
      rewrite ZMap.gss.
      rewrite ZMap.gso.
      reflexivity.
      assumption.
    }
    {
      rewrite ZMap.gss.
      rewrite ZMap.gso.
      reflexivity.
      assumption.
    }
  Qed.

  Lemma calculate_PDE_at_i_local_index: forall i index index' ptp,
    index' <> index ->
      ZMap.get index' (Calculate_PDE_at_i i index ptp) = ZMap.get index' ptp.
  Proof.
    intros.
    unfold Calculate_PDE_at_i.
    destruct (zle (262144 / 1024) i).
    destruct (zlt i (983040 / 1024)).
    rewrite ZMap.gso.
    reflexivity.
    assumption.    
    rewrite ZMap.gso.
    reflexivity.
    assumption.
    rewrite ZMap.gso.
    reflexivity.
    assumption.
  Qed.

  Lemma calculate_PDE_at_i_pmap_common: forall i index ptp, 
    0 <= i < kern_low \/ kern_high <= i < maxpage ->
      PDE_kern (ZMap.get index (Calculate_PDE_at_i (i/one_k) index ptp)) i. 
  Proof.
    intros.
    unfold Calculate_PDE_at_i.
    destruct H as [H1 | H2]. 
    {
      destruct H1.
      rewrite zle_false.
      rewrite ZMap.gss.
      unfold PDE_kern.
      unfold PDX.      
      simpl.
      replace (i * 4096 / 4194304) with (i / 1024).
      rewrite ZMap.gss.      
      reflexivity.
      xomega.
      xomega.
    }
    {
      destruct H2.   
      rewrite zle_true.
      rewrite zlt_false.
      rewrite ZMap.gss.
      unfold PDE_kern.
      unfold PDX.
      simpl.
      replace (i * 4096 / 4194304) with (i / 1024).
      rewrite ZMap.gss.
      reflexivity.
      xomega.
      xomega.
      xomega.
    }
  Qed.

  Lemma calculate_PDE_pmap_common: forall i j index ptp,
    0 <= i < kern_low \/ kern_high <= i < maxpage ->
      i / one_k <= Z.of_nat j ->
      PDE_kern (ZMap.get index (Calculate_PDE j index ptp)) i.
  Proof.
    intros.
    induction j as [|j' iH].
    {
      unfold Calculate_PDE.
      replace 0 with (i / 1024). 
      apply calculate_PDE_at_i_pmap_common.
      left.
      xomega.
      xomega.
    }
    {
      simpl.
      destruct (Z.eq_dec (i / 1024) (Z.of_nat (S j'))).
      {
        unfold Calculate_PDE_at_i.
        destruct H.
        rewrite zle_false.
        rewrite ZMap.gss.
        unfold PDE_kern.
        unfold PDX.
        replace (i * 4096 / (4096 * 1024)) with (i / 1024).
        rewrite e.
        rewrite ZMap.gss.
        reflexivity.
        xomega.
        xomega.
        rewrite zle_true.
        rewrite zlt_false.
        rewrite ZMap.gss.
        unfold PDE_kern.
        unfold PDX.
        replace (i * 4096 / (4096 * 1024)) with (i / 1024).
        rewrite e.
        rewrite ZMap.gss.
        reflexivity.
        xomega.
        xomega.
        xomega.
      }
      {
        unfold PDE_kern.
        rewrite calculate_PDE_at_i_local.
        unfold PDE_kern in iH.
        apply iH.
        xomega.
        unfold PDX.
        replace (i * 4096 / (4096 * 1024)) with (i / 1024).
        assumption.
        xomega.
      }
    }
  Qed.

  Lemma calculate_PDE_comm_local: forall i ptp index index',
    index' <> index ->
      ZMap.get index' (Calculate_PDE i index ptp) = 
      ZMap.get index' ptp.
  Proof.
    intros.
    induction i.
    {
      simpl.
      rewrite calculate_PDE_at_i_local_index.      
      reflexivity.
      assumption.
    }
    {
      simpl.
      rewrite calculate_PDE_at_i_local_index.
      assumption.
      assumption.
    }
  Qed.

  Lemma calculate_pt_comm_at_i_pmap_common: forall i ptp,
    PMap_common (ZMap.get i (Calculate_pt_comm_at_i i ptp)).
  Proof.
    unfold Calculate_pt_comm_at_i.
    unfold PMap_common.
    intros.
    apply calculate_PDE_pmap_common.
    assumption.
    xomega.
  Qed.

  Lemma calculate_pt_comm_at_i_local: forall i j ptp,
    i <> j ->
      ZMap.get i (Calculate_pt_comm_at_i j ptp) = ZMap.get i ptp.
  Proof.
    intros.
    unfold Calculate_pt_comm_at_i.
    rewrite calculate_PDE_comm_local.
    reflexivity.
    assumption.
  Qed.

  Lemma calculate_pt_comm_pmap_common: forall i j ptp,
    0 <= i <= (Z.of_nat j) -> PMap_common (ZMap.get i (Calculate_pt_comm j ptp)).
  Proof.
    intros.
    induction j.
    {
      replace i with 0.
      apply calculate_pt_comm_at_i_pmap_common.
      xomega.
    }
    {
      destruct (Z.eq_dec i (Z.of_nat (S j))).
      {
        simpl.
        rewrite <- e.
        apply calculate_pt_comm_at_i_pmap_common.
      }
      {
        simpl.
        rewrite calculate_pt_comm_at_i_local.
        apply IHj.
        xomega.
        assumption.
      }
    }
  Qed.

  Lemma real_ptp_PMap_common_nonkern: forall i ptp,
    0 <= i < 64 ->
      PMap_common (ZMap.get i (real_ptp ptp)).
  Proof.
    intros.
    unfold real_ptp.
    apply calculate_pt_comm_pmap_common.
    xomega.
  Qed.

  Lemma calculate_PDE_at_i_UP_or_ID: forall i index ptp,
    ZMap.get i (ZMap.get index (Calculate_PDE_at_i i index ptp)) = PDEUnPresent \/
    ZMap.get i (ZMap.get index (Calculate_PDE_at_i i index ptp)) = PDEID.
  Proof.
    intros.
    unfold Calculate_PDE_at_i.
    destruct (zle (262144 / 1024) i).
    destruct (zlt i (983040 / 1024)).
    left.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    reflexivity.
    right.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    reflexivity.
    right.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    reflexivity.
  Qed.

  Lemma calculate_PDE_UP_or_ID: forall i j index ptp,
    0 <= j <= Z.of_nat i ->
      ZMap.get j (ZMap.get index (Calculate_PDE i index ptp)) = PDEUnPresent \/
      ZMap.get j (ZMap.get index (Calculate_PDE i index ptp)) = PDEID.
  Proof.
    intros.
    induction i.
    {
      replace j with 0.
      apply calculate_PDE_at_i_UP_or_ID.
      xomega.
    }
    {
      simpl.
      destruct (Z.eq_dec j (Z.of_nat (S i))).
      rewrite <- e.
      apply calculate_PDE_at_i_UP_or_ID.
      rewrite calculate_PDE_at_i_local.
      apply IHi.
      xomega.
      assumption.
    }
  Qed.

  Lemma calculate_pt_comm_at_i_usr: forall i j ptp,
    0 <= j < one_k ->
      ZMap.get j (ZMap.get i (Calculate_pt_comm_at_i i ptp)) = PDEUnPresent \/
      ZMap.get j (ZMap.get i (Calculate_pt_comm_at_i i ptp)) = PDEID.
  Proof.
    intros.
    apply calculate_PDE_UP_or_ID.
    xomega.
  Qed.

  Lemma calculate_pt_comm_usr: forall i j k ptp,
    0 <= j < one_k -> 0 <= k <= Z.of_nat i ->
      ZMap.get j (ZMap.get k (Calculate_pt_comm i ptp)) = PDEUnPresent \/
      ZMap.get j (ZMap.get k (Calculate_pt_comm i ptp)) = PDEID.
  Proof.
    intros.
    induction i.
    {
      replace k with 0.
      apply calculate_pt_comm_at_i_usr.
      assumption.
      xomega.
    }
    {
      destruct (Z.eq_dec k (Z.of_nat (S i))).
      simpl.
      rewrite <- e.
      apply calculate_pt_comm_at_i_usr.
      assumption.
      simpl.
      rewrite calculate_pt_comm_at_i_local.
      apply IHi.
      xomega.
      assumption.
    }
  Qed.

  Lemma real_ptp_usr: forall j k ptp,
    0 <= j < one_k -> 0 <= k < num_proc ->
      ZMap.get j (ZMap.get k (real_ptp ptp)) = PDEUnPresent \/
      ZMap.get j (ZMap.get k (real_ptp ptp)) = PDEID.
  Proof.
    intros.
    unfold real_ptp.
    apply calculate_pt_comm_usr.
    assumption.
    xomega.
  Qed. 


  (*Function Calculate_PDX_at_i (i: Z) (index: Z) (ptp: PMapPool) : PMapPool := 
    (ZMap.set index (ZMap.set i (PDTValid (ZMap.init PTUndef)) (ZMap.get index ptp)) ptp).

  Fixpoint Calculate_PDX (i: nat) (index: Z) (ptp: PMapPool) : PMapPool :=
    match i with
      | O => Calculate_PDX_at_i 0 index ptp
      | S k => Calculate_PDX_at_i (Z.of_nat (S k)) index (Calculate_PDX k index ptp)
    end.

  Function Calculate_PTX_at_i (i: Z) (index: Z) (ptp: PMapPool) : PMapPool := 
    match ZMap.get (PDX i) (ZMap.get index ptp) with 
      | PDTValid pdt =>
        if Z_lt_dec i (kern_low * PgSize)
        then (ZMap.set index (ZMap.set (PDX i) (PDTValid (ZMap.set (PTX i) (PTValid i (PTK true)) pdt)) 
                                       (ZMap.get index ptp)) ptp)
        else if Z_le_dec (kern_high * PgSize) i
             then (ZMap.set index (ZMap.set (PDX i) (PDTValid (ZMap.set (PTX i) (PTValid i (PTK true)) pdt)) 
                                            (ZMap.get index ptp)) ptp)
             else (ZMap.set index (ZMap.set (PDX i) (PDTValid (ZMap.set (PTX i) PTUnPresent pdt)) (ZMap.get index ptp)) ptp)
      | _ => ptp (**r this case should never happen. *)
    end.

  Fixpoint Calculate_PTX (i: nat) (index: Z) (ptp: PMapPool) : PMapPool :=
    match i with
      | O => Calculate_PTX_at_i 0 index ptp
      | S k => Calculate_PTX_at_i (Z.of_nat (S k) * PgSize) index (Calculate_PTX k index ptp)
    end.

  Function Calculate_pt_comm_at_i (i: Z) (ptp: PMapPool) : PMapPool :=
    Calculate_PTX (Z.to_nat ((maxpage * PgSize - PgSize) / PgSize)) i (Calculate_PDX (Z.to_nat (one_k - 1)) i ptp).

  Fixpoint Calculate_pt_comm (i: nat) (ptp: PMapPool) : PMapPool := 
    match i with
      | O => Calculate_pt_comm_at_i 0 ptp
      | S k => Calculate_pt_comm_at_i (Z.of_nat (S k)) (Calculate_pt_comm k ptp)
    end.

  Definition real_ptp (ptp: PMapPool) := Calculate_pt_comm (Z.to_nat (num_proc - 1)) ptp.

  Lemma real_PTP_equiv: 
    forall ptp i,
      (forall i0 : Z, 0 <= i0 < 1048576 ->
                      (0 <= i0 < 262144 \/ 983040 <= i0 <= (Z.of_nat (Z.to_nat 1048575)) ->
                       PT_pos (ZMap.get i (real_ptp ptp)) i0 true) /\
                      (262144 <= i0 < 983040 -> PT_unp (ZMap.get i (real_ptp ptp)) i0)) ->
      (forall i0 : Z,
         0 <= i0 < 262144 \/ 983040 <= i0 < 1048576 ->
         PT_pos (ZMap.get i (real_ptp ptp)) i0 true) /\
      (forall i0 : Z,
         262144 <= i0 < 983040 -> PT_unp (ZMap.get i (real_ptp ptp)) i0).
  Proof.
    rewrite Z2Nat.id; try omega.
    intros.
    split.
    intros.
    assert(0 <= i0 < 1048576) by omega.
    destruct (H i0 H1).
    apply H2; omega.
    intros.
    assert(0 <= i0 < 1048576) by omega.
    destruct (H i0 H1).
    apply H3; omega.
  Qed.

  Lemma real_PTP_PDX_pdt_valid: 
    forall ptp i j, 0 <= i < maxpage -> j < num_proc ->
                    exists pdt,
                      ZMap.get (PDX (i * PgSize))
                               (ZMap.get j (Calculate_PDX (Z.to_nat 1023) j ptp)) = PDTValid pdt.
  Proof.
    intros.
    assert(ir: 0 <= PDX (i * 4096) <= 1023) by (unfold PDX; xomega).
    rewrite <- Z2Nat.id with 1023 in ir; try omega.
    induction (Z.to_nat 1023).
    rewrite Nat2Z.inj_0 in ir.
    replace (PDX (i * 4096)) with 0 by omega.
    simpl.
    unfold Calculate_PDX_at_i.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    esplit; reflexivity.
    simpl.
    unfold Calculate_PDX_at_i.
    rewrite ZMap.gss.
    rewrite ZMap.gsspec.
    destruct (ZIndexed.eq (PDX (i * 4096)) (Z.of_nat(S n))).
    esplit; reflexivity.
    rewrite Nat2Z.inj_succ in *.
    unfold Z.succ in *.
    apply IHn; omega.
  Qed.

  Lemma real_PTP_PTX_pdt_valid: 
    forall ptp n i j, 0 <= i < maxpage -> j < num_proc ->
                      exists pdt,
                        ZMap.get (PDX (i * 4096))
                                 (ZMap.get j
                                           (Calculate_PTX n j (Calculate_PDX (Z.to_nat 1023) j ptp))) = PDTValid pdt.
  Proof.
    intros.
    induction n.
    simpl.
    unfold Calculate_PTX_at_i.
    destruct (ZMap.get (PDX 0) (ZMap.get j (Calculate_PDX (Z.to_nat 1023) j ptp))).
    destruct (Z_lt_dec 0 (262144 * 4096)); try omega.
    rewrite ZMap.gss.
    rewrite ZMap.gsspec.
    destruct (ZIndexed.eq (PDX (i * 4096)) (PDX 0)).
    esplit; reflexivity.
    apply real_PTP_PDX_pdt_valid; omega.
    apply real_PTP_PDX_pdt_valid; omega.

    simpl.
    unfold Calculate_PTX_at_i.
    destruct (ZMap.get (PDX (Z.of_nat (S n) * 4096))
                       (ZMap.get j
                                 (Calculate_PTX n j (Calculate_PDX (Z.to_nat 1023) j ptp)))).
    destruct (Z_lt_dec (Z.of_nat (S n) * 4096) (262144 * 4096)).
    rewrite ZMap.gss.
    rewrite ZMap.gsspec.
    destruct (ZIndexed.eq (PDX (i * 4096)) (PDX (Z.of_nat (S n) * 4096))).
    esplit; reflexivity.
    apply IHn.
    destruct (Z_le_dec (983040 * 4096) (Z.of_nat (S n) * 4096)).
    rewrite ZMap.gss.
    rewrite ZMap.gsspec.
    destruct (ZIndexed.eq (PDX (i * 4096)) (PDX (Z.of_nat (S n) * 4096))).
    esplit; reflexivity.
    apply IHn.
    rewrite ZMap.gss.
    rewrite ZMap.gsspec.
    destruct (ZIndexed.eq (PDX (i * 4096)) (PDX (Z.of_nat (S n) * 4096))).
    esplit; reflexivity.
    apply IHn.
    apply IHn.
  Qed.

  Lemma real_PTP_PDX_irrelevant: 
    forall ptp n i j, i <> j ->
                      (ZMap.get i (Calculate_PDX (Z.to_nat 1023) j
                                                 (Calculate_pt_comm n ptp))) = 
                      (ZMap.get i (Calculate_pt_comm n ptp)).
  Proof.
    intros.
    induction (Z.to_nat 1023).
    simpl.
    unfold Calculate_PDX_at_i.
    rewrite ZMap.gso; try assumption.
    reflexivity.
    simpl.
    unfold Calculate_PDX_at_i.
    rewrite ZMap.gso; try assumption.
  Qed.

  Lemma real_PTP_PTX_irrelevant: 
    forall ptp n n0 i j, i <> j ->
                         (ZMap.get i (Calculate_PTX n0 j
                                                    (Calculate_PDX (Z.to_nat 1023) j
                                                                   (Calculate_pt_comm n ptp)))) = 
                         (ZMap.get i (Calculate_pt_comm n ptp)).
  Proof.
    intros.
    induction n0.
    simpl.
    unfold Calculate_PTX_at_i.
    destruct (ZMap.get (PDX 0)
                       (ZMap.get j
                                 (Calculate_PDX (Z.to_nat 1023) j (Calculate_pt_comm n ptp)))).
    destruct (Z_lt_dec 0 (262144 * 4096)); try omega.
    rewrite ZMap.gso; try assumption.
    apply real_PTP_PDX_irrelevant; assumption.
    apply real_PTP_PDX_irrelevant; assumption.
    simpl.
    unfold Calculate_PTX_at_i.
    destruct (ZMap.get (PDX (Z.of_nat (S n0) * 4096))
                       (ZMap.get j
                                 (Calculate_PTX n0 j
                                                (Calculate_PDX (Z.to_nat 1023) j (Calculate_pt_comm n ptp))))).
    destruct (Z_lt_dec (Z.of_nat (S n0) * 4096) (262144 * 4096)).
    rewrite ZMap.gso; try assumption.
    destruct (Z_le_dec (983040 * 4096) (Z.of_nat (S n0) * 4096)).
    rewrite ZMap.gso; try assumption.
    rewrite ZMap.gso; try assumption.
    assumption.
  Qed.

  Lemma real_PTP_PTX_diff: 
    forall i0 n,
      i0 <> Z.of_nat n + 1 ->
      i0 * 4096 / 4194304 = (Z.of_nat n + 1) * 4096 / 4194304 ->
      PTX (i0 * 4096) <> PTX ((Z.of_nat n + 1) * 4096).
  Proof.
    intros.
    unfold PTX; simpl.
    change 4194304 with (4096 * 1024) in H0.
    rewrite <- Zdiv_Zdiv in H0; try omega.
    rewrite Z_div_mult_full in *; try omega.
    intro.
    assert(1024 > 0) by omega.
    generalize (Z_div_mod_eq i0 1024 H2); intro.
    generalize (Z_div_mod_eq (Z.of_nat n + 1) 1024 H2); intro.
    rewrite H0, H1 in H3.
    rewrite <- Zdiv_Zdiv in H3; try omega.
    rewrite Z_div_mult_full in H3; omega.
  Qed.

  Lemma real_PTP_init_valid: forall ptp, PTP_init (real_ptp ptp) 0 num_proc.
  Proof.
    Opaque Z.of_nat Z.to_nat.
    generalize max_unsigned_val; intro muval.
    unfold PTP_init, PT_init, PT_common.
    intros ptp i irange.
    apply real_PTP_equiv.
    unfold PT_pos, PT_unp, real_ptp.
    assert(ir: 0 <= i <= 64 - 1) by omega.
    assert(ub: 64 - 1 < 64) by omega.
    rewrite <- Z2Nat.id with (64 - 1) in ir, ub; try omega.

    induction (Z.to_nat (64 - 1)).
    Case "i: 0".
    rewrite Nat2Z.inj_0 in ir.
    replace i with 0 by omega.
    simpl; unfold Calculate_pt_comm_at_i; simpl.
    
    intros.
    assert(ir1: 0 <= i0 <= 1048575) by omega.
    assert(ub1: 1048575 <= 1048575) by omega.
    rewrite <- Z2Nat.id with 1048575 in ir1; try omega.
    rewrite <- Z2Nat.id in ub1 at 1; try omega.
    change (4294963200 / 4096) with 1048575.
    induction (Z.to_nat 1048575).
    SCase "PTX: 0".
    rewrite Nat2Z.inj_0 in ir1.
    replace i0 with 0 by omega.
    simpl.
    unfold Calculate_PTX_at_i.
    assert(0 <= 0 < maxpage) by omega.
    assert(0 < num_proc) by omega.
    destruct (real_PTP_PDX_pdt_valid ptp 0 0 H0 H1) as [pdt pdtvalid].
    simpl in pdtvalid.
    rewrite pdtvalid.
    split.
    destruct (Z_lt_dec 0 (262144 * 4096)); try omega.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    intro.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gss.
    reflexivity.
    intro; omega.

    SCase "PTX: S n".
    simpl.
    unfold Calculate_PTX_at_i.
    assert(0 < num_proc) by omega.
    assert(0 <= Z.of_nat (S n) < maxpage).
    split.
    apply Nat2Z.is_nonneg.
    omega.

    assert(icase: i0 = Z.of_nat (S n) \/ i0 <> Z.of_nat (S n)) by omega.
    (* i0 = Z.of_nat (S n) *)
    Caseeq icase; intro.
    destruct (real_PTP_PTX_pdt_valid ptp n (Z.of_nat (S n)) 0 H1 H0) as [pdt pdtvalid].
    rewrite pdtvalid.
    simpl.
    rewrite <- H2 in *.
    split.
    intro.
    Caseeq H3; intro.
    destruct (Z_lt_dec (i0 * 4096) 1073741824); try omega.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gss.
    reflexivity.
    destruct (Z_lt_dec (i0 * 4096) 1073741824); try omega.
    destruct (Z_le_dec 4026531840 (i0 * 4096)); try omega.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gss.
    reflexivity.
    intro.
    destruct (Z_lt_dec (i0 * 4096) 1073741824); try omega.
    destruct (Z_le_dec 4026531840 (i0 * 4096)); try omega.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gss.
    reflexivity.

    (* i0 <> Z.of_nat (S n) *)
    split.
    intro.
    rewrite Nat2Z.inj_succ in *.
    unfold Z.succ in *.
    assert (0 <= i0 <= Z.of_nat n) by omega.
    assert (Z.of_nat n <= 1048575) by omega.
    assert (0 <= i0 < 262144 \/ 983040 <= i0 <= Z.of_nat n) by omega.
    destruct (IHn H4 H5).
    destruct (H7 H6) as [pdt pdtvalid].
    destruct pdtvalid as [pdtvalid pdxvalid].
    simpl.

    Caseeq H6; intro.
    unfold PDX in *; simpl in *.
    assert (icase: i0 * 4096 / 4194304 = (Z.of_nat n + 1) * 4096 / 4194304 \/ i0 * 4096 / 4194304 <> (Z.of_nat n + 1) * 4096 / 4194304) by omega.
    Caseeq icase; intro.
    rewrite H9 in *.
    rewrite pdtvalid.
    destruct (Z_lt_dec ((Z.of_nat n + 1) * 4096) 1073741824); try omega.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gso.
    assumption.
    apply real_PTP_PTX_diff; auto.
    destruct (Z_le_dec 4026531840 ((Z.of_nat n + 1) * 4096)); try omega.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gso.
    assumption.
    apply real_PTP_PTX_diff; auto.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gso.
    assumption.
    apply real_PTP_PTX_diff; auto.

    destruct (real_PTP_PTX_pdt_valid ptp n (Z.of_nat n + 1) 0 H1 H0) as [pdt' pdtvalid'].
    unfold PDX in pdtvalid'; simpl in pdtvalid'.
    rewrite pdtvalid'.
    destruct (Z_lt_dec ((Z.of_nat n + 1) * 4096) 1073741824); try omega.
    rewrite ZMap.gss.
    rewrite ZMap.gso; try assumption.
    exists pdt.
    auto.
    destruct (Z_le_dec 4026531840 ((Z.of_nat n + 1) * 4096)); try omega.
    rewrite ZMap.gss.
    rewrite ZMap.gso; try assumption.
    exists pdt.
    auto.
    rewrite ZMap.gss.
    rewrite ZMap.gso; try assumption.
    exists pdt.
    auto.
    
    unfold PDX in *; simpl in *.
    assert (icase: i0 * 4096 / 4194304 = (Z.of_nat n + 1) * 4096 / 4194304 \/ i0 * 4096 / 4194304 <> (Z.of_nat n + 1) * 4096 / 4194304) by omega.
    Caseeq icase; intro.
    rewrite H9 in *.
    rewrite pdtvalid.
    destruct (Z_lt_dec ((Z.of_nat n + 1) * 4096) 1073741824). omega.
    destruct (Z_le_dec 4026531840 ((Z.of_nat n + 1) * 4096)); [|omega]. 
    repeat rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gso.
    assumption.
    apply real_PTP_PTX_diff; auto.

    destruct (real_PTP_PTX_pdt_valid ptp n (Z.of_nat n + 1) 0 H1 H0) as [pdt' pdtvalid'].
    unfold PDX in pdtvalid'; simpl in pdtvalid'.
    rewrite pdtvalid'.
    destruct (Z_lt_dec ((Z.of_nat n + 1) * 4096) 1073741824). omega.
    destruct (Z_le_dec 4026531840 ((Z.of_nat n + 1) * 4096)); [| omega].
    rewrite ZMap.gss.
    rewrite ZMap.gso; try assumption.
    exists pdt.
    auto.

    intro.
    rewrite Nat2Z.inj_succ in *.
    unfold Z.succ in *.
    assert (0 <= i0 <= Z.of_nat n) by omega.
    assert (Z.of_nat n <= 1048575) by omega.
    destruct (IHn H4 H5).
    destruct (H7 H3) as [pdt pdtvalid].
    destruct pdtvalid as [pdtvalid pdxvalid].
    unfold PDX in *; simpl in *.
    assert (icase: i0 * 4096 / 4194304 = (Z.of_nat n + 1) * 4096 / 4194304 \/ i0 * 4096 / 4194304 <> (Z.of_nat n + 1) * 4096 / 4194304) by omega.
    Caseeq icase; intro.
    rewrite H8 in *.
    rewrite pdtvalid.
    destruct (Z_lt_dec ((Z.of_nat n + 1) * 4096) 1073741824).  omega.
    destruct (Z_le_dec 4026531840 ((Z.of_nat n + 1) * 4096)).
    repeat rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gso.
    assumption.
    apply real_PTP_PTX_diff; auto.
    repeat rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gso.
    assumption.
    apply real_PTP_PTX_diff; auto.

    destruct (real_PTP_PTX_pdt_valid ptp n (Z.of_nat n + 1) 0 H1 H0) as [pdt' pdtvalid'].
    unfold PDX in pdtvalid'; simpl in pdtvalid'.
    rewrite pdtvalid'.
    destruct (Z_lt_dec ((Z.of_nat n + 1) * 4096) 1073741824). omega.
    destruct (Z_le_dec 4026531840 ((Z.of_nat n + 1) * 4096)).
    rewrite ZMap.gss.
    rewrite ZMap.gso; try assumption.
    exists pdt.
    auto.
    rewrite ZMap.gss.
    rewrite ZMap.gso; try assumption.
    exists pdt.
    auto.

    Case "i: S n".
    simpl.
    unfold Calculate_pt_comm_at_i.
    simpl.
    assert(icase: i = Z.of_nat (S n) \/ i <> Z.of_nat (S n)) by omega.
    (* i = Z.of_nat (S n) *)
    destruct icase.
    rewrite H.
    change (4294963200 / 4096) with 1048575.
    
    intros.
    assert(ir1: 0 <= i0 <= 1048575) by omega.
    assert(ub1: 1048575 <= 1048575) by omega.
    rewrite <- Z2Nat.id with 1048575 in ir1; try omega.
    rewrite <- Z2Nat.id in ub1 at 1; try omega.

    induction (Z.to_nat 1048575).
    SCase "PTX: 0".
    rewrite Nat2Z.inj_0 in ir1.
    replace i0 with 0 by omega.
    unfold PDX in *; simpl in *.
    unfold Calculate_PTX_at_i.
    assert(0 <= 0 < maxpage) by omega.
    destruct (real_PTP_PDX_pdt_valid (Calculate_pt_comm n ptp) 0 (Z.of_nat (S n)) H1 ub) as [pdt pdtvalid].
    simpl in pdtvalid.
    rewrite pdtvalid.
    split.
    destruct (Z_lt_dec 0 (262144 * 4096)); try omega.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    intro.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gss.
    reflexivity.
    intro; omega.

    SCase "PTX: S n".
    simpl.
    unfold Calculate_PTX_at_i.
    assert(0 <= Z.of_nat (S n0) < maxpage).
    split.
    apply Nat2Z.is_nonneg.
    omega.

    assert(icase: i0 = Z.of_nat (S n0) \/ i0 <> Z.of_nat (S n0)) by omega.
    (* i0 = Z.of_nat (S n0) *)
    Caseeq icase; intro.
    destruct (real_PTP_PTX_pdt_valid (Calculate_pt_comm n ptp) n0 (Z.of_nat (S n0)) (Z.of_nat (S n)) H1 ub) as [pdt pdtvalid].
    rewrite pdtvalid.
    simpl.
    rewrite <- H2 in *.
    split.
    intro.
    Caseeq H3; intro.
    destruct (Z_lt_dec (i0 * 4096) 1073741824); [| omega].
    repeat rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gss.
    reflexivity.
    destruct (Z_lt_dec (i0 * 4096) 1073741824). omega.
    destruct (Z_le_dec 4026531840 (i0 * 4096)); [| omega].
    repeat rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gss.
    reflexivity.
    intro.
    destruct (Z_lt_dec (i0 * 4096) 1073741824). omega.
    destruct (Z_le_dec 4026531840 (i0 * 4096)). omega.
    repeat rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gss.
    reflexivity.

    (* i0 <> Z.of_nat (S n0) *)
    split.
    intro.
    rewrite Nat2Z.inj_succ in *.
    unfold Z.succ in *.
    assert (0 <= i0 <= Z.of_nat n0) by omega.
    assert (Z.of_nat n0 <= 1048575) by omega.
    assert (0 <= i0 < 262144 \/ 983040 <= i0 <= Z.of_nat n0) by omega.
    assert(IHn': (0 <= i0 < 262144 \/ 983040 <= i0 <= Z.of_nat n0 ->
                  exists pte : PTE,
                    ZMap.get (PDX (i0 * 4096))
                             (ZMap.get (Z.of_nat n + 1)
                                       (Calculate_PTX n0 (Z.of_nat n + 1)
                                                      (Calculate_PDX (Z.to_nat 1023) 
                                                                     (Z.of_nat n + 1) (Calculate_pt_comm n ptp)))) =
                    PDTValid pte /\
                    ZMap.get (PTX (i0 * 4096)) pte = PTValid (i0 * 4096) (PTK true)) /\
                 (262144 <= i0 < 983040 ->
                  exists pte : PTE,
                    ZMap.get (PDX (i0 * 4096))
                             (ZMap.get (Z.of_nat n + 1)
                                       (Calculate_PTX n0 (Z.of_nat n + 1)
                                                      (Calculate_PDX (Z.to_nat 1023) 
                                                                     (Z.of_nat n + 1) (Calculate_pt_comm n ptp)))) =
                    PDTValid pte /\ ZMap.get (PTX (i0 * 4096)) pte = PTUnPresent)).
    apply IHn0; try auto.
    intro.
    rewrite H in ir0.
    exfalso.
    omega.
    destruct IHn'.
    destruct (H7 H6) as [pdt pdtvalid].
    destruct pdtvalid as [pdtvalid pdxvalid].
    simpl.

    rewrite Nat2Z.inj_succ in *.
    unfold Z.succ in *.
    Caseeq H6; intro.
    unfold PDX in *; simpl in *.
    assert (icase: i0 * 4096 / 4194304 = (Z.of_nat n0 + 1) * 4096 / 4194304 \/ i0 * 4096 / 4194304 <> (Z.of_nat n0 + 1) * 4096 / 4194304) by omega.
    Caseeq icase; intro.
    unfold PDX in *; simpl in *.
    rewrite H9 in *.
    rewrite pdtvalid.
    destruct (Z_lt_dec ((Z.of_nat n0 + 1) * 4096) 1073741824).
    repeat rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gso.
    assumption.
    apply real_PTP_PTX_diff; auto.
    destruct (Z_le_dec 4026531840 ((Z.of_nat n0 + 1) * 4096)).
    repeat rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gso.
    assumption.
    apply real_PTP_PTX_diff; auto.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gso.
    assumption.
    apply real_PTP_PTX_diff; auto.

    destruct (real_PTP_PTX_pdt_valid (Calculate_pt_comm n ptp) n0 (Z.of_nat n0 + 1) (Z.of_nat n + 1) H1 ub) as [pdt' pdtvalid'].
    unfold PDX in pdtvalid'; simpl in pdtvalid'.
    rewrite pdtvalid'.
    destruct (Z_lt_dec ((Z.of_nat n0 + 1) * 4096) 1073741824).
    rewrite ZMap.gss.
    rewrite ZMap.gso; try assumption.
    exists pdt.
    auto.
    destruct (Z_le_dec 4026531840 ((Z.of_nat n0 + 1) * 4096)).
    rewrite ZMap.gss.
    rewrite ZMap.gso; try assumption.
    exists pdt.
    auto.
    rewrite ZMap.gss.
    rewrite ZMap.gso; try assumption.
    exists pdt.
    auto.
    
    assert (icase: i0 * 4096 / 4194304 = (Z.of_nat n0 + 1) * 4096 / 4194304 \/ i0 * 4096 / 4194304 <> (Z.of_nat n0 + 1) * 4096 / 4194304) by omega.
    unfold PDX in *; simpl in *.
    Caseeq icase; intro.
    rewrite H9 in *.
    rewrite pdtvalid.
    destruct (Z_lt_dec ((Z.of_nat n0 + 1) * 4096) 1073741824). omega.
    destruct (Z_le_dec 4026531840 ((Z.of_nat n0 + 1) * 4096)); [|omega].
    repeat rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gso.
    assumption.
    apply real_PTP_PTX_diff; auto.

    destruct (real_PTP_PTX_pdt_valid (Calculate_pt_comm n ptp) n0 (Z.of_nat n0 + 1) (Z.of_nat n + 1) H1 ub) as [pdt' pdtvalid'].
    unfold PDX in pdtvalid'; simpl in pdtvalid'.
    rewrite pdtvalid'.
    destruct (Z_lt_dec ((Z.of_nat n0 + 1) * 4096) 1073741824). omega.
    destruct (Z_le_dec 4026531840 ((Z.of_nat n0 + 1) * 4096)); [| omega].
    rewrite ZMap.gss.
    rewrite ZMap.gso; try assumption.
    exists pdt.
    auto.

    intro.
    rewrite Nat2Z.inj_succ in *.
    unfold Z.succ in *.
    assert (0 <= i0 <= Z.of_nat n0) by omega.
    assert (Z.of_nat n0 <= 1048575) by omega.
    assert(IHn': (0 <= i0 < 262144 \/ 983040 <= i0 <= Z.of_nat n0 ->
                  exists pte : PTE,
                    ZMap.get (PDX (i0 * 4096))
                             (ZMap.get (Z.of_nat n + 1)
                                       (Calculate_PTX n0 (Z.of_nat n + 1)
                                                      (Calculate_PDX (Z.to_nat 1023) 
                                                                     (Z.of_nat n + 1) (Calculate_pt_comm n ptp)))) =
                    PDTValid pte /\
                    ZMap.get (PTX (i0 * 4096)) pte = PTValid (i0 * 4096) (PTK true)) /\
                 (262144 <= i0 < 983040 ->
                  exists pte : PTE,
                    ZMap.get (PDX (i0 * 4096))
                             (ZMap.get (Z.of_nat n + 1)
                                       (Calculate_PTX n0 (Z.of_nat n + 1)
                                                      (Calculate_PDX (Z.to_nat 1023) 
                                                                     (Z.of_nat n + 1) (Calculate_pt_comm n ptp)))) =
                    PDTValid pte /\ ZMap.get (PTX (i0 * 4096)) pte = PTUnPresent)).
    apply IHn0; try auto.
    intro.
    rewrite H in ir0.
    exfalso.
    omega.
    destruct IHn'.
    destruct (H7 H3) as [pdt pdtvalid].
    destruct pdtvalid as [pdtvalid pdxvalid].
    unfold PDX in *; simpl in *.
    rewrite Nat2Z.inj_succ in *.
    unfold Z.succ in *.
    assert (icase: i0 * 4096 / 4194304 = (Z.of_nat n0 + 1) * 4096 / 4194304 \/ i0 * 4096 / 4194304 <> (Z.of_nat n0 + 1) * 4096 / 4194304) by omega.
    Caseeq icase; intro.
    rewrite H8 in *.
    rewrite pdtvalid.
    destruct (Z_lt_dec ((Z.of_nat n0 + 1) * 4096) 1073741824). omega.
    destruct (Z_le_dec 4026531840 ((Z.of_nat n0 + 1) * 4096)).
    repeat rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gso.
    assumption.
    apply real_PTP_PTX_diff; auto.
    repeat rewrite ZMap.gss.
    esplit.
    split.
    reflexivity.
    rewrite ZMap.gso.
    assumption.
    apply real_PTP_PTX_diff; auto.

    destruct (real_PTP_PTX_pdt_valid (Calculate_pt_comm n ptp) n0 (Z.of_nat n0 + 1) (Z.of_nat n + 1) H1 ub) as [pdt' pdtvalid'].
    unfold PDX in pdtvalid'; simpl in pdtvalid'.
    rewrite pdtvalid'.
    destruct (Z_lt_dec ((Z.of_nat n0 + 1) * 4096) 1073741824). omega.
    destruct (Z_le_dec 4026531840 ((Z.of_nat n0 + 1) * 4096)).
    rewrite ZMap.gss.
    rewrite ZMap.gso; try assumption.
    exists pdt.
    auto.
    rewrite ZMap.gss.
    rewrite ZMap.gso; try assumption.
    exists pdt.
    auto.
    
    (* i <> Z.of_nat (S n) *)
    intros.
    rewrite Nat2Z.inj_succ in H, ir, ub.
    unfold Z.succ in H, ir, ub.
    assert(tmpir: 0 <= i <= Z.of_nat n) by omega.
    assert(tmpub: Z.of_nat n < 64) by omega.

    change (4294963200 / 4096) with 1048575.
    assert(ir1: 0 <= i0 <= 1048575) by omega.
    assert(ub1: 1048575 <= 1048575) by omega.
    rewrite <- Z2Nat.id with 1048575 in ir1; try omega.
    rewrite <- Z2Nat.id in ub1 at 1; try omega.

    induction (Z.to_nat 1048575).
    SCase "PTX: 0".
    rewrite Nat2Z.inj_0 in ir1.
    replace i0 with 0 by omega.
    unfold PDX.
    simpl.
    unfold Calculate_PTX_at_i.
    assert(0 <= 0 < maxpage) by omega.
    rewrite Nat2Z.inj_succ.
    unfold Z.succ.
    destruct (real_PTP_PDX_pdt_valid (Calculate_pt_comm n ptp) 0 (Z.of_nat n + 1) H1 ub) as [pdt pdtvalid].
    simpl in pdtvalid.
    rewrite pdtvalid.
    destruct(IHn tmpir tmpub 0 H1).
    split.
    intro.
    destruct (H2 H4) as [pdt' pdtvalid'].
    destruct (Z_lt_dec 0 (262144 * 4096)); try omega.
    unfold PDX; simpl.
    rewrite ZMap.gso; try assumption.
    rewrite real_PTP_PDX_irrelevant.
    exists pdt'; auto.
    intro.
    rewrite H5 in tmpir; omega.
    intro; omega.

    SCase "PTX: S n".
    simpl.
    unfold Calculate_PTX_at_i.
    assert(0 <= Z.of_nat (S n0) < maxpage).
    split.
    apply Nat2Z.is_nonneg.
    omega.

    rewrite Nat2Z.inj_succ in *.
    rewrite Nat2Z.inj_succ in *.
    unfold Z.succ in *.
    assert(icase: i0 = Z.of_nat n0 + 1 \/ i0 <> Z.of_nat n0 + 1) by omega.
    (* i0 = Z.of_nat (S n0) *)
    Caseeq icase; intro.
    destruct (real_PTP_PTX_pdt_valid (Calculate_pt_comm n ptp) n0 (Z.of_nat n0 + 1) (Z.of_nat n + 1) H1 ub) as [pdt pdtvalid].
    rewrite pdtvalid.
    simpl.
    rewrite <- H2 in *.
    destruct (IHn tmpir tmpub i0 H1).
    clear IHn IHn0.
    split.
    intro.
    Caseeq H5; intro.
    destruct (Z_lt_dec (i0 * 4096) 1073741824); [| omega].
    unfold PDX; simpl.
    rewrite ZMap.gso; try assumption.
    rewrite real_PTP_PTX_irrelevant.
    apply H3.
    omega.
    intro rw; rewrite rw in tmpir; omega.
    destruct (Z_lt_dec (i0 * 4096) 1073741824). omega.
    destruct (Z_le_dec 4026531840 (i0 * 4096)); [| omega].
    unfold PDX; simpl.
    rewrite ZMap.gso; try assumption.
    rewrite real_PTP_PTX_irrelevant.
    apply H3.
    omega.
    intro rw; rewrite rw in tmpir; omega.
    intro.
    destruct (Z_lt_dec (i0 * 4096) 1073741824). omega.
    destruct (Z_le_dec 4026531840 (i0 * 4096)). omega.
    unfold PDX; simpl.
    rewrite ZMap.gso; try assumption.
    rewrite real_PTP_PTX_irrelevant.
    apply H4.
    omega.
    intro rw; rewrite rw in tmpir; omega.

    (* i0 <> Z.of_nat (S n0) *)
    destruct(IHn tmpir tmpub i0 H0).
    clear IHn IHn0.
    split.
    intro.
    unfold PDX; simpl.
    destruct (real_PTP_PTX_pdt_valid (Calculate_pt_comm n ptp) n0 (Z.of_nat n0 + 1) (Z.of_nat n + 1) H1 ub) as [pdt' pdtvalid'].
    unfold PDX in pdtvalid'; simpl in pdtvalid'.
    rewrite pdtvalid'.
    destruct (Z_lt_dec ((Z.of_nat n0 + 1) * 4096) 1073741824).
    rewrite ZMap.gso; try assumption.
    rewrite real_PTP_PTX_irrelevant.
    apply H3.
    apply H5.
    intro rw; rewrite rw in tmpir; omega.
    destruct (Z_le_dec 4026531840 ((Z.of_nat n0 + 1) * 4096)).
    rewrite ZMap.gso; try assumption.
    rewrite real_PTP_PTX_irrelevant.
    apply H3.
    apply H5.
    intro rw; rewrite rw in tmpir; omega.
    rewrite ZMap.gso; try assumption.
    rewrite real_PTP_PTX_irrelevant.
    apply H3.
    apply H5.
    intro rw; rewrite rw in tmpir; omega.

    intro.
    destruct (real_PTP_PTX_pdt_valid (Calculate_pt_comm n ptp) n0 (Z.of_nat n0 + 1) (Z.of_nat n + 1) H1 ub) as [pdt' pdtvalid'].
    rewrite pdtvalid'.
    unfold PDX; simpl.
    destruct (Z_lt_dec ((Z.of_nat n0 + 1) * 4096) 1073741824). omega.
    destruct (Z_le_dec 4026531840 ((Z.of_nat n0 + 1) * 4096)).
    rewrite ZMap.gso; try assumption.
    rewrite real_PTP_PTX_irrelevant.
    apply H4.
    apply H5.
    intro rw; rewrite rw in tmpir; omega.
    rewrite ZMap.gso; try assumption.
    rewrite real_PTP_PTX_irrelevant.
    apply H4.
    apply H5.
    intro rw; rewrite rw in tmpir; omega.
  Qed.*)

End Real_PTP.
