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
Require        CalRealPT.
Require Import Constant.
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import CommonTactic.
(*Require Import XOmega.*)

Section WithRealParamsOps.

  Context `{real_params_ops : RealParamsOps}.
  (** mem_init *)

  Class RealParams
  : Prop :=
    {
      real_valid_mm: MM_valid real_mm real_size;
      real_correct_mm: MM_correct real_mm real_size;
      real_valid_mm_kern: MM_kern real_mm real_size;
      real_valid_mm_size: 0< real_size <= Int.max_unsigned;
      real_vmxinfo_range: forall vmxinfo_idx, 1 <= vmxinfo_idx <= 14 -> 0 <= ZMap.get vmxinfo_idx real_vmxinfo <= Int.max_unsigned
    }.

  Section AT_and_NPS.

    Function maxs_at_i (i: Z) (mm: MMTable) : Z :=
      match ZMap.get i mm with
        | MMValid s l _ => (s + l) / PgSize + 1
        | _ => 0
      end.

    Fixpoint Calculate_nps (i: nat) (mm: MMTable) (size: Z) : Z := 
      match i with
        | O => maxs_at_i (Z.of_nat i) mm
        | S k => let (recnps, newnps) := (Calculate_nps k mm size, maxs_at_i (Z.of_nat (S k)) mm)
                 in if Z_lt_dec recnps newnps then newnps else recnps
      end.

    Definition real_nps := Calculate_nps (Z.to_nat (real_size - 1)) real_mm real_size.

    Fixpoint Calculate_AT (n:nat) (nps: Z) (mm:MMTable) (size:Z) (At: ATable) : ATable :=
      match n with
        | O => ZMap.set (Z.of_nat n) (ATValid false ATKern 0) At
        | S k => if Z_le_dec kern_low (Z.of_nat (S k))
                 then if Z_lt_dec (Z.of_nat (S k)) (Z.min kern_high nps)
                      then if MM_kern_valid_dec mm (Z.of_nat (S k)) size
                           then ZMap.set (Z.of_nat (S k)) (ATValid false ATNorm 0) (Calculate_AT k nps mm size At)
                           else ZMap.set (Z.of_nat (S k)) (ATValid false ATResv 0) (Calculate_AT k nps mm size At)
                      else  ZMap.set (Z.of_nat (S k)) (ATValid false ATKern 0) (Calculate_AT k nps mm size At)
                 else  ZMap.set (Z.of_nat (S k)) (ATValid false ATKern 0) (Calculate_AT k nps mm size At)
      end.
    
    Definition real_AT (AT: ATable) := Calculate_AT (Z.to_nat (real_nps-1)) real_nps real_mm real_size AT.

    Fixpoint Calculate_LAT (n:nat) (nps: Z) (mm:MMTable) (size:Z) (At: LATable) : LATable :=
      match n with
        | O => ZMap.set (Z.of_nat n) (LATValid false ATKern nil) At
        | S k => if Z_le_dec kern_low (Z.of_nat (S k))
                 then if Z_lt_dec (Z.of_nat (S k)) (Z.min kern_high nps)
                      then if MM_kern_valid_dec mm (Z.of_nat (S k)) size
                           then ZMap.set (Z.of_nat (S k)) (LATValid false ATNorm nil) (Calculate_LAT k nps mm size At)
                           else ZMap.set (Z.of_nat (S k)) (LATValid false ATResv nil) (Calculate_LAT k nps mm size At)
                      else  ZMap.set (Z.of_nat (S k)) (LATValid false ATKern nil) (Calculate_LAT k nps mm size At)
                 else  ZMap.set (Z.of_nat (S k)) (LATValid false ATKern nil) (Calculate_LAT k nps mm size At)
      end.

    Definition real_LAT (AT: LATable) := Calculate_LAT (Z.to_nat (real_nps-1)) real_nps real_mm real_size AT.

    Lemma real_relate_LATable:
      forall a1 a2,
        (*(forall i t n, ZMap.get i a1 = ATValid false t n -> n = 0) ->*)
        relate_LATable a1 a2 ->
        relate_LATable (real_AT a1) (real_LAT a2).
    Proof.
      intros.
      unfold real_AT, real_LAT.
      generalize (Z.to_nat (real_nps - 1)).
      induction n.
      - simpl.
        intros i.
        destruct (zeq i 0) as [ -> |];
          [ rewrite 2 ZMap.gss; auto using RELATE_VALID
          | rewrite 2 ZMap.gso; auto ].
      - simpl.
        remember (Z.pos (Pos.of_succ_nat n)) as n'.
        destruct (Z_le_dec 262144 n');
          [ destruct (Z_lt_dec n' (Z.min 983040 real_nps));
            [ destruct (MM_kern_valid_dec real_mm n' real_size) |] |];
          intros i;
          destruct (zeq i n') as [ -> |];
          solve [ rewrite 2 ZMap.gss; auto using RELATE_VALID
                | rewrite 2 ZMap.gso; auto ].
    Qed.

    (*Fixpoint Calculate_pperm (n:nat) (pperm: PPermT) : PPermT :=
      match n with
        | O => ZMap.set (Z.of_nat n) PGUndef pperm
        | S k => ZMap.set (Z.of_nat (S k)) PGUndef (Calculate_pperm k pperm)
      end.

    Definition real_pperm (pperm: PPermT) := Calculate_pperm (Z.to_nat (real_nps-1)) pperm.*)

    Context `{real_params: RealParams}.
    
    Lemma max_unsigned_val: Int.max_unsigned  = 4294967295.
    Proof.
      repeat autounfold; reflexivity.
    Qed.

    Lemma max_signed_val: Int.max_signed = 2147483647.
    Proof.
      repeat autounfold; reflexivity.
    Qed.

    Ltac Caseeq H := generalize H; apply or_ind; clear H.

    Lemma real_nps_range: kern_low <= real_nps <= maxpage.
    Proof.
      generalize max_unsigned_val; intro muval.
      generalize real_valid_mm_size; intro mmsize.
      generalize real_valid_mm; intro mmvalid.
      generalize real_valid_mm_kern; intro mmkern.
      unfold MM_valid in mmvalid.
      unfold MM_range in mmvalid.
      unfold MM_kern in mmkern.
      unfold MM_kern_range in mmkern.
      unfold MM_kern_valid in mmkern.
      unfold real_nps.
      assert(mmkern': exists i0 s l : Z,
                        0 <= i0 < real_size /\
                        ZMap.get i0 real_mm = MMValid s l MMUsable /\
                        s <= 262143 * 4096 /\ l + s >= 262144 * 4096).
      assert(tmp: 0 <= 262143 < kern_low) by omega.
      generalize (mmkern 262143 tmp); intro tmpH.
      simpl in *.
      assumption.
      clear mmkern.
      replace real_size with (real_size - 1 + 1) in mmvalid, mmkern' by omega.
      rewrite <- Z2Nat.id with (real_size - 1) in mmvalid, mmkern'; try omega.
      split.
      clear mmvalid.
      induction (Z.to_nat (real_size - 1)).
      rewrite Nat2Z.inj_0 in *.
      simpl in *.
      unfold maxs_at_i.
      do 5 (destruct mmkern' as [? mmkern']).
      destruct mmkern'.
      replace x with 0 in * by omega.
      rewrite H0.
      assert((x0 + x1) / 4096 >= 262144 * 4096 / 4096).
      apply Z_div_ge; omega.
      rewrite Z_div_mult_full in H3; try omega.

      Opaque Z.of_nat.
      simpl.
      destruct (Z_lt_dec (Calculate_nps n real_mm real_size)).
      do 5 (destruct mmkern' as [? mmkern']).
      destruct mmkern'.
      assert(icase: x = Z.of_nat (S n) \/ x <> Z.of_nat (S n)) by omega.
      Caseeq icase; intro.
      rewrite H3 in *.
      unfold maxs_at_i.
      rewrite H0.
      assert((x0 + x1) / 4096 >= 262144 * 4096 / 4096).
      apply Z_div_ge; omega.
      rewrite Z_div_mult_full in H4; try omega.
      rewrite Nat2Z.inj_succ in *.
      unfold Z.succ in *.
      assert(262144 <= Calculate_nps n real_mm real_size).
      apply IHn.
      intros.
      exists x, x0, x1.
      split.
      omega.
      auto.
      omega.    
      assert(Calculate_nps n real_mm real_size >= maxs_at_i (Z.of_nat (S n)) real_mm) by omega.
      do 5 (destruct mmkern' as [? mmkern']).
      destruct mmkern'.
      assert(icase: x = Z.of_nat (S n) \/ x <> Z.of_nat (S n)) by omega.
      Caseeq icase; intro.
      rewrite H4 in *.
      assert(kern_low <= maxs_at_i (Z.of_nat (S n)) real_mm).
      unfold maxs_at_i.
      rewrite H1.
      assert((x0 + x1) / 4096 >= 262144 * 4096 / 4096).
      apply Z_div_ge; omega.
      rewrite Z_div_mult_full in H5; try omega.
      omega.
      rewrite Nat2Z.inj_succ in *.
      unfold Z.succ in *.
      assert(262144 <= Calculate_nps n real_mm real_size).
      apply IHn.
      exists x, x0, x1.
      split.
      omega.
      auto.
      omega.

      clear mmkern'.
      induction (Z.to_nat (real_size - 1)).
      simpl.
      rewrite Nat2Z.inj_0 in *.
      simpl in *.
      unfold maxs_at_i.
      assert(tmp: 0 <= 0 < 1) by omega.    
      generalize (mmvalid 0 tmp); intro tmpH.
      do 5 (destruct tmpH as [? tmpH]).
      destruct tmpH.
      rewrite H.
      assert((x + x0) / 4096 <= 4294967294 / 4096).
      apply Z_div_le; omega.
      change (4294967294 / 4096) with 1048575 in H3.
      omega.

      Opaque Z.of_nat.
      simpl.
      destruct (Z_lt_dec (Calculate_nps n real_mm real_size)).
      assert(Calculate_nps n real_mm real_size <= 1048576).
      rewrite Nat2Z.inj_succ in *.
      unfold Z.succ in *.
      apply IHn.
      intros.
      apply mmvalid.
      omega.
      assert(tmp: 0 <= Z.of_nat (S n) < Z.of_nat (S n) + 1) by omega.    
      generalize (mmvalid (Z.of_nat (S n)) tmp); intro tmpH.
      do 5 (destruct tmpH as [? tmpH]).
      destruct tmpH.
      unfold maxs_at_i.
      rewrite H0.
      assert((x + x0) / 4096 <= 4294967294 / 4096).
      apply Z_div_le; omega.
      change (4294967294 / 4096) with 1048575 in H4.
      omega.
      apply IHn.
      intros.
      apply mmvalid.
      rewrite Nat2Z.inj_succ in *.
      unfold Z.succ in *.
      omega.
    Qed.

    Definition Cal_at_Well (x:Z) :=
      forall n m i nps mm size AT,
        0 <= i
        -> i<= n <= m
        -> m - n = x
        -> ZMap.get i (Calculate_AT (Z.to_nat n) nps mm size AT)
           = ZMap.get i (Calculate_AT (Z.to_nat (m)) nps mm size AT).
    
    Lemma cal_at_correct':
      forall x, 0<= x-> Cal_at_Well x.
    Proof.
      apply natlike_rec2.
      unfold Cal_at_Well.
      intros.
      assert(HP: m = n).
      omega.
      subst m.
      trivial.
      
      intros.
      unfold Cal_at_Well in *.
      intros.
      specialize (H0 n (Z.pred m) i nps mm size AT).
      assert(HM: i <= n <= m-1).
      omega.
      assert(HN: Z.pred m -n = z).
      omega.
      specialize (H0 H1 HM HN).
      rewrite H0.
      unfold Calculate_AT.
      case_eq (Z.to_nat m).
      intros.
      assert(HZM: (Z.to_nat (Z.pred m)) = 0%nat).
      rewrite Z2Nat.inj_pred.
      rewrite H4.
      reflexivity.
      rewrite HZM.
      trivial.
      fold Calculate_AT.
      
      intros.
      assert(HZM: Z.to_nat (Z.pred m) = n0).
      rewrite Z2Nat.inj_pred.
      rewrite H4; reflexivity.
      rewrite HZM.
      assert(HNOT:   i <> Z.of_nat (S n0)).
      red.
      rewrite <- H4.
      erewrite Z2Nat.id.
      intros.
      omega.
      omega.

      destruct ( Z_le_dec kern_low (Z.of_nat (S n0))).
      destruct ( Z_lt_dec (Z.of_nat (S n0)) (Z.min kern_high nps)).
      destruct (MM_kern_valid_dec mm (Z.of_nat (S n0)) size).
      erewrite ZMap.gso; trivial.
      
      erewrite ZMap.gso; trivial.

      erewrite ZMap.gso; trivial.

      erewrite ZMap.gso; trivial.
    Qed.  

    Lemma real_at_kern_valid: 
      forall AT, AT_kern (real_AT AT) real_nps.
    Proof.
      generalize real_nps_range; intro.
      unfold AT_kern.
      intros.
      specialize (cal_at_correct' (real_nps-1 -i)).
      intros.
      assert(0 <= real_nps - 1 - i) by omega.
      unfold real_AT.
      specialize (H1 H2).
      unfold Cal_at_Well in H1.
      specialize (H1 i (real_nps -1) i real_nps real_mm real_size AT).

      destruct H0 as [HH |HH].
      rewrite <- H1; try omega.
      clear H1.
      unfold Calculate_AT.
      case_eq (Z.to_nat i).
      intros.
      assert(HI: i = 0).
      case_eq (Z_eq_dec i 0).
      intros.
      trivial.
      intros.
      assert(HI: 0< i).
      omega.
      specialize (Z2Nat.inj_lt 0 i).
      intros.
      assert(HI1: 0<=0).
      omega.
      assert(HI2:0<=i).
      omega.
      specialize (H3 HI1 HI2).
      inv H3.
      specialize (H4 HI).
      rewrite H0 in H4.
      change (0%nat) with (Z.to_nat 0) in H0.
      apply Z2Nat.inj in H0.
      assumption.
      omega.
      omega.

      subst i.
      rewrite Nat2Z.inj_0.
      apply ZMap.gss.
      
      fold Calculate_AT.
      intros.
      rewrite <- H0.
      rewrite Z2Nat.id; try omega.
      case_eq (Z_le_dec kern_low i).
      intros.
      omega.
      intros.
      apply ZMap.gss.    
      
      rewrite <- H1; try omega.
      clear H2.
      unfold Calculate_AT.
      case_eq (Z.to_nat i).
      intros.
      specialize (Z2Nat.inj_lt 0 i).
      intros.
      assert(HI1: 0<=0).
      omega.
      assert(HI2:0<=i).
      omega.
      specialize (H2 HI1 HI2).
      inv H2.
      assert(HI: 0< i).
      omega.
      specialize (H3 HI).
      rewrite H0 in H3.
      change (Z.to_nat 0) with 0%nat in H3.
      omega.
      
      fold Calculate_AT.
      intros.
      rewrite <- H0.
      rewrite Z2Nat.id; try omega.
      case_eq (Z_le_dec kern_low i).
      intros.
      case_eq (Z_lt_dec i (Z.min kern_high real_nps)).
      intros.
      case_eq (Z_le_dec kern_high real_nps).
      intros.
      assert(HP: Z.min kern_high real_nps = kern_high).
      rewrite Z.min_l; trivial.
      omega.
      
      intros.
      omega.
      
      intros.
      apply ZMap.gss.
      
      intros.
      omega.
    Qed.

    Lemma real_at_usr_valid: 
      forall AT,
        AT_usr (real_AT AT) real_nps.
    Proof.
      generalize real_nps_range; intro.
      unfold AT_usr.
      intros.
      assert(HIN: i < real_nps).
      case_eq (Z_le_dec kern_high real_nps).
      intros.
      rewrite Z.min_l in H0; trivial.
      omega.
      
      intros.
      rewrite Z.min_r in H0; omega.

      specialize (cal_at_correct' (real_nps-1 -i)).
      intros.
      assert(HT: 0 <= real_nps - 1 - i).
      omega.
      specialize (H1 HT).
      unfold Cal_at_Well in H1.
      specialize (H1 i (real_nps -1) i real_nps real_mm real_size AT).
      unfold real_AT.

      rewrite <- H1; try omega.
      clear H1.
      exists false.
      unfold Calculate_AT.
      case_eq (Z.to_nat i).
      intros.
      specialize (Z2Nat.inj_lt 0 i).
      intros.
      assert(HI1: 0<=0).
      omega.
      assert(HI2:0<=i).
      omega.
      specialize (H2 HI1 HI2).
      inv H2.
      assert(HI: 0< i).
      omega.
      specialize (H3 HI).
      rewrite H1 in H3.
      change (Z.to_nat 0) with 0%nat in H3.
      omega.
      
      fold Calculate_AT.
      intros.
      rewrite <- H1.
      rewrite Z2Nat.id; try omega.
      case_eq (Z_le_dec kern_low i).
      intros.
      case_eq (Z_lt_dec i (Z.min kern_high real_nps)).
      intros.
      destruct (MM_kern_valid_dec real_mm i real_size).
      left.
      exists 0. apply ZMap.gss.
      right.
      apply ZMap.gss.
      
      intros.
      omega.
      intros.
      omega.
    Qed.

    Lemma real_pperm_valid:
      forall AT,
        consistent_ppage (real_AT AT) (ZMap.init PGUndef) real_nps.
    Proof.
      unfold consistent_ppage; intros.
      generalize real_nps_range; intro.
      assert(HIN: i < real_nps) by omega.
      assert(HT: 0 <= real_nps - 1 - i) by omega.
      specialize (cal_at_correct' _ HT).
      unfold Cal_at_Well.
      intros HCal.
      specialize (HCal i (real_nps -1) i real_nps real_mm real_size AT).
      unfold real_AT.

      rewrite <- HCal; try omega.
      clear HCal.
      unfold Calculate_AT.
      case_eq (Z.to_nat i); simpl.
      - intros.
        destruct (zeq i 0); subst.
        + change (Z.of_nat 0) with 0.
          rewrite ZMap.gss. rewrite ZMap.gi.
          split; intros.
          elim H2; trivial.
          inv H2.
        + specialize (Z2Nat.inj_lt 0 i).
          intros.
          assert(HI1: 0<=0) by omega.
          assert(HI2: 0<=i) by omega.
          specialize (H2 HI1 HI2).
          rewrite H1 in H2. simpl in H2.
          inv H2. exploit H3. omega.
          intros HF. inv HF.
      - fold Calculate_AT.
        intros.
        rewrite <- H1.
        rewrite Z2Nat.id; try omega.
        rewrite ZMap.gi.
        destruct (Z_le_dec 262144 i);
          [destruct (Z_lt_dec i (Z.min 983040 real_nps))|];
          [destruct (MM_kern_valid_dec real_mm i real_size)| | ];
          rewrite ZMap.gss; split; intros; try (elim H2; trivial; fail); inv H2.
    Qed.      

    Definition Cal_lat_Well (x:Z) :=
      forall n m i nps mm size AT,
        0 <= i
        -> i<= n <= m
        -> m - n = x
        -> ZMap.get i (Calculate_LAT (Z.to_nat n) nps mm size AT)
           = ZMap.get i (Calculate_LAT (Z.to_nat (m)) nps mm size AT).
    
    Lemma cal_lat_correct':
      forall x, 0<= x-> Cal_lat_Well x.
    Proof.
      apply natlike_rec2.
      unfold Cal_lat_Well.
      intros.
      assert(HP: m = n).
      omega.
      subst m.
      trivial.
      
      intros.
      unfold Cal_lat_Well in *.
      intros.
      specialize (H0 n (Z.pred m) i nps mm size AT).
      assert(HM: i <= n <= m-1).
      omega.
      assert(HN: Z.pred m -n = z).
      omega.
      specialize (H0 H1 HM HN).
      rewrite H0.
      unfold Calculate_LAT.
      case_eq (Z.to_nat m).
      intros.
      assert(HZM: (Z.to_nat (Z.pred m)) = 0%nat).
      rewrite Z2Nat.inj_pred.
      rewrite H4.
      reflexivity.
      rewrite HZM.
      trivial.
      fold Calculate_LAT.
      
      intros.
      assert(HZM: Z.to_nat (Z.pred m) = n0).
      rewrite Z2Nat.inj_pred.
      rewrite H4; reflexivity.
      rewrite HZM.
      assert(HNOT:   i <> Z.of_nat (S n0)).
      red.
      rewrite <- H4.
      erewrite Z2Nat.id.
      intros.
      omega.
      omega.

      destruct ( Z_le_dec kern_low (Z.of_nat (S n0))).
      destruct ( Z_lt_dec (Z.of_nat (S n0)) (Z.min kern_high nps)).
      destruct (MM_kern_valid_dec mm (Z.of_nat (S n0)) size).
      erewrite ZMap.gso; trivial.
      
      erewrite ZMap.gso; trivial.

      erewrite ZMap.gso; trivial.

      erewrite ZMap.gso; trivial.
    Qed.  

    Lemma real_lat_kern_valid: 
      forall AT, LAT_kern (real_LAT AT) real_nps.
    Proof.
      generalize real_nps_range; intro.
      unfold LAT_kern.
      intros.
      specialize (cal_lat_correct' (real_nps-1 -i)).
      intros.
      assert(0 <= real_nps - 1 - i) by omega.
      unfold real_LAT.
      specialize (H1 H2).
      unfold Cal_lat_Well in H1.
      specialize (H1 i (real_nps -1) i real_nps real_mm real_size AT).

      destruct H0 as [HH |HH].
      rewrite <- H1; try omega.
      clear H1.
      unfold Calculate_LAT.
      case_eq (Z.to_nat i).
      intros.
      assert(HI: i = 0).
      case_eq (Z_eq_dec i 0).
      intros.
      trivial.
      intros.
      assert(HI: 0< i).
      omega.
      specialize (Z2Nat.inj_lt 0 i).
      intros.
      assert(HI1: 0<=0).
      omega.
      assert(HI2:0<=i).
      omega.
      specialize (H3 HI1 HI2).
      inv H3.
      specialize (H4 HI).
      rewrite H0 in H4.
      change (0%nat) with (Z.to_nat 0) in H0.
      apply Z2Nat.inj in H0.
      assumption.
      omega.
      omega.

      subst i.
      rewrite Nat2Z.inj_0.
      apply ZMap.gss.
      
      fold Calculate_LAT.
      intros.
      rewrite <- H0.
      rewrite Z2Nat.id; try omega.
      case_eq (Z_le_dec kern_low i).
      intros.
      omega.
      intros.
      apply ZMap.gss.    
      
      rewrite <- H1; try omega.
      clear H2.
      unfold Calculate_LAT.
      case_eq (Z.to_nat i).
      intros.
      specialize (Z2Nat.inj_lt 0 i).
      intros.
      assert(HI1: 0<=0).
      omega.
      assert(HI2:0<=i).
      omega.
      specialize (H2 HI1 HI2).
      inv H2.
      assert(HI: 0< i).
      omega.
      specialize (H3 HI).
      rewrite H0 in H3.
      change (Z.to_nat 0) with 0%nat in H3.
      omega.
      
      fold Calculate_LAT.
      intros.
      rewrite <- H0.
      rewrite Z2Nat.id; try omega.
      case_eq (Z_le_dec kern_low i).
      intros.
      case_eq (Z_lt_dec i (Z.min kern_high real_nps)).
      intros.
      case_eq (Z_le_dec kern_high real_nps).
      intros.
      assert(HP: Z.min kern_high real_nps = kern_high).
      rewrite Z.min_l; trivial.
      omega.
      
      intros.
      omega.
      
      intros.
      apply ZMap.gss.
      
      intros.
      omega.
    Qed.

    Lemma real_lat_usr_valid: 
      forall AT,
        LAT_usr (real_LAT AT) real_nps.
    Proof.
      generalize real_nps_range; intro.
      unfold LAT_usr.
      intros.
      assert(HIN: i < real_nps).
      case_eq (Z_le_dec kern_high real_nps).
      intros.
      rewrite Z.min_l in H0; trivial.
      omega.
      
      intros.
      rewrite Z.min_r in H0; omega.

      specialize (cal_lat_correct' (real_nps-1 -i)).
      intros.
      assert(HT: 0 <= real_nps - 1 - i).
      omega.
      specialize (H1 HT).
      unfold Cal_lat_Well in H1.
      specialize (H1 i (real_nps -1) i real_nps real_mm real_size AT).
      unfold real_LAT.

      rewrite <- H1; try omega.
      clear H1.
      exists false.
      unfold Calculate_LAT.
      case_eq (Z.to_nat i).
      intros.
      specialize (Z2Nat.inj_lt 0 i).
      intros.
      assert(HI1: 0<=0).
      omega.
      assert(HI2:0<=i).
      omega.
      specialize (H2 HI1 HI2).
      inv H2.
      assert(HI: 0< i).
      omega.
      specialize (H3 HI).
      rewrite H1 in H3.
      change (Z.to_nat 0) with 0%nat in H3.
      omega.
      
      fold Calculate_LAT.
      intros.
      rewrite <- H1.
      rewrite Z2Nat.id; try omega.
      case_eq (Z_le_dec kern_low i).
      intros.
      case_eq (Z_lt_dec i (Z.min kern_high real_nps)).
      intros.
      destruct (MM_kern_valid_dec real_mm i real_size).
      left.
      exists nil. apply ZMap.gss.
      right.
      apply ZMap.gss.
      
      intros.
      omega.
      intros.
      omega.
    Qed.

    Lemma Lreal_pperm_valid:
      forall AT,
        Lconsistent_ppage (real_LAT AT) (ZMap.init PGUndef) real_nps.
    Proof.
      unfold Lconsistent_ppage; intros.
      generalize real_nps_range; intro.
      assert(HIN: i < real_nps) by omega.
      assert(HT: 0 <= real_nps - 1 - i) by omega.
      specialize (cal_lat_correct' _ HT).
      unfold Cal_lat_Well.
      intros HCal.
      specialize (HCal i (real_nps -1) i real_nps real_mm real_size AT).
      unfold real_LAT.

      rewrite <- HCal; try omega.
      clear HCal.
      unfold Calculate_LAT.
      case_eq (Z.to_nat i); simpl.
      - intros.
        destruct (zeq i 0); subst.
        + change (Z.of_nat 0) with 0.
          rewrite ZMap.gss. rewrite ZMap.gi.
          split; intros.
          elim H2; trivial.
          inv H2.
        + specialize (Z2Nat.inj_lt 0 i).
          intros.
          assert(HI1: 0<=0) by omega.
          assert(HI2: 0<=i) by omega.
          specialize (H2 HI1 HI2).
          rewrite H1 in H2. simpl in H2.
          inv H2. exploit H3. omega.
          intros HF. inv HF.
      - fold Calculate_LAT.
        intros.
        rewrite <- H1.
        rewrite Z2Nat.id; try omega.
        rewrite ZMap.gi.
        destruct (Z_le_dec 262144 i);
          [destruct (Z_lt_dec i (Z.min 983040 real_nps))|];
          [destruct (MM_kern_valid_dec real_mm i real_size)| | ];
          rewrite ZMap.gss; split; intros; try (elim H2; trivial; fail); inv H2.
    Qed.      

    (*Lemma real_lat_domain:
      forall ptp a,
        consistent_lat_domain ptp (real_LAT a) real_nps.
    Proof.

    Qed.*)

    Lemma real_LAT_all_valid_false_nil :
        forall a v, 0 < v < real_nps -> exists t,
          ZMap.get v (real_LAT a) = LATValid false t nil.
    Proof.
      unfold real_LAT.
      destruct real_nps in |- * at 1 2.
      - intros ? ? [ H0 H1 ].
        contradiction (Z.lt_irrefl _ (Z.lt_trans _ _ _ H0 H1)).
      - generalize dependent p.
        refine (Pos.peano_ind _ _ _).
        { (* base case, p = 1, is impossible because 0 < v < p *)
          intros ? ? [ H0 H1 ].
          rewrite <- Z.le_succ_l in H0.
          contradiction (Zle_not_lt _ _ H0 H1).
        }
        intros.
        rewrite Pos2Z.inj_succ in H0 |- *.
        change (Z.succ (Z.pos p) - 1) with (Z.pred (Z.succ (Z.pos p))).
        rewrite Z.pred_succ.

        (* force unfold one level of [Calculate_LAT] *)
        destruct (Z.to_nat (Z.pos p)) eqn:p_to_nat_eq; simpl.
        { (* [Z.to_nat (Z.pos p) = 0] is impossible *)
          simpl in p_to_nat_eq.
          destruct (Pos2Nat.is_succ p) as [ n eq_S_n ].
          rewrite eq_S_n in p_to_nat_eq; discriminate p_to_nat_eq.
        }
        rewrite <- p_to_nat_eq.
        rewrite Z2Nat.id; try discriminate.

        destruct (zeq v (Z.pos p)) as [ -> |].
        + destruct (Z_le_dec 262144 (Z.pos p));
            [ destruct (Z_lt_dec (Z.pos p) (Z.min 983040 real_nps)) |];
            [ destruct (MM_kern_valid_dec real_mm (Z.pos p) real_size) | |];
            rewrite ZMap.gss; eexists; reflexivity.
        + change (Z.pos p - 1) with (Z.pred (Z.pos p)) in H.
          rewrite Z2Nat.inj_pred, p_to_nat_eq in H.
          change (pred (S n)) with n in H.
          assert (0 < v < Z.pos p).
          { destruct H0; split; try assumption.
            rewrite Z.lt_succ_r in H1.
            apply Z.lt_eq_cases in H1.
            destruct H1; [ assumption | contradiction ].
          }
          destruct (Z_le_dec 262144 (Z.pos p));
            [ destruct (Z_lt_dec (Z.pos p) (Z.min 983040 real_nps)) |];
            [ destruct (MM_kern_valid_dec real_mm (Z.pos p) real_size) | |];
            rewrite ZMap.gso; auto.
      - intros ? ? [ H0 H1 ].
        assert (H2 := Z.lt_trans _ _ _ H0 H1).
        discriminate H2.
    Qed.

    Lemma Calculate_LAT_outside_small :
      forall n v nps mm size a,
        v < 0 -> ZMap.get v (Calculate_LAT n nps mm size a) = ZMap.get v a.
    Proof.
      induction n; simpl; intros; cases; zmap_solve; omega.
    Qed.

    Lemma Calculate_LAT_outside :
      forall n v nps mm size a,
        Z.of_nat n < v -> nps <= v -> ZMap.get v (Calculate_LAT n nps mm size a) = ZMap.get v a.
    Proof.
      induction n; simpl; intros; cases; zmap_solve; try omega;
        rewrite IHn; auto; rewrite Nat2Z.inj_succ in H; omega.
    Qed.

    Lemma Calculate_LAT_0 :
      forall n nps mm size a,
        Z.of_nat n < nps -> ZMap.get 0 (Calculate_LAT n nps mm size a) = LATValid false ATKern nil.
    Proof.
      induction n; simpl; intros; cases; zmap_solve; try omega;
        try solve [rewrite IHn; auto; rewrite Nat2Z.inj_succ in H; omega].
      contradiction n; auto.
    Qed.

    Lemma real_LAT_outside :
      forall v a,
        v < 0 \/ real_nps <= v -> ZMap.get v (real_LAT a) = ZMap.get v a.
    Proof.
      unfold real_LAT; intros v a Hcases; destruct Hcases.
      apply Calculate_LAT_outside_small; auto.
      apply Calculate_LAT_outside; auto.
      assert (Hrange:= real_nps_range); rewrite Z2Nat.id; omega.
    Qed.

    Lemma real_LAT_0_false_nil :
        forall a, ZMap.get 0 (real_LAT a) = LATValid false ATKern nil.
    Proof.
      unfold real_LAT; intros; apply Calculate_LAT_0.
      assert (Hrange:= real_nps_range); rewrite Z2Nat.id; omega.
    Qed.

    Lemma Lreal_at_consistent_lat_domain:
      forall p a,
        consistent_lat_domain (CalRealPT.real_pt p) (real_LAT a) real_nps.
    Proof.
      intros ? a ? v_range ?.
      destruct (real_LAT_all_valid_false_nil a _ v_range) as [ ? -> ];
        discriminate.
    Qed.

  End AT_and_NPS.

  Section AC.

    Definition real_quota_AT := unused_pages_AT (real_AT (ZMap.init ATUndef)) (Z.to_nat (real_nps-1)).
    Definition real_quota := unused_pages (real_LAT (ZMap.init LATUndef)) (Z.to_nat (real_nps-1)).
    Definition real_AC := ZMap.set 0 (mkContainer real_quota 0 0 nil true) (ZMap.init Container_unused).

    Lemma real_AT_unused_pages :
      forall n nps mm size AT AT',
        unused_pages_AT (Calculate_AT n nps mm size AT) n = 
        unused_pages_AT (Calculate_AT n nps mm size AT') n.
    Proof.
      induction n; simpl; intros; auto.
      simpl; change (Z.pos (Pos.of_succ_nat n)) with (Z_of_nat (S n)) in *.
      rewrite Nat2Z.inj_succ in *; rewrite <- Z.add_1_r in *.
      repeat match goal with
      | [ |- appcontext [if ?cmp then _ else _] ] => destruct cmp
      end; repeat rewrite ZMap.gss; f_equal; 
      repeat rewrite unused_pages_AT_outside; auto; omega.
    Qed.

    Lemma real_LAT_unused_pages :
      forall n nps mm size lat lat',
        unused_pages (Calculate_LAT n nps mm size lat) n = 
        unused_pages (Calculate_LAT n nps mm size lat') n.
    Proof.
      induction n; simpl; intros; auto.
      simpl; change (Z.pos (Pos.of_succ_nat n)) with (Z_of_nat (S n)) in *.
      rewrite Nat2Z.inj_succ in *; rewrite <- Z.add_1_r in *.
      repeat match goal with
      | [ |- appcontext [if ?cmp then _ else _] ] => destruct cmp
      end; repeat rewrite ZMap.gss; f_equal; 
      repeat rewrite unused_pages_outside; auto; omega.
    Qed.

    Lemma real_quota_unused_pages_AT :
      forall AT,
        unused_pages_AT (real_AT AT) (Z.to_nat (real_nps - 1)) = real_quota_AT.
    Proof.
      unfold real_AT, real_quota; intro; eapply real_AT_unused_pages.
    Qed.

    Lemma real_quota_unused_pages :
      forall lat,
        unused_pages (real_LAT lat) (Z.to_nat (real_nps - 1)) = real_quota.
    Proof.
       unfold real_LAT, real_quota; intro; eapply real_LAT_unused_pages.
    Qed.

    Lemma real_quota_convert : real_quota = real_quota_AT.
    Proof.
      unfold real_quota, real_quota_AT; apply unused_pages_relate.
      apply real_relate_LATable.
      intro; rewrite 2 ZMap.gi; constructor.
    Qed.

    Lemma unused_pages_AT_range : 
      forall n AT,
        0 <= unused_pages_AT AT n <= Z.of_nat n.
    Proof.
      induction n; simpl; intros; try omega.
      change (Z.pos (Pos.of_succ_nat n)) with (Z_of_nat (S n)) in *.      
      rewrite Nat2Z.inj_succ in *; rewrite <- Z.add_1_r in *.
      specialize (IHn AT); destruct (ZMap.get (Z.of_nat n + 1) AT) as [[|] [| |]|]; omega.
    Qed.

    Lemma unused_pages_range : 
      forall n lat,
        0 <= unused_pages lat n <= Z.of_nat n.
    Proof.
      induction n; simpl; intros; try omega.
      change (Z.pos (Pos.of_succ_nat n)) with (Z_of_nat (S n)) in *.      
      rewrite Nat2Z.inj_succ in *; rewrite <- Z.add_1_r in *.
      specialize (IHn lat); destruct (ZMap.get (Z.of_nat n + 1) lat) as [[|] [| |]|]; omega.
    Qed.

    Context `{real_params: RealParams}.

    Lemma real_quota_AT_range_nps :
      0 <= real_quota_AT <= real_nps - 1.
    Proof.
      assert (Hrange:= real_nps_range).
      rewrite <- (Z2Nat.id (real_nps-1)); try omega.
      apply unused_pages_AT_range.
    Qed.

    Lemma real_quota_range_nps :
      0 <= real_quota <= real_nps - 1.
    Proof.
      assert (Hrange:= real_nps_range).
      rewrite <- (Z2Nat.id (real_nps-1)); try omega.
      apply unused_pages_range.
    Qed.

    Lemma real_quota_AT_range :
      0 <= real_quota_AT <= maxpage.
    Proof.
      assert (H1:= real_nps_range); assert (H2:= real_quota_AT_range_nps); omega.
    Qed.

    Lemma real_quota_range :
      0 <= real_quota <= maxpage.
    Proof.
      assert (H1:= real_nps_range); assert (H2:= real_quota_range_nps); omega.
    Qed.

  End AC.

End WithRealParamsOps.
