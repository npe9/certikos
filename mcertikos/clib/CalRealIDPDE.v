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

Section Real_IDPDE.

  Function Calculate_idpte_at_i (i: Z) (pde_index: Z) (idp: IDPDE) : IDPDE := 
    let pde:= ZMap.get pde_index idp in
    if zlt pde_index 256 then
      ZMap.set pde_index (ZMap.set i (IDPTEValid (PTK true)) pde) idp
    else if zle 960 pde_index then
           ZMap.set pde_index (ZMap.set i (IDPTEValid (PTK true)) pde) idp
         else
           ZMap.set pde_index (ZMap.set i (IDPTEValid (PTK false)) pde) idp
  .

  Fixpoint Calculate_idpte (i: nat) (pde_index: Z) (idp: IDPDE) : IDPDE :=
    match i with
      | O => Calculate_idpte_at_i 0 pde_index idp
      | S k => Calculate_idpte_at_i (Z.of_nat (S k)) pde_index (Calculate_idpte k pde_index idp)
    end.

  Fixpoint Calculate_idpde (i: nat) (idp: IDPDE) : IDPDE :=
    match i with
      | O => Calculate_idpte (Z.to_nat (one_k - 1)) 0 idp
      | S k => Calculate_idpte (Z.to_nat (one_k - 1)) (Z.of_nat (S k)) (Calculate_idpde k idp)
    end.

  Definition real_idpde (idp: IDPDE): IDPDE := Calculate_idpde (Z.to_nat (one_k - 1)) idp.

  Lemma calculate_idpte_at_i_kern: forall idp i index,
    kern_low/one_k <= index < kern_high / one_k ->
    IDPTE_valid (ZMap.get index (Calculate_idpte_at_i i index idp)) i false.
  Proof.
    intros.
    unfold Calculate_idpte_at_i.
    unfold IDPTE_valid.
    destruct (zlt index 256).
    xomega.
    destruct (zle 960 index).
    xomega.
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    reflexivity.
  Qed.

  Lemma calculate_idpte_at_i_common: forall idp i index,
    0 <= index < kern_low/one_k \/ kern_high/one_k <= index < one_k -> 
    IDPTE_valid (ZMap.get index (Calculate_idpte_at_i i index idp)) i true.
  Proof.
    intros.
    unfold Calculate_idpte_at_i.
    unfold IDPTE_valid.
    destruct (zlt index 256).
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    reflexivity.
    destruct (zle 960 index).
    rewrite ZMap.gss.
    rewrite ZMap.gss.
    reflexivity.
    destruct H.
    xomega.
    xomega.
  Qed.

  Lemma calculate_idpte_at_i_index_local: forall idp i j index,
    j <> i -> 
      ZMap.get j (ZMap.get index (Calculate_idpte_at_i i index idp)) =
      ZMap.get j (ZMap.get index idp).
  Proof.
    intros.
    unfold Calculate_idpte_at_i.
    destruct (zlt index 256).
    rewrite ZMap.gss.
    rewrite ZMap.gso.
    reflexivity.
    assumption.
    destruct (zle 960 index).
    rewrite ZMap.gss.
    rewrite ZMap.gso.
    reflexivity.
    assumption.
    rewrite ZMap.gss.
    rewrite ZMap.gso.
    reflexivity.
    assumption.
  Qed.

  Lemma calculate_idpte_at_i_local: forall idp i j k,
    j <> i ->
      ZMap.get j (Calculate_idpte_at_i k i idp) =
      ZMap.get j idp.
  Proof.
    intros.
    unfold Calculate_idpte_at_i.
    destruct (zlt i 256).
    rewrite ZMap.gso.
    reflexivity.
    assumption.
    destruct (zle 960 i).
    rewrite ZMap.gso.
    reflexivity.
    assumption.
    rewrite ZMap.gso.    
    reflexivity.
    assumption.
  Qed.

  Lemma calculate_idpte_common: forall idp index i j,
    0 <= index < kern_low/one_k \/ kern_high/one_k <= index < one_k ->
    0 <= i <= Z.of_nat j ->
      IDPTE_valid (ZMap.get index (Calculate_idpte j index idp)) i true.
  Proof.
    unfold IDPTE_valid_page.
    intros.
    induction j.
    {
      replace i with 0.
      simpl.
      apply calculate_idpte_at_i_common.
      xomega.
      xomega.
    }
    {
      replace (Calculate_idpte (S j) index idp) with (Calculate_idpte_at_i 
        (Z.of_nat (S j)) index (Calculate_idpte j index idp)).
      destruct (Z.eq_dec i (Z.of_nat (S j))).
      rewrite e in *.
      apply calculate_idpte_at_i_common.
      assumption.
      unfold IDPTE_valid in *.
      rewrite calculate_idpte_at_i_index_local.
      apply IHj.
      xomega.
      assumption.
      reflexivity.
    }
  Qed.

  Lemma calculate_idpte_kern: forall idp index i j,
    kern_low/one_k <= index < kern_high/one_k ->
    0 <= i <= Z.of_nat j ->
      IDPTE_valid (ZMap.get index (Calculate_idpte j index idp)) i false.
  Proof.
    unfold IDPTE_valid_page.
    intros.
    induction j.
    {
      replace i with 0.
      simpl.
      apply calculate_idpte_at_i_kern.
      xomega.
      xomega.
    }
    {
      replace (Calculate_idpte (S j) index idp) with (Calculate_idpte_at_i 
        (Z.of_nat (S j)) index (Calculate_idpte j index idp)).
      destruct (Z.eq_dec i (Z.of_nat (S j))).
      rewrite e in *.
      apply calculate_idpte_at_i_kern.
      assumption.
      unfold IDPTE_valid in *.
      rewrite calculate_idpte_at_i_index_local.
      apply IHj.
      xomega.
      assumption.
      reflexivity.
    }
  Qed.

  Lemma calculate_idpte_local: forall idp i j k,
    j <> i ->
      ZMap.get j (Calculate_idpte k i idp) = ZMap.get j idp.
  Proof.
    intros.
    induction k.
    {
      simpl.
      rewrite calculate_idpte_at_i_local.
      reflexivity.
      assumption.
    }
    {
      replace (Calculate_idpte (S k) i idp) with (Calculate_idpte_at_i 
        (Z.of_nat (S k)) i (Calculate_idpte k i idp)).
      rewrite calculate_idpte_at_i_local.
      assumption.
      assumption.
      reflexivity.
    }
  Qed.

  Lemma calculate_idpde_common: forall idp i j,
    0 <= j < kern_low/one_k \/ kern_high/one_k <= j < one_k ->
    j <= Z.of_nat i ->
      IDPTE_valid_page (ZMap.get j (Calculate_idpde i idp)) true.
  Proof.
    intros.
    induction i.
    {
      replace j with 0.
      replace (Calculate_idpde 0 idp) with 
        (Calculate_idpte (Z.to_nat (one_k - 1)) 0 idp).
      unfold IDPTE_valid_page.
      intros.
      apply calculate_idpte_common.
      xomega.
      xomega.
      reflexivity.
      xomega.
    }
    {
      replace (Calculate_idpde (S i) idp) with
        (Calculate_idpte (Z.to_nat (one_k - 1)) (Z.of_nat (S i)) (Calculate_idpde i idp)).
      destruct (Z.eq_dec j (Z.of_nat (S i))).
      rewrite <- e.
      unfold IDPTE_valid_page in *.
      intros.
      apply calculate_idpte_common.
      assumption.
      xomega.
      rewrite calculate_idpte_local.
      apply IHi.
      xomega.
      assumption.
      reflexivity.
    }
  Qed.

  Lemma calculate_idpde_kern: forall idp i j,
    kern_low/one_k <= j < kern_high/one_k ->
    j <= Z.of_nat i ->
      IDPTE_valid_page (ZMap.get j (Calculate_idpde i idp)) false.
  Proof.
    intros.
    induction i.
    {
      replace j with 0.
      replace (Calculate_idpde 0 idp) with 
        (Calculate_idpte (Z.to_nat (one_k - 1)) 0 idp).
      unfold IDPTE_valid_page.
      intros.
      apply calculate_idpte_kern.
      xomega.
      xomega.
      reflexivity.
      xomega.
    }
    {
      replace (Calculate_idpde (S i) idp) with
        (Calculate_idpte (Z.to_nat (one_k - 1)) (Z.of_nat (S i)) (Calculate_idpde i idp)).
      destruct (Z.eq_dec j (Z.of_nat (S i))).
      rewrite <- e.
      unfold IDPTE_valid_page in *.
      intros.
      apply calculate_idpte_kern.
      assumption.
      xomega.
      rewrite calculate_idpte_local.
      apply IHi.
      xomega.
      assumption.
      reflexivity.
    }
  Qed.

  Lemma real_idpde_init:
    forall idp,
      IDPDE_init (real_idpde idp).
  Proof.
    intros.
    unfold IDPDE_init.
    split.
    {
      unfold real_idpde.
      unfold IDPDE_common.
      intros.
      apply calculate_idpde_common.
      unfold PDX.
      xomega.
      unfold PDX.
      xomega.
    }
    {
      unfold real_idpde.
      unfold IDPDE_kern.
      intros.
      apply calculate_idpde_kern.
      unfold PDX.
      xomega.
      unfold PDX.
      xomega.
    }
  Qed.

End Real_IDPDE.
