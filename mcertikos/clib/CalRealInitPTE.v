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

Section Real_InitPTE.

  Fixpoint Calculate_init_pte (i: nat) : PTE := 
    match i with 
      | O => ZMap.set 0 PTEUnPresent (ZMap.init PTEUndef)
      | S k => ZMap.set (Z.of_nat (S k)) PTEUnPresent (Calculate_init_pte k)
    end.


  Definition real_init_PTE : PTE := Calculate_init_pte (Z.to_nat (one_k - 1)).


  Lemma Calculate_init_pte_unp:
    forall n i,
      0 <= i < Z.of_nat (n) + 1 ->
      ZMap.get i (Calculate_init_pte n) = PTEUnPresent.
  Proof.
    Local Opaque Z.of_nat.
    induction n; simpl; intros.
    - Local Transparent Z.of_nat. simpl in H.
      assert (Heq: i = 0) by omega. subst.
      rewrite ZMap.gss. trivial.
    - destruct (zeq i (Z.of_nat (S n))); subst.
      + rewrite ZMap.gss. trivial.
      + rewrite ZMap.gso; eauto.
        eapply IHn. rewrite Nat2Z.inj_succ in *.
        omega.
  Qed.

  Lemma real_init_PTE_unp:
    forall i,
      0 <= i < one_k -> ZMap.get i real_init_PTE  = PTEUnPresent.
  Proof.
    intros. eapply Calculate_init_pte_unp; eauto.
  Qed.

  Lemma real_init_PTE_defined:
    forall i,
      0 <= i < one_k -> ZMap.get i real_init_PTE  <> PTEUndef.
  Proof.
    intros. 
    assert(ZMap.get i real_init_PTE  = PTEUnPresent).
    eapply real_init_PTE_unp; eauto. 
    congruence.
  Qed.

End Real_InitPTE.