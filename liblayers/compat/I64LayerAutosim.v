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
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcertx.backend.I64helpers.
Require Import compcert.backend.SelectLong.
Require Import compcertx.backend.SelectLongproofX.
Require Import liblayers.compat.CompatPrimSem.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatExternalCalls.
Require Import compcert.cfrontend.Ctypes.
Require Import liblayers.compat.I64Layer.
Require Import liblayers.compcertx.Observation.

Section WITHSTENCIL.

Context `{Hobs: Observation}.
Context `{Hstencil: Stencil}.
Context `{Hmem: Mem.MemoryModel}.
Context `{Hmwd: UseMemWithData mem}.

Lemma res_le_T_ok {A B} (x: A) (y: B):
  res_le ⊤%signature (OK x) (OK y).
Proof.
  repeat constructor.
Qed.

Hint Extern 10 (res_le ⊤%signature _ _) => apply res_le_T_ok.

Theorem L64_auto_sim:
    forall (D1 D2: compatdata) (R: compatrel D1 D2),
      cl_sim D1 D2 (freerg_inj _ _ _ R) L64 L64.
Proof.
  unfold L64. intros.
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros. inv H0.
    inv H1. inv H6.
    inv H4; try discriminate.
    simpl in Hxz.
    destruct (Float.longoffloat f0) eqn:?; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    {
      econstructor; simpl; eauto.
      rewrite Heqo. reflexivity.
    }
    split; eauto.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros. inv H0.
    inv H1. inv H6.
    inv H4; try discriminate.
    simpl in Hxz.
    destruct (Float.longuoffloat f0) eqn:?; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    {
      econstructor; simpl; eauto.
      rewrite Heqo. reflexivity.
    }
    split; eauto.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros. inv H0.
    inv H1. inv H6.
    inv H4; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    {
      econstructor; simpl; eauto.
    }
    split; eauto.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros. inv H0.
    inv H1. inv H6.
    inv H4; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    {
      econstructor; simpl; eauto.
    }
    split; eauto.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros. inv H0.
    inv H1. inv H6.
    inv H4; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    {
      econstructor; simpl; eauto.
    }
    split; eauto.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros. inv H0.
    inv H1. inv H6.
    inv H4; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    {
      econstructor; simpl; eauto.
    }
    split; eauto.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros. inv H0.
    inv H1. inv H6. inv H7.
    inv H4; try discriminate.
    inv H3; try discriminate.
    simpl in Hxz.
    destruct (
        Int64.eq i0 Int64.zero
                 || Int64.eq i (Int64.repr Int64.min_signed) &&
                 Int64.eq i0 Int64.mone
      ) eqn:?; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    {
      econstructor; simpl; eauto.
      rewrite Heqb. reflexivity.
    }
    split; eauto.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros. inv H0.
    inv H1. inv H6. inv H7.
    inv H4; try discriminate.
    inv H3; try discriminate.
    simpl in Hxz.
    destruct (
        Int64.eq i0 Int64.zero
      ) eqn:?; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    {
      econstructor; simpl; eauto.
      rewrite Heqb. reflexivity.
    }
    split; eauto.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros. inv H0.
    inv H1. inv H6. inv H7.
    inv H4; try discriminate.
    inv H3; try discriminate.
    simpl in Hxz.
    destruct (
        Int64.eq i0 Int64.zero
                 || Int64.eq i (Int64.repr Int64.min_signed) &&
                 Int64.eq i0 Int64.mone
      ) eqn:?; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    {
      econstructor; simpl; eauto.
      rewrite Heqb. reflexivity.
    }
    split; eauto.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros. inv H0.
    inv H1. inv H6. inv H7.
    inv H4; try discriminate.
    inv H3; try discriminate.
    simpl in Hxz.
    destruct (
        Int64.eq i0 Int64.zero
      ) eqn:?; try discriminate.
    inv Hxz.
    esplit. esplit. esplit. esplit.
    split.
    {
      econstructor; simpl; eauto.
      rewrite Heqb. reflexivity.
    }
    split; eauto.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros. inv H0.
    inv H1. inv H6. inv H7.
    esplit. esplit. esplit. esplit.
    split.
    {
      econstructor; simpl; eauto.
    }
    split.
    {
      inv H4; auto.
      inv H3; auto.
      simpl.
      destruct (Int.ltu i0 Int64.iwordsize'); auto.
    }
    split; eauto.
  }
  refine (oplus_sim_monotonic _ _ _ _ _ _ _ _ _).
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros. inv H0.
    inv H1. inv H6. inv H7.
    esplit. esplit. esplit. esplit.
    split.
    {
      econstructor; simpl; eauto.
    }
    split.
    {
      inv H4; auto.
      inv H3; auto.
      simpl.
      destruct (Int.ltu i0 Int64.iwordsize'); auto.
    }
    split; eauto.
  }
  {
    apply layer_sim_intro.
    constructor.
    constructor; auto.
    intros. inv H0.
    inv H1. inv H6. inv H7.
    esplit. esplit. esplit. esplit.
    split.
    {
      econstructor; simpl; eauto.
    }
    split.
    {
      inv H4; auto.
      inv H3; auto.
      simpl.
      destruct (Int.ltu i0 Int64.iwordsize'); auto.
    }
    split; eauto.
  }
Qed.

End WITHSTENCIL.
