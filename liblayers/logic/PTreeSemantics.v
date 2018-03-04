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
Require Import Coq.ZArith.ZArith.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST. (* For ident. *)
Require Import liblayers.lib.Decision.
Require Import liblayers.lib.OptionMonad.
Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.logic.PTrees.
Require Import liblayers.logic.PTreeLayers.
Require Import liblayers.logic.PTreeModules.
Require Export liblayers.logic.Semantics.

Local Existing Instance ptree_module_ops.
Local Existing Instance ptree_layer_sim_op.
Local Existing Instance ptree_layer_ops.
Local Transparent ptree_module ptree_module_ops.
Local Transparent ptree_layer ptree_layer_ops.
Local Opaque PTree.combine.


(** * Semantics of [ptree_module]s *)

Section PTREE_SEMANTICS_GENERAL.
  Context {F: Type}.
  Context `{Hlayer: Layers (ident := ident)}.
  Context `{Hprimsem: !Primitives primsem}.
  Context `{fsem_ops: !FunctionSemanticsOps ident F primsem V (ptree_module F V) layer}.
  Local Existing Instance ptree_module_prf.
  Local Existing Instance ptree_layer_prf.

  Definition ptree_semantics_def D M L i (d: res F): res (primsem D) :=
    κ <- d; semof_fundef D M L i κ.

  Global Instance ptree_semantics_def_monotonic:
    Proper
      (∀ -, (≤) ++> (≤) ++> - ==> - ==> res_le (≤))
      semof_fundef ->
    Proper
      (∀ -, (≤) ++> (≤) ++> - ==> res_le eq ++> res_le (≤))
      ptree_semantics_def.
  Proof.
    intros H D M1 M2 HM L1 L2 HL i d1 d2 Hd.
    unfold ptree_semantics_def.
    solve_monotonic.
    subst.
    solve_monotonic.
  Qed.

  Global Instance ptree_semantics_def_sim_monotonic:
    Proper
      (∀ R : simrel v1 v2, (≤) ++> sim R ++> - ==> - ==> res_le (sim R))
      semof_fundef ->
    Proper
      (∀ R, (≤) ++> sim R ++> - ==> res_le eq ++> res_le (sim R))
      ptree_semantics_def.
  Proof.
    intros H D1 D2 R M1 M2 HM L1 L2 HL i d1 d2 Hd.
    unfold ptree_semantics_def.
    destruct Hd as [? ? κ | err y]; subst; monad_norm; solve_monotonic.
  Qed.

  Definition ptree_semantics_mapdef D (M M': ptree_module F V) L:
    ptree_layer _ _ D :=
      (PTree.map (fun i => Monad.bind (semof_fundef D M L i)) (fst M'),
       snd M').

  Global Instance ptree_semantics_mapdef_monotonic D:
    Proper
      (∀ -, (≤) ++> (≤) ++> - ==> - ==> res_le (≤))
      semof_fundef ->
    Proper ((≤) ++> (≤) ++> (≤) ++> (≤)) (ptree_semantics_mapdef D).
  Proof.
    intros H.
    unfold ptree_semantics_mapdef.
    intros _ _ [Mf1 Mf2 HMf Mv1 Mv2 HMv].
    intros _ _ [Mf1' Mf2' HMf' Mv1' Mv2' HMv'].
    solve_monotonic.
    subst.
    solve_monotonic.
  Qed.

  Local Instance ptree_semantics_mapdef_sim_monotonic:
    Proper
      (∀ R : simrel v1 v2, (≤) ++> sim R ++> - ==> - ==> res_le (sim R))
      semof_fundef ->
    Proper (∀ R, (≤) ++> (≤) ++> sim R ++> sim R) ptree_semantics_mapdef.
  Proof.
    unfold ptree_semantics_mapdef.
    intros H D1 D2 R.
    intros _ _ [Mf1 Mf2 HMf Mv1 Mv2 HMv].
    intros _ _ [Mf1' Mf2' HMf' Mv1' Mv2' HMv'].
    solve_monotonic.
    subst.
    solve_monotonic.
  Qed.

  Context `{HFsem: !FunctionSemantics ident F primsem V (ptree_module F V) layer}.

  (*
  Lemma ptree_semantics_mapdef_hcomp D M M1 M2 L:
    ptree_semantics_mapdef D M M1 L ⊕
    ptree_semantics_mapdef D M M2 L ≤
    ptree_semantics_mapdef D M (M1 ⊕ M2) L.
  Proof.
    intros i; simpl.
    unfold ptree_semantics_mapdef; simpl.
    rewrite !PTree.gcombine by reflexivity.
    rewrite !PTree.gmap.
    rewrite !PTree.gcombine by reflexivity.
    destruct (M1 ! i) as [[|]|];
    destruct (M2 ! i) as [[|]|];
    simpl;
    constructor;
    reflexivity.
  Qed.
  *)

  Local Instance ptree_semof:
    Semof (ptree_module F V) layer (ptree_layer primsem V) :=
    {
      semof D M L :=
        ptree_semantics_mapdef D M M L
    }.

  Lemma ptree_get_semof_primitive {D} i (M: ptree_module F V) (L: layer D):
    get_layer_primitive i (〚M〛 L) = 
    semof_function M L i (get_module_function i M).
  Proof.
    simpl.
    unfold ptree_layer_primitive, ptree_semantics_mapdef; simpl.
    unfold semof_function, ptree_module_function; simpl.
    rewrite PTree.gmap.
    destruct ((fst M) ! i) as [[|]|]; reflexivity.
  Qed.
End PTREE_SEMANTICS_GENERAL.

Section PTREE_SEMANTICS_SPECIFIC.
  Context {F V: Type}.
  Context {layerdata simrel primsem} `{Hprimsem: Primitives layerdata simrel primsem}.
  Context `{fsem_ops: !FunctionSemanticsOps ident F primsem V (ptree_module F V) (ptree_layer primsem V)}.
  Local Existing Instance ptree_module_prf.
  Local Existing Instance ptree_layer_prf.
  Local Existing Instance ptree_semof.

  Local Instance ptree_semantics_ops:
    SemanticsOps _ _ _ _ (ptree_module F V) (ptree_layer primsem V) := {}.

  Lemma ptree_semantics_monotonic:
    Proper (∀ -, (≤) ++> (≤) ++> - ==> - ==> res_le (≤)) semof_fundef ->
    Proper (∀ -, (≤) ++> (≤) ++> (≤)) semof.
  Proof.
    intros H D M1 M2 HM L1 L2 HL.
    simpl.
    solve_monotonic.
  Qed.

  Lemma ptree_semantics_sim_monotonic:
    Proper
      (∀ R : simrel v1 v2, (≤) ++> sim R ++> - ==> - ==> res_le (sim R))
      semof_fundef ->
    Proper
      (∀ R, (≤) ++> sim R ++> sim R)
      semof.
  Proof.
    intros H D1 D2 R M1 M2 HM L1 L2 HL.
    simpl.
    apply ptree_semantics_mapdef_sim_monotonic; eauto.
  Qed.

  (*
  Lemma ptree_semantics_variable D i (τ: V) (L: ptree_layer primsem V D):
    i ↦ τ ≤ 〚i ↦ τ〛 L.
  Proof.
    intros j.
    simpl.
    unfold ptree_semantics_mapdef.
    rewrite !PTree.gmap.
    destruct (decide (j = i)) as [Hij | Hij].
    + subst.
      rewrite !PTree.gss; simpl.
      unfold ptree_semantics_def.
      monad_norm.
      reflexivity.
    + rewrite !PTree.gso by assumption.
      rewrite !PTree.gempty; simpl.
      monad_norm.
      reflexivity.
  Qed.
  *)

  (*
  Lemma ptree_semantics_vcomp D M N (L: ptree_layer primsem V D):
    (forall i (κi : F) (σi : primsem D) j (κj : F),
       get_layer_primitive i L = OK None ->
       get_layer_globalvar i L = OK None ->
       semof_fundef D M L i κi = OK σi ->
       (res_le (≤))
         (semof_fundef D M (L ⊕ i ↦ σi) j κj)
         (semof_fundef D (M ⊕ i ↦ κi) L j κj)) ->
    〚M〛 (〚N〛 L ⊕ L) ⊕ 〚N〛 L ≤ 〚M ⊕ N〛 L.
  *)

  Local Instance ptree_semantics_prf:
    FunctionSemantics ident F primsem V (ptree_module F V) (ptree_layer primsem V) ->
    Semantics _ _ _ _ (ptree_module F V) (ptree_layer primsem V).
  Proof.
    split; intros.
    * apply ptree_semantics_sim_monotonic.
      apply semof_fundef_sim_monotonic.
    * reflexivity.
    * simpl.
      unfold ptree_layer_primitive, ptree_semantics_mapdef; simpl.
      unfold ptree_module_function, semof_function; simpl.
      rewrite PTree.gmap; simpl.
      destruct ((fst M) ! i) as [[|]|]; reflexivity.
(*
    * apply ptree_semantics_vcomp.
      (** For some reason that does not unify on its own *)
      apply (semof_fundef_vcomp (FunctionSemantics := Hfsem)).
*)
    * destruct M as [Mf Mv], N as [Nf Nv].
      simpl.
      constructor; simpl.
      + intros i.
        rewrite !PTree.gcombine by reflexivity.
        rewrite !PTree.gmap.
        rewrite !PTree.gcombine by reflexivity.
        simpl.
        destruct (Mf!i) as [[|]|], (Nf!i) as [[|]|];
        simpl; monad_norm; simpl; repeat constructor.
        - apply upper_bound.
        - apply upper_bound.
        - transitivity (Some (semof_fundef D (Mf, Mv) L i f)).
          destruct (semof_fundef _ _ _ _ _); reflexivity.
          monotonicity.
          apply semof_fundef_sim_monotonic.
          transitivity ((Mf, Mv) ⊕ (Nf, Nv)).
          apply left_upper_bound.
          reflexivity.
          reflexivity.
        - apply semof_fundef_sim_monotonic.
          transitivity ((Mf, Mv) ⊕ (Nf, Nv)).
          apply right_upper_bound.
          reflexivity.
          reflexivity.
      + reflexivity.
  Qed.
End PTREE_SEMANTICS_SPECIFIC.
