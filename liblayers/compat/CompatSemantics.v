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
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import liblayers.lib.Decision.
Require Import liblayers.logic.PTrees.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.PTreeLayers.
Require Import liblayers.logic.PTreeSemantics.
Require Import liblayers.logic.LayerLogicImpl.
Require Export liblayers.compat.CompatLayerDef.
Require Import liblayers.compcertx.Observation.

(** * Semantics of languages *)

Section COMPAT_SEMANTICS.
  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel} `{Hmem': !UseMemWithData mem}.
  Context {F: Type}.
  Local Existing Instance ptree_module_ops.
  Local Existing Instance ptree_module_prf.
  Context `{fsem_ops: !FunctionSemanticsOps _ _ _ _ (ptree_module F _) compatlayer}.
  Context `{Hfsem: !FunctionSemantics _ _ _ _ (ptree_module F _) compatlayer}.

  Section COMPAT_SEMANTICS_DEF.
  Local Existing Instance ptree_layer_sim_op.
  Local Existing Instance ptree_layer_ops.
  Local Existing Instance ptree_layer_prf.
  Local Existing Instance ptree_semof.
  Local Existing Instance ptree_semantics_ops.
  Local Existing Instance ptree_semantics_prf.

  (** In order to use the theorems about [ptree_layer]s, we need to
    come up with a corresponding version of the [FunctionSemantics]
    instance. *)

  Local Instance compat_ptree_fsem_ops:
    FunctionSemanticsOps _ F compatsem (globvar type)
      (ptree_module _ _)
      (ptree_layer _ _) :=
    {
      semof_fundef D M L i κ :=
        semof_fundef D M (cl_inj L) i κ
    }.

  Local Instance compat_ptree_fsem_prf:
    FunctionSemantics _ F compatsem (globvar type)
      (ptree_module _ _)
      (ptree_layer _ _).
  Proof.
    split.
    * intros D1 D2 R M1 M2 HM L1 L2 HL i κ.
      simpl semof_fundef.
      apply semof_fundef_sim_monotonic; eauto.
      split; simpl.
      - assumption.
      - repeat constructor.
      - repeat constructor.
    (*
    * intros.
      destruct Hfsem.
      specialize (semof_fundef_vcomp D M (cl_inj L) i κi σi j κj).
      apply semof_fundef_vcomp; simpl; assumption.
    *)
  Qed.

  (** ** [Semantics] *)

  Local Instance compat_semof: Semof (ptree_module _ _) compatlayer compatlayer :=
    {
      semof D M L := cl_inj (〚M〛 L)
    }.

  Local Instance compat_semantics_ops:
    SemanticsOps ident F compatsem _ (ptree_module _ _) compatlayer := {}.

  (** FIXME: the following is heavily copy-and-pasted from
    PTreeSemantics.v, we should figure out a way to avoid this. *)

  Local Existing Instance ptree_module_prf.
  Local Existing Instance ptree_layer_prf.
  Local Existing Instance ptree_semof.
  Local Transparent ptree_layer_ops.
  Local Transparent ptree_module ptree_module_ops.
  Local Transparent ptree_layer ptree_layer_ops.
  Local Opaque PTree.combine.

  Lemma compat_semantics_monotonic:
    Proper (∀ -, (≤) ++> (≤) ++> - ==> - ==> res_le (≤)) semof_fundef ->
    Proper (∀ -, (≤) ++> (≤) ++> (≤)) semof.
  Proof.
    intros H D M1 M2 HM L1 L2 HL.
    simpl.
    solve_monotonic.
  Qed.

  Lemma compat_semantics_sim_monotonic:
    Proper (∀ R, (≤) ++> sim R ++> - ==> - ==> res_le (sim R)) semof_fundef ->
    Proper (∀ R, (≤) ++> sim R ++> sim R) semof.
  Proof.
    intros H D1 D2 R M1 M2 HM L1 L2 HL.
    simpl.
    apply cl_inj_sim_monotonic.
    apply ptree_semantics_mapdef_sim_monotonic; eauto.
  Qed.

  (*
  Lemma compat_semantics_vcomp D M N (L: compatlayer D):
    (forall i (κi : F) (σi : compatsem D) j (κj : F),
       get_layer_primitive i L = OK None ->
       get_layer_globalvar i L = OK None ->
       semof_fundef D M L i κi = OK σi ->
       (res_le (≤))
         (semof_fundef D M (L ⊕ i ↦ σi) j κj)
         (semof_fundef D (M ⊕ i ↦ κi) L j κj)) ->
    〚M〛 (〚N〛 L ⊕ L) ⊕ 〚N〛 L ≤ 〚M ⊕ N〛 L.
  *)

  Lemma compat_semantics_hcomp D M N (L : compatlayer D):
    〚M 〛 L ⊕ 〚N 〛 L ≤ 〚M ⊕ N 〛 L.
  Proof.
    destruct M as [Mf Mv], N as [Nf Nv].
    simpl.
    constructor; simpl.
    * constructor; simpl.
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
          pose proof (semof_fundef_sim_monotonic D D id) as H;
            simpl in H; apply H; clear H.
          transitivity ((Mf, Mv) ⊕ (Nf, Nv)).
          pose proof (left_upper_bound (Mf, Mv) (Nf, Nv)) as H;
            simpl in H; apply H; clear H.
          reflexivity.
          change (sim id L L).
          reflexivity.
        - pose proof (semof_fundef_sim_monotonic D D id) as H;
            simpl in H; apply H; clear H.
          transitivity ((Mf, Mv) ⊕ (Nf, Nv)).
          pose proof (right_upper_bound (Mf, Mv) (Nf, Nv)) as H;
            simpl in H; apply H; clear H.
          reflexivity.
          change (sim id L L).
          reflexivity.
      + reflexivity.
    * reflexivity.
    * reflexivity.
  Qed.

  Lemma compat_get_semof_primitive {D} i (M: ptree_module F (globvar type)) (L: compatlayer D):
    get_layer_primitive (layer := compatlayer) i (〚M〛 L) = 
    semof_function M L i (get_module_function i M).
  Proof.
    apply ptree_get_semof_primitive.
  Qed.

  Local Instance compat_semantics_prf:
    Semantics ident F compatsem _ (ptree_module _ _) compatlayer.
  Proof.
    split.
    * apply compat_semantics_sim_monotonic.
      apply semof_fundef_sim_monotonic.
    * reflexivity.
    * intros; apply compat_get_semof_primitive.
    (*
    * intros.
      apply compat_semantics_vcomp.
      (** For some reason that does not unify on its own *)
      apply (semof_fundef_vcomp (FunctionSemantics := Hfsem)).
    *)
    * apply compat_semantics_hcomp.
  Qed.

  End COMPAT_SEMANTICS_DEF.

  Local Existing Instance compat_semof.
  Local Existing Instance compat_semantics_ops.
  Local Existing Instance compat_semantics_prf.
  Local Existing Instance compat_ptree_fsem_ops.
  Local Existing Instance compat_ptree_fsem_prf.

  (** Quick test of the decision procedure. *)
  Goal
    forall D,
      module_layer_disjoint (D:=D) (F:=F)
        (1%positive ↦ {| gvar_info := Tvoid;
                          gvar_init := nil;
                          gvar_readonly := false;
                          gvar_volatile := false |})
        (2%positive ↦ {| gvar_info := Tvoid;
                         gvar_init := nil;
                         gvar_readonly := false;
                         gvar_volatile := false |}).
  Proof.
    intros D.
    decision.
  Qed.

  (** Versions of [compat_semantics_spec_xxx] with [module_layer_disjoint]. *)

  Lemma compat_semantics_spec_some_disj {D} M L i f:
    get_module_function i M = OK (Some f) ->
    get_layer_primitive i (〚M〛 L) = fmap Some (semof_fundef D M L i f).
  Proof.
    intros HMi.
    rewrite compat_get_semof_primitive.
    rewrite HMi.
    reflexivity.
  Qed.

  (** ** Instantiate the module system *)

  Global Instance compat_ll_ops:
    LayerLogicOps ident _ compatsem _ (ptree_module _ _) compatlayer :=
      logic_impl_ops.

  Global Instance compat_ll_prf:
    LayerLogic ident _ compatsem _ (ptree_module _ _) compatlayer :=
      logic_impl.

End COMPAT_SEMANTICS.

(** Fake [SimulationPaths] *)

Notation path_inj R := R (only parsing).
