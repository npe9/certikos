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
Require Import liblayers.lib.Decision.
Require Export liblayers.logic.Modules.
Require Export liblayers.logic.Layers.

Section WITH_LAYER_DATA.
Context {layerdata simrel} `{Hld: ReflexiveGraph layerdata simrel}.


(** * Semantics of modules *)

Class SemanticsOps ident F primsem V module layer
    `{module_ops: !ModuleOps ident F V module}
    `{primsem_prim_ops: !PrimitiveOps (V:=layerdata) primsem}
    `{layer_ops: !LayerOps ident primsem V layer} :=
  {
    lang_semof :> Semof module layer layer
  }.


(** * Semantics of individual function definitions *)

(** This is used as a general interface between implementations of
  types of layers and the semantics of languages. *)

Class FunctionSemanticsOps ident F primsem V module layer
    `{module_ops: !ModuleOps ident F V module}
    `{primsem_sim: !Sim simrel primsem}
    `{primsem_prim_ops: !PrimitiveOps primsem}
    `{layerqs_sim: !Sim simrel layer}
    `{layer_ops: !LayerOps ident primsem V layer} :=
  {
    semof_fundef D (M: module) (L: layer D): ident -> F -> res (primsem D)
  }.


(** * Specification *)

Class FunctionSemantics ident F primsem V module layer
    `{semof_ops: FunctionSemanticsOps ident F primsem V module layer}: Prop :=
  {

    semof_fundef_sim_monotonic :>
      Proper
        (∀ R, (≤) ++> sim R ++> - ==> - ==> res_le (sim R))
        semof_fundef
    (*
    semof_fundef_vcomp {D} (M: module) (L: layer D) i κi σi j κj:
      get_layer_primitive i L = OK None ->
      get_layer_globalvar i L = OK None ->
      semof_fundef D M L i κi = OK σi ->
      (res_le (≤))
        (semof_fundef D M (L ⊕ i ↦ σi) j κj)
        (semof_fundef D (M ⊕ i ↦ κi) L j κj)
    *)
  }.

Definition semof_function `{fsem_ops: FunctionSemanticsOps} :=
  fun {D} (M: module) (L: layer D) (i: ident) (d: res (option F)) =>
    mκ <- d;
    match mκ with
      | None => OK None
      | Some κ =>
        σ <- semof_fundef (FunctionSemanticsOps := fsem_ops) D M L i κ;
        OK (Some σ)
    end.

Class Semantics ident F primsem V module layer
    `{fsem_ops: FunctionSemanticsOps ident F primsem V module layer}
    `{lsem_ops: !SemanticsOps ident F primsem V module layer}
    `{primsem_sim: !Sim simrel primsem}
    `{layerqs_sim: !Sim simrel layer} :=
  {
    lang_semof_sim_monotonic :>
      Proper (∀ R, (≤) ++> sim R ++> sim R) semof;
    get_semof_globalvar {D} (i: ident) (M: module) (L: layer D):
      get_layer_globalvar i (〚M〛 L) =
      get_module_variable i M;
    get_semof_primitive {D} (i: ident) (M: module) (L: layer D):
      get_layer_primitive i (〚M〛 L) = 
      semof_function M L i (get_module_function i M);
    (*
    lang_semof_vcomp {D} (M N: module) (L: layer D):
      〚M〛 (〚N〛 L ⊕ L) ⊕ 〚N〛 L ≤ 〚M ⊕ N〛 L
    *)
    (** For now, only do horizontal composition. For later, this can
      be derived from [lang_semof_vcomp] as per the commented lemma
      below. *)
    lang_semof_hcomp {D} (M N: module) (L: layer D):
      〚M〛 L ⊕ 〚N〛 L ≤ 〚M ⊕ N〛 L
  }.


(** * Properties *)

(*
Lemma lang_semof_hcomp `{Semantics} `{!Modules _ _ _ _} `{!Layers _ _ _ _}:
  forall {D} (M N: module) (L: layer D),
    〚M〛 L ⊕ 〚N〛 L ≤ 〚M ⊕ N〛 L.
Proof.
  intros.
  transitivity (〚M〛 (〚N〛 L ⊕ L) ⊕ 〚N〛 L).
  * eapply oplus_monotonic; try reflexivity.
    apply lang_semof_monotonic; try reflexivity.
    apply right_upper_bound.
  * apply lang_semof_vcomp.
Qed.
*)

  Context `{HS: Semantics} `{HM: !Modules _ _ _ _} `{HL: !Layers _ _ _ _}.

  (** XXX: This is used when rewriting using (≡)-based theorems (commutativity...).
    It should be automated somehow. Maybe a [ProperQuery] phase for symmetric opening? *)
  Global Instance lang_semof_equiv_monotonic:
    Proper (∀ -, (≡) ==> (≡) ==> (≡)) semof | 10.
  Proof.
    intros D.
    apply le_equiv_op_mor.
    solve_monotonic.
  Qed.

  Definition module_layer_disjoint {D} (M: module) (L: layer D) :=
   forall i: ident,
    (isOKNone (get_module_function i M) /\ isOKNone (get_module_variable i M)) \/
    (isOKNone (get_layer_primitive i L) /\ isOKNone (get_layer_globalvar i L)).

  Instance mld_dec_aux {D} (M: module) (L: layer D):
    Decision
      ((forall i,
          (~ (isOKNone (get_module_function i M)) ->
           isOKNone (get_layer_primitive i L) /\
           isOKNone (get_layer_globalvar i L))) /\
       (forall i,
          (~ (isOKNone (get_module_variable i M)) ->
           isOKNone (get_layer_primitive i L) /\
           isOKNone (get_layer_globalvar i L)))).
  Proof.
    typeclasses eauto.
  Defined.

  Global Program Instance module_layer_disjoint_dec {D} M (L: layer D):
    Decision (module_layer_disjoint M L) :=
    match mld_dec_aux M L with
      | left H => left _
      | right H => right _
    end.
  Next Obligation.
    unfold module_layer_disjoint.
    simpl.
    intros i.
    destruct (decide (isOKNone (get_module_function i M))) as [HMf|HMf];
    destruct (decide (isOKNone (get_module_variable i M))) as [HMv|HMv];
    eauto.
  Qed.
  Next Obligation.
    unfold module_layer_disjoint.
    simpl.
    intros H'.
    apply H; clear Heq_anonymous H.
    split; intros i H; specialize (H' i).
    * tauto.
    * tauto.
  Qed.

  Lemma semantics_spec_some {D} M L i f:
    get_module_function i M = OK (Some f) ->
    get_layer_primitive i (〚M〛 L) = fmap (@Some _) (semof_fundef D M L i f).
  Proof.
    rewrite get_semof_primitive.
    unfold semof_function.
    intros H; rewrite H; clear H; monad_norm.
    reflexivity.
  Qed.

  (*
  Lemma semantics_spec_some_error {D} M (L: _ D) i f f':
    get_module_function i M = OK (Some f) ->
    get_layer_primitive i L = OK (Some f') ->
    get_layer_primitive i (〚M〛 L) = Error nil.
  Proof.
    destruct (semantics_cases (D:=D) M L i); try discriminate; eauto.
  Qed.
  *)

  Lemma semantics_spec_none {D} M L i:
    get_module_function i M = OK None ->
    get_layer_primitive (D:=D) i (〚M〛 L) = OK None.
  Proof.
    rewrite get_semof_primitive.
    intros H; rewrite H; clear H.
    reflexivity.
  Qed.

  (** FIXME: redundant *)
  Lemma semantics_spec_var {D} M L i:
    get_layer_globalvar (D := D) i (〚M〛 L) = get_module_variable i M.
  Proof.
    apply get_semof_globalvar.
  Qed.

  Lemma ptree_semantics_spec_error {D} M L i msg:
    get_module_function i M = Error msg ->
    get_layer_primitive (D:=D) i (〚M〛 L) = Error msg.
  Proof.
    rewrite get_semof_primitive.
    intros H; rewrite H; clear H.
    reflexivity.
  Qed.

  Lemma semantics_spec_inv {D} M L i σ:
    get_layer_primitive i (〚M〛 L) = OK (Some σ) ->
    exists κ,
      get_module_function i M = OK (Some κ) /\
      semof_fundef D M L i κ = OK σ.
  Proof.
    rewrite get_semof_primitive.
    unfold semof_function.
    destruct (get_module_function i M) as [[κ|]|]; try discriminate; monad_norm.
    intros H.
    inv_monad H.
    inversion H; subst.
    now eauto.
  Qed.

  Lemma semantics_spec_some_disj {D} M L i f:
    module_layer_disjoint M L ->
    get_module_function i M = OK (Some f) ->
    get_layer_primitive i (〚M〛 L) = fmap (@Some _) (semof_fundef D M L i f).
  Proof.
    unfold module_layer_disjoint, isOKNone.
    intros H; specialize (H i).
    rewrite get_semof_primitive.
    destruct H as [[Hf Hv]|[Hp Hv]]; try discriminate;
    inversion 1; subst; rewrite H; reflexivity.
  Qed.
End WITH_LAYER_DATA.
