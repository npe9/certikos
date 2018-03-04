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

(** * Language definitions *)

(** The type classes in the file can be used to define a language and
  instantiate the layer framework correspondingly.

  A language is characterized by the types it uses for identifiers,
  function definitions and variable definitions. We also need to
  define the domain that will be used to interpret the semantics of
  primitives, and the corresponding notion of simulations.

  Once these basic ingredients are provided, we need to provide
  instances of corresponding structures for modules and layers.
  If we use [positive] for identifiers, as Compcert does, this can be
  done automatically by [PTreeModules] and [PTreeLayers].

  The last step is to define the semantics of modules, by giving an
  interpretation in [∀ D, layer D -> layer D]: the semantics tells us,
  if we use a module [M] in a context which implements layer [L], that
  it will implement the specifications in the layer [〚M〛 L]. *)

Require Export liblayers.logic.Modules.
Require Export liblayers.logic.Layers.
Require Export liblayers.logic.Semantics.

(** ** Layer logic *)

(** The interface for the layer logic is given below. It is
  instantiated by the [LayerLogicImpl] Coq module, which interprets
  the module typing judgement [L1 ⊢ (R, M) : L2] in terms of the
  language's semantics as [sim R L2 (〚M〛 L1)]. *)

Class LayerLogicOps {layerdata simrel} ident F primsem V module layer
    `{sem_ops: SemanticsOps layerdata ident F primsem V module layer} :=
  {
    ll_vdash {D1 D2} :> Vdash (layer D1) (simrel D2 D1 * module) (layer D2)
  }.

Class LayerLogic {layerdata simrel} ident F primsem V module layer
    `{ll_ops: LayerLogicOps layerdata simrel ident F primsem V module layer}
    `{rg_ops: !ReflexiveGraphOps layerdata simrel}
    `{primsem_sim: !Sim simrel primsem}
    `{layer_sim: !Sim simrel layer} :=
  {
    (*
    sem_rule {D} (M: module) (L: layer D):
      L ⊢ (id, M) : 〚M〛 L;
    conseq_rule {D1 D2 D3 D4} R21 R32 R43 L1 L2 L3 L4 M:
      simRR D2 D1 R21 L2 L1 ->
      simRR D4 D3 R43 L4 L3 ->
      L2 ⊢ (R32, M) : L3 ->
      L1 ⊢ (R21 ∘ R32 ∘ R43, M) : L4;
    vcomp_rule D1 D2 D3 (R: simrel D2 D1) (S: simrel D3 D2) L1 L2 L3 M N:
      L1 ⊢ (R, M) : L2 ->
      L2 ⊢ (S, N) : L3 ->
      L1 ⊢ (R ∘ S, M ⊕ N) : L3;
    *)
    conseq_le_le D1 D2 (R: simrel D1 D2) L1 L2 L3 L4 M:
      L2 ⊢ (R, M) : L3 ->
      L2 ≤ L1 ->
      L4 ≤ L3 ->
      L1 ⊢ (R, M) : L4;
    hcomp_rule D D' (R: simrel D' D) L M1 M2 (L1 L2: layer D'):
      layers_disjoint L1 L \/ layers_disjoint L2 L ->
      L ⊢ (R, M1) : L1 ->
      L ⊢ (R, M2) : L2 ->
      L ⊢ (R, M1 ⊕ M2) : L1 ⊕ L2
  }.


(** * Derived rules *)

Section DERIVED_RULES.
  Context `{Hll: LayerLogic}.
  (* Context `{Hld: !Category layerdata simrel}. *)
  Context `{Hmodule: !Modules ident F V module}.
  Context `{Hlayer: !Layers ident primsem V layer}.
  Context `{fsem_ops: !FunctionSemanticsOps ident F primsem V module layer}.
  Context `{Hsem: !Semantics ident F primsem V module layer}.

  (** The following specialized versions of the consequence rule are
    easier to apply depending on situation, since you don't have to
    rewrite the relation involved to account for identities. *)

  (*
  Lemma conseq_le_sim {D1 D2} (R: simrel D2 D1) M L1 L2 L3 L4:
    L2 ⊢ (id, M) : L3 ->
    L2 ≤ L1 ->
    sim R L4 L3 ->
    L1 ⊢ (R, M) : L4.
  Proof.
    intros HM HL21 HL43.
    rewrite <- (cat_compose_id_left R).
    rewrite <- (cat_compose_id_right id).
    eapply conseq_rule; eassumption.
  Qed.

  Lemma conseq_sim_le {D1 D2} (R: simrel D2 D1) M L1 L2 L3 L4:
    L2 ⊢ (id, M) : L3 ->
    sim R L2 L1 ->
    L4 ≤ L3 ->
    L1 ⊢ (R, M) : L4.
  Proof.
    intros HM HL21 HL43.
    rewrite <- (cat_compose_id_right R).
    rewrite <- (cat_compose_id_right (R ∘ id)).
    eapply conseq_rule; eassumption.
  Qed.

  Lemma conseq_le_le {D1 D2} (R: simrel D2 D1) M L1 L2 L3 L4:
    L2 ⊢ (R, M) : L3 ->
    L2 ≤ L1 ->
    L4 ≤ L3 ->
    L1 ⊢ (R, M) : L4.
  Proof.
    intros HM HL21 HL43.
    rewrite <- (cat_compose_id_right R).
    rewrite <- (cat_compose_id_left R).
    eapply conseq_rule; eassumption.
  Qed.
  *)

  Lemma conseq_le_left {D1 D2} (R: simrel D1 D2) M L1 L1' L2:
    L1 ⊢ (R, M) : L2 ->
    L1 ≤ L1' ->
    L1' ⊢ (R, M) : L2.
  Proof.
    intros HM HL1.
    eapply conseq_le_le.
    * apply HM.
    * apply HL1.
    * reflexivity.
  Qed.

  Lemma conseq_le_right {D1 D2} (R: simrel D1 D2) M L1 L2 L2':
    L1 ⊢ (R, M) : L2 ->
    L2' ≤ L2 ->
    L1 ⊢ (R, M) : L2'.
  Proof.
    intros HM HL2.
    eapply conseq_le_le.
    * apply HM.
    * reflexivity.
    * apply HL2.
  Qed.

  (** The frame rule can be proved from horizontal composition and
    some consequence rules. *)

  (** Not sure how to fit [layers_disjoint] in though <<<
  Lemma frame_rule D D' (R: simrel D' D) L1 L2 M1 M2 L1' L2':
    L1 ⊢ (R, M1) : L1' ->
    L2 ⊢ (R, M2) : L2' ->
    L1 ⊕ L2 ⊢ (R, M1 ⊕ M2) : L1' ⊕ L2'.
  Proof.
    intros H1 H2.
    apply hcomp_rule.
    * eapply conseq_le_left; try eassumption.
      apply left_upper_bound.
    * eapply conseq_le_left; try eassumption.
      apply right_upper_bound.
  Qed.
  >>> **)
End DERIVED_RULES.
