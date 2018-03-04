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
Require Export liblayers.logic.Language.

Section WITH_SEMANTICS.
  Context {layerdata simrel ident F primsem V module layer}
    `{Hld: ReflexiveGraph layerdata simrel}
    `{Hmodule: Modules ident F V module}
    `{primsem_sim: !Sim simrel primsem}
    `{primsem_prim_ops: !PrimitiveOps primsem}
    `{Hprimsem: !ReflexiveGraphSim layerdata simrel primsem}
    `{layersim_op: !Sim simrel layer}
    `{Hlayercs: !ReflexiveGraphSim layerdata simrel layer}
    `{layer_ops: !LayerOps ident primsem V layer}
    `{Hlayer: !Layers ident primsem V layer}
    `{sem_ops: !SemanticsOps ident F primsem V module layer}
    `{fsem_ops: !FunctionSemanticsOps ident F primsem V module layer}
    `{Hsem: !Semantics ident F primsem V module layer}.

  Global Instance logic_impl_ops: LayerLogicOps ident F primsem V module layer :=
    {
      ll_vdash D1 D2 :=
        {| vdash L1 RM L2 := sim (fst RM) L2 (〚snd RM〛 L1 ⊕ L1) |}
    }.

  Lemma logic_impl_disym_hrule {D D'} (R: simrel D' D) L M1 M2 L1 L2:
    layers_disjoint L1 L ->
    L ⊢ (R, M1) : L1 ->
    L ⊢ (R, M2) : L2 ->
    L ⊢ (R, M1 ⊕ M2) : L1 ⊕ L2.
  Proof.
    unfold vdash; simpl.
    intros Hdisj H1 H2.
    apply layer_sim_cancel_disjoint in H1; try assumption.
    cut (〚M1〛 L ⊕ 〚M2〛 L ⊕ L ≤ 〚M1 ⊕ M2〛 L ⊕ L); [intro H; rewrite <- H | ].
    (*sim_transitivity (〚M1〛 L ⊕ 〚M2〛 L ⊕ L).*)
    * apply oplus_sim_monotonic; assumption.
    * rewrite <- associativity.
      apply oplus_monotonic (*oplus_sim_monotonic*); try reflexivity.
      pose proof (lang_semof_hcomp (D:=D)) as H; apply H.
  Qed.

  Global Instance logic_impl:
    LayerLogic ident F primsem V module layer.
  Proof.
    split.

Opaque module_oplus.

    (*
    (** [sem_rule] *)
    * intros D M L.
      unfold vdash; simpl.
      rewrite <- left_upper_bound.
      reflexivity.

    (** [conseq_rule] *)
    * intros D1 D2 D3 D4 R21 R32 R43 L1 L2 L3 L4 M.
      unfold vdash; simpl.
      intros H21 H43 H32.
      sim_transitivity L3; try assumption.
      sim_transitivity (〚M〛 L2 ⊕ L2); try assumption.
      apply oplus_sim_monotonic; trivial.
      apply lang_semof_sim_monotonic.
      - reflexivity.
      - assumption.

    (** [vcomp_rule] *)
    * intros D1 D2 D3 R S L1 L2 L3 M N.
      unfold vdash; simpl.
      intros H12 H23.
      sim_transitivity (〚N〛 L2 ⊕ L2); trivial.
      sim_transitivity (〚N〛 (〚M〛 L1 ⊕ L1) ⊕ 〚M〛 L1 ⊕ L1).
      + apply oplus_sim_monotonic; trivial.
        apply lang_semof_sim_monotonic.
        reflexivity.
        assumption.
      + rewrite <- associativity.
        apply oplus_sim_monotonic; try reflexivity.
        rewrite (commutativity M N).
        pose proof (lang_semof_vcomp (D:=D1)); apply H.
    *)

    (** [conseq_le_le] *)
    * intros D1 D2 R L1 L2 L3 L4 M.
      unfold vdash; simpl.
      intros H H12 H23.
      assert (H12': 〚M〛 L2 ⊕ L2 ≤ 〚M〛 L1 ⊕ L1) by solve_monotonic reflexivity.
      rewrite <- H12'.
      rewrite H23.
      assumption.

    (** [hcomp_rule] *)
    * intros D D' R L M1 M2 L1 L2 Hdisj H1 H2.
      destruct Hdisj as [Hdisj1 | Hdisj2].
      + apply logic_impl_disym_hrule; assumption.
      + simpl.
        rewrite (commutativity M1 M2).
        rewrite (commutativity L1 L2).
        apply logic_impl_disym_hrule; assumption.
  Qed.

  Lemma logic_intro {DL DH} (LL: layer DL) R M (LH: layer DH):
    sim R LH (〚M〛 LL ⊕ LL) ->
    LL ⊢ (R, M) : LH.
  Proof.
    tauto.
  Qed.

  Lemma vdash_oplus_empty {D1 D2} L1 (R: simrel D1 D2) M L2:
    L1 ⊢ (R, M) : L2 ->
    L1 ⊢ (R, M ⊕ ∅) : L2.
  Proof.
    intros HM.
    eapply (conseq_le_right _ _ _ (L2 ⊕ ∅)).
    - eapply hcomp_rule.
      + right.
        apply layers_disjoint_empty.
      + assumption.
      + simpl.
        apply lower_bound.
    - apply left_upper_bound.
  Qed.
End WITH_SEMANTICS.
