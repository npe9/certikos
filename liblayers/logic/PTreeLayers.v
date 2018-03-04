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
Require Import Coq.Lists.List.
Require Import compcert.common.AST. (* For ident. *)
Require Import liblayers.compcertx.ErrorMonad.
Require Import liblayers.lib.OptionMonad.
Require Import liblayers.lib.Decision.
Require Import liblayers.logic.PseudoJoin.
Require Import liblayers.logic.OptionOrders.
Require Import liblayers.logic.PTrees.
Require Import liblayers.logic.PTreeModules.
Require Export liblayers.logic.Layers.
Require Export liblayers.logic.Primitives.


(** * Construction of layers *)

Definition ptree_layer {layerdata} primsem V (D: layerdata) :=
  (PTree.t (res (primsem D)) * PTree.t (res V))%type.

Section PTREE_LAYER_INSTANCES.
  Context {layerdata simrel} `{Hprim: Primitives layerdata simrel}.
  Context {V: Type}.
  Local Existing Instance ptree_mapsto.

  Definition ptree_layer_conflict i :=
    MSG "duplicate symbol in layer: " :: CTX i :: nil.

  (** ** Querying functions *)

  (** The functions [ptree_layer_primitive] and [ptree_layer_globvar]
    retreive the primitive semantics or global variable definition
    associated with an identifier in a given layer. Because we want
    them to be monotonic, we need to distinguish between two kinds of
    failures.

    Consider [ptree_layer_primitive]. If the layer does not associate
    a primitive semantics to identifier [i], which is to say it is
    undefined at [i], or it is defined a a variable definition, then
    [ptree_layer_primitive] return [OK None]. We can interpret this
    as a successful determination that there is no primitive semantics
    at [i]. On the other hand, is the layer maps [i] to [anything]
    (the special "overdefined" value), then all bets are off: a
    smaller layer may very well contain a primitive
    definition. Consequently, [ptree_layer_primitive] returns [Error]
    to indicate failure to make any determination at all.

    The same principle applies for [ptree_layer_globvar]. *)

  Definition ptree_layer_primitive {D} i (L: ptree_layer primsem V D) :=
    option_res_flip ((fst L) ! i).

  Definition ptree_layer_globalvar {D} i (L: ptree_layer primsem V D) :=
    option_res_flip ((snd L) ! i).

  Local Instance ptree_layer_sim_op:
    Sim simrel (ptree_layer primsem V) :=
    {
      simRR D1 D2 R :=
        ptree_rel (option_le (res_le (sim R))) *
        ptree_rel (option_le (res_le eq))
    }.

  Local Instance ptree_layer_rg_sim_prf:
    ReflexiveGraphSim layerdata simrel (ptree_layer primsem V).
  Proof.
    split.
    * typeclasses eauto.
    * simpl.
      intros D1 D2 R.
      intros L1a L2a [L1af L2af HLaf L1av L2av HLav].
      intros L1b L2b [L1bf L2bf HLbf L1bv L2bv HLbv].
      inversion 1 as [? ? Hf ? ? Hv]; subst; clear H.
      constructor.
      + intros i.
        specialize (HLaf i).
        specialize (HLbf i).
        specialize (Hf i).
        revert Hprim HLaf HLbf Hf; clear; intros.
        destruct Hf as [y | x y Hxy];
          inversion HLaf; subst; try constructor;
          inversion HLbf; subst; try constructor.
        revert Hprim Hxy H1 H3; clear; intros.
        destruct Hxy as [x y Hxy | x err];
          inversion H3; subst; try constructor;
          inversion H1; subst; try constructor.
        rewrite H4.
        rewrite <- H0.
        assumption.
      + rewrite HLav.
        rewrite <- HLbv.
        assumption.
  Qed.

  Existing Instance option_res_oplus_op.
  Existing Instance ptree_emptyset.
  Existing Instance ptree_oplus.
  Existing Instance ptree_mapsto.

  Local Instance ptree_layer_ops:
    LayerOps ident primsem V (ptree_layer primsem V) :=
    {
      layer_empty D := {| emptyset := (PTree.empty _, PTree.empty _) |};
      layer_oplus D := {| oplus L1 L2 := (fst L1 ⊕ fst L2, snd L1 ⊕ snd L2) |};
      layer_mapsto_primitive D := {| mapsto i σ := (i ↦ OK σ, ∅) |};
      layer_mapsto_globalvar D := {| mapsto i τ := (∅, i ↦ OK τ) |};
      get_layer_primitive := @ptree_layer_primitive;
      get_layer_globalvar := @ptree_layer_globalvar;
      layers_disjoint D1 D2 L1 L2 :=
        ptree_disjoint (fst L1) (fst L2) /\
        ptree_disjoint (snd L1) (snd L2)
    }.
  Proof.
  * intros.
    unfold ptree_layer_primitive.
    refine (_
              (ptree_forall_decision_strong
                 (fun _ def => P (option_res_flip (Some def)))
                 (P (OK None))
                 _ _ (fst L))).
    apply decide_rewrite.
    split.
    + intros J i.
      generalize (J i).
      destruct ((fst L) ! i); simpl; monad_norm; auto.
    + intros J i.
      generalize (J i).
      destruct ((fst L) ! i); simpl; monad_norm; auto.
  * intros D P DP M.
    refine (_
              (ptree_forall_decision
                 (fun i _ => ptree_layer_primitive i M = OK None \/ P i) 
                 _ (fst M))).
    + apply decide_rewrite.
      unfold ptree_layer_primitive.
      unfold ptree_forall.
      split.
      - intros J i.
        destruct ((fst M) ! i) eqn:HM; try (compute; congruence).
        rewrite <- HM.
        intro.
        destruct (J _ _ HM); try contradiction.
        assumption.
      - intros.
        destruct (decide (option_res_flip (fst M) ! i = OK None)); auto.
    + intros; typeclasses eauto.
  * intros.
    unfold ptree_layer_globalvar.
    refine (_
              (ptree_forall_decision_strong
                 (fun _ def => P (option_res_flip (Some def)))
                 (P (OK None))
                 _ _ (snd L))).
    apply decide_rewrite.
    split.
    + intros J i.
      generalize (J i).
      destruct ((snd L) ! i); simpl; monad_norm; auto.
    + intros J i.
      generalize (J i).
      destruct ((snd L) ! i); simpl; monad_norm; auto.
  * intros D P DP M.
    refine (_
              (ptree_forall_decision
                 (fun i _ => ptree_layer_globalvar i M = OK None \/ P i) 
                 _ (snd M))).
    + apply decide_rewrite.
      unfold ptree_layer_globalvar.
      unfold ptree_forall.
      split.
      - intros J i.
        destruct ((snd M) ! i) eqn:HM; try (compute; congruence).
        rewrite <- HM.
        intro.
        destruct (J _ _ HM); try contradiction.
        assumption.
      - intros.
        destruct (decide (option_res_flip (snd M) ! i = OK None)); auto.
    + intros; typeclasses eauto.
  * typeclasses eauto.
  Defined.

  Arguments fmap : simpl never.

  Global Instance ptree_layer_primitive_monotonic:
    Proper
      (∀ R, - ==> sim R ++> res_le (option_le (sim R)))
      (@ptree_layer_primitive).
  Proof.
    unfold ptree_layer_primitive.
    intros D1 D2 R i L1 L2 HL.
    solve_monotonic.
    apply HL.
  Qed.

  Global Instance ptree_layer_globalvar_monotonic:
    Proper
      (∀ R, - ==> sim R ++> res_le (option_le eq))
      (@ptree_layer_globalvar).
  Proof.
    unfold ptree_layer_globalvar.
    intros D1 D2 R i L1 L2 HL.
    solve_monotonic.
    apply HL.
  Qed.

  Local Opaque PTree.combine.
  Local Opaque option_res_oplus_op.

  Global Instance ptree_layer_sim_pseudojoin:
    SimPseudoJoin layerdata simrel (ptree_layer primsem V) (fun D => (∅, ∅)).
  Proof.
    split; try typeclasses eauto.
    * intros D1 D2 R L H [Lp Lv].
      rewrite H.
      constructor; apply lower_bound.
    * intros D1 D2 R.
      intros _ _ [L1p L2p Hp L1v L2v Hv].
      intros _ _ [L1p' L2p' Hp' L1v' L2v' Hv'].
      constructor.
      + simpl.
        intros i.
        rewrite !PTree.gcombine by reflexivity.
        destruct (Hp  i) as [[[|]|] | _ _ [|? [|]]]; repeat constructor;
        destruct (Hp' i) as [[[|]|] | _ _ [|? [|]]]; repeat constructor;
        eauto.
      + simpl.
        intros i.
        rewrite !PTree.gcombine by reflexivity.
        destruct (Hv  i) as [[[|]|] | _ _ [|? [|]]]; repeat constructor;
        destruct (Hv' i) as [[[|]|] | _ _ [|? [|]]]; repeat constructor;
        eauto.
    * intros D L HL [Lp Lv].
      rewrite HL; clear L HL.
      constructor; intro i.
      + simpl.
        rewrite PTree.gcombine by reflexivity.
        rewrite PTree.gempty.
        destruct (Lp!i); reflexivity.
      + simpl.
        rewrite PTree.gcombine by reflexivity.
        rewrite PTree.gempty.
        destruct (Lv!i); reflexivity.
    * intros D [L1p L1v] [L2p L2v] [L3p L3v].
      simpl.
      constructor.
      + apply @associativity.
        apply ptree_combine_assoc.
        - reflexivity.
        - intros [[|]|] [[|]|] [[|]|]; repeat constructor; reflexivity.
      + apply @associativity.
        apply ptree_combine_assoc.
        - reflexivity.
        - intros [[|]|] [[|]|] [[|]|]; repeat constructor; reflexivity.
    * intros D [L1p L1v] [L2p L2v].
      simpl.
      constructor.
      + intros i.
        rewrite !PTree.gcombine by reflexivity.
        apply @commutativity.
        intros [[|]|] [[|]|]; repeat constructor; reflexivity.
      + intros i.
        rewrite !PTree.gcombine by reflexivity.
        apply @commutativity.
        intros [[|]|] [[|]|]; repeat constructor; reflexivity.
    * intros D [L1p L1v] [L2p L2v].
      simpl.
      constructor.
      + intros i.
        rewrite !PTree.gcombine by reflexivity.
        apply @left_upper_bound.
        intros [[|]|] [[|]|]; repeat constructor; reflexivity.
      + intros i.
        rewrite !PTree.gcombine by reflexivity.
        apply @left_upper_bound.
        intros [[|]|] [[|]|]; repeat constructor; reflexivity.
  Qed.

  Local Transparent option_res_oplus_op.

  Lemma option_fold {A} (o: option A):
    match o with
      | Some x => Some x
      | None => None
    end = o.
  Proof.
    destruct o; reflexivity.
  Qed.

  Local Instance ptree_layer_prf:
    Layers ident primsem V (ptree_layer primsem V).
  Proof.
    split.
    * typeclasses eauto.
    * simpl.
      solve_monotonic.

    * intros D i.
      simpl.
      unfold ptree_layer_primitive; simpl.
      rewrite PTree.gempty.
      reflexivity.
    * intros D i σ.
      simpl.
      unfold ptree_layer_primitive; simpl.
      rewrite PTree.gss.
      reflexivity.
    * intros D i j σ Hij.
      simpl.
      unfold ptree_layer_primitive; simpl.
      rewrite PTree.gso by assumption.
      rewrite PTree.gempty.
      reflexivity.
    * intros D i j τ.
      simpl.
      unfold ptree_layer_primitive; simpl.
      rewrite PTree.gempty.
      reflexivity.
    * intros D i L1 L2.
      simpl.
      unfold ptree_layer_primitive; simpl.
      rewrite PTree.gcombine by reflexivity.
      destruct ((fst L1) ! i) as [[σ1|]|];
      destruct ((fst L2) ! i) as [[σ2|]|];
      simpl;
      monad_norm;
      simpl;
      solve_monotonic.
    * typeclasses eauto.

    * intros D i.
      simpl.
      unfold ptree_layer_globalvar.
      rewrite PTree.gempty.
      reflexivity.
    * simpl.
      intros D i τ.
      unfold ptree_layer_globalvar; simpl.
      rewrite PTree.gss.
      reflexivity.
    * simpl.
      intros D i j τ Hij.
      unfold ptree_layer_globalvar; simpl.
      rewrite PTree.gso by assumption.
      rewrite PTree.gempty.
      reflexivity.
    * simpl.
      intros D i j τ.
      unfold ptree_layer_globalvar; simpl.
      rewrite PTree.gempty.
      reflexivity.
    * simpl.
      intros D i L1 L2.
      unfold ptree_layer_globalvar; simpl.
      rewrite PTree.gcombine by reflexivity.
      destruct ((snd L1) ! i) as [[τ1|]|];
      destruct ((snd L2) ! i) as [[τ2|]|];
      simpl;
      monad_norm;
      simpl;
      solve_monotonic.
    * typeclasses eauto.

    * intros D1 D2 L.
      split; intros i xi; simpl; rewrite PTree.gempty; discriminate.

    * intros D D' R [Lp Lv] [L1p L1v] [L2p L2v] [HLL2p HLL2v] H.
      Local Opaque option_res_oplus_op.
      simpl in *.
      inversion H as [? ? Hp ? ? Hv]; subst; clear H.
      constructor.
      + intros i.
        specialize (Hp i).
        specialize (HLL2p i); simpl in *.
        destruct (Lp ! i) as [σ|]; repeat constructor.
        specialize (HLL2p σ eq_refl).
        rewrite PTree.gcombine in Hp by reflexivity.
        rewrite HLL2p in Hp.
        destruct (L1p ! i) as [[|]|];
        assumption.
      + intros i.
        specialize (Hv i).
        specialize (HLL2v i); simpl in *.
        destruct (Lv ! i) as [τ|]; repeat constructor.
        specialize (HLL2v τ eq_refl).
        rewrite PTree.gcombine in Hv by reflexivity.
        rewrite HLL2v in Hv.
        destruct (L1v ! i) as [[|]|];
        assumption.
  Qed.
End PTREE_LAYER_INSTANCES.

(** Now, we can forget how [ptree_layer] is defined, and only access
  it through the interfaces above. This is necessary, to avoid
  instances from [PTree.v] to sneak in when using [ptree_layer]s.
  But it makes sense anyway. *)
Global Opaque ptree_layer.
Global Opaque ptree_layer_ops.
