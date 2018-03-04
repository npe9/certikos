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
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import compcertx.ia32.AsmX.
Require Import liblayers.lib.Decision.
Require Import liblayers.compcertx.ErrorMonad.
Require Export liblayers.logic.Layers.
Require Export liblayers.logic.PTreeLayers.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.LayerLogicImpl.
Require Export liblayers.compcertx.Stencil.
Require Export liblayers.compcertx.MemWithData.
Require Export liblayers.compat.CompatData.
Require Export liblayers.compat.CompatPrimSem.
Require Export liblayers.compat.CompatLayerDef.
Require Export liblayers.compat.CompatLayerFacts.
Require Import liblayers.compcertx.Observation.

Section WITH_MEMORY_MODEL.
  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel} `{Hmem': !UseMemWithData mem}.

  (** We need to know that external functions preserve kernel mode
    (and also other invariants) *)

  Definition sextcall_invs_defined {D} (σ: res (option (compatsem D))): bool :=
    match σ with
      | OK (Some (inl f)) =>
        match sextcall_invs _ f with
          | Error _ => false
          | _ => true
        end
      | _ => true
    end.

  Definition ExtcallInvariantsDefined {D} (L: compatlayer D): Prop :=
    forall i,
      (fun f => sextcall_invs_defined f = true)
      (get_layer_primitive i L).

  (* Declaring this instance is necessary to avoid [Existing Class]
    getting in the way of instance resolution *)
  Global Instance extcall_invariants_defined_dec:
    forall {D} (L: _ D), Decision.Decision (ExtcallInvariantsDefined L) := _.

  Existing Class ExtcallInvariantsDefined.

  (** Let us do the same for [PrimcallInvariants]. *)

  Definition sprimcall_invs_defined {D} (σ: res (option (compatsem D))): bool :=
    match σ with
      | OK (Some (inr f)) =>
        match sprimcall_invs _ f with
          | Error _ => false
          | _ => true
        end
      | _ => true
    end.

  Definition PrimcallInvariantsDefined {D} (L: compatlayer D): Prop :=
    forall i,
      (fun f => sprimcall_invs_defined f = true)
      (get_layer_primitive i L).

  (* Declaring this instance is necessary to avoid [Existing Class]
    getting in the way of instance resolution *)
  Global Instance primcall_invariants_defined_dec:
    forall {D} (L: _ D), Decision.Decision (PrimcallInvariantsDefined L) := _.

  Existing Class PrimcallInvariantsDefined.

  (** More general, less decidable classes. *)

  Class ExtcallInvariantsAvailable {D} (L: compatlayer D) :=
    extcall_invariants_available i σ:
      get_layer_primitive i L = OK (Some (compatsem_inl σ)) ->
      ExtcallInvariants σ.

  Class PrimcallInvariantsAvailable {D} (L: compatlayer D) :=
    primcall_invariants_available i σ:
      get_layer_primitive i L = OK (Some (compatsem_inr σ)) ->
      PrimcallInvariants σ.

  Global Instance extcall_invariants_defined_available {D} (L: compatlayer D):
    ExtcallInvariantsDefined L ->
    ExtcallInvariantsAvailable L.
  Proof.
    intros H i σ Hσ.
    specialize (H i).
    rewrite Hσ in H; clear Hσ.
    destruct σ as [step props invs]; simpl in *.
    destruct invs.
    * assumption.
    * discriminate.
  Qed.

  Global Instance primcall_invariants_defined_available {D} (L: compatlayer D):
    PrimcallInvariantsDefined L ->
    PrimcallInvariantsAvailable L.
  Proof.
    intros H i σ Hσ.
    specialize (H i).
    rewrite Hσ in H; clear Hσ.
    destruct σ as [step name props invs]; simpl in *.
    destruct invs.
    * assumption.
    * discriminate.
  Qed.

  Import Maps.
  Local Transparent ptree_layer_ops.

  Local Instance extcall_invariants_oplus {D} (L1 L2: compatlayer D):
    ExtcallInvariantsAvailable L1 ->
    ExtcallInvariantsAvailable L2 ->
    ExtcallInvariantsAvailable (L1 ⊕ L2).
  Proof.
    intros HL1 HL2 i σ Hσ.
    specialize (HL1 i).
    specialize (HL2 i).
    simpl in *.
    unfold ptree_layer_primitive in *; simpl in *.
    rewrite PTree.gcombine in Hσ by reflexivity.
    destruct ((fst (cl_base_layer L1)) ! i) as [[|]|];
    destruct ((fst (cl_base_layer L2)) ! i) as [[|]|];
    inversion Hσ; subst;
    simpl in *; monad_norm; simpl in *;
    eauto.
  Qed.

  Local Instance primcall_invariants_oplus {D} (L1 L2: compatlayer D):
    PrimcallInvariantsAvailable L1 ->
    PrimcallInvariantsAvailable L2 ->
    PrimcallInvariantsAvailable (L1 ⊕ L2).
  Proof.
    intros HL1 HL2 i σ Hσ.
    specialize (HL1 i).
    specialize (HL2 i).
    simpl in *.
    unfold ptree_layer_primitive in *; simpl in *.
    rewrite PTree.gcombine in Hσ by reflexivity.
    destruct ((fst (cl_base_layer L1)) ! i) as [[|]|];
    destruct ((fst (cl_base_layer L2)) ! i) as [[|]|];
    inversion Hσ; subst;
    simpl in *; monad_norm; simpl in *;
    eauto.
  Qed.

  Lemma cl_le_invs_ext `{D: compatdata}
        {L1 L2: compatlayer D}:
    forall (OKLayer: LayerOK L2),
      L1 ≤ L2 ->
      ExtcallInvariantsDefined L2 ->
      PrimcallInvariantsDefined L2 ->
      ExtcallInvariantsDefined L1.
  Proof.
    intros. inv H.
    eapply cl_le_layer_pointwise in cl_sim_layer.
    destruct cl_sim_layer as [Hprim _].
    unfold ExtcallInvariantsDefined in *.
    unfold PrimcallInvariantsDefined in *.
    intros. specialize (Hprim i). specialize (H0 i). specialize (H1 i).
    unfold LayerOK in OKLayer.
    destruct (OKLayer i) as [[σ Hσ] _ _].
    unfold sextcall_invs_defined in *.
    unfold sprimcall_invs_defined in *.
    destruct (get_layer_primitive i L2) as [[|]|]; simpl.
    - destruct c. 
      + inv Hprim. inv H3. 
        * reflexivity.
        * inv H5. simpl.
          specialize (sextcall_primsem_le_invs _ _ H4).
          simpl in H0.
          destruct (sextcall_invs D s); try discriminate.
          intros Hle. inv Hle. reflexivity.
      + inv Hprim. inv H3.
        * reflexivity.
        * inv H5. simpl.
          reflexivity. 
    - inv Hprim. inv H3. reflexivity.
    - inv Hσ.
  Qed.

  Lemma cl_le_invs_prim `{D: compatdata}
        {L1 L2: compatlayer D}:
    forall (OKLayer: LayerOK L2),
      L1 ≤ L2 ->
      ExtcallInvariantsDefined L2 ->
      PrimcallInvariantsDefined L2 ->
      PrimcallInvariantsDefined L1.
  Proof.
    intros. inv H.
    eapply cl_le_layer_pointwise in cl_sim_layer.
    destruct cl_sim_layer as [Hprim _].
    unfold ExtcallInvariantsDefined in *.
    unfold PrimcallInvariantsDefined in *.
    intros. specialize (Hprim i). specialize (H0 i). specialize (H1 i).
    unfold LayerOK in OKLayer.
    destruct (OKLayer i) as [[σ Hσ] _ _].
    unfold sextcall_invs_defined in *.
    unfold sprimcall_invs_defined in *.
    destruct (get_layer_primitive i L2) as [[|]|]; simpl.
    - destruct c. 
      + inv Hprim. inv H3. 
        * reflexivity.
        * inv H5. simpl. reflexivity.
      + inv Hprim. inv H3.
        * reflexivity.
        * inv H5; simpl.
          specialize (sprimcall_primsem_le_invs _ _ H4).
          destruct (sprimcall_invs D s); try discriminate.
          intros Hle. inv Hle. reflexivity.
    - inv Hprim. inv H3. reflexivity.
    - inv Hσ.
  Qed.

  Lemma cl_le_get_layer_prim_valid `{D: compatdata}
        {L1 L2: compatlayer D} {s: stencil}:
    forall (OKLayer: LayerOK L2),
      L1 ≤ L2 ->
      get_layer_prim_valid L2 s ->
      get_layer_prim_valid L1 s.
  Proof.
    intros. inv H.
    apply cl_le_layer_pointwise in cl_sim_layer.
    destruct cl_sim_layer as [Hprim Hvar].
    unfold get_layer_prim_valid in *.
    intros. specialize (H0 i). specialize (Hprim i).
    rewrite H in Hprim.
    destruct (OKLayer i) as [[σ Hσ] _ _].
    inv Hprim; simpl in *.
    - rewrite <- H2 in H0.
      inv H3; simpl in *. 
      specialize (H0 _ refl_equal).
      unfold compatsem_valid in *.
      inv H4; simpl in *.
      * inv H1. eapply sextcall_info_le_valid; try eassumption.  
      * inv H1. eapply sprimcall_info_le_valid; eassumption.  
    - rewrite <- H3 in Hσ.
      inv Hσ.
  Qed.
End WITH_MEMORY_MODEL.