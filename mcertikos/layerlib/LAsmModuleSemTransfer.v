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
Require Import Coqlib.
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Asm.
Require Import Conventions.
Require Import Machregs.
Require Import Observation.

Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.PTreeSemantics.
Require Import liblayers.compcertx.MemWithData.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatData.
Require Import liblayers.compat.CompatPrimSem.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatExternalCalls.

Require Import LAsmModuleSemDef.
Require Import LAsm.

Section TRANSFER.

  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.

  Context `{make_program_ops: !MakeProgramOps LAsm.function Ctypes.type LAsm.fundef unit}.
  Context `{make_program_prf: !MakeProgram LAsm.function Ctypes.type LAsm.fundef unit}.

  Lemma AccessorsDefined_oplus' `{D: compatdata}
        {L: compatlayer D}:
    forall i (σi: globvar Ctypes.type),
      AccessorsDefined (L ⊕ i ↦ σi) ->
      AccessorsDefined L.
  Proof.
    intros. apply accessors_defined_true in H.
    constructor. unfold accessors_defined in *.
    simpl in *.
    destruct (cl_exec_load L); try discriminate.
    destruct o; try discriminate.
    destruct (cl_exec_store L); try discriminate.
    destruct o; try discriminate.
    reflexivity.
  Qed.

  (*Lemma make_program_var_transfer `{D: compatdata} (L: compatlayer D) (M: module):
    forall s v τ,
    make_program s (M ⊕ v ↦ τ) L =
    make_program s M (L  ⊕ v ↦ τ).
  Proof.
  Qed.*)

  Require Import LAsmModuleSemAux.
  Require Import LAsmModuleSemProp.
  (*Require Import LayerModuleLemma.*)
  Require Import LAsmModuleSemSim.

  (*Lemma layer_oplus_globalvar_ok {D} (L: _ D) i (τ: globvar Ctypes.type):
    isOKNone (get_layer_primitive i L) ->
    isOKNone (get_layer_globalvar i L) ->
    LayerOK L ->
    LayerOK (L ⊕ i ↦ τ).
  Proof.
  Qed.*)

  Lemma accessors_weak_var_oplus `{D: compatdata}
        {L: compatlayer D}:
    forall (i: ident) (τ: globvar Ctypes.type), 
      accessors_weak_defined L = true ->
      accessors_weak_defined (L ⊕ i ↦ τ) = true.
  Proof.
    intros. unfold accessors_weak_defined in *.
    simpl in *. destruct (cl_exec_load L); try discriminate.
    destruct (cl_exec_store L); try discriminate.
    destruct o; destruct o0; simpl; try reflexivity.
  Qed.

  Lemma get_layer_primitive_oplus_var_same `{D: compatdata}
        {L: compatlayer D}:
    forall (i: ident) (τ: globvar Ctypes.type),
      LayerOK (L ⊕ i ↦ τ) ->
      forall i0,
      get_layer_primitive i0 L = get_layer_primitive i0 (L ⊕ i ↦ τ).
  Proof.
    intros. destruct (H i0) as [PrimOK _ _].
    destruct PrimOK as [? PrimOK].
    specialize (get_layer_primitive_oplus i0 L (i ↦ τ)).
    rewrite PrimOK.
    assert (HW: get_layer_primitive (D:=D) i0 (i ↦ τ) = OK None).
    {
      get_layer_normalize. reflexivity.
    }
    rewrite HW.
    destruct (get_layer_primitive i0 L); intros Hle; try destruct o;
    inv_monad Hle; reflexivity.
  Qed.

  Lemma layer_oplus_var_valid `{D: compatdata}
        {L: compatlayer D}:
    forall (i: ident) (τ: globvar Ctypes.type) s,
    forall (layer_valid: get_layer_prim_valid L s),
    get_layer_prim_valid L s->
    get_layer_prim_valid (L ⊕ i ↦ τ) s.
  Proof.
    intros. revert H.
    unfold get_layer_prim_valid.
    intros.
    eapply (H i0).
    specialize (get_layer_primitive_oplus i0 L (i ↦ τ)).
    rewrite H0.
    assert (Hvar:get_layer_primitive (D:=D) i0 (i ↦ τ) = OK None).
    {
      get_layer_normalize. reflexivity.
    }
    rewrite Hvar.
    destruct (get_layer_primitive i0 L);
    try destruct o; intros Hle; inv_monad Hle.
    reflexivity.
  Qed.

  Lemma layer_names_match_var_oplus {D} (L1: compatlayer D):
    forall (i: ident) (τ: globvar Ctypes.type),
    LayerOK (L1 ⊕ (i ↦ τ)) ->
    LayerNamesMatch D L1 ->
    LayerNamesMatch D (L1 ⊕ (i ↦ τ)).
  Proof.
    intros i τ HLplus [HL1ok HL1match].
    split; try assumption.
    intros i0 j σ Hi Hj.
    eapply HL1match; eauto.
    erewrite <- get_layer_primitive_oplus_var_same in Hi; try eassumption.
  Qed.

  Lemma layer_oplus_invs_prim_var `{D: compatdata}
        {L: compatlayer D}:
    forall (i: ident) (τ: globvar Ctypes.type),
      LayerOK (L ⊕ i ↦ τ) ->
      PrimcallInvariantsDefined L ->
      PrimcallInvariantsDefined (L ⊕ i ↦ τ).
  Proof.
    intros.
    unfold PrimcallInvariantsDefined in *.
    intros.
    erewrite <- get_layer_primitive_oplus_var_same; try eassumption.
    eapply H0.
  Qed.

  Lemma layer_oplus_invs_ext_var `{D: compatdata}
        {L: compatlayer D}:
    forall (i: ident) (τ: globvar Ctypes.type),
      LayerOK (L ⊕ i ↦ τ) ->
      ExtcallInvariantsDefined L ->
      ExtcallInvariantsDefined (L ⊕ i ↦ τ).
  Proof.
    intros.
    unfold ExtcallInvariantsDefined in *.
    intros.
    erewrite <- get_layer_primitive_oplus_var_same; try eassumption.
    eapply H0.
  Qed.

  Require Import LAsmModuleSem.

  Lemma LAsm_transfer_variable `{DL: compatdata} (LL: compatlayer DL) (M: module):
    forall (i v: ident) (τ: globvar Ctypes.type) x
           (LOK_L: LayerOK (〚M 〛 (LL ⊕ v ↦ τ) ⊕ LL ⊕ v ↦ τ)),
      res_le (option_le (compatsem_le DL))
             (OK (Some (LAsmModuleSemDef.lasm_primsem M (LL ⊕ v ↦ τ) i x)))
             (OK (Some (LAsmModuleSemDef.lasm_primsem (M ⊕ v ↦ τ) LL i x))).
  Proof.
    Local Opaque oplus semof mapsto compatlayer_ops.
    intros. 
    assert (HlayerOK: LayerOK (LL ⊕ v ↦ τ)).
    {
      eapply layer_ok_antitonic; try eassumption.
      unfold flip.
      apply right_upper_bound.
    }

    constructor. constructor.
    constructor. constructor; simpl; [|reflexivity|constructor].
    constructor; simpl; [|reflexivity|].
    - intros s Hs.
      inversion 1. 
      exploit (AccessorsDefined_oplus' (D:=DL) (L:=LL)); try eassumption.
      intros acc_def_prf'.

      pose proof Hge as HgeL.
      simpl in *.
      destruct (Decision.decide (ExtcallInvariantsDefined LL)); try discriminate.
      destruct (Decision.decide (PrimcallInvariantsDefined LL)); try discriminate.
      destruct (Decision.decide (LayerNamesMatch DL LL)); try discriminate.
      destruct (Decision.decide (get_layer_prim_valid LL s)); try discriminate.
      caseEq (accessors_weak_defined LL); intros; rewrite H0 in *;
      try discriminate.
      rename H0 into Hacc.

      assert (Hmake: isOK (make_program s (M ⊕ v ↦ τ) LL)).
      {
        caseEq (make_program s (M ⊕ v ↦ τ) LL); intros;
        rewrite H0 in *; try discriminate.
        esplit; eauto.
      }
      assert (OKLayer: LayerOK LL).
      {
        eapply make_program_layer_ok; eauto.
      }

      assert (Hge': make_globalenv s (M ⊕ v ↦ τ) LL = ret ge).
      {
        destruct Hmake as [p' Hmake].
        pose proof Hmake as Hmake'.
        eapply make_program_var_transfer in Hmake; try eassumption.
        eapply make_program_make_globalenv in Hmake.
        unfold module, module_ops, ident in *.
        simpl in *. unfold ident in *.
        rewrite Hge in Hmake.
        inv Hmake.
        eapply make_program_make_globalenv in Hmake'.
        assumption.
      }

      econstructor; eauto.
      eapply plus_sim_plus; eauto.
      intros. 
      apply plus_one.
      eapply (layer_le_step (LL ⊕ v ↦ τ) LL); eauto; intros.
      Local Transparent oplus mapsto semof compatlayer_ops.
      * unfold acc_exec_load in *.
        destruct (acc_exec_load_strong LL).
        destruct (acc_exec_load_strong (LL ⊕ v ↦ τ)).
        simpl in e1. rewrite e0 in e1.
        inv_monad e1. inv H3.
        assumption.
      * unfold acc_exec_store in *.
        destruct (acc_exec_store_strong LL).
        destruct (acc_exec_store_strong (LL ⊕ v ↦ τ)).
        simpl in e1. rewrite e0 in e1.
        inv_monad e1. inv H3.
        assumption.
      * apply make_globalenv_stencil_matches in Hge.
        eapply stencil_matches_unique in Hge; try apply H1; subst.              
        assumption.
      * specialize (get_layer_primitive_oplus i0 LL (v ↦ τ)).
        rewrite H1. get_layer_normalize.
        intros Hle.
        destruct (get_layer_primitive i0 LL); try destruct o;
        inv_monad Hle.
        esplit. split; reflexivity.

    - (* sprimcall_valid *)
      Local Opaque oplus semof mapsto compatlayer_ops.
      simpl. intros.
      destruct (Decision.decide (ExtcallInvariantsDefined LL)); try discriminate.
      destruct (Decision.decide (PrimcallInvariantsDefined LL)); try discriminate.
      destruct (Decision.decide (LayerNamesMatch DL LL)); try discriminate.
      destruct (Decision.decide (get_layer_prim_valid LL s)); try discriminate. 
      caseEq (accessors_weak_defined LL); intros; rewrite H0 in *;
      try discriminate.
      rename H0 into Hacc.
      assert (Hmake: isOK (make_program s (M ⊕ v ↦ τ) LL)).
      {
        caseEq (make_program s (M ⊕ v ↦ τ) LL); intros;
        rewrite H0 in *; try discriminate.
        esplit; eauto.
      }
      assert (OKLayer: LayerOK LL).
      {
        eapply make_program_layer_ok; eauto.
      }
      assert (OKModule: ModuleOK (M ⊕ v ↦ τ)).
      {
        eapply make_program_module_ok; eauto.
      }
      exploit (make_program_get_module_variable_prop s (M ⊕ v ↦ τ) LL v); try eassumption.
      {
        destruct (OKModule v) as [_ VarOK _].
        eapply get_module_variable_right; try assumption.
        get_module_normalize. reflexivity.
      }
      intros [Hf[Hprim Hvar]].

      (*exploit (layer_oplus_globalvar_ok LL v τ); try eassumption.
      intros HlayerOK. *)
      destruct Hmake as [p' Hmake].        
      destruct (Decision.decide
                  (ExtcallInvariantsDefined (LL ⊕ v ↦ τ))).
      destruct (Decision.decide
                  (PrimcallInvariantsDefined (LL ⊕ v ↦ τ))).
      destruct (Decision.decide
                  (LayerNamesMatch DL (LL ⊕ v ↦ τ))).
      destruct (Decision.decide
                  (get_layer_prim_valid (LL ⊕ v ↦ τ) s)).
      Local Transparent layer_oplus mapsto.

      rewrite (accessors_weak_var_oplus v τ Hacc).

      * eapply make_program_var_transfer in Hmake; try eassumption.
        rewrite Hmake. reflexivity.
      * elim n.
        eapply layer_oplus_var_valid; eauto.
      * elim n.
        eapply layer_names_match_var_oplus; eauto.
      * elim n.
        eapply layer_oplus_invs_prim_var; eassumption.
      * elim n.
        eapply layer_oplus_invs_ext_var; eassumption.
  Qed.

End TRANSFER.