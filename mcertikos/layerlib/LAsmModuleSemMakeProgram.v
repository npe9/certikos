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
(** This file provide the semantics for the [Asm] instructions. Since we introduce paging mechanisms, the semantics of memory load and store are different from [Compcert Asm]*)
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
Require Import AsmX.
Require Import Conventions.
Require Import Machregs.
Require Import AuxLemma.
Require Import CommonTactic.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.PTreeSemantics.
Require Import liblayers.compcertx.MemWithData.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatData.
Require Import liblayers.compat.CompatPrimSem.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatExternalCalls.
Require Import CompCertBuiltins.
Require Import LAsm.
Require Import MemoryExtra.
Require Import Observation.

Require Export LAsmModuleSemDef.
Require Import LAsmModuleSemAux.
(*Require Export LAsmModuleSemProp.
Require Import LAsmModuleSemHighInv.
Require Import LAsmModuleSemLowInv.
Require Import LAsmModuleSemAsmInv.
Require Import LAsmModuleSemMonotonic.*)

(** ** Semantics of LAsm modules *)

Section ModuleSemantics.

  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
  Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

  Opaque module_oplus.

  Lemma make_globalenv_vertical:
    forall D s M L i κi σi ge ge',
      semof_fundef D M L i κi = OK σi
      -> make_globalenv s M (L ⊕ i ↦ σi) = ret ge
      -> make_globalenv s (M ⊕ i ↦ κi) L = ret ge'
      (* For internal functions *)
      ->(forall b f, Genv.find_funct_ptr ge b = Some (Internal f)
                     -> Genv.find_funct_ptr ge' b = Some (Internal f))
        (* For external functions that not i*)
        /\ (forall b id sg, 
              id <> i
              -> Genv.find_funct_ptr ge b = Some (External (EF_external id sg))
              -> Genv.find_funct_ptr ge' b = Some (External (EF_external id sg)))
        (* For i*)
        /\ (forall b sg, 
              Genv.find_funct_ptr ge b = Some (External (EF_external i sg))
              -> Genv.find_funct_ptr ge' b = Some (Internal κi)).
  Proof.
    intros until ge'.
    intros SEMOF Hge Hge'.
    assert (MOK: ModuleOK (M ⊕ i ↦ κi)).
    {
      unfold make_globalenv in Hge'.
      inv_monad Hge'.
      eapply make_program_module_ok with (s0 := s) (L0 := L).
      unfold isOK. eauto.
    }

    split.
    {
      intros.
      exploit @make_globalenv_find_funct_ptr.
      { eexact Hge. }
      { eassumption. }
      destruct 1 as (j & SYMB & K).
      destruct K as [K | K].
      {
        destruct K as (? & MOD & INT).
        exploit @make_globalenv_get_module_function.
        { eexact Hge'. }
        {
          instantiate (2 := j).
          instantiate (1 := f).
          exploit @get_module_function_monotonic.
          { apply (oplus_le_left M (i ↦ κi)). }
          instantiate (1 := j).
          rewrite MOD.
          inversion 1; subst.
          {
            inv H3.
            simpl in INT. congruence.
          }
          exfalso.
          symmetry in H3.
          destruct (MOK j) as [[κ Hκ] _ _].
          congruence.
        }
        { reflexivity. }
        destruct 1 as (b' & SYMB' & FUNCT').
        erewrite stencil_matches_symbols in SYMB by eauto using make_globalenv_stencil_matches.
        erewrite stencil_matches_symbols in SYMB' by eauto using make_globalenv_stencil_matches.
        replace b' with b in * by congruence.
        assumption.
      }
      {
        exfalso.
        destruct K as (? & ? & ?). discriminate.
      }
    }
    split.
    {    
      intros.
      exploit @make_globalenv_find_funct_ptr.
      { eexact Hge. }
      { eassumption. }
      destruct 1 as (j & SYMB & K).
      destruct K as [K | K].
      {
        exfalso.
        destruct K as (? & ? & ?). discriminate.
      }
      destruct K as (? & LAY & EXT).
      generalize EXT.
      inversion 1; subst.
      exploit @make_globalenv_get_layer_primitive.
      { eexact Hge'. }
      {
        eapply @get_layer_primitive_right_neq; eauto.
      }
      { reflexivity. }
      destruct 1 as (b' & SYMB' & FUNCT').
      erewrite stencil_matches_symbols in SYMB by eauto using make_globalenv_stencil_matches.
      erewrite stencil_matches_symbols in SYMB' by eauto using make_globalenv_stencil_matches.
      replace b' with b in * by congruence.
      assumption.
    }
    {
      intros.
      exploit @make_globalenv_find_funct_ptr.
      { eexact Hge. }
      { eassumption. }
      destruct 1 as (j & SYMB & K).
      destruct K as [K | K].
      {
        exfalso.
        destruct K as (? & ? & ?). discriminate.
      }
      destruct K as (? & LAY & EXT).
      generalize EXT.
      inversion 1; subst.
      exploit @make_globalenv_get_module_function.
      { eexact Hge'. }
      {
        instantiate (2 := i).
        instantiate (1 := κi).
        exploit @get_module_function_monotonic.
        {
          etransitivity.
          * apply (oplus_le_left (i ↦ κi) M).
          * apply oplus_comm_le.
        }
        instantiate (1 := i).
        rewrite get_module_function_mapsto.
        inversion 1; subst.
        {
          inv H3.
          reflexivity.
        }
        exfalso.
        symmetry in H3.
        destruct (MOK i) as [[κ Hκ] _ _].
        congruence.
      }
      { reflexivity. }
      destruct 1 as (b' & SYMB' & FUNCT').
      erewrite stencil_matches_symbols in SYMB by eauto using make_globalenv_stencil_matches.
      erewrite stencil_matches_symbols in SYMB' by eauto using make_globalenv_stencil_matches.
      replace b' with b in * by congruence.
      assumption.
    }    
  Qed.

  Lemma make_program_vertical:
    forall D s M L i κi σi p,
      make_program s (M ⊕ i ↦ κi) L = OK p
      -> semof_fundef D M L i κi = OK σi
      -> exists p', make_program s M (L ⊕ i ↦ σi) = OK p'.
  Proof.
    intros until p.
    intros MKP SEM.
    assert (MKP': isOK (make_program s (M ⊕ i ↦ κi) L))
      by (rewrite MKP; unfold isOK; eauto).
    pose proof (make_program_module_ok _ _ _ MKP') as MOK.
    pose proof (make_program_layer_ok _ _ _ MKP') as LOK'.
    exploit @module_oplus_function_same; eauto.
    intro FUN.
    exploit @make_program_get_module_function_prop; eauto.
    intros (INT & LPRIM & LVAR).
    pose proof (layer_oplus_primitive_ok L i σi LPRIM LVAR LOK') as LOK.
    exploit @module_oplus_function_ok_elim; eauto.
    intros (NOFUN & NOVAR).
    assert (GOK: isOK (make_globalenv s (M ⊕ i ↦ κi) L)).
    { unfold make_globalenv. rewrite MKP. monad_norm. unfold isOK; simpl. eauto. }
    destruct GOK as (? & GOK).

    apply make_program_exists; eauto.
    * eapply module_ok_antitonic; eauto.
      apply oplus_le_left.
    * intro j.
      destruct (peq j i).
    + subst.
      rewrite layer_oplus_primitive_same; eauto.
      inversion 1; subst.
      unfold isOK; simpl; split; eauto.
    + rewrite layer_oplus_primitive_other; eauto.
      erewrite <- module_oplus_function_other; eauto.
      erewrite <- module_oplus_variable; eauto.
      intro.
      eapply make_program_get_layer_primitive_prop; eauto.
      * intro j.
        destruct (peq j i).
    + intros ? ABS.
      exfalso.
      subst.
      unfold isOKNone in NOFUN.
      rewrite NOFUN in ABS.
      discriminate.
    + intro.
      erewrite <- module_oplus_function_other; eauto.
      rewrite layer_oplus_primitive_other; eauto.
      rewrite layer_oplus_globalvar; eauto.
      eapply make_program_get_module_function_prop; eauto.
      * intros j ?.
               erewrite layer_oplus_globalvar; eauto.
        intro NOVARL.
        exploit @make_program_get_layer_globalvar_prop; eauto.
        intros (? & ? & ?).
        erewrite <- module_oplus_variable; eauto.
        destruct (peq j i).
    + subst.
      unfold isOKNone in NOFUN.
      rewrite NOFUN.
      unfold isOKNone at 1.
      eauto.
    + erewrite <- module_oplus_function_other; eauto.
      * intros j ? NOVAR'.
        destruct (peq j i).
    + subst.
      exfalso.
      unfold isOKNone in NOVAR.
      rewrite NOVAR in NOVAR'.
      discriminate.
    + erewrite <- module_oplus_variable in NOVAR'; eauto.
      rewrite layer_oplus_globalvar; eauto.
      rewrite layer_oplus_primitive_other; eauto.
      eapply make_program_get_module_variable_prop; eauto.
      * intros j ?.
               destruct (peq j i).
    + subst.
      intros _.
      destruct INT.
      exploit @make_globalenv_get_module_function; eauto.
      intros (? & SYMB & _).
      erewrite stencil_matches_symbols in SYMB
                                       by (eapply make_globalenv_stencil_matches; eauto).
      unfold isSome. eauto.
    + rewrite layer_oplus_primitive_other; eauto.
      intro PRIM.
      exploit @make_program_get_layer_primitive_prop; eauto.
      intros [EXT _].
      destruct EXT.
      exploit @make_globalenv_get_layer_primitive; eauto.
      intros (? & SYMB & _).
      erewrite stencil_matches_symbols in SYMB
                                       by (eapply make_globalenv_stencil_matches; eauto).
      unfold isSome. eauto.
      * intros j ?.
               rewrite layer_oplus_globalvar; eauto.
        intro VAR.
        exploit @make_program_get_layer_globalvar_prop; eauto.
        intros [NONVOL _].
        exploit @make_globalenv_get_layer_globalvar; eauto.
        intros (? & SYMB & _).
        erewrite stencil_matches_symbols in SYMB
                                         by (eapply make_globalenv_stencil_matches; eauto).
        unfold isSome. eauto.
      * intros j ?.
               destruct (peq j i).
    + subst.
      unfold isOKNone in NOFUN.
      rewrite NOFUN.
      discriminate.
    + erewrite <- module_oplus_function_other; eauto.
      intro.
      exploit @make_program_get_module_function_prop; eauto.
      intros [INT' _].
      destruct INT'.
      exploit @make_globalenv_get_module_function; eauto.
      intros (? & SYMB & _).
      erewrite stencil_matches_symbols in SYMB
                                       by (eapply make_globalenv_stencil_matches; eauto).
      unfold isSome. eauto.
      * intros j ?.
               erewrite <- module_oplus_variable; eauto.
        intro.
        exploit @make_program_get_module_variable_prop; eauto.
        intros [NONVOL _].
        exploit @make_globalenv_get_module_variable; eauto.
        intros (? & SYMB & _).
        erewrite stencil_matches_symbols in SYMB
                                         by (eapply make_globalenv_stencil_matches; eauto).
        unfold isSome. eauto.
  Qed.

  Lemma make_globlenv_monotonic_weak {D1: compatdata} {D2: compatdata}
        {R: compatrel D1 D2} `{L1: compatlayer D1} `{L2: compatlayer D2}:
    forall M1 M2 s ge1,
      M1 ≤ M2 ->
      cl_sim D1 D2 (freerg_inj _ _ _ R) L1 L2 ->
      make_globalenv s M1 L1 = ret ge1 ->
      forall ge2, make_globalenv s M2 L2 = ret ge2 ->
                  ge1 ≤ ge2.
  Proof.
    unfold make_globalenv.
    intros until 2. intro MKG. inv_monad MKG. subst.
    intros ? MKG. inv_monad MKG. subst.
    eapply globalenv_monotonic; eauto.
    assert (LEP: res_le program_le (make_program s M1 L1) (make_program s M2 L2))
      by (eapply make_program_sim_monotonic; eauto; typeclasses eauto).
    rewrite H3 in LEP.
    inversion LEP; subst.
    rewrite H2 in H1.
    inv H1.
    assumption.
  Qed.

  Lemma make_globlenv_monotonic_weak' {D: compatdata}
        `{L1: compatlayer D} `{L2: compatlayer D}:
    forall M1 M2 s ge1,
      M1 ≤ M2 ->
      L1 ≤ L2 ->
      make_globalenv s M1 L1 = ret ge1 ->
      forall ge2, make_globalenv s M2 L2 = ret ge2 ->
                  ge1 ≤ ge2.
  Proof.
    unfold make_globalenv.
    intros until 2. intro MKG. inv_monad MKG. subst.
    intros ? MKG. inv_monad MKG. subst.
    eapply globalenv_monotonic; eauto.
    assert (LEP: res_le program_le (make_program s M1 L1) (make_program s M2 L2))
      by (eapply make_program_monotonic; eauto; typeclasses eauto).
    rewrite H3 in LEP.
    inversion LEP; subst.
    rewrite H2 in H1.
    inv H1.
    assumption.
  Qed.
 
  Lemma make_program_sim_monotonic_exists {D1: compatdata} {D2: compatdata}
        {R: compatrel D1 D2} `{L1: compatlayer D1} `{L2: compatlayer D2}:
    forall M1 M2 s p,
      M1 ≤ M2 ->
      cl_sim D1 D2 (freerg_inj _ _ _ R) L1 L2 ->
      make_program s M2 L2 = OK p ->
      exists p', make_program s M1 L1 = OK p'.
  Proof.
    intros M1 M2 s p LEM SIM MKP.
    assert (LEP: res_le program_le (make_program s M1 L1) (make_program s M2 L2))
      by (eapply make_program_sim_monotonic; eauto; typeclasses eauto).
    rewrite MKP in LEP.
    inversion LEP; subst.
    eauto.
  Qed.

  Lemma make_program_monotonic_exists {D: compatdata}
        `{L1: compatlayer D} `{L2: compatlayer D}:
    forall M1 M2 s p,
      M1 ≤ M2 ->
      L1 ≤ L2 ->
      make_program s M2 L2 = OK p ->
      exists p', make_program s M1 L1 = OK p'.
  Proof.
    intros M1 M2 s p LEM SIM MKP.
    assert (LEP: res_le program_le (make_program s M1 L1) (make_program s M2 L2))
      by (eapply make_program_monotonic; eauto; typeclasses eauto).
    rewrite MKP in LEP.
    inversion LEP; subst.
    eauto.
  Qed.

  Lemma make_program_le `{D: compatdata}
        {L: compatlayer D}:
    forall (i: ident) M κi s,
      isOK (make_program s M (L ⊕ i ↦ lasm_primsem M L i κi)) ->
      get_layer_primitive i L = OK None ->
      get_layer_globalvar i L = OK None ->
      LayerOK L ->
      LayerOK (L ⊕ i ↦ lasm_primsem M L i κi) ->
      isOK (make_program s M L).
  Proof.
    intros.
    assert (HW: forall i0 v,
                  get_layer_primitive i0 L = OK (Some v) ->
                  get_layer_primitive i0 (L ⊕ i ↦ lasm_primsem M L i κi) = OK (Some v)).
    {
      intros.
      destruct (peq i0 i); subst.
      congruence.
      erewrite (layer_oplus_primitive_other (D:= D)); eauto 2.      
    }

    assert (Hge: isOK (make_globalenv s M (L ⊕ i ↦ lasm_primsem M L i κi))).
    {
      destruct H as [p' Hp].
      esplit.
      eapply make_program_make_globalenv; eauto 2.
    }
    destruct Hge as [ge Hge].
    exploit (make_globalenv_stencil_matches (D:= D)); eauto 2.
    intros Hsm. inv Hsm.
    eapply make_program_exists; eauto 2; intros.
    - eapply (make_program_module_ok); eauto 2. 
    - eapply make_program_get_layer_primitive_prop; eauto 2.
    - eapply make_program_get_module_function_prop in H; eauto 2.
      destruct H as [? ?].
      split; trivial.
      destruct (peq i0 i); subst.
      + auto.
      + erewrite (layer_oplus_primitive_other (D:= D)) in H5; eauto 2.
        erewrite (layer_oplus_globalvar) in H5; eauto 2.
    - eapply make_program_get_layer_globalvar_prop; eauto 2.
      erewrite (layer_oplus_globalvar); eauto 2.
    - eapply make_program_get_module_variable_prop in H; eauto 2.
      destruct H as [? ?].
      split; trivial.
      destruct (peq i0 i); subst.
      + auto.
      + erewrite (layer_oplus_primitive_other (D:= D)) in H5; eauto 2.
        erewrite (layer_oplus_globalvar) in H5; eauto 2.
    - erewrite <- stencil_matches_symbols.
      exploit (make_globalenv_get_layer_primitive (D:=D)); eauto 2.
      reflexivity.
      intros [?[Hs _]].
      esplit; eassumption.
    - erewrite <- stencil_matches_symbols.
      exploit (make_globalenv_get_layer_globalvar (D:=D)); eauto 2.
      erewrite (layer_oplus_globalvar); eauto 2.
      intros [?[Hs _]].
      esplit; eassumption.
    - erewrite <- stencil_matches_symbols.
      exploit (make_globalenv_get_module_function (D:=D)); eauto 2.
      reflexivity.
      intros [?[Hs _]].
      esplit; eassumption.
    - erewrite <- stencil_matches_symbols.
      exploit (make_globalenv_get_module_variable (D:=D)); eauto 2.
      intros [?[Hs _]].
      esplit; eassumption.
  Qed.

End ModuleSemantics.
