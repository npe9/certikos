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
(*Require Import CompCertBuiltins.*)
Require Import LAsm.
Require Import MemoryExtra.
Require Import Observation.

Require Export LAsmModuleSemDef.
(*Require Export LAsmModuleSemProp.
Require Import LAsmModuleSemHighInv.
Require Import LAsmModuleSemLowInv.
Require Import LAsmModuleSemAsmInv.
Require Import LAsmModuleSemAux.
Require Import LAsmModuleSemMonotonic.*)

(** ** Semantics of LAsm modules *)

Section ModuleSemantics.

  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
  Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

  Lemma cl_sim_invs_ext  {D1: compatdata} {D2: compatdata}
        {L1} {L2} {R: compatrel D1 D2}:
    forall (OKLayer: LayerOK L2),
      cl_sim D1 D2 (freerg_inj _ _ _ R) L1 L2 ->
      ExtcallInvariantsDefined L2 ->
      PrimcallInvariantsDefined L2 ->
      ExtcallInvariantsDefined L1.
  Proof.
    intros. inv H.
    eapply cl_sim_layer_pointwise in cl_sim_layer.
    destruct cl_sim_layer as [Hprim _].
    unfold ExtcallInvariantsDefined in *.
    unfold PrimcallInvariantsDefined in *.
    intros. specialize (Hprim i). specialize (H0 i). specialize (H1 i).
    destruct (OKLayer i) as [[σ Hσ] _ _].
    unfold sextcall_invs_defined in *.
    unfold sprimcall_invs_defined in *.
    destruct (get_layer_primitive i L2) as [[|]|]; simpl.
    - destruct c. 
      + inv Hprim. inv H3. 
        * reflexivity.
        * inv H5. simpl.
          specialize (sextcall_sim_invs _ _ _ H4).
          destruct (sextcall_invs D2 s); try discriminate.
          intros Hle. inv Hle. reflexivity.
      + inv Hprim. inv H3.
        * reflexivity.
        * inv H5. simpl.
          reflexivity. simpl.
          specialize (sextcall_sprimcall_invs _ _ _ H4).
          destruct (sprimcall_invs D2 s); try discriminate.
          intros Hle. inv Hle. reflexivity.
    - inv Hprim. inv H3. reflexivity.
    - discriminate.
  Qed.

  Lemma cl_sim_invs_prim  {D1: compatdata} {D2: compatdata}
        {L1} {L2} {R: compatrel D1 D2}:
    forall (OKLayer: LayerOK L2),
      cl_sim D1 D2 (freerg_inj _ _ _ R) L1 L2 ->
      ExtcallInvariantsDefined L2 ->
      PrimcallInvariantsDefined L2 ->
      PrimcallInvariantsDefined L1.
  Proof.
    intros. inv H.
    eapply cl_sim_layer_pointwise in cl_sim_layer.
    destruct cl_sim_layer as [Hprim _].
    unfold ExtcallInvariantsDefined in *.
    unfold PrimcallInvariantsDefined in *.
    intros. specialize (Hprim i). specialize (H0 i). specialize (H1 i).
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
          specialize (sprimcall_sim_invs _ _ _ H4).
          destruct (sprimcall_invs D2 s); try discriminate.
          intros Hle. inv Hle. reflexivity.
          reflexivity.
    - inv Hprim. inv H3. reflexivity.
    - inv Hσ.
  Qed.

  Lemma cl_sim_LayerOK {D1: compatdata} {D2: compatdata}
        {L1} {L2} {R: compatrel D1 D2}:
    cl_sim D1 D2 (freerg_inj _ _ _ R) L1 L2 ->
    LayerOK L2 ->
    LayerOK L1.
  Proof.
    intros. inv H.
    apply cl_sim_layer_pointwise in cl_sim_layer.
    destruct cl_sim_layer as [Hprim Hvar].
    split.
    - intros.
      destruct (H0 i) as [[σ Hσ] _ _].
      specialize (Hprim i).
      rewrite Hσ in Hprim.
      inv Hprim. simpl. rewrite <- H.
      econstructor; eauto.
    - intros.
      destruct (H0 i) as [_ [τ Hτ] _].
      specialize (Hvar i).
      rewrite Hτ in Hvar.
      inv Hvar. simpl. rewrite <- H.
      econstructor; eauto.
    - destruct (H0 i) as [_ _ [Hp|Hv]].
      + left.
        specialize (Hprim i).
        unfold isOKNone in Hp.
        rewrite Hp in *.
        inversion Hprim as [x1 x2 Hx Hx1 Hx2 | ]; subst.
        inversion Hx; subst.
        simpl.
        rewrite <- Hx1.
        constructor.
      + right.
        specialize (Hvar i).
        unfold isOKNone in Hv.
        rewrite Hv in *.
        inversion Hvar as [x1 x2 Hx Hx1 Hx2 | ]; subst.
        inversion Hx; subst.
        simpl.
        rewrite <- Hx1.
        constructor.
  Qed.

  Lemma cl_sim_get_layer_prim_valid {D1: compatdata} {D2: compatdata}
        {L1} {L2} {R: compatrel D1 D2} {s: stencil}:
    forall (OKLayer: LayerOK L2),
      cl_sim D1 D2 (freerg_inj _ _ _ R) L1 L2 ->
      get_layer_prim_valid L2 s ->
      get_layer_prim_valid L1 s.
  Proof.
    intros. inv H.
    apply cl_sim_layer_pointwise in cl_sim_layer.
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
      * eapply sextcall_sim_valid; eassumption.  
      * eapply sprimcall_sim_valid; eassumption.  
      * eapply sextcall_sprimcall_sim_valid; eassumption.  
    - destruct (OKLayer i) as [[σ' Hσ'] _ _].
      simpl in *.
      congruence.
  Qed.

  Lemma layer_oplus_invs_ext `{D: compatdata}
        {L: compatlayer D}:
    forall (i: ident) M κi,
    get_layer_primitive i L = OK None ->
    LayerOK (L ⊕ i ↦ lasm_primsem M L i κi) ->
    ExtcallInvariantsDefined L ->
    PrimcallInvariantsDefined L ->
    ExtcallInvariantsDefined (L ⊕ i ↦ lasm_primsem M L i κi).
  Proof.
    intros.
    unfold ExtcallInvariantsDefined in *.
    unfold PrimcallInvariantsDefined in *.
    intros. 
    destruct (peq i i0); subst.
    - rewrite layer_oplus_primitive_same by assumption.
      simpl. reflexivity.
    - rewrite layer_oplus_primitive_other by congruence.
      eauto.
  Qed.

  Lemma layer_oplus_prim_valid `{D: compatdata}
        {L: compatlayer D}:

    forall `{accessors_def: accessors_weak_defined L = true},
    forall `{names_match: !LayerNamesMatch D L},
    forall `{extinv_defined: !ExtcallInvariantsDefined L},
    forall `{priminv_defined: !PrimcallInvariantsDefined L},
    forall (i: ident) M κi s p,
    forall (layer_valid: get_layer_prim_valid L s),
    forall (makeprogram: make_program s M L = OK p),
    get_layer_primitive i L = OK None ->
    LayerOK (L ⊕ i ↦ lasm_primsem M L i κi) ->
    get_layer_prim_valid L s->
    get_layer_prim_valid (L ⊕ i ↦ lasm_primsem M L i κi) s.
  Proof.
    intros. revert H1.
    unfold get_layer_prim_valid .
    intros.
    destruct (peq i i0); subst.
    - rewrite layer_oplus_primitive_same in H2 by assumption.
      inv H2.
      simpl.
      destruct (Decision.decide (LayerOK L)).
      destruct (Decision.decide (ExtcallInvariantsDefined L)).
      destruct (Decision.decide (PrimcallInvariantsDefined L)).
      destruct (Decision.decide (LayerNamesMatch D L)).
      destruct (Decision.decide (get_layer_prim_valid L s)).
      rewrite accessors_def.
      destruct (make_program s M L); try discriminate.
      + reflexivity.
      + elim n. assumption.
      + elim n. assumption.
      + elim n. assumption.
      + elim n. assumption.
      + elim n. eapply layer_ok_antitonic; eauto.
        rewrite <- left_upper_bound.
        reflexivity.
    - rewrite layer_oplus_primitive_other in H2 by congruence.
      eauto.
  Qed.

  (*Lemma layer_oplus_invs_prim `{D: compatdata}
        {L: compatlayer D}:
    forall (i: ident) M κi,
    get_layer_primitive i L = OK None ->
    LayerOK (L ⊕ i ↦ lasm_primsem M L i κi) ->
    ExtcallInvariantsDefined L ->
    PrimcallInvariantsDefined L ->
    PrimcallInvariantsDefined (L ⊕ i ↦ lasm_primsem M L i κi).
  Proof.
    intros.
    unfold ExtcallInvariantsDefined in *.
    unfold PrimcallInvariantsDefined in *.
    intros. 
    destruct (peq i i0); subst.
    - specialize (layer_oplus_primitive_same (D:= D) _ _ _ H0 H).
      intros Hlayer.
      unfold sprimcall_invs_defined.
      rewrite Hlayer.
      simpl. reflexivity.
    - exploit (layer_oplus_primitive_other (D:= D)); eauto 2.
      intros HW. rewrite HW.
      eauto.
  Qed.*)

  Lemma cl_le_LayerOK `{D: compatdata}
        {L1 L2: compatlayer D}:
    L1 ≤ L2 ->
    LayerOK L2 ->
    LayerOK L1.
  Proof.
    intros H HL2. inv H.
    apply cl_le_layer_pointwise in cl_sim_layer.
    destruct cl_sim_layer as [Hprim Hvar].
    intros i. split.
    - destruct (HL2 i) as [[σ Hσ] _ _].
      specialize (Hprim i).
      rewrite Hσ in Hprim.
      inversion Hprim as [x y Hxy Hx Hy | ]; subst.
      simpl; rewrite <- Hx.
      econstructor; eauto.
    - destruct (HL2 i) as [_ [τ Hτ] _].
      specialize (Hvar i).
      rewrite Hτ in Hvar.
      inversion Hvar as [x y Hxy Hx Hy | ]; subst.
      simpl; rewrite <- Hx.
      econstructor; eauto.
    - destruct (HL2 i) as [_ _ [Hp|Hv]]; [left | right].
      + specialize (Hprim i).
        rewrite Hp in Hprim.
        inversion Hprim as [x y Hxy Hx Hy | ]; subst.
        simpl; rewrite <- Hx.
        inversion Hxy.
        constructor.
      + specialize (Hvar i).
        rewrite Hv in Hvar.
        inversion Hvar as [x y Hxy Hx Hy | ]; subst.
        simpl; rewrite <- Hx.
        inversion Hxy.
        constructor.
  Qed.

  (* Warning! This lemma should be incorrect.
 We have to modify the AccessorsDefined. *)

  Lemma accessors_monotonic_sim {D1: compatdata} {D2: compatdata}
        {R: compatrel D1 D2} `{L1: compatlayer D1} `{L2: compatlayer D2}:
    cl_sim D1 D2 (freerg_inj _ _ _ R) L1 L2 ->
    accessors_weak_defined L2 = true ->
    AccessorsDefined L1 ->
    AccessorsDefined L2.
  Proof.
    intros. apply accessors_defined_true in H1.
    constructor. inv H.
    unfold accessors_defined in *.
    unfold accessors_weak_defined in *.
    destruct (cl_exec_load L1); try discriminate.
    destruct o; try discriminate.
    inv cl_sim_load.
    - rewrite <- H2 in H0.
      inv H3.
      destruct (cl_exec_store L1); try discriminate.
      destruct o; try discriminate.
      inv cl_sim_store.
      + inv H5. reflexivity.
      + rewrite <- H5 in H0. discriminate.
    - rewrite <- H3 in H0. discriminate.
  Qed.

  Lemma accessors_monotonic_le {D: compatdata}
        {L1 L2: compatlayer D}:
    L1 ≤ L2 ->
    accessors_weak_defined L2 = true ->
    AccessorsDefined L1 ->
    AccessorsDefined L2.
  Proof.
    intros. apply accessors_defined_true in H1.
    constructor. inv H.
    simpl in *.
    unfold accessors_defined in *.
    unfold accessors_weak_defined in *.
    destruct (cl_exec_load L1); try discriminate.
    destruct o; try discriminate.
    inv cl_sim_load.
    - rewrite <- H2 in H0.
      inv H3.
      destruct (cl_exec_store L1); try discriminate.
      destruct o; try discriminate.
      inv cl_sim_store.
      + inv H4. reflexivity.
      + rewrite <- H4 in H0. discriminate.
    - rewrite <- H3 in H0. discriminate.
  Qed.

  Lemma accessors_monotonic_weak_sim {D1: compatdata} {D2: compatdata}
        {R: compatrel D1 D2} `{L1: compatlayer D1} `{L2: compatlayer D2}:
    cl_sim D1 D2 (freerg_inj _ _ _ R) L1 L2 ->
    accessors_weak_defined L2 = true ->
    accessors_weak_defined L1 = true.
  Proof.
    intros. inv H.
    unfold accessors_weak_defined in *.
    destruct (cl_exec_load L2); try discriminate.
    inv cl_sim_load.
    destruct (cl_exec_store L2); try discriminate.
    inv cl_sim_store.
    reflexivity.
  Qed.

  Lemma accessors_monotonic_weak_le {D: compatdata}
        {L1 L2: compatlayer D}:
    L1 ≤ L2 ->
    accessors_weak_defined L2 = true ->
    accessors_weak_defined L1 = true.
  Proof.
    intros. inv H.
    unfold accessors_weak_defined in *.
    destruct (cl_exec_load L2); try discriminate.
    inv cl_sim_load.
    destruct (cl_exec_store L2); try discriminate.
    inv cl_sim_store.
    reflexivity.
  Qed.

  Lemma accessors_weak_oplus `{D: compatdata}
        {L: compatlayer D}:
    forall (i: ident) M κi,
      accessors_weak_defined L = true ->
      accessors_weak_defined (L ⊕ i ↦ lasm_primsem M L i κi) = true.
  Proof.
    intros. unfold accessors_weak_defined in *.
    simpl in *. destruct (cl_exec_load L); try discriminate.
    destruct (cl_exec_store L); try discriminate.
    destruct o; destruct o0; simpl; try reflexivity.
  Qed.

  Lemma AccessorsDefined_oplus `{D: compatdata}
        {L: compatlayer D}:
    forall i (σi: compatsem D),
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

  Lemma accessors_defined_weak `{D: compatdata} {L: compatlayer D}:
    AccessorsDefined L ->
    accessors_weak_defined L = true.
  Proof.
    intros. apply accessors_defined_true in H.
    unfold accessors_defined in H.
    unfold accessors_weak_defined.
    destruct (cl_exec_load L); try discriminate.
    destruct o; try discriminate.
    destruct (cl_exec_store L); try discriminate.
    destruct o; try discriminate.
    reflexivity.
  Qed.

End ModuleSemantics.
