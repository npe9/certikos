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

Require Import LAsmModuleSem.
Require Import LAsmModuleSemAux.
Require Import LAsmModuleSemMakeProgram.
Require Import LAsmModuleSemSim.
Require Import LAsmModuleSemInvariants.
Require Import LAsm.
Require Import CommonTactic.
Require Import InitMem.
Require Import RefinementTactic.
Require Import AuxLemma.
Require Import Behavior.
Import LAsm.
(*Require Import LayerModuleLemma.*)

Section WITHLAYERS.
  
  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.
  Context `{builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet}.

  Context `{make_program_ops: !MakeProgramOps LAsm.function Ctypes.type LAsm.fundef unit}.
  Context `{make_program_prf: !MakeProgram LAsm.function Ctypes.type LAsm.fundef unit}.

  Inductive match_states {D1: compatdata} {D2: compatdata} {R: compatrel D1 D2}:
    stencil -> (state (mem:= mwd D1)) -> (state (mem:= mwd D2)) -> Prop :=
  | match_states_intro:
      forall s f rs m d rs' m' d',
      MatchPrimcallStates R s f rs m d rs' m' d' ->
      high_level_invariant d ->
      high_level_invariant d' ->
      low_level_invariant (Mem.nextblock m') d' ->
      asm_invariant (mem:= mwd D2) s rs' (m', d') ->
      match_states s (State rs (m, d)) (State rs' (m', d')).

  Lemma match_states_observe 
        {D1: compatdata} {D2: compatdata} {R: compatrel D1 D2} :
    forall sten p (s1 : state (mem:= mwd D1)) (s2 : state (mem:= mwd D2)),
      match_states sten s1 s2 -> 
      observe_lasm _ p s1 = observe_lasm _ p s2.
  Proof.
    intros sten p s1 s2 Hmatch; inv Hmatch; simpl.
    inv H.
    inv match_extcall_states.
    destruct R.
    destruct crel_prf; eauto.
  Qed.

  Lemma one_step_sim_monotonic_alt {D1: compatdata} {D2: compatdata}
        {L1} {L2} {R: compatrel D1 D2}
        `{acc_def_prf1: !AccessorsDefined L1}
        `{names1: !LayerNamesMatch D1 L1}
        `{acc_def_prf2: !AccessorsDefined L2}
        `{names2: !LayerNamesMatch D2 L2}:
    forall `{memory_model_x: !Mem.MemoryModelX mem},
    forall `{extcall_inv_def_prf1: !ExtcallInvariantsAvailable L1},
    forall `{primcall_inv_def_prf1: !PrimcallInvariantsAvailable L1},
    forall `{extcall_inv_def_prf2: !ExtcallInvariantsAvailable L2},
    forall `{primcall_inv_def_prf2: !PrimcallInvariantsAvailable L2},
    forall `{builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet},
    forall (s: stencil) ge ge' rs1 rs1' m1 m1' d1 d1' rs2 m2 d2 t, 
    forall (Hglobalenv: exists M, make_globalenv (D:=D2) s M L2 = OK ge'),
    forall (Hge_external': 
              forall b ef, 
                Genv.find_funct_ptr ge' b = Some (External ef) ->
                exists i sg, ef = EF_external i sg),
    forall (OKLayer: LayerOK L2),
    forall (ValidLayer: get_layer_prim_valid L2 s),
      stencil_matches s ge ->
      stencil_matches s ge' ->
      ge ≤ ge' ->
      cl_sim D1 D2 (freerg_inj _ _ _ R) L1 L2 ->
      match_states s (State rs1 (m1, d1)) (State rs2 (m2, d2)) ->
      (step (lcfg_ops:= LC L1)) 
        ge (State rs1 (m1, d1)) t (State rs1' (m1', d1')) ->
      exists rs2' m2' d2',
        (step (lcfg_ops:= LC L2)) 
          ge' (State rs2 (m2, d2)) t (State rs2' (m2', d2'))
          /\ match_states s (State rs1' (m1', d1')) (State rs2' (m2', d2')).
  Proof.
    intros. inv H3.
    exploit (one_step_sim_monotonic'_avail s ge ge'); eauto 1.
    intros [f'[rs2'[m2'[d2'[Hstep[Hmatch[Hhigh[Hhigh'[Hlow Hasm]]]]]]]]].
    refine_split'; eauto 2.
    econstructor; eauto 2.
  Qed.

  Lemma get_module_function_oplus_ok_left i M1 M2 κ:
    ModuleOK (M1 ⊕ M2) ->
    get_module_function i M1 = OK (Some κ) ->
    get_module_function i (M1 ⊕ M2) = OK (Some κ).
  Proof.
    intros HM HM1i.
    assert (HMi: res_le (option_le eq) (get_module_function i M1)
                                       (get_module_function i (M1 ⊕ M2))). {
      apply get_module_function_monotonic.
      apply left_upper_bound.
    }
    destruct (HM i) as [[κ' Hκ'] _ _].
    destruct HMi as [_ _ [|] | ]; try discriminate.
    congruence.
  Qed.

  Lemma get_module_function_oplus_ok_right i M1 M2 κ:
    ModuleOK (M1 ⊕ M2) ->
    get_module_function i M1 = OK (Some κ) ->
    get_module_function i (M1 ⊕ M2) = OK (Some κ).
  Proof.
    intros HM HM1i.
    assert (HMi: res_le (option_le eq) (get_module_function i M1)
                                       (get_module_function i (M1 ⊕ M2))). {
      apply get_module_function_monotonic.
      apply left_upper_bound.
    }
    destruct (HM i) as [[κ' Hκ'] _ _].
    destruct HMi as [_ _ [|] | ]; try discriminate.
    congruence.
  Qed.

  Lemma res_option_oplus_none_inv {A} (x y: res (option A)):
    x ⊕ y = OK None ->
    x = OK None /\ y = OK None.
  Proof.
    destruct x as [[|]|], y as [[|]|];
    inversion 1;
    split;
    reflexivity.
  Qed.

  Lemma get_module_function_oplus_ok_either i M1 M2 δ:
    ModuleOK (M1 ⊕ M2) ->
    get_module_function i (M1 ⊕ M2) = OK δ ->
    (get_module_function i M1 = OK δ /\ isOKNone (get_module_function i M2)) \/
    (isOKNone (get_module_function i M1) /\ get_module_function i M2 = OK δ).
  Proof.
    intros HM Hi.
    destruct (HM i) as [[f Hf] [v Hv] Hdisj].
    revert Hdisj Hf Hv Hi.
    get_module_normalize.
    unfold isOKNone.
    intros [Hdisj|Hdisj] Hf Hv Hδ;
    apply res_option_oplus_none_inv in Hdisj;
    destruct Hdisj as [H1 H2];
    rewrite H1, H2 in *.
    * left.
      split; [assumption|reflexivity].
    * destruct (get_module_function i M1) as [[|]|];
      destruct (get_module_function i M2) as [[|]|];
      try discriminate.
      + left.
        split; [assumption|reflexivity].
      + right.
        split; [reflexivity|assumption].
      + left.
        split; [assumption|reflexivity].
  Qed.

  (** XXX: this is only true in the current implementation. Ultimately
    we'll want to do something else. *)
  Lemma get_layer_primitive_oplus_either {D} i L1 L2 σ:
    get_layer_primitive (D:=D) i (L1 ⊕ L2) = OK (Some σ) ->
    get_layer_primitive i L1 = OK (Some σ) \/
    get_layer_primitive i L2 = OK (Some σ).
  Proof.
    get_layer_normalize.
    destruct (get_layer_primitive i L1) as [[|]|];
    destruct (get_layer_primitive i L2) as [[|]|];
    try discriminate;
    intros H.
    * left; assumption.
    * right; assumption.
  Qed.

  Lemma make_globalenv_module_ok {D} s M L:
    isOK (make_globalenv (D:=D) s M L) ->
    ModuleOK M.
  Proof.
    intros [ge Hge].
    unfold make_globalenv in Hge.
    inv_monad Hge.
    eapply make_program_module_ok.
    exists x.
    eassumption.
  Qed.

  Lemma make_globalenv_vertical' {D} `{L: compatlayer D}:
    forall s CTXT (M: module) ge ge',
      stencil_matches s ge ->
      stencil_matches s ge' ->
      make_globalenv s CTXT (〚 M 〛 L ⊕ L) = ret ge
      -> make_globalenv s (CTXT ⊕ M) L = ret ge'
                     (* For internal functions *)
      -> (forall b f, Genv.find_funct_ptr ge b = Some (Internal f)
                      -> Genv.find_funct_ptr ge' b = Some (Internal f))
         (* For external functions that not i*)
         /\ (forall b id sg, 
               isOKNone (get_module_function id M) 
               -> Genv.find_funct_ptr ge b = Some (External (EF_external id sg))
               -> Genv.find_funct_ptr ge' b = Some (External (EF_external id sg)))
         (* For i*)
         /\ (forall b id sg f, 
               get_module_function id M = OK (Some f) ->
               Genv.find_funct_ptr ge b = Some (External (EF_external id sg))
               -> Genv.find_funct_ptr ge' b = Some (Internal f)).
  Proof.
    intros until ge'.
    intros Hsge Hsge' Hge Hge'.
    assert (MOK: ModuleOK (CTXT ⊕ M)).
    {
      eapply make_globalenv_module_ok.
      eexists; eassumption.
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
          apply get_module_function_oplus_ok_left; eauto.
          simpl in INT.
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
      edestruct (make_globalenv_get_layer_primitive s (CTXT ⊕ M) L ge'); eauto.
      {
        edestruct (get_layer_primitive_oplus_either j (〚M〛L) L);
        try eassumption.
        exfalso.
        unfold isOKNone in H.
        rewrite get_semof_primitive in H1.
        unfold semof_function in H1.
        inversion EXT; subst; clear EXT.
        rewrite H in H1.
        discriminate.
      }
      destruct H1 as [Hjx0 Hx0id].
      erewrite stencil_matches_symbols in Hjx0 by eassumption.
      erewrite stencil_matches_symbols in SYMB by eassumption.
      congruence.
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
        instantiate (2 := id).
        instantiate (1 := f).
        exploit @get_module_function_monotonic.
        {
          apply (right_upper_bound CTXT M).
        }
        instantiate (1 := id).
        rewrite H.
        inversion 1; subst.
        {
          inv H4.
          inv H1.
          inv H5.
          * simpl in *.
            congruence.
          * destruct (MOK id) as [[a Ha] _ _].
            simpl in *.
            congruence.
        }
        exfalso.
        symmetry in H4.
        destruct (MOK id) as [MOK_FUN _ _].
        generalize MOK_FUN.
        simpl.
        rewrite H4.
        destruct 1; discriminate.
      }
      { reflexivity. }
      destruct 1 as (b' & SYMB' & FUNCT').
      erewrite stencil_matches_symbols in SYMB by eauto using make_globalenv_stencil_matches.
      erewrite stencil_matches_symbols in SYMB' by eauto using make_globalenv_stencil_matches.
      replace b' with b in * by congruence.
      assumption.
    }    
  Qed.

  Lemma res_option_oplus_some_inv {A} (x: A) (y: res (option A)) (z: A):
    (OK (Some x)) ⊕ y = OK (Some z) ->
    x = z.
  Proof.
    intros H.
    destruct y as [[|]|]; inversion H.
    reflexivity.
  Qed.

  Lemma get_layer_primitive_right_eq' {D} `{L: compatlayer D}: 
    forall i (σ: compatsem D) M f,
      get_layer_primitive i (〚 M 〛 L ⊕ L) = OK (Some σ) ->
      get_module_function i M = OK (Some f) ->
      LayerOK L ->
      semof_fundef D M L i f = OK σ.
  Proof.
    intros.
    rewrite get_layer_primitive_oplus in H.
    rewrite get_semof_primitive in H.
    unfold semof_function in H.
    rewrite H0 in H.
    monad_norm.
    destruct (semof_fundef _ _ _ _ _) as [σ'|err]; try discriminate.
    monad_norm.
    apply res_option_oplus_some_inv in H.
    congruence.
  Qed.

  Lemma get_layer_primitive_right_neq' {D} `{L: compatlayer D}: 
    forall i (σi: compatsem D) M,
      get_layer_primitive i (〚 M 〛 L ⊕ L) = OK (Some σi) ->
      isOKNone (get_module_function i M) ->
      get_layer_primitive i L = OK (Some σi).
  Proof.
    intros.
    rewrite get_layer_primitive_oplus in H.
    rewrite get_semof_primitive in H.
    unfold isOKNone in *; rewrite H0 in H.
    unfold semof_function in H.
    monad_norm.
    rewrite id_left in H.
    assumption.
  Qed.

  Lemma one_step_vertical_composition {D} `{L: compatlayer D} {M}
        (L_ACC_DEF: LAsm.AccessorsDefined L)
        (L_NAMES: LayerNamesMatch D L)
        (L_ACC_DEF': LAsm.AccessorsDefined (〚M 〛 L ⊕ L)):
    forall s ge ge' CTXT r r' (m m': mem) (d d': D) t,
    forall (extinv: ExtcallInvariantsDefined L),
    forall (priminv: PrimcallInvariantsDefined L),
    forall (valid_prim: get_layer_prim_valid L s),
      make_globalenv s CTXT (〚 M 〛 L ⊕ L) = ret ge
      -> make_globalenv s (CTXT ⊕ M) L = ret ge'
      -> step (lcfg_ops:= LC (〚 M 〛 L ⊕ L)) ge (State r (m, d)) t (State r' (m', d'))
      -> plus (step (lcfg_ops:= LC L)) ge' 
              (State r (m, d)) t (State r' (m', d')).
  Proof.
    intros. pose proof H0 as Hge_match'. pose proof H as Hge_match.
    apply make_globalenv_stencil_matches in H0.
    apply make_globalenv_stencil_matches in H.
    pose proof H as Hge. pose proof H0 as Hge'.
    inv H. inv H0.
    assert (Hsymbol: forall i, Genv.find_symbol ge' i = Genv.find_symbol ge i).
    {
      intros; abstract congruence.
    }
    unfold fundef in *.
    assert (Hgenv_next: Genv.genv_next ge' = Genv.genv_next ge).
    {
      unfold fundef.
      intros; abstract congruence.
    }
    assert(Hvolatile: forall b1 : block, block_is_volatile ge' b1 = block_is_volatile ge b1).
    {
      unfold fundef.
      intros; abstract congruence.
    } 

    generalize Hge_match. intro HgeL_dup.
    eapply make_globalenv_vertical' in HgeL_dup; eauto.
    destruct HgeL_dup as [Hinternal [Hext Hext']].

    assert (Hge_external':
              forall b ef, 
                Genv.find_funct_ptr ge b = Some (External ef) ->
                exists i sg, ef = EF_external i sg).
    {
      intros until ef; eapply ge_external_valid; eauto.
    } 

    assert (mk_prog': isOK (make_program s (CTXT ⊕ M) L)).
    {
      unfold make_globalenv in Hge_match'.
      inv_monad Hge_match'.
      esplit; eauto.
    }

    assert (mk_prog: isOK(make_program s M L)).
    {
      destruct mk_prog' as [? mk_prog'].
      eapply make_program_monotonic_exists; try eassumption; try reflexivity.
      apply right_upper_bound.
    }

    assert (Hmoduleok: ModuleOK M).
    {
      eapply make_program_module_ok; eassumption.
    }

    assert (Hlayerok: LayerOK L).
    {
      eapply make_program_layer_ok; try eassumption.
    }

    assert (Hget: forall i,
                    (exists func, get_module_function i M = OK (Some func))
                    \/ (isOKNone (get_module_function i M))).
    {
      intros.
      destruct (Hmoduleok i) as [Hfun _ _].
      revert Hfun.
      destruct (get_module_function i M); eauto.
      destruct o; eauto.
      destruct 1.
      discriminate.
    }

    eapply vcomp_step; try eapply H2; eauto 2; intros.
    - assert(HW: acc_exec_load (〚M 〛 L ⊕ L) = acc_exec_load L).
      {
        unfold acc_exec_load.
        destruct (acc_exec_load_strong (〚M 〛 L ⊕ L)).
        simpl in e.
        destruct (acc_exec_load_strong L).
        rewrite e0 in e. abstract (inversion e; trivial).
      }
      rewrite <- HW.
      erewrite exec_load_symbols_preserved; eauto.
    - assert(HW': acc_exec_store (〚M 〛 L ⊕ L) = acc_exec_store L).
      {
        unfold acc_exec_store.
        destruct (acc_exec_store_strong (〚M 〛 L ⊕ L)).
        simpl in e.
        destruct (acc_exec_store_strong L).
        rewrite e0 in e. abstract (inversion e; trivial).
      }
      rewrite <- HW'.
      erewrite exec_store_symbols_preserved; eauto.
    - eapply Hge_external' in H.
      destruct H as [?[? ?]]; subst. inv H0.
    - (* external call *)
      destruct (Hget i) as [?|?].
      (* OK (Some f))*)
      destruct H2 as [funcp ?].
      specialize (Hext' _ _ _ _ H2 H).
      eapply (get_layer_primitive_right_eq') in H0; eauto; subst.
      inv H0. 

      (* None *)
      split; eauto. 
      eapply get_layer_primitive_right_neq'; eauto.

    - (* primitive call *)
      destruct (Hget i) as [?|?].

      + (* OK (Some f))*)
        destruct H5 as [funcp ?].
        specialize (Hext' _ _ _ _ H5 H).
        eapply (get_layer_primitive_right_eq') in H0; eauto. subst.
        exploit (compatsem_primcall_le (D:= D)); eauto.
        * reflexivity.
        * econstructor; eauto.
        * inv H0. simpl.
          intros.
          eapply stencil_matches_unique in H0; try apply Hge. subst.
          destruct (Decision.decide (ExtcallInvariantsDefined L)).
          destruct (Decision.decide (PrimcallInvariantsDefined L)).
          destruct (Decision.decide (LayerNamesMatch D L)).
          destruct (Decision.decide (get_layer_prim_valid L s1)).
          rewrite accessors_defined_weak; try assumption.
          destruct mk_prog as [? mk_prog].
          rewrite mk_prog. reflexivity.
          elim n; assumption.
          elim n; assumption.
          elim n; assumption.
          elim n; assumption.

        * intros Hsem'; inv Hsem'.
          eapply stencil_matches_unique in H2; try apply Hge. subst.
          inv H0; simpl in H4.
          inv H4.
          pose proof Hge0 as Hge0'.
          apply make_globalenv_stencil_matches in Hge0.
          apply make_globalenv_split_module_right in Hge_match'.
          destruct Hge_match' as [?[HgeL Hle'']].
          unfold fundef in *.
          rewrite Hge0' in HgeL. inv HgeL.
          eapply one_sim_plus; eauto. intros.
          eapply one_step_monotonic; eauto.      

      + (* None *) 
        exploit Hext; eauto. intros Hfind.
        apply plus_one. 
        eapply exec_step_prim_call; eauto.
        eapply get_layer_primitive_right_neq' in H0; eauto.
        econstructor; eauto.
        refine_split'; eauto.
        eapply stencil_matches_unique in H2; try apply Hge. subst.
        econstructor; eauto.
  Qed.

  Remark annot_arguments_determ_with_data {D}:
    forall rs (m: mwd D) params args1 args2,
      annot_arguments rs m params args1 -> annot_arguments rs m params args2 -> args1 = args2.
  Proof.
    unfold annot_arguments. intros. revert params args1 H args2 H0. 
    induction 1; intros. 
    inv H0; auto.
    inv H1. decEq; eauto. inv H; inv H4. auto. congruence. 
  Qed.

  Remark extcall_arguments_determ_with_data {D}:
    forall rs (m: mwd D) sg args1 args2,
      extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
  Proof.
    intros until m.
    assert (forall ll vl1, list_forall2 (extcall_arg rs m) ll vl1 ->
                           forall vl2, list_forall2 (extcall_arg rs m) ll vl2 -> vl1 = vl2).
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; auto. 
    inv H; inv H3; congruence.
    intros. red in H0; red in H1. eauto. 
  Qed.

  Lemma external_prim_false {D} `{L: compatlayer D}
        (acc_def_prf: LAsm.AccessorsDefined L):
    forall ge ef WB args t1 t2 res (m m' m'0: mwd D) rs rs',
      external_call' (external_calls_ops:= compatlayer_extcall_ops L) WB ef ge args m t1 res m' ->
      primitive_call (LayerConfigurationOps:= LC (acc_def_prf:= acc_def_prf) L) ef ge rs m t2 rs' m'0 ->
      False.
  Proof.
    intros.
    inv H. inv H0. destruct H as [?[?[?[? ?]]]]; subst.
    simpl in *. destruct H1 as [?[? ?]].
    rewrite H in H0. inv H0.
    inv H1. inv H2. destruct H0 as [?[?[?[? _]]]].
    inv H4.
  Qed.
 
  Lemma make_program_ok_disjoint {D} s M L p:
    make_program (D:=D) s M L = OK p ->
    module_layer_disjoint M L.
  Proof.
    intros.
    unfold module_layer_disjoint.
    assert (pOK: isOK (make_program s M L)).
    {
      esplit. eassumption.
    }
    intros i.
    pose proof (make_program_layer_ok s M L pOK) as LOK.
    destruct (LOK i) as [Lprim Lvar _].
    destruct Lprim as [x Lprim].
    destruct x.
    {
      left. eapply make_program_get_layer_primitive_prop; eassumption.
    }
    {
      destruct Lvar as [? Lvar].
      destruct x.
      {
        left. eapply make_program_get_layer_globalvar_prop; eassumption.
      }
      right.
      rewrite Lprim, Lvar.
      split; constructor.
    }
  Qed.

  Lemma get_layer_primitive_semof {D} i M (L: compatlayer D) σ:
    get_layer_primitive i (〚M〛 L ⊕ L) = OK (Some σ) ->
    (exists σ', get_layer_primitive i L = OK (Some σ')) \/
    (exists κ, get_module_function i M = OK (Some κ)).
  Proof.
    intros Hi.
    edestruct (get_layer_primitive_oplus_either i (〚M〛L) L) as [H|H].
    + eassumption.
    + right.
      rewrite get_semof_primitive in H.
      unfold semof_function in H.
      destruct (get_module_function i M) as [[|]|]; inversion H.
      eauto.
    + left.
      eauto.
  Qed.
  
  (*Lemma layer_oplus_layer_ok `{D: compatdata} (L1 L2: compatlayer D):
    layers_disjoint L1 L2 ->
    LayerOK L1 ->
    LayerOK L2 ->
    LayerOK (L1 ⊕ L2).
  Proof.*)

  Lemma res_option_oplus_ok_inv {A} (x y: res (option A)) (z: option A):
    x ⊕ y = OK z -> (isOK x /\ isOKNone y) \/ (isOK y /\ isOKNone x).
  Proof.
    destruct x as [[|]|], y as [[|]|]; try discriminate; eauto.
  Qed.

  Lemma res_option_oplus_ok_some_inv {A} (x y: res (option A)) (z: A):
    x ⊕ y = OK (Some z) ->
    (x = OK (Some z) /\ y = OK None) \/
    (x = OK None /\ y = OK (Some z)).
  Proof.
    destruct x as [[|]|], y as [[|]|]; try discriminate; eauto.
  Qed.

  Lemma res_option_oplus_ok_none_inv {A} (x y: res (option A)):
    isOKNone (x ⊕ y) ->
    isOKNone x /\ isOKNone y.
  Proof.
    destruct x as [[|]|], y as [[|]|]; try discriminate; eauto.
  Qed.

  Lemma make_program_vertical':
    forall D (LL: compatlayer D)  s M  CTXT p
      (Hlayer_mo: LayerOK (〚 M 〛 LL ⊕ LL)),
      make_program s (CTXT ⊕ M) LL = OK p
      -> exists p', make_program s CTXT (〚 M 〛 LL ⊕ LL) = OK p'.
  Proof.
    intros until p.
    intros Hlayer_mo MKP.
    assert (MKP': isOK (make_program s (CTXT ⊕ M) LL))
      by (rewrite MKP; unfold isOK; eauto).
    pose proof (make_program_module_ok _ _ _ MKP') as MOK.
    pose proof (make_program_layer_ok _ _ _ MKP') as LOK'.
    apply make_program_exists; eauto.

    * eapply module_ok_antitonic; eauto.
      unfold flip.
      apply left_upper_bound.

    * intros i fe Hi.
      specialize (get_layer_primitive_oplus i (〚M 〛 LL) LL).
      intros Hle.
      destruct (LOK' i) as [Lprim Lvar _].
      destruct Lprim as [? Lprim].
      rewrite Lprim in Hle. rewrite Hi in Hle.
      split; [eexists; reflexivity|].
      destruct x.
      {
        exploit (make_program_get_layer_primitive_prop (D:=D)); eauto.
        intros ( _ & Hmo & Hva).
        split.
        - eapply get_module_function_none_oplus in Hmo. eapply Hmo.
        - eapply get_module_variable_none_oplus in Hva. eapply Hva.
      }
      {
        destruct (MOK i) as [[κ Hκ] [τ Hτ] _].
        get_module_normalize_in Hκ.
        get_module_normalize_in Hτ.

        clear Hi Lprim Lvar.
        rewrite id_right in Hle.
        split.
        * rewrite get_semof_primitive in Hle.
          destruct (get_module_function i M) as [[|]|]; try discriminate.
          destruct (res_option_oplus_ok_inv _ _ _ Hκ) as [[HC HM] | [HM HC]].
          - discriminate.
          - assumption.
        * destruct (MOK i) as [_ _ [Hf|Hv]].
          - rewrite get_semof_primitive in Hle.
            rewrite get_module_function_oplus in Hf.
            destruct (get_module_function i M) as [[|]|]; try discriminate.
            destruct (get_module_function i CTXT) as [[|]|]; try discriminate.
          - rewrite get_module_variable_oplus in Hv.
            destruct (get_module_variable i M) as [[|]|];
            destruct (get_module_variable i CTXT) as [[|]|];
            try discriminate.
            reflexivity.
      }

    * intros i fi Hfi.
      split; [eexists; reflexivity|].
      destruct (MOK i) as [[κ MOK1] [τ MOK2] Mdisj].
      specialize (get_module_function_oplus i CTXT M).
      rewrite Hfi. rewrite MOK1.
      destruct (get_module_function i M) as [[|]|] eqn:HMi; try discriminate.
      intros H; inversion H; subst; clear H.
      exploit (make_program_get_module_function_prop (D:=D)); eauto.
      intros (Hfalse & Lprim & Lvar).
      rewrite MOK1 in Mdisj.
      destruct Mdisj as [Mvar|Mvar]; try discriminate.
      get_layer_normalize.
      unfold isOKNone in *.
      split.
      + rewrite get_semof_primitive.
        rewrite HMi.
        rewrite Lprim.
        reflexivity.
      + rewrite get_semof_globalvar.
        rewrite Lvar.
        rewrite get_module_variable_oplus in Mvar.
        destruct (get_module_variable i M) as [[|]|];
        destruct (get_module_variable i CTXT) as [[|]|];
        try discriminate.
        reflexivity.

    * intros i fi Hfi.
      rewrite get_layer_globalvar_oplus in Hfi.
      rewrite get_semof_globalvar in Hfi.
      apply res_option_oplus_ok_some_inv in Hfi.
      destruct Hfi as [[HMi HLi] | [HMi HLi]].
      + exploit (make_program_get_module_variable_prop s (CTXT ⊕ M) LL i fi); eauto.
        - destruct (MOK i) as [_ [τ Hτ] _].
          revert Hτ.
          get_module_normalize.
          rewrite HMi.
          destruct (get_module_variable i CTXT) as [[|]|]; try discriminate.
          reflexivity.
        - intros (Hfi & Lprim & Lvar).
          split;eauto.
          split.
          {
            destruct (MOK i) as [_ _ CMdisj].
            get_module_normalize_in CMdisj.
            destruct CMdisj as [Hf|Hv].
            - apply res_option_oplus_ok_none_inv in Hf.
              destruct Hf.
              assumption.
            - apply res_option_oplus_ok_none_inv in Hv.
              destruct Hv.
              congruence.
          }
          {
            destruct (MOK i) as [_ [τ CMvar] _].
            get_module_normalize_in CMvar.
            apply res_option_oplus_ok_inv in CMvar.
            destruct CMvar as [[? ?] | [? ?]].
            - congruence.
            - assumption.
          }
      + exploit (make_program_get_layer_globalvar_prop s (CTXT ⊕ M) LL i fi); eauto.
        get_module_normalize.
        intros (Hgvar & Hf & Hv).
        split; eauto.
        split.
        - apply res_option_oplus_ok_none_inv in Hf.
          destruct Hf.
          assumption.
        - apply res_option_oplus_ok_none_inv in Hv.
          destruct Hv.
          assumption.

    * intros i fi Hfi.
      destruct (MOK i) as [MOK1 [? MOK2]].
      specialize (get_module_variable_oplus i CTXT M).
      rewrite Hfi. rewrite MOK2.
      intros Hle.
      specialize (get_module_variable_isOK i CTXT M).
      rewrite MOK2. intros HW.
      exploit HW. esplit; reflexivity.
      intros (_ & HM). clear HW.
      destruct HM as [? HM].
      rewrite HM in Hle.
      destruct x0; inv_monad Hle.
      exploit (make_program_get_module_variable_prop (D:=D)); eauto.
      intros (Hfalse & Lprim & Lvar).
      split; try assumption.
      specialize (get_module_function_variable_disjoint (CTXT ⊕ M) i).
      rewrite MOK2.
      intros HW.
      destruct HW as [HF|]; try discriminate.
      get_module_normalize_in HF.
      apply res_option_oplus_ok_none_inv in HF.
      destruct HF as [_ HF].
      get_layer_normalize.
      rewrite get_semof_primitive.
      rewrite get_semof_globalvar.
      unfold isOKNone in *.
      subrewrite'.
      split; reflexivity.

    * intros i σ Hiσ.
      apply make_program_make_globalenv in MKP.
      destruct (get_layer_primitive_semof i M LL _ Hiσ) as [[σ' Hσ']|[κ Hκ]].
      + exploit (make_globalenv_get_layer_primitive s (CTXT ⊕ M) LL); eauto.
        reflexivity.
        intros (b & Hb & _).
        erewrite stencil_matches_symbols in Hb.
        eexists; eassumption.
        eapply make_globalenv_stencil_matches; eauto.
      + exploit (make_globalenv_get_module_function s (CTXT ⊕ M) LL); eauto.
        - instantiate (1:=κ); instantiate (1:=i).
          destruct (MOK i) as [MOK' _]; clear MOK.
          destruct MOK' as [? MOK].
          specialize (get_module_function_oplus i CTXT M).
          rewrite MOK. rewrite Hκ.
          intros Hle.
          Transparent oplus.
          destruct (get_module_function i CTXT); try destruct o;
          inv_monad Hle. reflexivity.
        - reflexivity.
        - intros (b & Hb & _).
          eapply make_globalenv_stencil_matches in MKP; eauto.
          inv MKP. rewrite stencil_matches_symbols in Hb.
          rewrite Hb. esplit; reflexivity.
    * intros i σ Hiσ.
      apply make_program_make_globalenv in MKP.
      destruct (LOK' i) as [LOK1 LOK2].
      destruct LOK2 as [? LOK2].
      specialize (get_layer_globalvar_oplus i (〚M 〛 LL) LL).
      rewrite Hiσ. rewrite LOK2.
      intros Hle.
      exploit (make_globalenv_stencil_matches (D:=D)); eauto.
      intros Hsten. inv Hsten.
      destruct x.
      {
        exploit (make_globalenv_get_layer_globalvar (D:=D)); eauto.
        intros (? & Hsym & _).
        rewrite stencil_matches_symbols in Hsym.
        rewrite Hsym. esplit; reflexivity.
      }
      {
        destruct LOK1 as [? LOK1].
        destruct x.
        {
          exploit (make_globalenv_get_layer_primitive (D:=D)); eauto.
          reflexivity.
          intros (? & Hsym & _).
          rewrite stencil_matches_symbols in Hsym.
          rewrite Hsym. esplit; reflexivity.
        }          
        {
          destruct (MOK i) as [MOK1 MOK2].
          destruct MOK1 as [? MOK1].
          destruct x.
          {
            exploit (make_globalenv_get_module_function (D:=D)); eauto.
            reflexivity.
            intros (? & Hsym & _).
            rewrite stencil_matches_symbols in Hsym.
            rewrite Hsym. esplit; reflexivity.
          }
          {
            eapply get_module_function_none_oplus in MOK1.
            destruct MOK1 as [MOK11 MOK12].
            rewrite get_layer_globalvar_oplus, get_semof_globalvar in Hiσ.
            apply res_option_oplus_ok_some_inv in Hiσ.
            destruct Hiσ as [[HMi HLi] | [HMi HLi]]; try congruence.
            destruct MOK2 as [σ' Hσ'].
            rewrite get_module_variable_oplus in Hσ'.
            rewrite HMi in Hσ'.
            destruct (get_module_variable i CTXT) as [[|]|] eqn:HCi;
              try discriminate.
            exploit (make_globalenv_get_module_variable (D:=D)); eauto.
            {
              instantiate (2:=i).
              get_module_normalize.
              rewrite HCi, HMi.
              reflexivity.
            }
            intros (? & Hsym & _).
            rewrite stencil_matches_symbols in Hsym.
            rewrite Hsym. esplit; reflexivity.
          }
        }
      }

    * intros i σ Hiσ.
      apply make_program_make_globalenv in MKP.
      destruct (MOK i) as [MOK1 MOK2 _].
      destruct MOK1 as [? MOK1].
      specialize (get_module_function_oplus i CTXT M).
      rewrite Hiσ. rewrite MOK1.
      intros Hle.
      destruct (get_module_function i M); try destruct o; inv_monad Hle.
      exploit (make_globalenv_get_module_function (D:=D)); eauto.
      reflexivity.
      intros (? & Hsym & _).
      exploit (make_globalenv_stencil_matches (D:=D)); eauto.
      intros Hsten. inv Hsten.
      rewrite stencil_matches_symbols in Hsym.
      rewrite Hsym. esplit; reflexivity.

    * intros i σ Hiσ.
      apply make_program_make_globalenv in MKP.
      destruct (MOK i) as [_ MOK1 _].
      destruct MOK1 as [? MOK1].
      specialize (get_module_variable_oplus i CTXT M).
      rewrite Hiσ. rewrite MOK1.
      intros Hle.
      destruct (get_module_variable i M); try destruct o; inv_monad Hle.
      exploit (make_globalenv_get_module_variable (D:=D)); eauto.
      intros (? & Hsym & _).
      exploit (make_globalenv_stencil_matches (D:=D)); eauto.
      intros Hsten. inv Hsten.
      rewrite stencil_matches_symbols in Hsym.
      rewrite Hsym. esplit; reflexivity.
  Qed.

  Lemma accessors_monotonic_plus_none {D: compatdata}
        {L1 L2: compatlayer D}:
    AccessorsDefined L1 ->
    cl_exec_load L2 = OK None ->
    cl_exec_store L2 = OK None ->
    AccessorsDefined (L2 ⊕ L1).
  Proof.
    intros.
    apply accessors_defined_true in H.
    econstructor.
    unfold accessors_defined in *.
    simpl. rewrite H0, H1.
    caseEq (cl_exec_load L1); intros; rewrite H2 in H; simpl in *; try discriminate.
    destruct o; simpl in *; try discriminate.
    caseEq (cl_exec_store L1); intros; rewrite H3 in H; simpl in *; try discriminate.
    destruct o; simpl in *; try discriminate.
    reflexivity.
  Qed.

  Lemma LayerOK_not_None `{D: compatdata} (L: compatlayer D):
    forall i,
      LayerOK L ->
      ~isOKNone (get_layer_primitive i L) ->
      exists func, get_layer_primitive i L = OK (Some func).
  Proof.
    intros. destruct (H i) as [[σ Hσ] _ _].
    rewrite Hσ in *; clear Hσ.
    destruct σ as [|]; eauto.
    elim H0; reflexivity.
  Qed.

  Lemma LayerOK_elim `{D: compatdata} (L: compatlayer D):
    forall i v,
      LayerOK L ->
      get_layer_globalvar i L = OK (Some v) ->
      get_layer_primitive i L = OK None.
  Proof.
    intros. 
    destruct (H i) as [Hlayer _ Hdisj].
    rewrite H0 in Hdisj.
    destruct Hdisj; try discriminate.
    assumption.
  Qed.

  Instance lasm_semantics_names_match {D} (M: module) (L: compatlayer D):
    LayerOK (〚M〛 L) ->
    LayerNamesMatch D (〚M〛 L).
  Proof.
    split.
    * assumption.
    * intros i j σ Hi Hj.
      rewrite get_semof_primitive in Hi.
      destruct (get_module_function i M) as [[|]|]; try discriminate.
      inversion Hi; subst; clear Hi.
      simpl in *.
      congruence.
  Qed.

  Instance layer_names_match_oplus {D} (L1 L2: compatlayer D):
    LayerOK (L1 ⊕ L2) ->
    LayerNamesMatch D L1 ->
    LayerNamesMatch D L2 ->
    LayerNamesMatch D (L1 ⊕ L2).
  Proof.
    intros HLplus [HL1ok HL1match] [HL2ok HL2match].
    split; try assumption.
    intros i j σ Hi Hj.
    specialize (HL1match i j σ).
    specialize (HL2match i j σ).
    edestruct (get_layer_primitive_oplus_either i L1 L2); eauto.
  Qed.

  Local Existing Instance extcall_invariants_oplus.
  Local Existing Instance primcall_invariants_oplus.

  Theorem soundness_simulation:
    forall {DH DL: compatdata}
           (R: freerg compatrel DH DL)
           (LH: compatlayer DH)
           (LL: compatlayer DL)
           (LH_ACC_DEF: LAsm.AccessorsDefined LH)
           (LL_ACC_DEF: LAsm.AccessorsDefined LL)
           (LH_RECEPT: ExternalCallsXDefined (LH))
           (LL_DETERM: ExternalCallsXDefined (LL))
           (LL_DETERM': PrimitiveCallsXDefined LL)
           (LH_INV: ExtcallInvariantsDefined LH)
           (LL_INV: ExtcallInvariantsDefined LL)
           (LH_PRIM_INV: PrimcallInvariantsDefined LH)
           (LL_PRIM_INV: PrimcallInvariantsDefined LL)
           (LH_NAMES: LayerNamesMatch DH LH)
           (LL_NAMSE: LayerNamesMatch DL LL)
           (M: LAsm.module)
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet)
           (REFINE: cl_sim _ _ R LH (〚 M 〛 LL ⊕ LL))
           (INIT_SIM: cl_init_sim _ _ R LH M LL)
           (CTXT: LAsm.module) s pl
           (PL: make_program s (CTXT ⊕ M) LL = OK pl)
           (prim_valid: get_layer_prim_valid LL s)
           ph
           (PH: make_program s CTXT LH = OK ph)

           (***  XXX: We have to add this LayerOK pre-condition for now on, 
                      hopefully we can remove it in the future ***)
           (HLayerOK': LayerOK (〚 M 〛 LL ⊕ LL))
           (p : principal),
      simulation
        (LAsm.semantics (lcfg_ops := LC LH) ph)
        (LAsm.semantics (lcfg_ops := LC LL) pl)
        (observe_lasm _ p) (observe_lasm _ p).
  Proof.
    intros; rename p into pp. 
    assert (acc_def_prf2: AccessorsDefined (〚M 〛 LL ⊕ LL)).
    {
      eapply accessors_monotonic_plus_none; try assumption; simpl; reflexivity.
    }

    (** Thanks to [INIT_SIM], we know that [R] cannot be the identity relation. *)
    destruct R as [| DL R].
    {
      simpl in *.
      elim INIT_SIM.
    }

    apply simulation_no_stutter with (sim_match:= match_states(D1:=DH)(D2:=DL) s).
    + (* match observe *)
      intros [rs1 [m1 d1]] [rs2 [m2 d2]] Hmatch.
      exploit match_states_observe; eauto.
    + (* match final state *)
      intros. inv H0.
      inv H. inv H4.
      unfold Pregmap.get in *.
      econstructor; eauto.
      specialize (match_reg PC).
      rewrite H1 in match_reg. inv match_reg.
      reflexivity.
      specialize (match_reg EAX).
      rewrite H2 in match_reg. inv match_reg.
      reflexivity.
    + (* one_plus step soundness *)
      intros. simpl in H. simpl.
      assert (Hle: CTXT ≤ CTXT) by reflexivity.
      assert (Hge: make_globalenv s CTXT LH = ret (Genv.globalenv ph)).
      {
        unfold make_globalenv. rewrite PH.
        reflexivity.
      }
      
      assert (Hp: isOK (make_program s CTXT (〚M 〛 LL ⊕ LL))).
      {
        eapply make_program_vertical'; eassumption.
      }            
      assert (Hge': isOK (make_globalenv s CTXT (〚M 〛 LL ⊕ LL))).
      {
        destruct Hp as [p Hp].
        eapply make_program_make_globalenv in Hp.
        esplit. eauto.
      }    
      destruct Hge' as [ge' Hge'].
      specialize (make_globlenv_monotonic_weak _ _ _ _ Hle REFINE Hge ge' Hge'); eauto 2.
      intros Hle'.
      (* INSTANCE_NOT_FOUND: The following instances are required, but currently we could not prove *)
      (* We can add them to sprimcall_sim, or to the definition of semof_fundef of LAsm *)

      pose proof Hge as Hge_match.
      apply make_globalenv_stencil_matches in Hge.
      pose proof Hge' as Hge_match'.
      apply make_globalenv_stencil_matches in Hge'.
      destruct s1, s2, s1'. destruct m, m0, m1.
      assert (Hge_external':
                forall b ef, 
                  Genv.find_funct_ptr ge' b = Some (External ef) ->
                  exists i sg, ef = EF_external i sg) by
          abstract
            (intros until ef; eapply ge_external_valid; eauto).

      assert (OKLayer: LayerOK (〚M 〛 LL ⊕ LL)).
      {
        eapply make_program_layer_ok; eassumption.
      }

      assert (Hnames: LayerNamesMatch DL (〚M〛 LL ⊕ LL)). {
        apply layer_names_match_oplus; eauto.
        apply lasm_semantics_names_match; eauto.
        rewrite <- left_upper_bound in OKLayer.
        eassumption.
      }
      exploit (one_step_sim_monotonic_alt s (Genv.globalenv ph) ge'); eauto 2.

      pose proof prim_valid as prim_valid'.
      {
        unfold get_layer_prim_valid in *.
        intros.
        specialize (get_layer_primitive_oplus i (〚M 〛 LL) LL). rewrite H1.
        intros Heq.
        caseEq (get_layer_primitive i (〚M 〛 LL)); intros; rewrite H2 in Heq;
        try destruct o; caseEq (get_layer_primitive i LL); intros; rewrite H3 in Heq;
        try destruct o; inv_monad Heq; try discriminate.
        {
          assert (MOK: ModuleOK M).
          {
            assert (HmOK: ModuleOK (CTXT ⊕ M)).
            {
              eapply make_program_module_ok.
              esplit; eauto.
            }
            eapply module_ok_antitonic; try eassumption.
            apply right_upper_bound.
          }
          destruct (MOK i) as [[[|] MOK'] _ _].
          {
            assert (mk_prog: isOK(make_program s M LL)).
            {
              eapply make_program_monotonic_exists; try eassumption; try reflexivity.
              apply right_upper_bound.
            }
            rewrite get_semof_primitive in H2.
            rewrite MOK' in H2.
            unfold semof_function in H2; monad_norm.
            unfold module, module_ops in *.
            simpl in *.
            inv_monad H2.
            inv H2.
            subst.
            simpl.
            destruct (Decision.decide (ExtcallInvariantsDefined LL)).
            destruct (Decision.decide (PrimcallInvariantsDefined LL)).
            destruct (Decision.decide (LayerNamesMatch DL LL)).
            destruct (Decision.decide (get_layer_prim_valid LL s)).
            rewrite accessors_defined_weak; try assumption.
            destruct mk_prog as [? mk_prog].
            unfold module, module_ops in *.
            rewrite mk_prog. reflexivity.
            elim n; assumption.
            elim n; assumption.
            elim n; assumption.
            elim n; assumption.
          }
          {
            rewrite get_semof_primitive in H2.
            rewrite MOK' in H2.
            discriminate.
          }
        }
        eauto.
      }
      
      intros [rs2' [m2'[d2'[Hstep' Hmatch']]]].
      refine_split'; eauto 2.
      assert (Hge'': make_globalenv s (CTXT ⊕ M) LL = ret (Genv.globalenv pl)).
      {
        unfold make_globalenv. rewrite PL.
        reflexivity.
      }
      (*assert (Hle'': LL ≤ 〚M 〛 LL ⊕ LL) by apply right_upper_bound.*)
      eapply (one_step_vertical_composition(L:=LL)); eauto.
  Qed.

  Theorem soundness_forward:
    forall {DH DL: compatdata}
           (R: freerg compatrel DH DL)
           (LH: compatlayer DH)
           (LL: compatlayer DL)
           (LH_ACC_DEF: LAsm.AccessorsDefined LH)
           (LL_ACC_DEF: LAsm.AccessorsDefined LL)
           (LH_RECEPT: ExternalCallsXDefined (LH))
           (LL_DETERM: ExternalCallsXDefined (LL))
           (LL_DETERM': PrimitiveCallsXDefined LL)
           (LH_INV: ExtcallInvariantsDefined LH)
           (LL_INV: ExtcallInvariantsDefined LL)
           (LH_PRIM_INV: PrimcallInvariantsDefined LH)
           (LL_PRIM_INV: PrimcallInvariantsDefined LL)
           (LH_NAMES: LayerNamesMatch DH LH)
           (LL_NAMSE: LayerNamesMatch DL LL)
           (M: LAsm.module)
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet)
           (REFINE: cl_sim _ _ R LH (〚 M 〛 LL ⊕ LL))
           (INIT_SIM: cl_init_sim _ _ R LH M LL)
           (CTXT: LAsm.module) s pl
           (PL: make_program s (CTXT ⊕ M) LL = OK pl)
           (prim_valid: get_layer_prim_valid LL s)
           ph
           (PH: make_program s CTXT LH = OK ph)

           (***  XXX: We have to add this LayerOK pre-condition for now on, 
hopefully we can remove it in the future ***)
           (HLayerOK': LayerOK (〚 M 〛 LL ⊕ LL)),
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC LH) ph)
        (LAsm.semantics (lcfg_ops := LC LL) pl).
    Proof.
      intros. 
      assert (acc_def_prf2: AccessorsDefined (〚M 〛 LL ⊕ LL)).
      {
        eapply accessors_monotonic_plus_none; try assumption; simpl; reflexivity.
      }

      (** Thanks to [INIT_SIM], we know that [R] cannot be the identity relation. *)
      destruct R as [| DL R].
      {
        simpl in *.
        elim INIT_SIM.
      }
      eapply forward_simulation_plus with (match_states:= match_states s).
      + (* find_symbol *)
        intros.
        assert (Hge: make_globalenv s (CTXT ⊕ M) LL = ret (Genv.globalenv pl)).
        {
          unfold make_globalenv. rewrite PL.
          reflexivity.
        }           
        assert (Hge': make_globalenv s CTXT LH = ret (Genv.globalenv ph)).
        {
          unfold make_globalenv. rewrite PH.
          reflexivity.
        }           
        apply make_globalenv_stencil_matches in Hge.          
        apply make_globalenv_stencil_matches in Hge'.          
        inv Hge. inv Hge'.
        erewrite stencil_matches_symbols.
        erewrite stencil_matches_symbols0.
        trivial.

      + (* initial state *)
        intros. inv H.
        assert (Hge: make_globalenv s CTXT LH = ret (Genv.globalenv ph)).
        {
          unfold make_globalenv. rewrite PH.
          reflexivity.
        }            
        apply make_globalenv_stencil_matches in Hge.
        inv Hge. 
        assert (Hge: make_globalenv s (CTXT ⊕ M) LL = ret (Genv.globalenv pl)).
        {
          unfold make_globalenv. rewrite PL.
          reflexivity.
        }            
        apply make_globalenv_stencil_matches in Hge.
        inv Hge.
        
        assert(Hprog_defs: prog_defs_le (prog_defs ph) (prog_defs pl)).
        {
          inv REFINE.
          eapply cl_sim_layer_pointwise in cl_sim_layer.
          destruct cl_sim_layer as [Hprim Hvar].
          assert (HLayerOK: LayerOK LH).
          {
            eapply make_program_layer_ok.
            esplit. eassumption.
          }
          (*assert (HLayerOK': LayerOK (〚M 〛 LL ⊕ LL)).
            {
              assert (Hp: isOK (make_program s CTXT (〚M 〛 LL ⊕ LL))).
              {
                eapply make_program_vertical'; eassumption.
              }    
              eapply make_program_layer_ok; eassumption.
            }*)
          eapply make_program_init_mem_le; try eassumption;
          intros.
          - destruct H.
            + eapply LayerOK_not_None in HLayerOK; eauto.
              destruct HLayerOK as [func Hprim'].
              specialize (Hprim i).
              rewrite Hprim' in Hprim.
              specialize (get_layer_primitive_oplus i (〚M 〛 LL) LL). 
              intros Heq.
              destruct (HLayerOK' i) as [HLayerOK _ _].
              destruct HLayerOK as [? HLayerOK].
              rewrite HLayerOK in Hprim. rewrite HLayerOK in Heq.
              Opaque mapsto semof.
              inv Hprim. inv H3.
              simpl in Heq.
              caseEq (get_layer_primitive i LL); intros; simpl in H1; rewrite H1 in *.
              destruct o.
              * (*get_layer_primitive i LL = OK Some*)
                left. red; intros. inv H3.
              * (*get_layer_primitive i LL = OK None*)
                right. red; intros.
                specialize (get_module_function_oplus i CTXT M).
                unfold isOKNone in H3.
                rewrite H3. intros Hle. simpl in Hle.
                caseEq (get_module_function i M); intros; rewrite H4 in *;
                try destruct o; destruct (get_module_function i CTXT);
                try destruct o; inv_monad Hle; try discriminate.
                rewrite get_layer_primitive_oplus in HLayerOK.
                rewrite get_semof_primitive in HLayerOK.
                rewrite H4 in HLayerOK.
                simpl in HLayerOK.
                rewrite H1 in HLayerOK.
                discriminate.
              * left; discriminate.
            + right. red; intros. elim H.
              specialize (get_module_function_oplus i CTXT M).
              unfold isOKNone in H1. rewrite H1.
              intros Hle. simpl in Hle.
              destruct (get_module_function i CTXT).
              destruct o. destruct (get_module_function i M); try destruct o; inv_monad Hle; try discriminate.
              reflexivity.
              destruct (get_module_function i M); try destruct o; inv_monad Hle; try discriminate.
          - destruct H.
            + clear HLayerOK.
              (*destruct HLayerOK as [_ Hvar'].*)
              specialize (Hvar i).
              (*specialize (Hvar' i).
                destruct Hvar' as [? Hvar'].
                rewrite Hvar' in Hvar.*)
              rewrite H in Hvar.
              specialize (get_layer_globalvar_oplus i (〚M 〛 LL) LL). 
              intros Heq.
              specialize (LayerOK_elim _ i v HLayerOK'). intros Him.
              destruct (HLayerOK' i) as [_ HLayerOK _].
              destruct HLayerOK as [? HLayerOK].
              rewrite HLayerOK in Hvar. rewrite HLayerOK in Heq.
              Opaque mapsto semof.
              inv Hvar. inv H3. specialize (Him HLayerOK).
              simpl in Heq.
              caseEq (get_layer_globalvar i LL); intros; simpl in H1; rewrite H1 in *.
              destruct o.
              * (*get_layer_globalvar i LL = OK Some*)
                caseEq (get_layer_globalvar i (〚M 〛 LL)); intros; simpl in H2; rewrite H2 in Heq;
                try destruct o; inv_monad Heq.
                discriminate.
                inv H4. left; reflexivity.
              * (*get_layer_globalvar i LL = OK None*)
                right.
                rewrite get_layer_globalvar_oplus in HLayerOK.
                rewrite get_semof_globalvar in HLayerOK.
                setoid_rewrite H1 in HLayerOK.
                rewrite id_right in HLayerOK.
                assert (MCOK: ModuleOK (CTXT ⊕ M)).
                {
                  eapply make_program_module_ok.
                  eexists.
                  eassumption.
                }
                destruct (MCOK i) as [_ [y' Hy'] _].
                get_module_normalize_in Hy'.
                apply res_option_oplus_ok_inv in Hy'.
                destruct Hy' as [[HC HM] | [HM HC]]; try congruence.
                get_module_normalize.
                rewrite HC.
                rewrite id_left.
                assumption.
              * (*get_layer_globalvar i LL = OK None*)
                caseEq (get_layer_globalvar i (〚M 〛 LL)); intros; simpl in H2;
                rewrite H2 in Heq; try destruct o; inv_monad Heq.
            + right. 
              specialize (get_module_variable_oplus i CTXT M).
              intros Hle.
              exploit (make_program_module_ok s (CTXT ⊕ M) LL).
              esplit; eassumption.
              intros [_ Hmo _].
              destruct Hmo as [? Hmo]. rewrite Hmo in Hle.
              simpl in *. unfold module in *. 
              rewrite H in Hle.
              destruct (get_module_variable i M); try destruct o;
              inv_monad Hle.
              * discriminate.
              * inv H2.
                assumption.
        }
        
        (* Are there any lemmas to prove the init_mem exists*)
        assert (Hinit_mem_exists: exists m': mwd DL, Genv.init_mem pl = Some m').
        {
          (*This is the only lemma that I can find*)
          eapply (Genv.init_mem_exists pl).
          intros.
          exploit (make_program_gvar (D:=DL)); try eassumption.
          intros [vi[Hg Hor]].
          inv INIT_SIM.
          destruct Hor as [Hor|Hor].
          - specialize (get_module_variable_oplus i CTXT M).
            rewrite Hor. intros Hle. 
            simpl in Hle.
            caseEq (get_module_variable i CTXT); intros;
            rewrite H1 in Hle; try destruct o; 
            caseEq (get_module_variable i M); intros;
            rewrite H2 in Hle; try destruct o; inv_monad Hle;
            try discriminate; inv H4.
            + rewrite (Genv.init_data_list_valid_symbols_preserved _ (Genv.globalenv ph)).
              * specialize (Genv.init_mem_valid _ _ H0).
                intros HW. specialize (HW i (globvar_map make_varinfo vi)).
                apply HW. 
                eapply make_program_get_module_variable; try eassumption.
              * intros. congruence.
            + simpl. eauto 2.
          - specialize (cl_init_sim_low i). 
            congruence.
        }

        destruct Hinit_mem_exists as [? ?].
        destruct m0, x. erewrite init_mem_with_data in H0.
        (* It is required to prove the relate and match empty data *)
        assert(Hcl_init_mem: cl_init_sim_mem DH DL R s m0).
        {
          inv INIT_SIM. 
          eapply cl_init_sim_init_mem with (CTXT:= CTXT) ; eauto.
          erewrite PL. erewrite init_mem_with_data in H.
          caseEq (Genv.init_mem pl); intros; rewrite H1 in H; try discriminate. 
          inv H. rewrite <- H1.
          reflexivity.
        }

        assert(Hprog_main: (prog_main ph) = (prog_main pl)).
        {
          erewrite make_program_prog_main; try eassumption.
          erewrite make_program_prog_main; try eassumption.
          reflexivity.
        }

        pose proof H as Hinit_mem'.
        erewrite init_mem_with_data in H.          
        caseEq (Genv.init_mem ph); intros; rewrite H1 in H0; contra_inv.
        caseEq (Genv.init_mem pl); intros; rewrite H2 in H; contra_inv.
        inv H. inv H0.
        exploit (Genv.init_mem_le_genv_next _ _ Hprog_defs); eauto.
        intros Hnextblock.
        assert(Hgenv_next: Mem.nextblock m = genv_next s).
        {
          eapply Genv.init_mem_genv_next in H1.
          rewrite <- H1.
          assumption.
        }
        assert(Hgenv_next': Mem.nextblock m0 = genv_next s).
        {
          eapply Genv.init_mem_genv_next in H2.
          rewrite <- H2.
          assumption.
        }
        assert (Hval_inj: forall reg,
                            val_inject (Mem.flat_inj (genv_next s)) (Pregmap.get reg (Pregmap.init Vundef))
                                       (Pregmap.get reg (Pregmap.init Vundef))).
        {
          intros. unfold Pregmap.get. rewrite Pregmap.gi.
          constructor.
        }
        esplit. split; eauto.
        econstructor; eauto.
        subst rs0 ge.
        econstructor; eauto.
        econstructor; eauto.
        econstructor; eauto.
        * (* Mem.inject *)
          rewrite <- Hgenv_next.
          exploit (Genv.init_mem_le_inject _ _ Hprog_defs); eauto.
        * (* relate_AbData *)
          eapply cl_init_sim_relate; eauto.
        * (* match_AbData *)
          eapply cl_init_sim_match; eauto.
        * (* flat_inj *)
          unfold Mem.flat_inj. intros.
          destruct (plt b1 (genv_next s)); contra_inv.
          inv H. split; reflexivity.
        * (* nextblock *)
          rewrite Hnextblock. xomega.
        * (* no perm *)
          inv INIT_SIM.
          red; intros. specialize (cl_init_sim_glbl _ H).

          (* XXXX: How to prove the new_glbl identifiers has no permission on the init_mem??*)
          (* XXX: We have to prove the Genv.find_func_ptr and Genv_find_var_info are none*)
          (* XXX: How to guarrantee that new_glbl is not defined in the module M ?????*)
          apply make_program_make_globalenv in PH.
          assert (HmOK: ModuleOK (CTXT ⊕ M)).
          {
            eapply make_program_module_ok.
            esplit; eauto.
          }
          rename HLayerOK' into HLOK.
          (*assert (HLOK: LayerOK (〚M 〛 LL ⊕ LL)).
            {
              eapply make_program_layer_ok.
              eapply make_program_vertical'; eassumption.
            }*)
          assert (MOK: ModuleOK M).
          {
            eapply module_ok_antitonic; try eassumption.
            apply right_upper_bound.
          }

          eapply Genv.init_mem_no_perm; eauto.
          erewrite stencil_matches_symbols; now eauto.
          (* Genv.find_funct_ptr (Genv.globalenv ph) b = None *)

          {
            caseEq (Genv.find_funct_ptr (Genv.globalenv ph) b); intros; try reflexivity.
            { 
              eapply make_globalenv_find_funct_ptr in H4; eauto.
              destruct H4 as [i0[Hf Hmo]].
              erewrite stencil_matches_symbols in Hf.
              specialize (genv_vars_inj _ _ _ _ H0 Hf).
              intros; subst.
              specialize (cl_init_sim_glbl_module _ H).
              destruct cl_init_sim_glbl_module as [vi Hmo'].
              destruct Hmo as [ Hmo| Hmo].
              {
                destruct Hmo as [i'[Hmo _]].
                destruct (HmOK i0) as [Hmog Hmov HNone].
                destruct HNone.
                {
                  unfold isOKNone in *.
                  rewrite get_module_function_oplus in H4.
                  rewrite Hmo in H4.
                  destruct (get_module_function i0 M) as [[|]|]; discriminate.
                }
                {
                  specialize (get_module_variable_oplus i0 CTXT M).
                  unfold isOKNone in H4. rewrite H4.
                  rewrite Hmo'. intros Hle. simpl in Hle. 
                  destruct (get_module_variable i0 CTXT) as [[|]|]; discriminate.
                }
              }
              inv REFINE.
              eapply cl_sim_layer_pointwise in cl_sim_layer.
              destruct Hmo as [fe[Hmo _]].
              destruct cl_sim_layer as [cl_layer _].
              specialize (cl_layer i0).
              rewrite Hmo in cl_layer.
              assert (~ isOKNone (get_layer_primitive i0 (〚M 〛 LL ⊕ LL))).
              {
                simpl; inv cl_layer; try discriminate.
                inv H6. discriminate.
              }
              exploit (LayerOK_not_None (D:= DL)); eauto.
              intros [func Hl].
              specialize (get_layer_primitive_oplus i0 (〚M 〛 LL) LL). 
              rewrite Hl. intros Hle.
              caseEq (get_layer_primitive i0 LL); intros;
              rewrite H5 in Hle; try destruct o;
              caseEq (get_layer_primitive i0 (〚M 〛 LL)); intros;
              rewrite H6 in Hle; try destruct o; inv Hle.
              {
                specialize (cl_init_sim_glbl_prim _ H).
                rewrite Hmo in cl_init_sim_glbl_prim.
                inv cl_init_sim_glbl_prim.
              }
              {
                destruct (MOK i0) as [MOK1 MOK2 _].
                exploit get_module_function_variable_disjoint; eauto.
                intros HT. inv HT.
                {
                  rewrite get_semof_primitive in H6.
                  unfold isOKNone in H7; rewrite H7 in H6.
                  discriminate.
                }
                {
                  rewrite Hmo' in H7. inv H7.
                }
              }
            }
          }
          (* Genv.find_var_info (Genv.globalenv ph) b = None *)
          {
            caseEq (Genv.find_var_info (Genv.globalenv ph) b); intros; try reflexivity.
            { 
              eapply make_globalenv_find_var_info in H4; eauto.
              destruct H4 as [i0[Hf Hmo]].
              destruct Hmo as [vi0[_ Hmo]].
              erewrite stencil_matches_symbols in Hf.
              specialize (genv_vars_inj _ _ _ _ H0 Hf).
              intros; subst.
              specialize (cl_init_sim_glbl_module _ H).
              destruct cl_init_sim_glbl_module as [vi Hmo'].
              destruct Hmo as [ Hmo| Hmo].
              {
                destruct (HmOK i0) as [_ Hmov _].
                specialize (get_module_variable_oplus i0 CTXT M).
                rewrite Hmo. rewrite Hmo'.
                destruct Hmov as [? Hmov]. rewrite Hmov.
                intros Hle. inv Hle.
              }
              rewrite Hmo in cl_init_sim_glbl.
              inv cl_init_sim_glbl.
            }
          }

        * (* b< Mem.nextblock m *)
          intros. rewrite Hgenv_next.
          eapply genv_symb_range in H0.
          xomega.
        * (* val_inject *)
          val_inject_simpl.
          unfold symbol_offset.
          erewrite stencil_matches_symbols.
          erewrite stencil_matches_symbols0.
          rewrite Hprog_main.
          caseEq (find_symbol s (prog_main pl)); intros.
          assert (Mem.flat_inj (genv_next s) b = Some (b, 0%Z)).
          {
            eapply stencil_find_symbol_inject'; eauto.
          }
          econstructor; eauto.
          constructor.
        * (* high_level_inv *)
          eapply empty_data_high_level_invariant.            
        * (* high_level_inv *)
          eapply empty_data_high_level_invariant.            
        * (* low_level_invariant *)
          eapply empty_data_low_level_invariant.
        * (* asm_inv *)
          split; eauto.
          econstructor; eauto.
          lift_unfold. rewrite Hgenv_next'. xomega.
          lift_unfold. eapply Genv.initmem_inject_neutral; eauto.
          lift_unfold. rewrite Hgenv_next'.
          val_inject_simpl.
          unfold symbol_offset.
          erewrite stencil_matches_symbols0.
          caseEq (find_symbol s (prog_main pl)); intros.
          assert (Mem.flat_inj (genv_next s) b = Some (b, 0%Z)).
          {
            eapply stencil_find_symbol_inject'; eauto.
          }
          econstructor; eauto.
          constructor.
          repeat (eapply AsmX.set_reg_wt; try constructor).
          unfold symbol_offset.
          destruct (Genv.find_symbol (Genv.globalenv pl) (prog_main pl)); constructor.
      + (* final state *)
        intros. inv H0.
        inv H. inv H4.
        unfold Pregmap.get in *.
        econstructor; eauto.
        specialize (match_reg PC).
        rewrite H1 in match_reg. inv match_reg.
        reflexivity.
        specialize (match_reg EAX).
        rewrite H2 in match_reg. inv match_reg.
        reflexivity.

      + (* one_plus step soundness *)
        intros. simpl in H. simpl.
        assert (Hle: CTXT ≤ CTXT) by reflexivity.
        assert (Hge: make_globalenv s CTXT LH = ret (Genv.globalenv ph)).
        {
          unfold make_globalenv. rewrite PH.
          reflexivity.
        }
        
        assert (Hp: isOK (make_program s CTXT (〚M 〛 LL ⊕ LL))).
        {
          eapply make_program_vertical'; eassumption.
        }            
        assert (Hge': isOK (make_globalenv s CTXT (〚M 〛 LL ⊕ LL))).
        {
          destruct Hp as [p Hp].
          eapply make_program_make_globalenv in Hp.
          esplit. eauto.
        }    
        destruct Hge' as [ge' Hge'].
        specialize (make_globlenv_monotonic_weak _ _ _ _ Hle REFINE Hge ge' Hge'); eauto 2.
        intros Hle'.
        (* INSTANCE_NOT_FOUND: The following instances are required, but currently we could not prove *)
        (* We can add them to sprimcall_sim, or to the definition of semof_fundef of LAsm *)

        pose proof Hge as Hge_match.
        apply make_globalenv_stencil_matches in Hge.
        pose proof Hge' as Hge_match'.
        apply make_globalenv_stencil_matches in Hge'.
        destruct s1, s2, s1'. destruct m, m0, m1.
        assert (Hge_external':
                  forall b ef, 
                    Genv.find_funct_ptr ge' b = Some (External ef) ->
                    exists i sg, ef = EF_external i sg) by
            abstract
              (intros until ef; eapply ge_external_valid; eauto).

        assert (OKLayer: LayerOK (〚M 〛 LL ⊕ LL)).
        {
          eapply make_program_layer_ok; eassumption.
        }

        assert (Hnames: LayerNamesMatch DL (〚M〛 LL ⊕ LL)). {
          apply layer_names_match_oplus; eauto.
          apply lasm_semantics_names_match; eauto.
          rewrite <- left_upper_bound in OKLayer.
          eassumption.
        }

        exploit (one_step_sim_monotonic_alt s (Genv.globalenv ph) ge'); eauto 2.

        pose proof prim_valid as prim_valid'.
        {
          unfold get_layer_prim_valid in *.
          intros.
          specialize (get_layer_primitive_oplus i (〚M 〛 LL) LL). rewrite H1.
          intros Heq.
          caseEq (get_layer_primitive i (〚M 〛 LL)); intros; rewrite H2 in Heq;
          try destruct o; caseEq (get_layer_primitive i LL); intros; rewrite H3 in Heq;
          try destruct o; inv_monad Heq; try discriminate.
          {
            assert (MOK: ModuleOK M).
            {
              assert (HmOK: ModuleOK (CTXT ⊕ M)).
              {
                eapply make_program_module_ok.
                esplit; eauto.
              }
              eapply module_ok_antitonic; try eassumption.
              apply right_upper_bound.
            }
            destruct (MOK i) as [[[|] MOK'] _ _].
            {
              assert (mk_prog: isOK(make_program s M LL)).
              {
                eapply make_program_monotonic_exists; try eassumption; try reflexivity.
                apply right_upper_bound.
              }
              rewrite get_semof_primitive in H2.
              rewrite MOK' in H2.
              unfold semof_function in H2; monad_norm.
              unfold module, module_ops in *.
              simpl in *.
              inv_monad H2.
              inv H2.
              subst.
              simpl.
              destruct (Decision.decide (ExtcallInvariantsDefined LL)).
              destruct (Decision.decide (PrimcallInvariantsDefined LL)).
              destruct (Decision.decide (LayerNamesMatch DL LL)).
              destruct (Decision.decide (get_layer_prim_valid LL s)).
              rewrite accessors_defined_weak; try assumption.
              destruct mk_prog as [? mk_prog].
              unfold module, module_ops in *.
              rewrite mk_prog. reflexivity.
              elim n; assumption.
              elim n; assumption.
              elim n; assumption.
              elim n; assumption.
            }
            {
              rewrite get_semof_primitive in H2.
              rewrite MOK' in H2.
              discriminate.
            }
          }
          eauto.
        }
        
        intros [rs2' [m2'[d2'[Hstep' Hmatch']]]].
        refine_split'; eauto 2.
        assert (Hge'': make_globalenv s (CTXT ⊕ M) LL = ret (Genv.globalenv pl)).
        {
          unfold make_globalenv. rewrite PL.
          reflexivity.
        }
        (*assert (Hle'': LL ≤ 〚M 〛 LL ⊕ LL) by apply right_upper_bound.*)
        eapply one_step_vertical_composition; eauto.
    (** eapply cl_le_invs_ext; try eassumption.
     * eapply cl_le_invs_prim; try eassumption.
     * eapply cl_le_get_layer_prim_valid; try eassumption.*)
    Qed.

  Theorem soundness_determinate :
    forall {DL: compatdata}
           (LL: compatlayer DL)
           (LL_ACC_DEF: LAsm.AccessorsDefined LL)
           (LL_DETERM: ExternalCallsXDefined LL)
           (LL_DETERM': PrimitiveCallsXDefined LL)
           M s pl
           (PL: make_program s M LL = OK pl),
      determinate (LAsm.semantics (lcfg_ops := LC LL) pl).
  Proof.
    intros.
    assert(externalcall_prf: ExternalCalls (mwd DL) 
                                           (external_calls_ops:= compatlayer_extcall_ops LL)).
    {
      eapply compatlayer_extcall_strong; assumption.
    }
    intros; constructor; simpl; intros.
    - (* determ *)
      inv H; inv H0; Equalities.
      + split. constructor. auto.
      + discriminate.
      + discriminate.
      + inv H11. 
      + inv H4. inv H9.
        specialize (Events.external_call_determ (external_calls_ops:= compatlayer_extcall_ops LL)
                                                _ _ _ _ _ _ _ _ _ _ _ H H0).
        intros [? ?]. esplit; eauto.
        intros. destruct H4 as [? ?]; subst; trivial.
      + discriminate.
      + inv H5. inv H13.
        assert (vargs0 = vargs) by (eapply annot_arguments_determ_with_data; eauto). subst.
        specialize (Events.external_call_determ (external_calls_ops:= compatlayer_extcall_ops LL)
                                                _ _ _ _ _ _ _ _ _ _ _ H H0).
        intros [? ?]. esplit; eauto.
        intros. destruct H5 as [? ?]; subst; trivial.
      + inv H4. inv H9.
        assert (args0 = args) by (eapply extcall_arguments_determ_with_data; eauto). subst.
        specialize (Events.external_call_determ (external_calls_ops:= compatlayer_extcall_ops LL)
                                                _ _ _ _ _ _ _ _ _ _ _ H H0).
        intros [? ?]. esplit; eauto.
        intros. destruct H4 as [? ?]; subst; trivial.
      + specialize (external_prim_false _ _ _ _ _ _ _ _ _ _ _ _ _ H4 H10).
        intros HF; inv HF.
      + specialize (external_prim_false _ _ _ _ _ _ _ _ _ _ _ _ _ H8 H3).
        intros HF; inv HF.
      +
        inv H3. inv H9.
        destruct H as [?[?[?[? Hsem]]]]; subst.
        destruct H0 as [?[?[?[? Hsem']]]]; subst.
        inv H. rewrite H0 in H2. inv H2.
        inv Hsem. inv Hsem'. 
        eapply stencil_matches_unique in H4; try apply H. subst.
        unfold PrimitiveCallsXDefined in *.
        specialize (LL_DETERM' x0).
        rewrite H0 in LL_DETERM'. simpl in LL_DETERM'.
        caseEq (sprimcall_props DL σ); intros; rewrite H3 in *; try discriminate.
        specialize (primitive_call_determ _ _ _ _ _ _ _ H2 H5).
        intros [? ?]; subst.
        split; eauto. constructor.
    - (* trace length *)
      red; intros; inv H; simpl.
      omega.
      inv H3. eapply external_call_trace_length; eauto.
      inv H4. eapply external_call_trace_length; eauto.
      inv H3. eapply external_call_trace_length; eauto.
      inv H2. destruct H as [?[?[?[? Hsem]]]]; subst.
      inv Hsem. simpl. omega.
    - (* initial states *)
      inv H; inv H0. f_equal. congruence.
    - (* final no step *)
      inv H. unfold Vzero in H0. red; intros; red; intros. inv H; congruence.
    - (* final states *)
      inv H; inv H0. congruence.
  Qed.

  Theorem soundness_receptive :
    forall {DH: compatdata}
           (LH: compatlayer DH)
           (LH_ACC_DEF: LAsm.AccessorsDefined LH)
           (LH_EXT: ExternalCallsXDefined LH)
           M s ph
           (PL: make_program s M LH = OK ph),
      receptive (LAsm.semantics (lcfg_ops := LC LH) ph).
  Proof.
    intros.
    assert(externalcall_prf: ExternalCalls (mwd DH) 
                                             (external_calls_ops:= compatlayer_extcall_ops LH)).
    {
      eapply compatlayer_extcall_strong; assumption.
    }
    split.
    inversion 1; subst.
    - inversion 1; subst; eauto.
    - intros. inv H3.
      exploit (external_call_receptive 
                 (mem:= mwd DH) 
                 (external_calls_ops:= compatlayer_extcall_ops LH)); eauto.
      intros [? [? ?]]. esplit. econstructor; eauto. econstructor; eauto. 
    - intros. inv H4.
      exploit (external_call_receptive 
                 (mem:= mwd DH) 
                 (external_calls_ops:= compatlayer_extcall_ops LH)); eauto.
      intros [? [? ?]]. esplit. eapply exec_step_annot; eauto. econstructor; eauto. 
    - intros. inv H3.
      exploit (external_call_receptive 
                 (mem:= mwd DH) 
                 (external_calls_ops:= compatlayer_extcall_ops LH)); eauto.
      intros [? [? ?]]. esplit. eapply exec_step_external; eauto. econstructor; eauto. 
    - intros. pose proof H2 as Hprim.  inv Hprim.
      destruct H4 as [?[?[?[? Hsem]]]]; subst.
      inv Hsem. inv H3.
      esplit. eapply exec_step_prim_call; eauto.
    - (* single event *)
      red; intros; inv H; simpl.
      omega.
      inv H3. eapply external_call_trace_length; eauto.
      inv H4. eapply external_call_trace_length; eauto.
      inv H3. eapply external_call_trace_length; eauto.
      inv H2. destruct H as [?[?[?[? Hsem]]]]; subst.
      inv Hsem. simpl. omega.
  Qed.

  Theorem soundness:
    forall {DH DL: compatdata}
           (R: freerg compatrel DH DL)
           (LH: compatlayer DH)
           (LL: compatlayer DL)
           (LH_ACC_DEF: LAsm.AccessorsDefined LH)
           (LL_ACC_DEF: LAsm.AccessorsDefined LL)
           (LH_RECEPT: ExternalCallsXDefined (LH))
           (LL_DETERM: ExternalCallsXDefined (LL))
           (LL_DETERM': PrimitiveCallsXDefined LL)
           (LH_INV: ExtcallInvariantsDefined LH)
           (LL_INV: ExtcallInvariantsDefined LL)
           (LH_PRIM_INV: PrimcallInvariantsDefined LH)
           (LL_PRIM_INV: PrimcallInvariantsDefined LL)
           (LH_NAMES: LayerNamesMatch DH LH)
           (LL_NAMSE: LayerNamesMatch DL LL)
           (M: LAsm.module)
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet)
           (REFINE: cl_sim _ _ R LH (〚 M 〛 LL ⊕ LL))
           (INIT_SIM: cl_init_sim _ _ R LH M LL)
           (CTXT: LAsm.module) s pl
           (PL: make_program s (CTXT ⊕ M) LL = OK pl)
           (prim_valid: get_layer_prim_valid LL s)
           ph
           (PH: make_program s CTXT LH = OK ph)

           (***  XXX: We have to add this LayerOK pre-condition for now on, 
hopefully we can remove it in the future ***)
           (HLayerOK': LayerOK (〚 M 〛 LL ⊕ LL)),
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC LH) ph)
        (LAsm.semantics (lcfg_ops := LC LL) pl).
  Proof.

    intros. 
    assert (acc_def_prf2: AccessorsDefined (〚M 〛 LL ⊕ LL)).
    {
      eapply accessors_monotonic_plus_none; try assumption; simpl; reflexivity.
    }

    (** Thanks to [INIT_SIM], we know that [R] cannot be the identity relation. *)
    destruct R as [| DL R].
    {
      simpl in *.
      elim INIT_SIM.
    }

    eapply forward_to_backward_simulation; eauto.
    - eapply soundness_forward; eauto.
    - eapply soundness_receptive; eauto.
    - eapply soundness_determinate; eauto.
  Qed.

End WITHLAYERS.
