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
Require Import LAsmModuleSem.
Require Import Observation.

Section WITHMEM.

  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
  Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

  Inductive asm_primitive_le {D}: relation (compatsem D) :=
  | asm_primitive_le_sextcall:
      forall (σ1 σ2: sprimcall_primsem D)
             (SEM: forall (s: stencil) rs rs' m m',
                     sprimcall_primsem_step D σ1 s rs m rs' m' ->
                     sprimcall_valid σ2 s = true ->
                     (Mem.nextblock m <= Mem.nextblock m')%positive
                     /\ exists f' m0' rs0', 
                          sprimcall_primsem_step D σ2 s rs m rs0' m0'
                          /\ inject_incr (Mem.flat_inj (Mem.nextblock m')) f'
                          /\ Memtype.Mem.inject f' m' m0'
                          /\ (Mem.nextblock m' <= Mem.nextblock m0')%positive
                          /\ (forall l,
                                Val.lessdef (Pregmap.get l rs')
                                            (Pregmap.get l rs0'))
             )
             (Hsig: sprimcall_sig σ2 = sprimcall_sig σ1)
             (Hvalid: forall s, sprimcall_valid σ2 s = true -> sprimcall_valid σ1 s = true)
             (Hname: option_le eq (sprimcall_name _ σ1) (sprimcall_name _ σ2))
             (INV: isError (sprimcall_invs D σ2)),
             (*(INV: isError (sprimcall_invs D σ2)),*)
        asm_primitive_le (compatsem_inr σ1) (compatsem_inr σ2).

  Record asm_spec_le {D} (L1 L2: compatlayer D): Prop :=
    {
      asm_spec_le_primitive:
        forall i,
          res_le (option_le (asm_primitive_le)) (get_layer_primitive i L1) (get_layer_primitive i L2)
      ;
      asm_spec_le_globalvars:
        forall i,
          res_le (option_le eq) (get_layer_globalvar i L1) (get_layer_globalvar i L2)
      ;
      asm_spec_le_load:
        res_le (option_le eq) (cl_exec_load L1) (cl_exec_load L2)
      ;
      asm_spec_le_store:
        res_le (option_le eq) (cl_exec_store L1) (cl_exec_store L2)

    }.

  Local Existing Instance extcall_invariants_defined_dec.
  Local Existing Instance primcall_invariants_defined_dec.
  Local Existing Instance prim_valid_dec.

  Lemma asm_sem_intro {D} (i: ident) (f: function) (L: compatlayer D) (σ: sprimcall_primsem D):
    (forall s rs rs' m m' p ,
       sprimcall_primsem_step D σ s rs m rs' m' ->
       make_program s (i ↦ f) L = ret p ->
       (Mem.nextblock m <= Mem.nextblock m')%positive
       /\ exists f' m0' rs0',
            lasm_step (i ↦ f) L i s rs m rs0' m0' 
            /\ inject_incr (Mem.flat_inj (Mem.nextblock m')) f'
            /\ Memtype.Mem.inject f' m' m0'
            /\ (Mem.nextblock m' <= Mem.nextblock m0')%positive
            /\ (forall l,
                  Val.lessdef (Pregmap.get l rs')
                              (Pregmap.get l rs0'))
    ) ->
    fn_sig f = sprimcall_sig σ ->
    (forall s, (if Decision.decide (ExtcallInvariantsDefined L)
                then
                  if Decision.decide (PrimcallInvariantsDefined L)
                  then
                   if Decision.decide (LayerNamesMatch D L)
                   then
                    if Decision.decide (get_layer_prim_valid L s)
                    then
                      if accessors_weak_defined L then
                        match make_program s (i ↦ f) L with
                          | OK _ => true
                          | Error _ => false
                        end
                      else false
                    else false
                   else false
                  else false
                else false) = true -> sprimcall_valid σ s = true) ->
    isError (sprimcall_invs D σ) ->
    forall Hname: option_le eq (sprimcall_name D σ) (Some i),
    forall NOCONFLICT: get_layer_primitive i L = OK None,
    asm_spec_le (i ↦ compatsem_inr σ) (〚i ↦ f〛 L).
  Proof.
    intros.
    constructor.
    { (* primitives *)
      intros.  
      destruct (Coqlib.peq i0 i). 
      - subst.
        rewrite get_layer_primitive_mapsto.
        generalize (get_module_function_mapsto i f).
        intro MODULE.

        pose proof (compat_get_semof_primitive i (i ↦ f) L) as Hsemof.
        lazymatch goal with
          H: ?y1 = ?y2 |-
          ?R ?x ?y3 =>
          replace y3 with y2 by apply H;
          clear H
        end.

        rewrite get_module_function_mapsto.
        unfold semof_function.
        simpl.
        monad_norm.
        constructor. constructor. constructor. simpl.
        + intros.
          (*destruct (Decision.decide (LayerOK L)); try discriminate.*)
          destruct (Decision.decide (ExtcallInvariantsDefined L)); try discriminate.
          destruct (Decision.decide (PrimcallInvariantsDefined L)); try discriminate.
          destruct (Decision.decide (LayerNamesMatch D L)); try discriminate.
          destruct (Decision.decide (get_layer_prim_valid L s)); try discriminate.
          caseEq (accessors_weak_defined L); intros;
          rewrite H5 in H4; try discriminate.
          destruct (make_program s (i ↦ f) L) eqn:Hmp; try discriminate.
          eapply H; eauto.
        + assumption.
        + assumption.
        + assumption.
        + simpl. esplit. eauto.
      - (* none *)
        rewrite get_layer_primitive_mapsto_other_primitive; eauto.
        apply lower_bound.
    }
    { (* variables *)
      intro i0.
      rewrite get_layer_globalvar_mapsto_primitive.
      match goal with
        | |- res_le _ _ ?x => destruct x as  [ [ ? | ] | ?]
      end;
        repeat constructor.
    }
    { (* exec_load *)
      reflexivity.
    }
    { (* exec_store *)
      reflexivity.
    }
  Qed.

End WITHMEM.

Section WITHMEMX.

  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.

  Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
  Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

  Lemma val_inject_lessdef_compose: 
    forall j v1 v2, val_inject j v1 v2 -> forall v3, Val.lessdef v2 v3 -> val_inject j v1 v3.
  Proof.
    inversion 1; subst; inversion 1; subst; auto.
  Qed.

  Lemma asm_primitive_le_compose {D1: compatdata} {D2: compatdata} {R: compatrel D1 D2}:
    forall x0 x1 x2,
      compatsim (freerg_inj _ _ _ R) (compatsem_inr x0) x1 ->
      asm_primitive_le x1 x2 ->
      compatsim (freerg_inj _ _ _ R) (compatsem_inr x0) x2.
  Proof.
    intros. inv H0.
    inv H. inv H2. econstructor. econstructor.
    - intros. exploit sprimcall_sim_step; eauto 1. 
      eapply Hvalid; trivial.
      intros [f'[rs2'[m2'[d2'[Hstep Hmatch]]]]].
      exploit SEM; eauto.
      intros [Hnextblock' [f''[m2''[rs2''[Hstep'[Hincr[Hinject[Hnextblock Hles]]]]]]]].
      destruct m2''.
      inv ASM_INV.
      inv inv_inject_neutral.
      lift_unfold.
      destruct Hinject as [Hinject Heq]. subst.

      inv Hmatch.
      inv match_extcall_states.
      assert (COMPOSE: compose_meminj f' f'' = f').
      {
        apply FunctionalExtensionality.functional_extensionality.
        unfold compose_meminj.
        intro x.
        destruct (f' x) as [ [y delta] | ] eqn:Heqx; try congruence.
        exploit Mem.valid_block_inject_2; eauto.
        unfold Mem.valid_block.
        intro.
        replace (f'' y) with (Some (y, 0%Z)).
        f_equal. f_equal. omega.
        symmetry. apply Hincr. unfold Mem.flat_inj. 
        destruct (plt y (Mem.nextblock m2')) eqn:Hlt.
        reflexivity.
        exfalso. apply n. xomega. 
      }    
      refine_split'. 
      eapply Hstep'.
      econstructor.
      + econstructor; eauto. 
        * rewrite <- COMPOSE. 
          eapply Mem.inject_compose; eauto. 
        * rewrite <- COMPOSE. eapply match_compose; eauto.
          eapply inject_incr_trans.
          2: eassumption.
          eapply flat_inj_inject_incr.
          xomega.
        * xomega.
      + intros.
        eapply val_inject_lessdef_compose; eauto.
    - congruence.
    - eauto.
    - etransitivity; try eassumption.
    - destruct INV as [i1 INV].
      rewrite INV.
      constructor.
  Qed.

  Lemma asm_spec_compose D1 D2 R i x L1 L2:
    cl_sim D1 D2 (freerg_inj _ _ _ R) (i ↦ compatsem_inr x) L1 ->
    asm_spec_le L1 L2 ->
    cl_sim D1 D2 (freerg_inj _ _ _ R) (i ↦ compatsem_inr x) L2.
  Proof.
    intros. inv H0. inv H.
    apply cl_sim_layer_pointwise in cl_sim_layer.
    destruct cl_sim_layer as [cl_sim_layer_prim cl_sim_layer_var].
    econstructor; try (constructor; constructor).
    - apply cl_sim_layer_pointwise.
      split.
      + intro. 
        destruct (peq i i0); subst.
        * specialize (cl_sim_layer_prim i0).          
          rewrite get_layer_primitive_mapsto.
          rewrite get_layer_primitive_mapsto in cl_sim_layer_prim.
          specialize (asm_spec_le_primitive0 i0).
          simpl.
          inv asm_spec_le_primitive0; try constructor.
          inv cl_sim_layer_prim; try congruence.
          rewrite <- H in H3. inv H3.
          inv H1; inv H4; try constructor.
          eapply asm_primitive_le_compose; eauto.
        * specialize (cl_sim_layer_prim i).          
          rewrite get_layer_primitive_mapsto_other_primitive; eauto.        
          specialize (asm_spec_le_primitive0 i0).
          simpl.
          inv asm_spec_le_primitive0; try constructor.
          constructor.
      + (* variables *)
        intros. etransitivity; eauto.
    - simpl.
      inv asm_spec_le_load0.
      constructor.
      econstructor.
      constructor.
    - simpl.
      inv asm_spec_le_store0.
      constructor.
      econstructor.
      constructor.
  Qed.

  Lemma val_list_inject_lessdef_compose:
    forall j v1 v2 (rs2: regset), val_list_inject j v1 (map rs2 v2) -> 
                                  forall rs3, (forall r, Val.lessdef (rs2 r) (rs3 r))
                                              -> val_list_inject j v1 (map rs3 v2).
  Proof.
    induction v1; subst; intros. 
    - destruct v2; inv H. simpl. constructor.
    - destruct v2; inv H.
      simpl.
      constructor.
      + eapply val_inject_lessdef_compose; eauto.
      + eauto.
  Qed.

  Lemma asm_primitive_le_compose_inl {D1: compatdata} {D2: compatdata} {R: compatrel D1 D2}:
    forall x0 x1 x2,
      compatsim (freerg_inj _ _ _ R) (compatsem_inl x0) x1 ->
      asm_primitive_le x1 x2 ->
      compatsim (freerg_inj _ _ _ R) (compatsem_inl x0) x2.
  Proof.
    intros. inv H0.
    inv H. inv H2. econstructor. econstructor.
    - intros. destruct sextcall_sprimcall_sim_step as [i[name Hsimstep]].
      exists i. split; try assumption.
      rewrite name in Hname. inv Hname. reflexivity.
      intros.
      exploit Hsimstep; clear Hsimstep; eauto 1.
      eapply Hvalid; trivial.
      intros [f'[rs2'[m2'[d2'[Hstep Hmatch]]]]].
      destruct Hmatch as (Hmatch & Hincr & Hval & Hless & Hpc & Hesp).
      exploit SEM; eauto.
      intros [Hnextblock' [f''[m2''[rs2''[Hstep'[Hincr'[Hinject[Hnextblock Hles]]]]]]]].
      destruct m2''.
      inv ASM_INV.
      inv inv_inject_neutral.
      Opaque Conventions1.destroyed_at_call.
      lift_unfold.
      destruct Hinject as [Hinject Heq]. subst.

      inv Hmatch.
      assert (COMPOSE: compose_meminj f' f'' = f').
      {
        apply FunctionalExtensionality.functional_extensionality.
        unfold compose_meminj.
        intro x.
        destruct (f' x) as [ [y delta] | ] eqn:Heqx; try congruence.
        exploit Mem.valid_block_inject_2; eauto.
        unfold Mem.valid_block.
        intro.
        replace (f'' y) with (Some (y, 0%Z)).
        f_equal. f_equal. omega.
        symmetry. apply Hincr'. unfold Mem.flat_inj. 
        destruct (plt y (Mem.nextblock m2')) eqn:Hlt.
        reflexivity.
        exfalso. apply n. xomega. 
      }
      refine_split'. 
      eapply Hstep'.
      econstructor; try eassumption.
      + rewrite <- COMPOSE. 
        eapply Mem.inject_compose; eauto.
      + rewrite <- COMPOSE. eapply match_compose; eauto.
        eapply inject_incr_trans.
        2: eassumption.
        Require Import AuxLemma.
        eapply flat_inj_inject_incr.
        xomega.
      + xomega.
      + assumption.
      + eapply val_list_inject_lessdef_compose; eauto.
      + intros.
        eapply Val.lessdef_trans; try eassumption.
        eapply Hless; eauto.
        eapply Hles.
      + eapply Val.lessdef_trans; eauto.
      + eapply Val.lessdef_trans; eauto.
    - congruence.
    - eauto.
    - destruct INV as [i1 INV].
      rewrite INV.
      constructor.
  Qed.

  Lemma asm_spec_compose_inl D1 D2 R i x L1 L2:
    cl_sim D1 D2 (freerg_inj _ _ _ R) (i ↦ compatsem_inl x) L1 ->
    asm_spec_le L1 L2 ->
    cl_sim D1 D2 (freerg_inj _ _ _ R) (i ↦ compatsem_inl x) L2.
  Proof.
    intros. inv H0. inv H.
    apply cl_sim_layer_pointwise in cl_sim_layer.
    destruct cl_sim_layer as [cl_sim_layer_prim cl_sim_layer_var].
    econstructor; try (constructor; constructor).
    - apply cl_sim_layer_pointwise.
      split.
      + intro. 
        destruct (peq i i0); subst.
        * specialize (cl_sim_layer_prim i0).          
          rewrite get_layer_primitive_mapsto.
          rewrite get_layer_primitive_mapsto in cl_sim_layer_prim.
          specialize (asm_spec_le_primitive0 i0).
          simpl.
          inv asm_spec_le_primitive0; try constructor.
          inv cl_sim_layer_prim; try congruence.
          rewrite <- H in H3. inv H3.
          inv H1; inv H4; try constructor.
          eapply asm_primitive_le_compose_inl; eauto.
        * specialize (cl_sim_layer_prim i).          
          rewrite get_layer_primitive_mapsto_other_primitive; eauto.        
          specialize (asm_spec_le_primitive0 i0).
          simpl.
          inv asm_spec_le_primitive0; try constructor.
          constructor.
      + (* variables *)
        intros. etransitivity; eauto.
    - simpl.
      inv asm_spec_le_load0.
      constructor.
      econstructor.
      constructor.
    - simpl.
      inv asm_spec_le_store0.
      constructor.
      econstructor.
      constructor.
  Qed.

End WITHMEMX.
