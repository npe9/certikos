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
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import MemoryX.
Require Import MemWithData.
Require Import EventsX.
Require Import Globalenvs.
Require Import LAsm.
Require Import Smallstep.
Require Import ClightBigstep.
Require Import Cop.
Require Import ZArith.Zwf.
Require Import VCGen.
Require Import RealParams.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatGenSem.
Require Import CompatClightSem.
Require Import PrimSemantics.
Require Import Clight.
Require Import CDataTypes.
Require Import Ctypes.
Require Import I64Layer.
Require Import CompCertiKOSproof.
Require Import LinkTactic.
Require Import LayerCalculusLemma.
Require Import PThreadIntro.
Require Import PThreadInit.
Require Import PThreadIntroCSource.
Require Import PThreadIntroCode.
Require Import ThreadInitGen.
Require Import ThreadInitGenSpec.
Require Import ThreadInitGenLinkSource.
Require Import ObjThread.
Require Import ObjQueue.
Require Import PseudoJoinReflection.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Notation HDATA := AbstractDataType.RData.
  Notation LDATA := AbstractDataType.RData.

  Notation HDATAOps := (cdata (cdata_ops := pthreadinit_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := mshareintro_data_ops) LDATA).

  Let used : compatlayer LDATAOps := (* pt_free ↦ gensem pt_free_spec
           ⊕ *) shared_mem_init ↦ gensem sharedmem_init_spec
           ⊕ tcb_init ↦ gensem tcb_init_spec.
  Lemma usage_le: used ≤ pthreadintro.
  Proof.
    le_oplus.
  Qed.

  (*
  Lemma thread_free_correct :
    forall COMPILABLE: LayerCompilable (pthreadintro ⊕ L64),
    forall MOK: ModuleOK (thread_free ↦ f_thread_free),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (thread_free ↦ f_thread_free) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATAOps)
             (thread_free ↦ gensem (fun a d => thread_free_spec d a))
             (〚 M2 〛(pthreadintro ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply thread_free_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PTHREADINTROCODE.thread_free_code_correct.
    - transitivity used.
      + apply oplus_monotonic; [ reflexivity | apply right_upper_bound ].
      + apply usage_le.
  Qed.
  *)

  Lemma thread_init_correct :
    forall COMPILABLE: LayerCompilable (pthreadintro ⊕ L64),
    forall MOK: ModuleOK (thread_init ↦ f_thread_init),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (thread_init ↦ f_thread_init) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (thread_init ↦ gensem thread_init_spec)
             (〚 M2 〛(pthreadintro ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply thread_init_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PTHREADINTROCODE.thread_init_code_correct.
    - apply usage_le.
  Qed.

  Record PThreadInit_impl_inverted (M: module): Prop :=
    {
      PThreadInit_thread_free: module;
      PThreadInit_thread_init: module;
      (*
      PThreadInit_thread_free_transf:
        CompCertiKOS.transf_module (thread_free ↦ f_thread_free) =
        ret PThreadInit_thread_free;
       *)
      PThreadInit_thread_init_transf:
        CompCertiKOS.transf_module (thread_init ↦ f_thread_init) =
        ret PThreadInit_thread_init;
      PThreadInit_M:
        M = ((*PThreadInit_thread_free ⊕*) PThreadInit_thread_init) ⊕ ∅;
      PThreadInit_MOK:
        LayerOK (〚M〛 (pthreadintro ⊕ L64) ⊕ pthreadintro ⊕ L64)
    }.

  Lemma module_impl_imply:
    forall M, PThreadInit_impl = OK M -> PThreadInit_impl_inverted M.
  Proof.
    unfold PThreadInit_impl. intros M HM.
    inv_monad' HM.
    econstructor.
    eassumption.
    eassumption.
    inv HM1; reflexivity.
    assumption.
  Qed.

  Lemma link_correct_aux:
    forall M, PThreadInit_impl = OK M ->
              pthreadintro ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATAOps), M)
              : pthreadinit ⊕ L64.
  Proof.
    unfold PThreadInit_impl. intros M HM.
    apply module_impl_imply in HM; destruct HM; subst.
    unfold pthreadinit, pthreadinit_fresh.
    eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      layer_link_split_tac.
      (* - apply thread_free_correct; code_correct_tac. *)
      - apply thread_init_correct; code_correct_tac.
    }
    {
      eapply layer_link_new_glbl_both.
      apply oplus_sim_monotonic.
      apply passthrough_correct.
      apply L64_auto_sim.
    }
  Qed.

  Require Import FlatMemory.
  Require Import Decision.
  Require Import LAsmModuleSem.
  Require Import Soundness.
  Require Import CompatExternalCalls.
  Require Import AuxLemma.
  Require Import Behavior.

  Lemma init_correct:
    forall M, PThreadInit_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA) (pthreadinit ⊕ L64) M (pthreadintro ⊕ L64).
  Proof.
    intros.
    pose proof (fun i => module_ok_variable M i (H0 i)) as MOK; clear H0.
    apply cl_init_sim_intro.
    - constructor; simpl; trivial.
      constructor; simpl; trivial. apply FlatMem.flatmem_empty_inj.
      apply kctxt_inj_empty.
      constructor.
    - intros; inv H0.
    - intros; inv H0.
    - intros; inv H0.
    - intros.
      apply module_impl_imply in H; destruct H; subst.
      transf_none i. specialize (MOK i).
      assert (get_module_variable i (((*PThreadInit_thread_free ⊕ *) PThreadInit_thread_init) ⊕ ∅) = OK None).
      {
        get_module_variable_relfexivity.
      }
      unfold module, module_ops in *.
      congruence.
    - decision.
  Qed.

  Theorem cl_simulation:
    forall p (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      PThreadInit_impl = OK M ->
      make_program s CTXT (pthreadinit ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pthreadintro ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (pthreadinit ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pthreadintro ⊕ L64)) pl)
        (observe_lasm _ p) (observe_lasm _ p).
  Proof.
    intros.
    eapply (soundness_simulation (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    apply module_impl_imply in H; destruct H; assumption.
  Qed.

  Theorem cl_forward_simulation:
    forall (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      PThreadInit_impl = OK M ->
      make_program s CTXT (pthreadinit ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pthreadintro ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (pthreadinit ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pthreadintro ⊕ L64)) pl).
  Proof.
    intros.
    eapply (soundness_forward (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    apply module_impl_imply in H; destruct H; assumption.
  Qed.

  Theorem cl_backward_simulation:
    forall (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      PThreadInit_impl = OK M ->
      make_program s CTXT (pthreadinit ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pthreadintro ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (pthreadinit ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pthreadintro ⊕ L64)) pl).
  Proof.
    intros.
    eapply (soundness (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    apply module_impl_imply in H; destruct H; assumption.
  Qed.

  Require Import LAsmModuleSemMakeProgram.

  Theorem make_program_exists:
    forall (s: stencil) (CTXT M: module) pl,
      PThreadInit_impl = OK M ->
      make_program s (CTXT ⊕ M) (pthreadintro ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (pthreadinit ⊕ L64) = OK ph.
  Proof.
    intros.
    exploit link_correct_aux; eauto.
    eapply make_program_vertical' in H0.
    destruct H0 as [p' Hmake].
    intros Hle.
    eapply make_program_sim_monotonic_exists.
    2: eapply Hle.
    reflexivity.
    eassumption.
    apply module_impl_imply in H; destruct H; assumption.
  Qed.

End WITHCOMPCERTIKOS.
