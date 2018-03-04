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
Require Import PQueueIntro.
Require Import PQueueInit.
Require Import PQueueIntroCSource.
Require Import PQueueIntroCode.
Require Import QueueInitGen.
Require Import QueueInitGenSpec.
Require Import QueueInitGenLinkSource.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Notation HDATA := AbstractDataType.RData.
  Notation LDATA := AbstractDataType.RData.

  Notation HDATAOps := (cdata (cdata_ops := pqueueinit_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := pthreadinit_data_ops) LDATA).

  Definition oplus_monotonic := PseudoJoin.oplus_monotonic
    (A := compatlayer (cdata _ (cdata_ops := pthreadinit_data_ops))).
  Definition oplus_sim_monotonic := PseudoJoin.oplus_sim_monotonic.
  Definition right_upper_bound := Structures.right_upper_bound
    (A := compatlayer (cdata _ (cdata_ops := pthreadinit_data_ops))).
  Definition left_upper_bound := Structures.left_upper_bound
    (A := compatlayer (cdata _ (cdata_ops := pthreadinit_data_ops))).

  Let L1 := set_prev ↦ gensem set_prev_spec
         ⊕ set_next ↦ gensem set_next_spec
         ⊕ get_head ↦ gensem get_head_spec
         ⊕ get_tail ↦ gensem get_tail_spec
         ⊕ get_prev ↦ gensem get_prev_spec
         ⊕ get_next ↦ gensem get_next_spec
         ⊕ set_head ↦ gensem set_head_spec
         ⊕ set_tail ↦ gensem set_tail_spec.
  Lemma L1_le: L1 ≤ pqueueintro.
  Proof.
    sim_oplus.
  Qed.

  Let L2 : compatlayer LDATAOps :=
      thread_init ↦ gensem thread_init_spec
    ⊕ tdq_init ↦ gensem tdq_init_spec.
  Lemma L2_le: L2 ≤ pqueueintro.
  Proof.
    sim_oplus.
  Qed.

  Lemma enqueue_correct :
    forall COMPILABLE: LayerCompilable (pqueueintro ⊕ L64),
    forall MOK: ModuleOK (enqueue ↦ f_enqueue),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (enqueue ↦ f_enqueue) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (enqueue ↦ gensem enqueue_spec)
             (〚 M2 〛(pqueueintro ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply enqueue_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PQUEUEINTROCODE.enqueue_code_correct.
    - transitivity L1; [| apply L1_le ].
      unfold L1.
      apply oplus_monotonic; [ reflexivity |].
      apply oplus_monotonic; [ reflexivity |].
      apply le_right.
      apply oplus_monotonic; [ reflexivity |].
      apply le_right.
      apply le_right.
      reflexivity.
  Qed.

  Lemma dequeue_correct :
    forall COMPILABLE: LayerCompilable (pqueueintro ⊕ L64),
    forall MOK: ModuleOK (dequeue ↦ f_dequeue),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (dequeue ↦ f_dequeue) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (dequeue ↦ gensem dequeue_spec)
             (〚 M2 〛(pqueueintro ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply dequeue_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PQUEUEINTROCODE.dequeue_code_correct.
    - transitivity L1; [| apply L1_le ].
      unfold L1.
      apply oplus_monotonic; [ reflexivity |].
      apply le_right.
      apply oplus_monotonic; [ reflexivity |].
      apply le_right.
      apply le_right.
      reflexivity.
  Qed.

  Lemma queue_rmv_correct :
    forall COMPILABLE: LayerCompilable (pqueueintro ⊕ L64),
    forall MOK: ModuleOK (queue_rmv ↦ f_queue_rmv),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (queue_rmv ↦ f_queue_rmv) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (queue_rmv ↦ gensem queue_rmv_spec)
             (〚 M2 〛(pqueueintro ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply queue_rmv_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PQUEUEINTROCODE.queue_rmv_code_correct.
    - transitivity L1; [| apply L1_le ].
      unfold L1.
      apply oplus_monotonic; [ reflexivity |].
      apply oplus_monotonic; [ reflexivity |].
      apply le_right.
      apply le_right.
      reflexivity.
  Qed.

  Lemma tdqueue_init_correct :
    forall COMPILABLE: LayerCompilable (pqueueintro ⊕ L64),
    forall MOK: ModuleOK (tdqueue_init ↦ f_tdqueue_init),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (tdqueue_init ↦ f_tdqueue_init) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (tdqueue_init ↦ gensem tdqueue_init_spec)
             (〚 M2 〛(pqueueintro ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply tdqueue_init_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PQUEUEINTROCODE.tdqueue_init_code_correct.
    - apply L2_le.
  Qed.

  Record PQueueInit_impl_inverted (M: module): Prop :=
    {
      PQueueInit_enqueue: module;
      PQueueInit_dequeue: module;
      PQueueInit_queue_rmv: module;
      PQueueInit_tdqueue_init: module;
      PQueueInit_enqueue_transf:
        CompCertiKOS.transf_module (enqueue ↦ f_enqueue) =
        ret PQueueInit_enqueue;
      PQueueInit_dequeue_transf:
        CompCertiKOS.transf_module (dequeue ↦ f_dequeue) =
        ret PQueueInit_dequeue;
      PQueueInit_queue_rmv_transf:
        CompCertiKOS.transf_module (queue_rmv ↦ f_queue_rmv) =
        ret PQueueInit_queue_rmv;
      PQueueInit_tdqueue_init_transf:
        CompCertiKOS.transf_module (tdqueue_init ↦ f_tdqueue_init) =
        ret PQueueInit_tdqueue_init;
      PQueueInit_M:
        M = (PQueueInit_enqueue ⊕ PQueueInit_dequeue ⊕
             PQueueInit_queue_rmv ⊕ PQueueInit_tdqueue_init) ⊕ ∅;
      PQueueInit_OK:
        LayerOK (〚M 〛 (pqueueintro ⊕ L64) ⊕ pqueueintro ⊕ L64)
    }.

  Lemma module_impl_imply:
    forall M, PQueueInit_impl = OK M -> PQueueInit_impl_inverted M.
  Proof.
    unfold PQueueInit_impl. intros M HM.
    inv_monad' HM.
    econstructor.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    inv HM4. reflexivity.
    apply x4.
  Qed.
  
  Lemma link_correct_aux:
    forall M, PQueueInit_impl = OK M ->
              pqueueintro ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), M)
              : pqueueinit ⊕ L64.
  Proof.
    unfold PQueueInit_impl. intros M HM.
    apply module_impl_imply in HM; destruct HM; subst.
    unfold pqueueinit, pqueueinit_fresh.
    eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      layer_link_split_tac.
      - apply enqueue_correct; code_correct_tac.
      - apply dequeue_correct; code_correct_tac.
      - apply queue_rmv_correct; code_correct_tac.
      - apply tdqueue_init_correct; code_correct_tac.
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
    forall M, PQueueInit_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA) (pqueueinit ⊕ L64) M (pqueueintro ⊕ L64).
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
    - intros. unfold PQueueInit_impl in H.
      apply module_impl_imply in H; destruct H; subst.
      transf_none i. specialize (MOK i).
      assert (get_module_variable i
                ((PQueueInit_enqueue ⊕ PQueueInit_dequeue ⊕
                  PQueueInit_queue_rmv ⊕ PQueueInit_tdqueue_init) ⊕ ∅) = OK None).
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
      PQueueInit_impl = OK M ->
      make_program s CTXT (pqueueinit ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pqueueintro ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (pqueueinit ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pqueueintro ⊕ L64)) pl)
        (observe_lasm _ p) (observe_lasm _ p).
  Proof.
    intros.
    eapply (soundness_simulation (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    eapply module_impl_imply in H.
    destruct H. assumption.
  Qed.

  Theorem cl_forward_simulation:
    forall (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      PQueueInit_impl = OK M ->
      make_program s CTXT (pqueueinit ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pqueueintro ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (pqueueinit ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pqueueintro ⊕ L64)) pl).
  Proof.
    intros.
    eapply (soundness_forward (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    eapply module_impl_imply in H.
    destruct H. assumption.
  Qed.

  Theorem cl_backward_simulation:
    forall (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      PQueueInit_impl = OK M ->
      make_program s CTXT (pqueueinit ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pqueueintro ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (pqueueinit ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pqueueintro ⊕ L64)) pl).
  Proof.
    intros.
    eapply (soundness (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    eapply module_impl_imply in H.
    destruct H. assumption.
  Qed.

  Require Import LAsmModuleSemMakeProgram.

  Theorem make_program_exists:
    forall (s: stencil) (CTXT M: module) pl,
      PQueueInit_impl = OK M ->
      make_program s (CTXT ⊕ M) (pqueueintro ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (pqueueinit ⊕ L64) = OK ph.
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
    apply module_impl_imply in H; destruct H; subst.
    eassumption.
  Qed.

End WITHCOMPCERTIKOS.
