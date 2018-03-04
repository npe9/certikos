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
Require Import PCurID.
Require Import PThreadSched.
Require Import PCurIDCSource.
Require Import PCurIDCode.
Require Import ThreadSchedGen.
Require Import ThreadSchedGenSpec.
Require Import ThreadSchedGenLinkSource.
Require Import ThreadSchedGenAsmSource.
Require Import ThreadSchedGenAsm.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.
  
  Notation HDATA := AbstractDataType.RData.
  Notation LDATA := AbstractDataType.RData.

  Notation HDATAOps := (cdata (cdata_ops := pthreadsched_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := pcurid_data_ops) LDATA).

  Definition oplus_monotonic := PseudoJoin.oplus_monotonic
    (A := compatlayer (cdata _ (cdata_ops := pcurid_data_ops))).
  Definition oplus_sim_monotonic := PseudoJoin.oplus_sim_monotonic.
  Definition right_upper_bound := Structures.right_upper_bound
    (A := compatlayer (cdata _ (cdata_ops := pcurid_data_ops))).
  Definition left_upper_bound := Structures.left_upper_bound
    (A := compatlayer (cdata _ (cdata_ops := pcurid_data_ops))).

  (*
  Lemma thread_kill_correct :
    forall COMPILABLE: LayerCompilable (pcurid ⊕ L64),
    forall MOK: ModuleOK (thread_kill ↦ f_thread_kill),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (thread_kill ↦ f_thread_kill) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (thread_kill ↦ gensem thread_kill_spec)
             (〚 M2 〛(pcurid ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply thread_kill_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PCURIDCODE.thread_kill_code_correct.
    - transitivity pcurid_impl; [| apply impl_le ].
      apply le_right, le_right, le_right.
      apply oplus_monotonic; [ reflexivity |].
      apply oplus_monotonic; [ reflexivity |].
      apply le_right, le_right.
      reflexivity.
  Qed.
  *)

  Lemma thread_spawn_correct :
    forall COMPILABLE: LayerCompilable (pcurid ⊕ L64),
    forall MOK: ModuleOK (thread_spawn ↦ f_thread_spawn),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (thread_spawn ↦ f_thread_spawn) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (thread_spawn ↦ dnew_compatsem thread_spawn_spec)
             (〚 M2 〛(pcurid ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply thread_spawn_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PCURIDCODE.thread_spawn_code_correct.
    - sim_oplus.
  Qed.

  Lemma thread_wakeup_correct :
    forall COMPILABLE: LayerCompilable (pcurid ⊕ L64),
    forall MOK: ModuleOK (thread_wakeup ↦ f_thread_wakeup),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (thread_wakeup ↦ f_thread_wakeup) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (thread_wakeup ↦ gensem thread_wakeup_spec)
             (〚 M2 〛(pcurid ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply thread_wakeup_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PCURIDCODE.thread_wakeup_code_correct.
    - sim_oplus.
  Qed.

  Lemma sched_init_correct :
    forall COMPILABLE: LayerCompilable (pcurid ⊕ L64),
    forall MOK: ModuleOK (sched_init ↦ f_sched_init),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (sched_init ↦ f_sched_init) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (sched_init ↦ gensem sched_init_spec)
             (〚 M2 〛(pcurid ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply sched_init_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PCURIDCODE.sched_init_code_correct.
    - sim_oplus.
  Qed.

  Lemma thread_sched_correct:
      cl_sim _ _
             (crel HDATA LDATA)
             (thread_sched ↦ primcall_thread_schedule_compatsem thread_sched_spec (prim_ident:= thread_sched))
             (〚 thread_sched ↦ threadsched_function 〛 pcurid).
  Proof.
    intros.
    eapply link_assembly; eauto.
    - eapply thread_sched_spec_ref.
    - eapply thread_sched_code_correct.
  Qed.

  Record PThreadSched_impl_inverted (M: module): Prop :=
    {
      (*
      PThreadSched_thread_kill: module;
      *)
      PThreadSched_thread_spawn: module;
      PThreadSched_thread_wakeup: module;
      PThreadSched_sched_init: module;
      (*
      PThreadSched_thread_kill_transf:
        CompCertiKOS.transf_module (thread_kill ↦ f_thread_kill) =
        ret PThreadSched_thread_kill;
      *)
      PThreadSched_thread_spawn_transf:
        CompCertiKOS.transf_module (thread_spawn ↦ f_thread_spawn) =
        ret PThreadSched_thread_spawn;
      PThreadSched_thread_wakeup_transf:
        CompCertiKOS.transf_module (thread_wakeup ↦ f_thread_wakeup) =
        ret PThreadSched_thread_wakeup;
      PThreadSched_sched_init_transf:
        CompCertiKOS.transf_module (sched_init ↦ f_sched_init) =
        ret PThreadSched_sched_init;
      PThreadSched_M:
        M = (((*PThreadSched_thread_kill ⊕*) PThreadSched_thread_spawn ⊕ PThreadSched_thread_wakeup ⊕ PThreadSched_sched_init)
               ⊕ (thread_sched ↦ threadsched_function)) ⊕ ∅;
      PThreadSched_MOK:
        LayerOK (〚M〛 (pcurid ⊕ L64) ⊕ pcurid ⊕ L64)
    }.

  Lemma module_impl_imply:
    forall M, PThreadSched_impl = OK M -> PThreadSched_impl_inverted M.
  Proof.
    unfold PThreadSched_impl. intros M HM.
    inv_monad' HM.
    econstructor.
    (*
    eassumption.
    *)
    eassumption.
    eassumption.
    eassumption.
    inv HM3. reflexivity.
    apply x3.
  Qed.

  Lemma link_correct_aux:
    forall M, PThreadSched_impl = OK M ->
              pcurid ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), M)
              : pthreadsched ⊕ L64.
  Proof.
    unfold PThreadSched_impl. intros M HM.
    apply module_impl_imply in HM; destruct HM; subst.
    unfold pthreadsched, pthreadsched_fresh_c, pthreadsched_fresh_asm.
    eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      hcomp_tac.
      {
        layer_link_split_tac.
        (*
        - apply thread_kill_correct; code_correct_tac.
        *)
        - apply thread_spawn_correct; code_correct_tac.
        - apply thread_wakeup_correct; code_correct_tac.
        - apply sched_init_correct; code_correct_tac.
      }
      {
        apply Language.conseq_le_left with pcurid; [| apply left_upper_bound ].
        layer_link_split_tac; apply thread_sched_correct.
      }
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
    forall M, PThreadSched_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA) (pthreadsched ⊕ L64) M (pcurid ⊕ L64).
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
    - intros. unfold PThreadSched_impl in H.
      apply module_impl_imply in H; destruct H; subst.
      transf_none i. specialize (MOK i).
      assert (get_module_variable i ((((*PThreadSched_thread_kill ⊕*) PThreadSched_thread_spawn ⊕ PThreadSched_thread_wakeup ⊕ PThreadSched_sched_init) ⊕ thread_sched ↦ threadsched_function) ⊕ ∅) = OK None).
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
      PThreadSched_impl = OK M ->
      make_program s CTXT (pthreadsched ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pcurid ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (pthreadsched ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pcurid ⊕ L64)) pl)
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
      PThreadSched_impl = OK M ->
      make_program s CTXT (pthreadsched ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pcurid ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (pthreadsched ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pcurid ⊕ L64)) pl).
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
      PThreadSched_impl = OK M ->
      make_program s CTXT (pthreadsched ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pcurid ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (pthreadsched ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pcurid ⊕ L64)) pl).
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
      PThreadSched_impl = OK M ->
      make_program s (CTXT ⊕ M) (pcurid ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (pthreadsched ⊕ L64) = OK ph.
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
