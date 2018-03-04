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
Require Import PThreadSched.
Require Import PThread.
Require Import ThreadGen.
Require Import ThreadGenSpec.
Require Import ThreadGenLinkSource.
Require Import ThreadGenAsmSource.
Require Import ThreadGenAsm.
Require Import ThreadGenAsm1.
Require Import ObjThread.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.
  
  Notation HDATA := AbstractDataType.RData.
  Notation LDATA := AbstractDataType.RData.

  Notation HDATAOps := (cdata (cdata_ops := pthread_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := pthreadsched_data_ops) LDATA).

  Lemma thread_yield_correct:
      cl_sim _ _
             (crel HDATA LDATA)
             (thread_yield ↦ primcall_thread_schedule_compatsem thread_yield_spec (prim_ident:= thread_yield))
             (〚 thread_yield ↦ threadyield_function 〛 pthreadsched).
  Proof.
    intros.
    eapply link_assembly; eauto.
    - eapply thread_yield_spec_ref.
    - eapply thread_yield_code_correct.
  Qed.

  Lemma thread_sleep_correct:
      cl_sim _ _
             (crel HDATA LDATA)
             (thread_sleep ↦ primcall_thread_transfer_compatsem thread_sleep_spec)
             (〚 thread_sleep ↦ threadsleep_function 〛 pthreadsched).
  Proof.
    intros.
    eapply link_assembly; eauto.
    - eapply thread_sleep_spec_ref.
    - eapply thread_sleep_code_correct.
  Qed.

  Lemma link_correct_aux:
    forall M, PThread_impl = OK M ->
              pthreadsched ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), M)
              : pthread ⊕ L64.
  Proof.
    unfold PThread_impl. intros M HM.
    inv_monad' HM. subst.
    unfold pthread, pthread_fresh.
    eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      apply Language.conseq_le_left with pthreadsched; [| apply left_upper_bound ].
      layer_link_split_tac.
      - apply thread_yield_correct.
      - apply thread_sleep_correct.
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
    forall M, PThread_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA) (pthread ⊕ L64) M (pthreadsched ⊕ L64).
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
    - intros. unfold PThread_impl in H.
      Local Opaque oplus.
      inv_monad' H.
      transf_none i. specialize (MOK i).
      assert (get_module_variable i
                                  ((thread_yield ↦ threadyield_function
                                                 ⊕ thread_sleep ↦ threadsleep_function) ⊕ ∅) = OK None).
      {
        get_module_variable_relfexivity.
      }
      unfold module, module_ops in *.
      simpl in H.
      congruence.
    - decision.
  Qed.

  Theorem cl_simulation:
    forall p (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      PThread_impl = OK M ->
      make_program s CTXT (pthread ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pthreadsched ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (pthread ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pthreadsched ⊕ L64)) pl)
        (observe_lasm _ p) (observe_lasm _ p).
  Proof.
    intros.
    eapply (soundness_simulation (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    intros. unfold PThread_impl in H.
    inv_monad' H.
    decision.
  Qed.

  Theorem cl_forward_simulation:
    forall (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      PThread_impl = OK M ->
      make_program s CTXT (pthread ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pthreadsched ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (pthread ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pthreadsched ⊕ L64)) pl).
  Proof.
    intros.
    eapply (soundness_forward (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    intros. unfold PThread_impl in H.
    inv_monad' H.
    decision.
  Qed.

  Theorem cl_backward_simulation:
    forall (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      PThread_impl = OK M ->
      make_program s CTXT (pthread ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pthreadsched ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (pthread ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pthreadsched ⊕ L64)) pl).
  Proof.
    intros.
    eapply (soundness (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    intros. unfold PThread_impl in H.
    inv_monad' H.
    decision.
  Qed.

  Require Import LAsmModuleSemMakeProgram.

  Theorem make_program_exists:
    forall (s: stencil) (CTXT M: module) pl,
      PThread_impl = OK M ->
      make_program s (CTXT ⊕ M) (pthreadsched ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (pthread ⊕ L64) = OK ph.
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

    intros. unfold PThread_impl in H.
    inv_monad' H.
    decision.
  Qed.

End WITHCOMPCERTIKOS.
