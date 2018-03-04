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
Require Import PQueueInit.
Require Import PAbQueue.
Require Import AbQueueGen.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Notation HDATA := AbstractDataType.RData.
  Notation LDATA := AbstractDataType.RData.

  Notation HDATAOps := (cdata (cdata_ops := pabqueue_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := pqueueinit_data_ops) LDATA).

  Lemma link_correct_aux:
              pqueueinit ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), ∅)
              : pabqueue ⊕ L64.
  Proof.
    eapply layer_link_new_glbl_both.
    apply oplus_sim_monotonic.
    apply passthrough_correct.
    apply L64_auto_sim.
  Qed.

  Require Import FlatMemory.
  Require Import Decision.
  Require Import LAsmModuleSem.
  Require Import Soundness.
  Require Import CompatExternalCalls.
  Require Import AuxLemma.
  Require Import Behavior.

  Lemma init_correct:
    cl_init_sim (mops := module_ops)
                HDATAOps LDATAOps (crel HDATA LDATA)
                (pabqueue ⊕ L64) ∅ (pqueueinit ⊕ L64).
  Proof.
    apply cl_init_sim_intro.
    - constructor; simpl; trivial.
      constructor; simpl; trivial. apply FlatMem.flatmem_empty_inj.
      + apply kctxt_inj_empty.
      + (* AbQ_RealQ *)
        constructor.
        * (* abqueue_match_dllist *)
          intros qi l qi_range.
          rewrite ZMap.gi.
          discriminate.
        * (* abtcbpool_tcbpool *)
          intros i tds inq i_range.
          rewrite ZMap.gi.
          discriminate.
      + constructor.
    - intros _ [].
    - intros _ [].
    - intros _ [].
    - intros.
      assert (get_module_variable (ModuleOps := module_ops) i ∅ = OK None)
        by get_module_variable_relfexivity.
      congruence.
    - decision.
  Qed.

  Theorem cl_simulation:
    forall p (s: stencil) (CTXT : module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      make_program s CTXT (pabqueue ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ ∅) (pqueueinit ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (pabqueue ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pqueueinit ⊕ L64)) pl)
        (observe_lasm _ p) (observe_lasm _ p).
  Proof.
    intros.
    eapply (soundness_simulation (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
  Qed.

  Theorem cl_forward_simulation:
    forall (s: stencil) (CTXT : module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      make_program s CTXT (pabqueue ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ ∅) (pqueueinit ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (pabqueue ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pqueueinit ⊕ L64)) pl).
  Proof.
    intros.
    eapply (soundness_forward (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
  Qed.

  Theorem cl_backward_simulation:
    forall (s: stencil) (CTXT : module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      make_program s CTXT (pabqueue ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ ∅) (pqueueinit ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (pabqueue ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pqueueinit ⊕ L64)) pl).
  Proof.
    intros.
    eapply (soundness (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
  Qed.

  Require Import LAsmModuleSemMakeProgram.

  Theorem make_program_exists:
    forall (s: stencil) (CTXT : module) pl,
      make_program s (CTXT ⊕ ∅) (pqueueinit ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (pabqueue ⊕ L64) = OK ph.
  Proof.
    intros.
    eapply make_program_vertical' in H.
    destruct H as [p' Hmake].
    assert (Hle := link_correct_aux).
    eapply make_program_sim_monotonic_exists.
    2: eapply Hle.
    reflexivity.
    eassumption.

    decision.
  Qed.

End WITHCOMPCERTIKOS.
