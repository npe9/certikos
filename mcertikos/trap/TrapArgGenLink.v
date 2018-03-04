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
Require Import TTrapArg.
Require Import PProcCSource.
Require Import PProcCode.
Require Import TrapArgGen.
Require Import TrapArgGenSpec.
Require Import TrapArgGenLinkSource.
(*Require Import TrapArgGenAsmSource.*)
(*Require Import TrapArgGenAsm.*)
Require Import LayerCalculusLemma.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.
  
  Notation HDATA := AbstractDataType.RData.
  Notation LDATA := AbstractDataType.RData.

  Notation HDATAOps := (cdata (cdata_ops := pproc_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := pproc_data_ops) LDATA).

  Definition oplus_monotonic := PseudoJoin.oplus_monotonic
    (A := compatlayer (cdata _ (cdata_ops := pproc_data_ops))).
  Definition oplus_sim_monotonic := PseudoJoin.oplus_sim_monotonic.
  Definition right_upper_bound := Structures.right_upper_bound
    (A := compatlayer (cdata _ (cdata_ops := pproc_data_ops))).
  Definition left_upper_bound := Structures.left_upper_bound
    (A := compatlayer (cdata _ (cdata_ops := pproc_data_ops))).

  Let L2 := get_curid ↦ gensem get_curid_spec
         ⊕ uctx_get ↦ gensem uctx_get_spec.
  Let L3 := get_curid ↦ gensem get_curid_spec
         ⊕ uctx_set ↦ gensem uctx_set_spec.

  Lemma L2_le : L2 ≤ pproc.
  Proof.
    le_oplus.
  Qed.

  Lemma L3_le : L3 ≤ pproc.
  Proof.
    le_oplus.
  Qed.

  Lemma uctx_arg1_correct :
    forall COMPILABLE: LayerCompilable (pproc ⊕ L64),
    forall MOK: ModuleOK (uctx_arg1 ↦ f_uctx_arg1),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (uctx_arg1 ↦ f_uctx_arg1) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (uctx_arg1  ↦ gensem uctx_arg1_spec)
             (〚 M2 〛(pproc ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply uctx_arg1_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PPROCCODE.uctx_arg1_code_correct.
    - apply L2_le.
  Qed.

  Lemma uctx_arg2_correct :
    forall COMPILABLE: LayerCompilable (pproc ⊕ L64),
    forall MOK: ModuleOK (uctx_arg2 ↦ f_uctx_arg2),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (uctx_arg2 ↦ f_uctx_arg2) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (uctx_arg2  ↦ gensem uctx_arg2_spec)
             (〚 M2 〛(pproc ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply uctx_arg2_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PPROCCODE.uctx_arg2_code_correct.
    - apply L2_le.
  Qed.

  Lemma uctx_arg3_correct :
    forall COMPILABLE: LayerCompilable (pproc ⊕ L64),
    forall MOK: ModuleOK (uctx_arg3 ↦ f_uctx_arg3),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (uctx_arg3 ↦ f_uctx_arg3) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (uctx_arg3  ↦ gensem uctx_arg3_spec)
             (〚 M2 〛(pproc ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply uctx_arg3_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PPROCCODE.uctx_arg3_code_correct.
    - apply L2_le.
  Qed.

  Lemma uctx_arg4_correct :
    forall COMPILABLE: LayerCompilable (pproc ⊕ L64),
    forall MOK: ModuleOK (uctx_arg4 ↦ f_uctx_arg4),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (uctx_arg4 ↦ f_uctx_arg4) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (uctx_arg4  ↦ gensem uctx_arg4_spec)
             (〚 M2 〛(pproc ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply uctx_arg4_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PPROCCODE.uctx_arg4_code_correct.
    - apply L2_le.
  Qed.

  Lemma uctx_arg5_correct :
    forall COMPILABLE: LayerCompilable (pproc ⊕ L64),
    forall MOK: ModuleOK (uctx_arg5 ↦ f_uctx_arg5),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (uctx_arg5 ↦ f_uctx_arg5) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (uctx_arg5  ↦ gensem uctx_arg5_spec)
             (〚 M2 〛(pproc ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply uctx_arg5_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PPROCCODE.uctx_arg5_code_correct.
    - apply L2_le.
  Qed.

  Lemma uctx_arg6_correct :
    forall COMPILABLE: LayerCompilable (pproc ⊕ L64),
    forall MOK: ModuleOK (uctx_arg6 ↦ f_uctx_arg6),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (uctx_arg6 ↦ f_uctx_arg6) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (uctx_arg6  ↦ gensem uctx_arg6_spec)
             (〚 M2 〛(pproc ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply uctx_arg6_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PPROCCODE.uctx_arg6_code_correct.
    - apply L2_le.
  Qed.

  Lemma uctx_set_errno_correct :
    forall COMPILABLE: LayerCompilable (pproc ⊕ L64),
    forall MOK: ModuleOK (uctx_set_errno ↦ f_uctx_set_errno),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (uctx_set_errno ↦ f_uctx_set_errno) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (uctx_set_errno  ↦ gensem uctx_set_errno_spec)
             (〚 M2 〛(pproc ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply uctx_set_errno_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PPROCCODE.uctx_set_errno_code_correct.
    - apply L3_le.
  Qed.

  Lemma uctx_set_retval1_correct :
    forall COMPILABLE: LayerCompilable (pproc ⊕ L64),
    forall MOK: ModuleOK (uctx_set_retval1 ↦ f_uctx_set_retval1),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (uctx_set_retval1 ↦ f_uctx_set_retval1) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (uctx_set_retval1  ↦ gensem uctx_set_retval1_spec)
             (〚 M2 〛(pproc ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply uctx_set_retval1_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PPROCCODE.uctx_set_retval1_code_correct.
    - apply L3_le.
  Qed.

  Lemma uctx_set_retval2_correct :
    forall COMPILABLE: LayerCompilable (pproc ⊕ L64),
    forall MOK: ModuleOK (uctx_set_retval2 ↦ f_uctx_set_retval2),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (uctx_set_retval2 ↦ f_uctx_set_retval2) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (uctx_set_retval2  ↦ gensem uctx_set_retval2_spec)
             (〚 M2 〛(pproc ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply uctx_set_retval2_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PPROCCODE.uctx_set_retval2_code_correct.
    - apply L3_le.
  Qed.

  Lemma uctx_set_retval3_correct :
    forall COMPILABLE: LayerCompilable (pproc ⊕ L64),
    forall MOK: ModuleOK (uctx_set_retval3 ↦ f_uctx_set_retval3),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (uctx_set_retval3 ↦ f_uctx_set_retval3) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (uctx_set_retval3  ↦ gensem uctx_set_retval3_spec)
             (〚 M2 〛(pproc ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply uctx_set_retval3_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PPROCCODE.uctx_set_retval3_code_correct.
    - apply L3_le.
  Qed.

  Lemma uctx_set_retval4_correct :
    forall COMPILABLE: LayerCompilable (pproc ⊕ L64),
    forall MOK: ModuleOK (uctx_set_retval4 ↦ f_uctx_set_retval4),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (uctx_set_retval4 ↦ f_uctx_set_retval4) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (uctx_set_retval4  ↦ gensem uctx_set_retval4_spec)
             (〚 M2 〛(pproc ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply uctx_set_retval4_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PPROCCODE.uctx_set_retval4_code_correct.
    - apply L3_le.
  Qed.

  Record TTrapArg_impl_inverted (M: module) : Prop :=
    {
      TTrapArg_uctx_arg1 : module;
      TTrapArg_uctx_arg2 : module;
      TTrapArg_uctx_arg3 : module;
      TTrapArg_uctx_arg4 : module;
      TTrapArg_uctx_arg5 : module;
      TTrapArg_uctx_arg6 : module;
      TTrapArg_uctx_set_errno : module;
      TTrapArg_uctx_set_retval1 : module;
      TTrapArg_uctx_set_retval2 : module;
      TTrapArg_uctx_set_retval3 : module;
      TTrapArg_uctx_set_retval4 : module;
      TTrapArg_uctx_arg1_trans : CompCertiKOS.transf_module (uctx_arg1 ↦ f_uctx_arg1) = ret TTrapArg_uctx_arg1;
      TTrapArg_uctx_arg2_trans : CompCertiKOS.transf_module (uctx_arg2 ↦ f_uctx_arg2) = ret TTrapArg_uctx_arg2;
      TTrapArg_uctx_arg3_trans : CompCertiKOS.transf_module (uctx_arg3 ↦ f_uctx_arg3) = ret TTrapArg_uctx_arg3;
      TTrapArg_uctx_arg4_trans : CompCertiKOS.transf_module (uctx_arg4 ↦ f_uctx_arg4) = ret TTrapArg_uctx_arg4;
      TTrapArg_uctx_arg5_trans : CompCertiKOS.transf_module (uctx_arg5 ↦ f_uctx_arg5) = ret TTrapArg_uctx_arg5;
      TTrapArg_uctx_arg6_trans : CompCertiKOS.transf_module (uctx_arg6 ↦ f_uctx_arg6) = ret TTrapArg_uctx_arg6;
      TTrapArg_uctx_set_errno_trans : CompCertiKOS.transf_module (uctx_set_errno ↦ f_uctx_set_errno) = ret TTrapArg_uctx_set_errno;
      TTrapArg_uctx_set_retval1_trans : CompCertiKOS.transf_module (uctx_set_retval1 ↦ f_uctx_set_retval1) = ret TTrapArg_uctx_set_retval1;
      TTrapArg_uctx_set_retval2_trans : CompCertiKOS.transf_module (uctx_set_retval2 ↦ f_uctx_set_retval2) = ret TTrapArg_uctx_set_retval2;
      TTrapArg_uctx_set_retval3_trans : CompCertiKOS.transf_module (uctx_set_retval3 ↦ f_uctx_set_retval3) = ret TTrapArg_uctx_set_retval3;
      TTrapArg_uctx_set_retval4_trans : CompCertiKOS.transf_module (uctx_set_retval4 ↦ f_uctx_set_retval4) = ret TTrapArg_uctx_set_retval4;
      TTrapArg_M: M = (
        (
          TTrapArg_uctx_arg1 ⊕ TTrapArg_uctx_arg2 ⊕ TTrapArg_uctx_arg3 ⊕
          TTrapArg_uctx_arg4 ⊕ TTrapArg_uctx_arg5 ⊕ TTrapArg_uctx_arg6 ⊕
          TTrapArg_uctx_set_errno ⊕
          TTrapArg_uctx_set_retval1 ⊕
          TTrapArg_uctx_set_retval2 ⊕
          TTrapArg_uctx_set_retval3 ⊕
          TTrapArg_uctx_set_retval4
        ) ⊕ ∅);
      TTrapArg_Mok: LayerOK (〚M 〛 (pproc ⊕ L64) ⊕ pproc ⊕ L64)
    }.

  Lemma module_impl_imply:
    forall M, TTrapArg_impl = OK M -> TTrapArg_impl_inverted M.
  Proof.
    unfold TTrapArg_impl. intros M HM.
    inv_monad' HM.
    econstructor.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    inv HM11. reflexivity.
    apply x11.
  Qed.

  Lemma link_correct_aux:
    forall M, TTrapArg_impl = OK M ->
              pproc ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), M)
              : ttraparg ⊕ L64.
  Proof.
    unfold TTrapArg_impl. intros M HM.
    eapply module_impl_imply in HM; destruct HM; subst.

    unfold ttraparg, ttraparg_fresh.
    eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      layer_link_split_tac.
      - apply uctx_arg1_correct; code_correct_tac.
      - apply uctx_arg2_correct; code_correct_tac.
      - apply uctx_arg3_correct; code_correct_tac.
      - apply uctx_arg4_correct; code_correct_tac.
      - apply uctx_arg5_correct; code_correct_tac.
      - apply uctx_arg6_correct; code_correct_tac.
      - apply uctx_set_errno_correct; code_correct_tac.
      - apply uctx_set_retval1_correct; code_correct_tac.
      - apply uctx_set_retval2_correct; code_correct_tac.
      - apply uctx_set_retval3_correct; code_correct_tac.
      - apply uctx_set_retval4_correct; code_correct_tac.
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
    forall M, TTrapArg_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA) (ttraparg ⊕ L64) M (pproc ⊕ L64).
  Proof.
    intros.
    pose proof (fun i => module_ok_variable M i (H0 i)) as MOK; clear H0.
    apply cl_init_sim_intro.
    - constructor; simpl; trivial.
      constructor; simpl; trivial. apply FlatMem.flatmem_empty_inj.
      + apply kctxt_inj_empty.
      + apply uctxt_inj_empty.
      + constructor.
    - intros; inv H0.
    - intros; inv H0.
    - intros; inv H0.
    - intros.
      eapply module_impl_imply in H; destruct H; subst.

      transf_none i. specialize (MOK i).
      assert (get_module_variable i (
        (TTrapArg_uctx_arg1 ⊕ TTrapArg_uctx_arg2 ⊕ TTrapArg_uctx_arg3 ⊕
         TTrapArg_uctx_arg4 ⊕ TTrapArg_uctx_arg5 ⊕ TTrapArg_uctx_arg6 ⊕
         TTrapArg_uctx_set_errno ⊕
         TTrapArg_uctx_set_retval1 ⊕
         TTrapArg_uctx_set_retval2 ⊕
         TTrapArg_uctx_set_retval3 ⊕
         TTrapArg_uctx_set_retval4) ⊕ ∅) = OK None).
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
      TTrapArg_impl = OK M ->
      make_program s CTXT (ttraparg ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pproc ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (ttraparg ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pproc ⊕ L64)) pl)
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
      TTrapArg_impl = OK M ->
      make_program s CTXT (ttraparg ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pproc ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (ttraparg ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pproc ⊕ L64)) pl).
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
      TTrapArg_impl = OK M ->
      make_program s CTXT (ttraparg ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pproc ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (ttraparg ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pproc ⊕ L64)) pl).
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
      TTrapArg_impl = OK M ->
      make_program s (CTXT ⊕ M) (pproc ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (ttraparg ⊕ L64) = OK ph.
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
    eapply module_impl_imply in H.
    eapply TTrapArg_Mok; assumption.
  Qed.

End WITHCOMPCERTIKOS.
