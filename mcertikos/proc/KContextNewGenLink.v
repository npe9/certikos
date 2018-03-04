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
Require Import PKContext.
Require Import PKContextNew.
Require Import PKContextCSource.
Require Import PKContextCode.
Require Import KContextNewGen.
Require Import KContextNewGenSpec.
Require Import KContextNewGenLinkSource.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Notation HDATA := AbstractDataType.RData.
  Notation LDATA := AbstractDataType.RData.

  Notation HDATAOps := (cdata HDATA).
  Notation LDATAOps := (cdata LDATA).

  Lemma usage_le:
       pt_new ↦ gensem pt_new_spec
    ⊕ set_RA ↦ kctxt_ra_compatsem
    ⊕ set_SP ↦ kctxt_sp_compatsem
    ≤ pkcontext.
  Proof.
    le_oplus.
  Qed.

  Lemma kctxt_new_correct :
    forall COMPILABLE: LayerCompilable (pkcontext ⊕ L64),
    forall MOK: ModuleOK (kctxt_new ↦ f_kctxt_new),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (kctxt_new ↦ f_kctxt_new) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (kctxt_new ↦ dnew_compatsem ObjThread.kctxt_new_spec)
             (〚 M2 〛(pkcontext ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply kctxt_new_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PKCONTEXTCODE.kctxt_new_code_correct.
    - apply usage_le.
  Qed.

  (** XXX: added **)
  Record PKCONTEXTNEW_impl_inverted (M: module) : Prop:=
    {
      PKCONTEXTNEW_kctxt_new: module;
      PKCONTEXTNEW_kctxt_new_transf: CompCertiKOS.transf_module (kctxt_new ↦ f_kctxt_new) = ret PKCONTEXTNEW_kctxt_new;
      PKCONTEXTNEW_M: M = (PKCONTEXTNEW_kctxt_new ⊕ ∅);
      PKCONTEXTNEW_Mok: LayerOK (〚M 〛 (pkcontext ⊕ L64) ⊕ pkcontext ⊕ L64)
    }.

  (** XXX: added **)
  Lemma module_impl_imply:
    forall M, PKContextNew_impl = OK M -> PKCONTEXTNEW_impl_inverted M.
  Proof.
    unfold PKContextNew_impl. intros M HM.
    inv_monad' HM.
    econstructor.
    eassumption.
    inv HM1. reflexivity.
    apply x1.
  Qed.

  Lemma link_correct_aux:
    forall M, PKContextNew_impl = OK M ->
              pkcontext ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), M)
              : pkcontextnew ⊕ L64.
  Proof.
    (** XXX: added **)
    intros M HM.
    eapply module_impl_imply in HM; destruct HM; subst.

    unfold pkcontextnew, pkcontextnew_fresh.
    eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      layer_link_split_tac.
      apply kctxt_new_correct; code_correct_tac.
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
    forall M, PKContextNew_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA) (pkcontextnew ⊕ L64) M (pkcontext ⊕ L64).
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
      (** XXX: added **)
      eapply module_impl_imply in H; destruct H; subst.
      transf_none i. specialize (MOK i).

      assert (get_module_variable i (PKCONTEXTNEW_kctxt_new ⊕ ∅) = OK None).
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
      PKContextNew_impl = OK M ->
      make_program s CTXT (pkcontextnew ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pkcontext ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (pkcontextnew ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pkcontext ⊕ L64)) pl)
        (observe_lasm _ p) (observe_lasm _ p).
  Proof.
    intros.
    eapply (soundness_simulation (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    (** XXX: added **)
    eapply module_impl_imply in H.
    destruct H. assumption.
  Qed.

  Theorem cl_forward_simulation:
    forall (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      PKContextNew_impl = OK M ->
      make_program s CTXT (pkcontextnew ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pkcontext ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (pkcontextnew ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pkcontext ⊕ L64)) pl).
  Proof.
    intros.
    eapply (soundness_forward (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    (** XXX: added **)
    eapply module_impl_imply in H.
    destruct H. assumption.
  Qed.

  Theorem cl_backward_simulation:
    forall (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      PKContextNew_impl = OK M ->
      make_program s CTXT (pkcontextnew ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pkcontext ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (pkcontextnew ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pkcontext ⊕ L64)) pl).
  Proof.
    intros.
    eapply (soundness (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    (** XXX: added **)
    eapply module_impl_imply in H.
    destruct H. assumption.
  Qed.

  Require Import LAsmModuleSemMakeProgram.

  Theorem make_program_exists:
    forall (s: stencil) (CTXT M: module) pl,
      PKContextNew_impl = OK M ->
      make_program s (CTXT ⊕ M) (pkcontext ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (pkcontextnew ⊕ L64) = OK ph.
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
    (** XXX: added **)
    eapply module_impl_imply in H.
    destruct H. assumption.
  Qed.

End WITHCOMPCERTIKOS.
