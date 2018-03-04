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
Require Import MPTIntro.
Require Import MPTOp.
Require Import MPTIntroCode.
Require Import PTOpGen.
Require Import PTOpGenSpec.
Require Import MPTIntroCSource.
Require Import LinkTemplate.
Require Import LinkTactic.
Require Import PTOpGenLinkSource.

Section WITHCOMPCERTIKOS.
  Context `{compcertikos_prf: CompCertiKOS}.
  Context `{real_params_prf : RealParams}.
  
  Notation HDATA := AbstractDataType.RData.
  Notation LDATA := AbstractDataType.RData.

  Notation HDATAOps := (cdata HDATA).
  Notation LDATAOps := (cdata LDATA).

  Require Import Coqlib.
  Require Import FlatMemory.
  Require Import Decision.
  Require Import LAsmModuleSem.
  Require Import Soundness.
  Require Import CompatExternalCalls.
  Require Import Behavior.

  Lemma init_correct:
    forall M, MPTOp_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA) (mptop ⊕ L64) M (mptintro ⊕ L64).
  Proof.
    intros.
    pose proof (fun i => module_ok_variable M i (H0 i)) as MOK; clear H0.
    apply cl_init_sim_intro.
    - constructor; simpl; trivial.
      constructor; simpl; trivial. apply FlatMem.flatmem_empty_inj.
      constructor.
    - intros; inv H0.
    - intros; inv H0.
    - intros; inv H0.
    - intros. 
      inv_link_impl H; subst.
      transf_none i. specialize (MOK i).
      assert (get_module_variable i (((M6 ⊕ M5 ⊕ M4 ⊕ M3 ⊕ M2 ⊕ M1 ⊕ M0 ⊕ ∅) ⊕ ∅) ⊕ ∅) = OK None).
      {
        get_module_variable_relfexivity.
      }
      congruence.
    - decision.
  Qed.

  Lemma link_correct_aux:
    forall M, MPTOp_impl = OK M ->
              mptintro ⊕ L64
                    ⊢ (path_inj (crel _ _), M)
              : mptop ⊕ L64.
  Proof.
    link_correct_aux.
    - link_cfunction ptRead_spec_ref MPTINTROCODE.pt_read_code_correct.
    - link_cfunction ptReadPDE_spec_ref MPTINTROCODE.pt_read_pde_code_correct.
    - link_cfunction ptInsertAux_spec_ref MPTINTROCODE.pt_insert_aux_code_correct.
    - link_cfunction ptInsertPDE_spec_ref MPTINTROCODE.pt_insert_pde_code_correct.
    - link_cfunction ptRmvAux_spec_ref MPTINTROCODE.pt_rmv_aux_code_correct.
    - link_cfunction ptRmvPDE_spec_ref MPTINTROCODE.pt_rmv_pde_code_correct.
    - link_cfunction idpde_init_spec_ref MPTINTROCODE.idpde_init_code_correct.
    - apply passthrough_correct.
  Qed.

  Theorem cl_simulation:
    forall p (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      MPTOp_impl = OK M ->
      make_program s CTXT (mptop ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (mptintro ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (mptop ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (mptintro ⊕ L64)) pl)
        (observe_lasm _ p) (observe_lasm _ p).
  Proof.
    intros.
    eapply (soundness_simulation (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    inv_link_impl H; subst.
    assumption.
  Qed.

  Theorem cl_forward_simulation:
    forall (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      MPTOp_impl = OK M ->
      make_program s CTXT (mptop ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (mptintro ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (mptop ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (mptintro ⊕ L64)) pl).
  Proof.
    intros.
    eapply (soundness_forward (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    inv_link_impl H; subst.
    assumption.
  Qed.

  Theorem cl_backward_simulation:
    forall (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      MPTOp_impl = OK M ->
      make_program s CTXT (mptop ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (mptintro ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (mptop ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (mptintro ⊕ L64)) pl).
  Proof.
    intros.
    eapply (soundness (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.

    inv_link_impl H; subst.
    assumption.
  Qed.

  Require Import LAsmModuleSemMakeProgram.

  Theorem make_program_exists:
    forall (s: stencil) (CTXT M: module) pl,
      MPTOp_impl = OK M ->
      make_program s (CTXT ⊕ M) (mptintro ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (mptop ⊕ L64) = OK ph.
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

    inv_link_impl H; subst.
    assumption.
  Qed.

End WITHCOMPCERTIKOS.
