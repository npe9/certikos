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
Require Import LinkTactic.
Require Import CompCertiKOSproof.
Require Import LayerCalculusLemma.

Require Import MPTInit.
Require Import MPTNew.
Require Import MPTInitCode.
Require Import PTNewGen.
Require Import PTNewGenSpec.
Require Import MPTInitCSource.
Require Import PTNewGenLinkSource.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.
  Context `{real_params_prf : RealParams}.

  Notation HDATA := AbstractDataType.RData.
  Notation LDATA := AbstractDataType.RData.

  Notation HDATAOps := (cdata (cdata_ops := mptinit_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := mptinit_data_ops) LDATA).

  Lemma pt_resv_correct:
    forall COMPILABLE: LayerCompilable (mptinit ⊕ L64),
    forall MOK: ModuleOK (pt_resv ↦ f_pt_resv),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (pt_resv ↦ f_pt_resv) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (pt_resv ↦ gensem ptResv_spec)
             (〚 M2 〛(mptinit ⊕ L64)).
  Proof. 
    intros.
    eapply link_compiler; eauto.
    - eapply ptResv_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MPTINITCODE.pt_resv_code_correct.
    - le_oplus.
  Qed.

  Lemma pt_resv2_correct:
    forall COMPILABLE: LayerCompilable (mptinit ⊕ L64),
    forall MOK: ModuleOK (pt_resv2 ↦ f_pt_resv2),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (pt_resv2 ↦ f_pt_resv2) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (pt_resv2 ↦ gensem ptResv2_spec)
             (〚 M2 〛(mptinit ⊕ L64)).
  Proof. 
    intros.
    eapply link_compiler; eauto.
    - eapply ptResv2_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MPTINITCODE.pt_resv2_code_correct.
    - le_oplus.
  Qed.

  Lemma pt_new_correct:
    forall COMPILABLE: LayerCompilable (mptinit ⊕ L64),
    forall MOK: ModuleOK (pt_new ↦ f_pt_new),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (pt_new ↦ f_pt_new) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (pt_new ↦ gensem pt_new_spec)
             (〚 M2 〛(mptinit ⊕ L64)).
  Proof. 
    intros.
    eapply link_compiler; eauto.
    - eapply pt_new_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MPTINITCODE.pt_new_code_correct.
    - le_oplus.
  Qed.

  (*
  Lemma pt_free_correct:
    forall COMPILABLE: LayerCompilable (mptinit ⊕ L64),
    forall MOK: ModuleOK (pt_free ↦ f_pt_free),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (pt_free ↦ f_pt_free) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (pt_free ↦ gensem pt_free_spec)
             (〚 M2 〛(mptinit ⊕ L64)).
  Proof. 
    intros.
    eapply link_compiler; eauto.
    - eapply pt_free_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MPTINITCODE.pt_free_code_correct.
    - le_oplus.
  Qed.
  *)

  Lemma pmap_init_correct:
    forall COMPILABLE: LayerCompilable (mptinit ⊕ L64),
    forall MOK: ModuleOK (pmap_init ↦ f_pmap_init),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (pmap_init ↦ f_pmap_init) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (pmap_init ↦ gensem pmap_init_spec)
             (〚 M2 〛(mptinit ⊕ L64)).
  Proof. 
    intros.
    eapply link_compiler; eauto.
    - eapply pmap_init_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MPTINITCODE.pmap_init_code_correct.
    - le_oplus.
  Qed.

  (** XXX: added **)
  Record MPTNEW_impl_inverted (M: module) : Prop:=
    {
      MPTNEW_pt_resv: module;
      MPTNEW_pt_resv2: module;
      MPTNEW_pt_new: module;
      (*
      MPTNEW_pt_free: module;
       *)
      MPTNEW_pmap_init: module;
      MPTNEW_pt_resv_transf: CompCertiKOS.transf_module (pt_resv ↦ f_pt_resv) = ret MPTNEW_pt_resv;
      MPTNEW_pt_resv2_transf: CompCertiKOS.transf_module (pt_resv2 ↦ f_pt_resv2) = ret MPTNEW_pt_resv2;
      MPTNEW_pt_new_transf: CompCertiKOS.transf_module (pt_new ↦ f_pt_new) = ret MPTNEW_pt_new;
      (*
      MPTNEW_pt_free_transf: CompCertiKOS.transf_module (pt_free ↦ f_pt_free) = ret MPTNEW_pt_free;
       *)
      MPTNEW_pmap_init_transf: CompCertiKOS.transf_module (pmap_init ↦ f_pmap_init) = ret MPTNEW_pmap_init;
      MPTNEW_M: M = ((MPTNEW_pt_resv ⊕ MPTNEW_pt_resv2 ⊕ MPTNEW_pt_new ⊕ (*MPTNEW_pt_free ⊕*) MPTNEW_pmap_init) ⊕ ∅);
      MPTNEW_Mok: LayerOK (〚M 〛 (mptinit ⊕ L64) ⊕ mptinit ⊕ L64)
    }.

  (** XXX: added **)
  Lemma module_impl_imply:
    forall M, MPTNew_impl = OK M -> MPTNEW_impl_inverted M.
  Proof.
    unfold MPTNew_impl. intros M HM.
    inv_monad' HM.
    econstructor.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    (*eassumption.*)
    inv HM4. reflexivity.
    apply x4.
  Qed.

  Lemma link_correct_aux:
    forall M, MPTNew_impl = OK M ->
              mptinit ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), M)
              : mptnew ⊕ L64.
  Proof.
    (** XXX: added **)
    intros M HM.
    eapply module_impl_imply in HM; destruct HM; subst.

    eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      unfold mptnew_fresh.
      layer_link_split_tac.
      - apply pt_resv_correct; code_correct_tac.
      - apply pt_resv2_correct; code_correct_tac.
      - apply pt_new_correct; code_correct_tac.
      (*
      - apply pt_free_correct; code_correct_tac.
       *)
      - apply pmap_init_correct; code_correct_tac.
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
  Require Import Behavior.

  Lemma init_correct:
    forall M, MPTNew_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA) (mptnew ⊕ L64) M (mptinit ⊕ L64).
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
      (** XXX: added **)
      eapply module_impl_imply in H; destruct H; subst.

      transf_none i. specialize (MOK i).
      assert (get_module_variable i ((MPTNEW_pt_resv ⊕ MPTNEW_pt_resv2 ⊕ MPTNEW_pt_new ⊕ (*MPTNEW_pt_free ⊕*) MPTNEW_pmap_init)⊕ ∅) = OK None).
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
      MPTNew_impl = OK M ->
      make_program s CTXT (mptnew ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (mptinit ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (mptnew ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (mptinit ⊕ L64)) pl)
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
      MPTNew_impl = OK M ->
      make_program s CTXT (mptnew ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (mptinit ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (mptnew ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (mptinit ⊕ L64)) pl).
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
      MPTNew_impl = OK M ->
      make_program s CTXT (mptnew ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (mptinit ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (mptnew ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (mptinit ⊕ L64)) pl).
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
      MPTNew_impl = OK M ->
      make_program s (CTXT ⊕ M) (mptinit ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (mptnew ⊕ L64) = OK ph.
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
