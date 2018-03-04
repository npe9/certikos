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

Require Import MALT.
Require Import MALOp.
Require Import MALInit.
Require Import MALOpCode.
Require Import ALGen.
Require Import ALGenSpec.
Require Import MALOpCSource.
Require Import ALGenLinkSource.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.
  Context `{real_params_prf : RealParams}.

  Notation HDATA := AbstractDataType.RData.
  Notation LDATA := AbstractDataType.RData.

  Notation HDATAOps := (cdata (cdata_ops := malt_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := malop_data_ops) LDATA).
  
  Lemma pfree_correct:
    forall COMPILABLE: LayerCompilable (malop ⊕ L64),
    forall MOK: ModuleOK (pfree ↦ f_pfree),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (pfree ↦ f_pfree) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (pfree ↦ gensem pfree'_spec)
             (〚 M2 〛(malop ⊕ L64)).
  Proof. 
    intros.
    eapply link_compiler; eauto.
    - eapply pfree_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MALOPCODE.pfree_code_correct.
    - le_oplus.
  Qed.

  Lemma palloc_correct:
    forall COMPILABLE: LayerCompilable (malop ⊕ L64),
    forall MOK: ModuleOK (palloc ↦ f_palloc),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (palloc ↦ f_palloc) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (palloc ↦ gensem palloc'_spec)
             (〚 M2 〛(malop ⊕ L64)).
  Proof. 
    intros.
    eapply link_compiler; eauto.
    - eapply palloc_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MALOPCODE.palloc_code_correct.
    - le_oplus.
  Qed.

  (** XXX: added **)
  Record MALT_impl_inverted (M: module) : Prop:=
    {
      MALT_palloc: module;
      MALT_pfree: module;
      MALT_palloc_transf: CompCertiKOS.transf_module (palloc ↦ f_palloc) = ret MALT_palloc;
      MALT_pfree_transf: CompCertiKOS.transf_module (pfree ↦ f_pfree) = ret MALT_pfree;
      MALT_M: M = ((MALT_palloc ⊕ MALT_pfree) ⊕ ∅);
      MALT_Mok: LayerOK (〚M 〛 (malop ⊕ L64) ⊕ malop ⊕ L64)
    }.

  (** XXX: added **)
  Lemma module_impl_imply:
    forall M, MALT_impl = OK M -> MALT_impl_inverted M.
  Proof.
    unfold MALT_impl. intros M HM.
    inv_monad' HM.
    econstructor.
    eassumption.
    eassumption.
    inv HM2. reflexivity.
    apply x2.
  Qed.

  Lemma link_correct_aux:
    forall M, MALT_impl = OK M ->
              malop ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), M)
              : malt ⊕ L64.
  Proof.
    (** XXX: added **)
    intros M HM.
    eapply module_impl_imply in HM; destruct HM; subst.

    eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      hcomp_tac.
      {
        layer_link_split_tac.
        apply palloc_correct; code_correct_tac.
      }
      {
        layer_link_split_tac.
        apply pfree_correct; code_correct_tac.
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
Require Import Behavior.

  Lemma init_correct:
    forall M, MALT_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA) (malt ⊕ L64) M (malop ⊕ L64).
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
      assert (get_module_variable i ((MALT_palloc ⊕ MALT_pfree) ⊕ ∅) = OK None).
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
      MALT_impl = OK M ->
      make_program s CTXT (malt ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (malop ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (malt ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (malop ⊕ L64)) pl)
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
      MALT_impl = OK M ->
      make_program s CTXT (malt ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (malop ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (malt ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (malop ⊕ L64)) pl).
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
      MALT_impl = OK M ->
      make_program s CTXT (malt ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (malop ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (malt ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (malop ⊕ L64)) pl).
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
      MALT_impl = OK M ->
      make_program s (CTXT ⊕ M) (malop ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (malt ⊕ L64) = OK ph.
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
