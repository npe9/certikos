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
Require Import PThreadInit.
Require Import PQueueIntro.
Require Import PThreadInitCSource.
Require Import PThreadInitCode.
Require Import QueueIntroGen.
Require Import QueueIntroGenSpec.
Require Import QueueIntroGenLinkSource.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Lemma get_head_correct :
    forall COMPILABLE: LayerCompilable ((TDQPool_LOC ↦ tdqpool_loc_type ⊕ pthreadinit) ⊕ L64),
    forall MOK: ModuleOK (get_head ↦ f_get_head),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (get_head ↦ f_get_head) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (get_head ↦ gensem get_head_spec)
             (〚 M2 〛((TDQPool_LOC ↦ tdqpool_loc_type ⊕ pthreadinit) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply get_head_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PTHREADINITCODE.get_head_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma get_tail_correct :
    forall COMPILABLE: LayerCompilable ((TDQPool_LOC ↦ tdqpool_loc_type ⊕ pthreadinit) ⊕ L64),
    forall MOK: ModuleOK (get_tail ↦ f_get_tail),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (get_tail ↦ f_get_tail) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (get_tail ↦ gensem get_tail_spec)
             (〚 M2 〛((TDQPool_LOC ↦ tdqpool_loc_type ⊕ pthreadinit) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply get_tail_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PTHREADINITCODE.get_tail_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma set_head_correct :
    forall COMPILABLE: LayerCompilable ((TDQPool_LOC ↦ tdqpool_loc_type ⊕ pthreadinit) ⊕ L64),
    forall MOK: ModuleOK (set_head ↦ f_set_head),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (set_head ↦ f_set_head) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (set_head ↦ gensem set_head_spec)
             (〚 M2 〛((TDQPool_LOC ↦ tdqpool_loc_type ⊕ pthreadinit) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply set_head_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PTHREADINITCODE.set_head_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma set_tail_correct :
    forall COMPILABLE: LayerCompilable ((TDQPool_LOC ↦ tdqpool_loc_type ⊕ pthreadinit) ⊕ L64),
    forall MOK: ModuleOK (set_tail ↦ f_set_tail),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (set_tail ↦ f_set_tail) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (set_tail ↦ gensem set_tail_spec)
             (〚 M2 〛((TDQPool_LOC ↦ tdqpool_loc_type ⊕ pthreadinit) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply set_tail_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PTHREADINITCODE.set_tail_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma tdq_init_correct :
    forall COMPILABLE: LayerCompilable ((TDQPool_LOC ↦ tdqpool_loc_type ⊕ pthreadinit) ⊕ L64),
    forall MOK: ModuleOK (tdq_init ↦ f_tdq_init),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (tdq_init ↦ f_tdq_init) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (tdq_init ↦ gensem tdq_init_spec)
             (〚 M2 〛((TDQPool_LOC ↦ tdqpool_loc_type ⊕ pthreadinit) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply tdq_init_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PTHREADINITCODE.tdq_init_code_correct.
    - apply left_upper_bound.
  Qed.

  (** XXX: added **)
  Record PQueueIntro_impl_inverted (M: module) : Prop:=
    {
      PQUEUEINTRO_get_head: module;
      PQUEUEINTRO_get_tail: module;
      PQUEUEINTRO_set_head: module;
      PQUEUEINTRO_set_tail: module;
      PQUEUEINTRO_tdq_init: module;
      PQUEUEINTRO_get_head_transf: CompCertiKOS.transf_module (get_head ↦ f_get_head) = ret PQUEUEINTRO_get_head;
      PQUEUEINTRO_get_tail_transf: CompCertiKOS.transf_module (get_tail ↦ f_get_tail) = ret PQUEUEINTRO_get_tail;
      PQUEUEINTRO_set_head_transf: CompCertiKOS.transf_module (set_head ↦ f_set_head) = ret PQUEUEINTRO_set_head;
      PQUEUEINTRO_set_tail_transf: CompCertiKOS.transf_module (set_tail ↦ f_set_tail) = ret PQUEUEINTRO_set_tail;
      PQUEUEINTRO_tdq_init_transf: CompCertiKOS.transf_module (tdq_init ↦ f_tdq_init) = ret PQUEUEINTRO_tdq_init;

      PQUEUEINTRO_M: M = (((PQUEUEINTRO_get_head ⊕ PQUEUEINTRO_get_tail ⊕ PQUEUEINTRO_set_head ⊕ PQUEUEINTRO_set_tail 
                                                 ⊕ PQUEUEINTRO_tdq_init)
                             ⊕ TDQPool_LOC ↦ tdqpool_loc_type)
                            ⊕ ∅);
      PQUEUEINTRO_Mok: LayerOK (〚M 〛 (pthreadinit ⊕ L64) ⊕ pthreadinit ⊕ L64);
      PQUEUEINTRO_Lok: LayerOK
                         (〚PQUEUEINTRO_get_head ⊕ PQUEUEINTRO_get_tail ⊕ PQUEUEINTRO_set_head ⊕ PQUEUEINTRO_set_tail 
                                                 ⊕ PQUEUEINTRO_tdq_init〛
                            ((pthreadinit ⊕ L64) ⊕ TDQPool_LOC ↦ tdqpool_loc_type)
                            ⊕ (pthreadinit ⊕ L64) ⊕ TDQPool_LOC ↦ tdqpool_loc_type)
    }.

  (** XXX: added **)
  Lemma module_impl_imply:
    forall M, PQueueIntro_impl = OK M -> PQueueIntro_impl_inverted M.
  Proof.
    unfold PQueueIntro_impl. intros M HM.
    inv_monad' HM.
    inv_monad' HM0. 
    econstructor.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    inv HM1. reflexivity.
    apply x1.
    apply x6.
  Qed.

  Lemma link_correct_aux:
    forall M, PQueueIntro_impl = OK M ->
              pthreadinit ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), M)
              : pqueueintro ⊕ L64.
  Proof.
    (** XXX: added **)
    intros M HM.
    eapply module_impl_imply in HM; destruct HM; subst.

    unfold pqueueintro, pqueueintro_fresh.
    eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      apply transfer_variable.

      (** XXX: added **)
      apply PQUEUEINTRO_Lok.
      eapply (LayerOK_impl_subst PQUEUEINTRO_Mok0).
      apply module_le_left.
      reflexivity.

      layer_link_split_tac.
      - apply get_head_correct; code_correct_tac.
      - apply get_tail_correct; code_correct_tac.
      - apply set_head_correct; code_correct_tac.
      - apply set_tail_correct; code_correct_tac.
      - apply tdq_init_correct; code_correct_tac.
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
  Require Import CommonTactic.
  Require Import LayerCalculusLemma.
  Require Import AuxLemma.
  Require Import Behavior.

  Lemma init_correct:
    forall M, PQueueIntro_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA)
                          (pqueueintro ⊕ L64) M (pthreadinit ⊕ L64).
  Proof.
    Opaque oplus.
    intros.
    pose proof (fun i => module_ok_variable M i (H0 i)) as MOK; clear H0.
    apply cl_init_sim_intro.
    - intros. 

      (** XXX: added **)
      eapply module_impl_imply in H; destruct H; subst.

      inv_monad' H0.
      generalize (make_program_make_globalenv _ _ _ _ H1).
      intros HP. pose proof HP as HP'.
      eapply make_globalenv_stencil_matches in HP'.
      inv_make_globalenv HP.
      rewrite  (stencil_matches_symbols _ _ HP') in *.
      inv HP'.
      constructor.
      + constructor; simpl; trivial.
        * apply FlatMem.flatmem_empty_inj.
        * apply kctxt_inj_empty.
      + econstructor; eauto.
        * econstructor; eauto.
          specialize (Genv.init_mem_characterization _ _ Hbvi H2); eauto.
          unfold Genv.perm_globvar; simpl; intros [Hperm _].
          assert(HVALID: forall ofs, 0<= ofs < (num_chan + 1) * 2 ->
                                     Mem.valid_access m2 Mint32 b (ofs * 4) Writable).
          {
            intros; split; simpl.
            change (Z.max 520 0) with 520 in Hperm.
            unfold Mem.range_perm in *.
            intros. apply Hperm. omega.
            apply Zdivide_mult_r. apply Zdivide_refl.
          }
          assert(HEX: forall ofs,  0<= ofs < (num_chan + 1) * 2 ->
                                   (exists v, Mem.load Mint32 m2 b (ofs * 4) = Some v)).
          {
            intros; apply (Mem.valid_access_load).
            apply Mem.valid_access_implies with Writable.
            apply HVALID; trivial.
            constructor.
          }
          intros.
          assert (HOS1: 0<= ofs * 2 < 65 * 2) by omega.
          assert (HOS2: 0<= ofs * 2 + 1 < 65 * 2) by omega.
          destruct (HEX _ HOS1) as [v1 HEX1].
          destruct (HEX _ HOS2) as [v2 HEX2].
          pose proof (HVALID _ HOS1) as HV1.
          pose proof (HVALID _ HOS2) as HV2.
          replace (ofs * 2 * 4) with (ofs * 8) in *.
          replace ((ofs * 2 + 1) * 4) with (ofs * 8 + 4) in *.
          refine_split'; eauto.
          rewrite ZMap.gi. constructor.
          omega. omega.

    - intros. destruct H0 as [HF|HF]; inv HF; reflexivity.
    - intros. destruct H0 as [HF|HF]; inv HF; reflexivity.
    - intros.

      (** XXX: added **)
      eapply module_impl_imply in H; destruct H; subst.
      transf_none i. specialize (MOK i).

      destruct H0 as [HF|HF]; inv HF; econstructor.
      get_module_variable_relfexivity.

    - intros.
      (** XXX: added **)
      eapply module_impl_imply in H; destruct H; subst.
      transf_none i. specialize (MOK i).

      destruct (peq i TDQPool_LOC); subst.
      + eapply (get_module_varible_OK_Some_left tdqpool_loc_type) in H0; subst.
        reflexivity.
        destruct (get_module_variable_isOK _ _ _ MOK) as [HT1 _].
        get_module_variable_relfexivity.
      + assert (get_module_variable
                  i (((PQUEUEINTRO_get_head
                         ⊕ PQUEUEINTRO_get_tail
                         ⊕ PQUEUEINTRO_set_head
                         ⊕ PQUEUEINTRO_set_tail ⊕ PQUEUEINTRO_tdq_init)
                        ⊕ TDQPool_LOC ↦ tdqpool_loc_type) ⊕ ∅)
                = OK None).
        {
          abstract get_module_variable_relfexivity.
        }
        unfold module, module_ops in *.
        congruence.
    - decision.
  Qed.

  Theorem cl_simulation:
    forall p (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      PQueueIntro_impl = OK M ->
      make_program s CTXT (pqueueintro ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pthreadinit ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (pqueueintro ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pthreadinit ⊕ L64)) pl)
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
      PQueueIntro_impl = OK M ->
      make_program s CTXT (pqueueintro ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pthreadinit ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (pqueueintro ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pthreadinit ⊕ L64)) pl).
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
      PQueueIntro_impl = OK M ->
      make_program s CTXT (pqueueintro ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pthreadinit ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (pqueueintro ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pthreadinit ⊕ L64)) pl).
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
      PQueueIntro_impl = OK M ->
      make_program s (CTXT ⊕ M) (pthreadinit ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (pqueueintro ⊕ L64) = OK ph.
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
