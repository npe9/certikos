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
Require Import PKContextNew.
Require Import PThreadIntro.
Require Import PKContextNewCSource.
Require Import PKContextNewCode.
Require Import ThreadIntroGen.
Require Import ThreadIntroGenSpec.
Require Import ThreadIntroGenLinkSource.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Lemma get_state_correct :
    forall COMPILABLE: LayerCompilable ((TCBPool_LOC ↦ tcbpool_loc_type ⊕ pkcontextnew) ⊕ L64),
    forall MOK: ModuleOK (get_state ↦ f_get_state),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (get_state ↦ f_get_state) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (get_state ↦ gensem get_state_spec)
             (〚 M2 〛((TCBPool_LOC ↦ tcbpool_loc_type ⊕ pkcontextnew) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply get_state_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PKCONTEXTNEWCODE.get_state_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma get_prev_correct :
    forall COMPILABLE: LayerCompilable ((TCBPool_LOC ↦ tcbpool_loc_type ⊕ pkcontextnew) ⊕ L64),
    forall MOK: ModuleOK (get_prev ↦ f_get_prev),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (get_prev ↦ f_get_prev) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (get_prev ↦ gensem get_prev_spec)
             (〚 M2 〛((TCBPool_LOC ↦ tcbpool_loc_type ⊕ pkcontextnew) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply get_prev_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PKCONTEXTNEWCODE.get_prev_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma get_next_correct :
    forall COMPILABLE: LayerCompilable ((TCBPool_LOC ↦ tcbpool_loc_type ⊕ pkcontextnew) ⊕ L64),
    forall MOK: ModuleOK (get_next ↦ f_get_next),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (get_next ↦ f_get_next) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (get_next ↦ gensem get_next_spec)
             (〚 M2 〛((TCBPool_LOC ↦ tcbpool_loc_type ⊕ pkcontextnew) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply get_next_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PKCONTEXTNEWCODE.get_next_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma set_state_correct :
    forall COMPILABLE: LayerCompilable ((TCBPool_LOC ↦ tcbpool_loc_type ⊕ pkcontextnew) ⊕ L64),
    forall MOK: ModuleOK (set_state ↦ f_set_state),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (set_state ↦ f_set_state) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (set_state ↦ gensem set_state_spec)
             (〚 M2 〛((TCBPool_LOC ↦ tcbpool_loc_type ⊕ pkcontextnew) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply set_state_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PKCONTEXTNEWCODE.set_state_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma set_prev_correct :
    forall COMPILABLE: LayerCompilable ((TCBPool_LOC ↦ tcbpool_loc_type ⊕ pkcontextnew) ⊕ L64),
    forall MOK: ModuleOK (set_prev ↦ f_set_prev),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (set_prev ↦ f_set_prev) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (set_prev ↦ gensem set_prev_spec)
             (〚 M2 〛((TCBPool_LOC ↦ tcbpool_loc_type ⊕ pkcontextnew) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply set_prev_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PKCONTEXTNEWCODE.set_prev_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma set_next_correct :
    forall COMPILABLE: LayerCompilable ((TCBPool_LOC ↦ tcbpool_loc_type ⊕ pkcontextnew) ⊕ L64),
    forall MOK: ModuleOK (set_next ↦ f_set_next),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (set_next ↦ f_set_next) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (set_next ↦ gensem set_next_spec)
             (〚 M2 〛((TCBPool_LOC ↦ tcbpool_loc_type ⊕ pkcontextnew) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply set_next_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PKCONTEXTNEWCODE.set_next_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma tcb_init_correct :
    forall COMPILABLE: LayerCompilable ((TCBPool_LOC ↦ tcbpool_loc_type ⊕ pkcontextnew) ⊕ L64),
    forall MOK: ModuleOK (tcb_init ↦ f_tcb_init),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (tcb_init ↦ f_tcb_init) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (tcb_init ↦ gensem tcb_init_spec)
             (〚 M2 〛((TCBPool_LOC ↦ tcbpool_loc_type ⊕ pkcontextnew) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply tcb_init_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PKCONTEXTNEWCODE.tcb_init_code_correct.
    - apply left_upper_bound.
  Qed.

  Require Import PKContext.

  (** XXX: added **)
  Record PThreadIntro_impl_inverted (M: module) : Prop:=
    {
      PTHREADINTRO_get_state: module;
      PTHREADINTRO_get_prev: module;
      PTHREADINTRO_get_next: module;
      PTHREADINTRO_set_state: module;
      PTHREADINTRO_set_prev: module;
      PTHREADINTRO_set_next: module;
      PTHREADINTRO_tcb_init: module;
      PTHREADINTRO_get_state_transf: CompCertiKOS.transf_module (get_state ↦ f_get_state) = ret PTHREADINTRO_get_state;
      PTHREADINTRO_get_prev_transf: CompCertiKOS.transf_module (get_prev ↦ f_get_prev) = ret PTHREADINTRO_get_prev;
      PTHREADINTRO_get_next_transf: CompCertiKOS.transf_module (get_next ↦ f_get_next) = ret PTHREADINTRO_get_next;
      PTHREADINTRO_set_state_transf: CompCertiKOS.transf_module (set_state ↦ f_set_state) = ret PTHREADINTRO_set_state;
      PTHREADINTRO_set_prev_transf: CompCertiKOS.transf_module (set_prev ↦ f_set_prev) = ret PTHREADINTRO_set_prev;
      PTHREADINTRO_set_next_transf: CompCertiKOS.transf_module (set_next ↦ f_set_next) = ret PTHREADINTRO_set_next;
      PTHREADINTRO_tcb_init_transf: CompCertiKOS.transf_module (tcb_init ↦ f_tcb_init) = ret PTHREADINTRO_tcb_init;
      PTHREADINTRO_M: M = (((PTHREADINTRO_get_state ⊕ PTHREADINTRO_get_prev ⊕ PTHREADINTRO_get_next
                                                    ⊕ PTHREADINTRO_set_state ⊕ PTHREADINTRO_set_prev 
                                                    ⊕ PTHREADINTRO_set_next ⊕ PTHREADINTRO_tcb_init)
                             ⊕ TCBPool_LOC ↦ tcbpool_loc_type)
                             ⊕ ∅);
      PTHREADINTRO_Mok: LayerOK (〚M 〛 (pkcontextnew ⊕ L64) ⊕ pkcontextnew ⊕ L64);
      PTHREADINTRO_Lok: LayerOK
                         (〚PTHREADINTRO_get_state ⊕ PTHREADINTRO_get_prev ⊕ PTHREADINTRO_get_next
                                                   ⊕ PTHREADINTRO_set_state ⊕ PTHREADINTRO_set_prev 
                                                   ⊕ PTHREADINTRO_set_next ⊕ PTHREADINTRO_tcb_init〛
                            ((pkcontextnew ⊕ L64) ⊕ TCBPool_LOC ↦ tcbpool_loc_type)
                            ⊕ (pkcontextnew ⊕ L64) ⊕ TCBPool_LOC ↦ tcbpool_loc_type)
    }.

  (** XXX: added **)
  Lemma module_impl_imply:
    forall M, PThreadIntro_impl = OK M -> PThreadIntro_impl_inverted M.
  Proof.
    unfold PThreadIntro_impl. intros M HM.
    inv_monad' HM.
    inv_monad' HM0. 
    econstructor.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    inv HM1. reflexivity.
    apply x1.
    apply x8.
  Qed.

  Lemma link_correct_aux:
    forall M, PThreadIntro_impl = OK M ->
              pkcontextnew ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), M)
              : pthreadintro ⊕ L64.
  Proof.
    (** XXX: added **)
    intros M HM.
    eapply module_impl_imply in HM; destruct HM; subst.

    unfold pthreadintro, pthreadintro_fresh.
    eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      apply transfer_variable.

      (** XXX: added **)
      apply PTHREADINTRO_Lok.
      eapply (LayerOK_impl_subst PTHREADINTRO_Mok0).
      apply module_le_left.
      reflexivity.

      layer_link_split_tac.
      - apply get_state_correct; code_correct_tac.
      - apply get_prev_correct; code_correct_tac.
      - apply get_next_correct; code_correct_tac.
      - apply set_state_correct; code_correct_tac.
      - apply set_prev_correct; code_correct_tac.
      - apply set_next_correct; code_correct_tac.
      - apply tcb_init_correct; code_correct_tac.
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
    forall M, PThreadIntro_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA)
                          (pthreadintro ⊕ L64) M (pkcontextnew ⊕ L64).
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
          assert(HVALID: forall ofs, 0<= ofs < num_proc * 3 ->
                                     Mem.valid_access m2 Mint32 b (ofs * 4) Writable).
          {
            intros; split; simpl.
            change (Z.max 768 0) with 768 in Hperm.
            unfold Mem.range_perm in *.
            intros. apply Hperm. omega.
            apply Zdivide_mult_r. apply Zdivide_refl.
          }
          assert(HEX: forall ofs,  0<= ofs < num_proc * 3 ->
                                   (exists v, Mem.load Mint32 m2 b (ofs * 4) = Some v)).
          {
            intros; apply (Mem.valid_access_load).
            apply Mem.valid_access_implies with Writable.
            apply HVALID; trivial.
            constructor.
          }
          intros.
          assert (HOS1: 0<= ofs * 3 < 64 * 3) by omega.
          assert (HOS2: 0<= ofs * 3 + 1 < 64 * 3) by omega.
          assert (HOS3: 0<= ofs * 3 + 2 < 64 * 3) by omega.
          destruct (HEX _ HOS1) as [v1 HEX1].
          destruct (HEX _ HOS2) as [v2 HEX2].
          destruct (HEX _ HOS3) as [v3 HEX3].
          pose proof (HVALID _ HOS1) as HV1.
          pose proof (HVALID _ HOS2) as HV2.
          pose proof (HVALID _ HOS3) as HV3.
          replace (ofs * 3 * 4) with (ofs * 12) in *.
          replace ((ofs * 3 + 1) * 4) with (ofs * 12 + 4) in *.
          replace ((ofs * 3 + 2) * 4) with (ofs * 12 + 8) in *.
          refine_split'; eauto.
          rewrite ZMap.gi. constructor.
          omega. omega. omega.

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

      destruct (peq i TCBPool_LOC); subst.
      + eapply (get_module_varible_OK_Some_left tcbpool_loc_type) in H0; subst.
        reflexivity.
        destruct (get_module_variable_isOK _ _ _ MOK) as [HT1 _].
        get_module_variable_relfexivity.
      + assert (get_module_variable
                  i (((PTHREADINTRO_get_state
                         ⊕ PTHREADINTRO_get_prev
                         ⊕ PTHREADINTRO_get_next
                         ⊕ PTHREADINTRO_set_state
                         ⊕ PTHREADINTRO_set_prev
                         ⊕ PTHREADINTRO_set_next ⊕ PTHREADINTRO_tcb_init)
                        ⊕ TCBPool_LOC ↦ tcbpool_loc_type) ⊕ ∅) = OK None).
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
      PThreadIntro_impl = OK M ->
      make_program s CTXT (pthreadintro ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pkcontextnew ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (pthreadintro ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pkcontextnew ⊕ L64)) pl)
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
      PThreadIntro_impl = OK M ->
      make_program s CTXT (pthreadintro ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pkcontextnew ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (pthreadintro ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pkcontextnew ⊕ L64)) pl).
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
      PThreadIntro_impl = OK M ->
      make_program s CTXT (pthreadintro ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pkcontextnew ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (pthreadintro ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pkcontextnew ⊕ L64)) pl).
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
      PThreadIntro_impl = OK M ->
      make_program s (CTXT ⊕ M) (pkcontextnew ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (pthreadintro ⊕ L64) = OK ph.
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
