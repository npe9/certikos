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
Require Import MShare.
Require Import PKContext.
Require Import MShareCSource.
Require Import MShareCode.
Require Import KContextGen.
Require Import KContextGenSpec.
Require Import KContextGenLinkSource.
Require Import KContextGenAsmSource.
Require Import KContextGenAsm.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.
  
  Notation HDATA := AbstractDataType.RData.
  Notation LDATA := AbstractDataType.RData.

  Notation HDATAOps := (cdata (cdata_ops := mshareintro_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := mshareintro_data_ops) LDATA).

  Lemma set_RA_correct :
    forall COMPILABLE: LayerCompilable ((KCtxtPool_LOC ↦ kctxtpool_loc_type ⊕ mshare) ⊕ L64),
    forall MOK: ModuleOK (set_RA ↦ f_set_RA),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (set_RA ↦ f_set_RA) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (set_RA ↦ kctxt_ra_compatsem)
             (〚 M2 〛((KCtxtPool_LOC ↦ kctxtpool_loc_type ⊕ mshare) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply kctxt_ra_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MPTNEWCODE.set_RA_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma set_SP_correct:
    forall COMPILABLE: LayerCompilable ((KCtxtPool_LOC ↦ kctxtpool_loc_type ⊕ mshare) ⊕ L64),
    forall MOK: ModuleOK (set_SP ↦ f_set_SP),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (set_SP ↦ f_set_SP) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (set_SP ↦ kctxt_sp_compatsem)
             (〚 M2 〛((KCtxtPool_LOC ↦ kctxtpool_loc_type ⊕ mshare) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply kctxt_sp_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MPTNEWCODE.set_SP_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma kctxt_switch_correct:
      cl_sim _ _
             (crel HDATA LDATA)
             (kctxt_switch ↦ primcall_kctxt_switch_compatsem kctxt_switch_spec)
             (〚 kctxt_switch ↦ cswitch_function 〛 mshare).
  Proof.
    intros.
    eapply link_assembly; eauto.
    - eapply kctxt_switch_spec_ref.
    - eapply kctxt_switch_code_correct.
  Qed.

  (** XXX: added **)
  Record PKContext_impl_inverted (M: module) : Prop:=
    {
      PKCONTEXT_set_RA: module;
      PKCONTEXT_set_SP: module;
      PKCONTEXT_set_RA_transf: CompCertiKOS.transf_module (set_RA ↦ f_set_RA) = ret PKCONTEXT_set_RA;
      PKCONTEXT_set_SP_transf: CompCertiKOS.transf_module (set_SP ↦ f_set_SP) = ret PKCONTEXT_set_SP;

      PKCONTEXT_M: M = (((PKCONTEXT_set_RA ⊕ PKCONTEXT_set_SP)
                        ⊕ KCtxtPool_LOC ↦ kctxtpool_loc_type)
                        ⊕ ((kctxt_switch ↦ cswitch_function)
                             ⊕ ∅));
      PKCONTEXT_Mok: LayerOK (〚M 〛 (mshare ⊕ L64) ⊕ mshare ⊕ L64);
      PKCONTEXT_Lok: LayerOK
                     (〚PKCONTEXT_set_RA ⊕ PKCONTEXT_set_SP〛
                        ((mshare ⊕ L64) ⊕ KCtxtPool_LOC ↦ kctxtpool_loc_type)
                        ⊕ (mshare ⊕ L64) ⊕ KCtxtPool_LOC ↦ kctxtpool_loc_type)
    }.

  Lemma module_impl_imply:
    forall M, PKContext_impl = OK M -> PKContext_impl_inverted M.
  Proof.
    unfold PKContext_impl. intros M HM.
    inv_monad' HM.
    inv_monad' HM0. 
    econstructor.
    eassumption.
    eassumption.
    inv HM1. reflexivity.
    apply x1.
    apply x3.
  Qed.

  Lemma link_correct_aux:
    forall M, PKContext_impl = OK M ->
              mshare ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), M)
              : pkcontext ⊕ L64.
  Proof.
    (** XXX: added **)
    intros M HM.
    eapply module_impl_imply in HM; destruct HM; subst.

    unfold pkcontext, pkcontext_fresh.
    eapply conseq_le_assoc_comm. eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      apply transfer_variable.

      (** XXX: added **)
      apply PKCONTEXT_Lok.
      eapply (LayerOK_impl_subst PKCONTEXT_Mok0).
      apply module_le_left.
      reflexivity.

      unfold pkcontext_fresh_c.
      layer_link_split_tac.
      - apply set_RA_correct; code_correct_tac.
      - apply set_SP_correct; code_correct_tac.
    }
    hcomp_tac.
    {
      apply Language.conseq_le_left with mshare; [| apply left_upper_bound ].
      layer_link_split_tac; apply kctxt_switch_correct.
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
  Require Import Behavior.

  Lemma init_correct:
    forall M, PKContext_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA) (pkcontext ⊕ L64) M (mshare ⊕ L64).
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
      + econstructor; eauto.
        * econstructor; eauto.
          Opaque Val.load_result.
          specialize (Genv.init_mem_characterization _ _ Hbvi H2); eauto.
          unfold Genv.perm_globvar; simpl; intros [Hperm _]. intros.
          assert(HVALID: Mem.valid_access m2 Mint32 b (ofs * 24 + n * 4) Writable).
          {
            split; simpl.
            change (Z.max 1536 0) with 1536 in Hperm.
            unfold Mem.range_perm in *.
            intros. apply Hperm. apply ZtoPreg_range in H0. abstract omega.
            unfold Z.divide.
            exists (ofs * 6 + n).
            abstract omega.
          }
          assert(HEX: exists v, Mem.load Mint32 m2 b (ofs * 24 + n * 4) = Some v).
          {
            intros; apply (Mem.valid_access_load).
            apply Mem.valid_access_implies with Writable.
            apply HVALID; trivial. constructor.
          }
          destruct HEX as [v1 HEX1].
          refine_split'; eauto.
          repeat rewrite ZMap.gi. constructor.

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

      destruct (peq i KCtxtPool_LOC); subst.
      + eapply (get_module_varible_OK_Some_left kctxtpool_loc_type) in H0; subst.
        reflexivity.
        destruct (get_module_variable_isOK _ _ _ MOK) as [HT1 _].
        get_module_variable_relfexivity.
      + assert (get_module_variable
                  i (((PKCONTEXT_set_RA ⊕ PKCONTEXT_set_SP)
                        ⊕ KCtxtPool_LOC ↦ kctxtpool_loc_type)
                       ⊕ kctxt_switch ↦ cswitch_function ⊕ ∅) = OK None).
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
      PKContext_impl = OK M ->
      make_program s CTXT (pkcontext ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (mshare ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (pkcontext ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (mshare ⊕ L64)) pl)
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
      PKContext_impl = OK M ->
      make_program s CTXT (pkcontext ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (mshare ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (pkcontext ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (mshare ⊕ L64)) pl).
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
      PKContext_impl = OK M ->
      make_program s CTXT (pkcontext ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (mshare ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (pkcontext ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (mshare ⊕ L64)) pl).
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
      PKContext_impl = OK M ->
      make_program s (CTXT ⊕ M) (mshare ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (pkcontext ⊕ L64) = OK ph.
  Proof.
    intros.
    exploit link_correct_aux; [eauto|].
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
