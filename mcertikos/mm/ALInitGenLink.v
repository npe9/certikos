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
Require Import MBoot.
Require Import MALInit.
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
Require Import ALInitGen.
Require Import MBootCode.
Require Import ALInitGenSpec.
Require Import LinkTactic.
Require Import MBootCSource.
Require Import ALInitGenLinkSource.
Require Import CompCertiKOSproof.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Lemma set_at_norm_correct:
    forall COMPILABLE: LayerCompilable ((AT_LOC ↦ at_loc_type ⊕ mboot) ⊕ L64),
    forall MOK: ModuleOK (set_norm ↦ f_set_norm),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (set_norm ↦ f_set_norm) = OK M2 ->
      cl_sim HDATAOps LDATAOps
             (crel HDATA LDATA)
             (set_norm ↦ gensem set_at_norm_spec)
             (〚 M2 〛((AT_LOC ↦ at_loc_type ⊕ mboot) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply setatnorm_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MBOOTCODE.set_norm_correct.
    - apply left_upper_bound.
  Qed.

  Lemma set_at_u_correct:
    forall COMPILABLE: LayerCompilable ((AT_LOC ↦ at_loc_type ⊕ mboot) ⊕ L64),
    forall MOK: ModuleOK (at_set ↦ f_at_set),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (at_set ↦ f_at_set) = OK M2 ->
      cl_sim _ _
        (crel HDATA LDATA)
        (at_set ↦ gensem set_at_u_spec)
        (〚 M2 〛((AT_LOC ↦ at_loc_type ⊕ mboot) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply setatu_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MBOOTCODE.at_set_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma is_at_norm_correct:
    forall COMPILABLE: LayerCompilable ((AT_LOC ↦ at_loc_type ⊕ mboot) ⊕ L64),
    forall MOK: ModuleOK (is_norm ↦ f_is_norm),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (is_norm ↦ f_is_norm) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (is_norm ↦ gensem is_at_norm_spec)
             (〚 M2 〛((AT_LOC ↦ at_loc_type ⊕ mboot) ⊕ L64)).
  Proof.  
    intros.
    eapply link_compiler; eauto.
    - eapply getatnorm_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MBOOTCODE.is_norm_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma get_at_u_correct:
    forall COMPILABLE: LayerCompilable ((AT_LOC ↦ at_loc_type ⊕ mboot) ⊕ L64),
    forall MOK: ModuleOK (at_get ↦ f_at_get),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (at_get ↦ f_at_get) = OK M2 ->
      cl_sim _ _
        (crel HDATA LDATA)
        (at_get ↦ gensem get_at_u_spec)
        (〚 M2 〛((AT_LOC ↦ at_loc_type ⊕ mboot) ⊕ L64)).
  Proof. 
    intros.
    eapply link_compiler; eauto.
    - eapply getatu_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MBOOTCODE.at_get_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma set_nps_correct:
    forall COMPILABLE: LayerCompilable ((NPS_LOC ↦ nps_loc_type ⊕ mboot) ⊕ L64),
    forall MOK: ModuleOK (set_nps ↦ f_set_nps),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (set_nps ↦ f_set_nps) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (set_nps ↦ gensem set_nps_spec)
             (〚 M2 〛((NPS_LOC ↦ nps_loc_type ⊕ mboot) ⊕ L64)).
  Proof. 
    intros.
    eapply link_compiler; eauto.
    - eapply setnps_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MBOOTCODE.set_nps_correct.
    - apply left_upper_bound.
  Qed.

  Lemma get_nps_correct:
    forall COMPILABLE: LayerCompilable ((NPS_LOC ↦ nps_loc_type ⊕ mboot) ⊕ L64),
    forall MOK: ModuleOK (get_nps ↦ f_get_nps),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (get_nps ↦ f_get_nps) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (get_nps ↦ gensem get_nps_spec)
             (〚 M2 〛((NPS_LOC ↦ nps_loc_type ⊕ mboot) ⊕ L64)).
  Proof. 
    intros.
    eapply link_compiler; eauto.
    - eapply getnps_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MBOOTCODE.get_nps_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma get_at_c_correct:
    forall COMPILABLE: LayerCompilable ((AT_LOC ↦ at_loc_type ⊕ mboot) ⊕ L64),
    forall MOK: ModuleOK (at_get_c ↦ f_at_get_c),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (at_get_c ↦ f_at_get_c) = OK M2 ->
      cl_sim _ _
        (crel HDATA LDATA)
        (at_get_c ↦ gensem get_at_c_spec)
        (〚 M2 〛((AT_LOC ↦ at_loc_type ⊕ mboot) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply getatc_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MBOOTCODE.at_get_c_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma set_at_c_correct:
    forall COMPILABLE: LayerCompilable ((AT_LOC ↦ at_loc_type ⊕ mboot) ⊕ L64),
    forall MOK: ModuleOK (at_set_c ↦ f_at_set_c),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (at_set_c ↦ f_at_set_c) = OK M2 ->
      cl_sim _ _
        (crel HDATA LDATA)
        (at_set_c ↦ gensem set_at_c_spec)
        (〚 M2 〛((AT_LOC ↦ at_loc_type ⊕ mboot) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply setatc_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply MBOOTCODE.at_set_c_code_correct.
    - apply left_upper_bound.
  Qed.

  Record MALInit_impl_inverted (M: module) : Prop:=
    {
      MALINIT_at_get: module;
      MALINIT_is_norm: module;
      MALINIT_at_get_c: module;
      MALINIT_at_set: module;
      MALINIT_set_norm: module;
      MALINIT_at_set_c: module;
      MALINIT_set_nps: module;
      MALINIT_get_nps: module;
      MALINIT_at_get_transf: CompCertiKOS.transf_module (at_get ↦ f_at_get) = ret MALINIT_at_get;
      MALINIT_is_norm_transf: CompCertiKOS.transf_module (is_norm ↦ f_is_norm) = ret MALINIT_is_norm;
      MALINIT_at_get_c_transf: CompCertiKOS.transf_module (at_get_c ↦ f_at_get_c) = ret MALINIT_at_get_c;
      MALINIT_at_set_transf: CompCertiKOS.transf_module (at_set ↦ f_at_set) = ret MALINIT_at_set;
      MALINIT_set_norm_transf: CompCertiKOS.transf_module (set_norm ↦ f_set_norm) = ret MALINIT_set_norm;
      MALINIT_at_set_c_transf: CompCertiKOS.transf_module (at_set_c ↦ f_at_set_c) = ret MALINIT_at_set_c;
      MALINIT_set_nps_transf: CompCertiKOS.transf_module (set_nps ↦ f_set_nps) = ret MALINIT_set_nps;
      MALINIT_get_nps_transf: CompCertiKOS.transf_module (get_nps ↦ f_get_nps) = ret MALINIT_get_nps;
      MALINIT_M: M = ((((MALINIT_at_get ⊕ MALINIT_is_norm ⊕ MALINIT_at_get_c ⊕ MALINIT_at_set ⊕ MALINIT_set_norm ⊕ MALINIT_at_set_c)
                        ⊕ (AT_LOC ↦ at_loc_type))
                        ⊕ ((MALINIT_set_nps ⊕ MALINIT_get_nps)  ⊕  (NPS_LOC ↦ nps_loc_type)))
                        ⊕ ∅);
      MALINIT_Mok: LayerOK (〚M 〛 (mboot ⊕ L64) ⊕ mboot ⊕ L64);
      MALINIT_Lok: LayerOK
                     (〚MALINIT_at_get ⊕ MALINIT_is_norm ⊕ MALINIT_at_get_c ⊕ MALINIT_at_set ⊕ MALINIT_set_norm ⊕ MALINIT_at_set_c〛
                        ((mboot ⊕ L64) ⊕ AT_LOC ↦ at_loc_type)
                        ⊕ (mboot ⊕ L64) ⊕ AT_LOC ↦ at_loc_type);
      MALINIT_Lok': LayerOK
                      (〚MALINIT_set_nps ⊕ MALINIT_get_nps〛
                         ((mboot ⊕ L64) ⊕ NPS_LOC ↦ nps_loc_type)
                         ⊕ (mboot ⊕ L64) ⊕ NPS_LOC ↦ nps_loc_type)
    }.

  Lemma module_impl_imply:
    forall M, MALInit_impl = OK M -> MALInit_impl_inverted M.
  Proof.
    unfold MALInit_impl. intros M HM.
    (*Local Opaque oplus semof mapsto ptree_layer_ops.*)
    inv_monad' HM.
    inv_monad' HM0. 
    inv_monad' HM1. 
    econstructor.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    inv HM2. reflexivity.
    apply x2.
    apply x8.
    apply x10.
  Qed.

  Lemma link_correct_aux:
    forall M, MALInit_impl = OK M ->
              (*forall (OKLayer: LayerOK (〚M 〛 (mboot ⊕ L64) ⊕ (mboot ⊕ L64))),*)
              mboot ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), M)
              : malinit ⊕ L64.
  Proof.
    Require Import LinkTemplate.
    intros M HM.
    eapply module_impl_imply in HM; destruct HM; subst.
    unfold malinit.
    eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      hcomp_tac.
      {
        eapply transfer_variable.
        apply MALINIT_Lok.
        eapply (LayerOK_impl_subst MALINIT_Mok0).

        apply module_le_left.
        apply module_le_left.
        reflexivity.

        layer_link_split_tac.
        - apply get_at_u_correct; code_correct_tac.
        - apply is_at_norm_correct; code_correct_tac.
        - apply get_at_c_correct; code_correct_tac.
        - apply set_at_u_correct; code_correct_tac.
        - apply set_at_norm_correct; code_correct_tac.
        - apply set_at_c_correct; code_correct_tac.
      }
      {
        apply transfer_variable.
        apply MALINIT_Lok'.

        eapply (LayerOK_impl_subst MALINIT_Mok0).

        apply module_le_left.
        apply module_le_right.
        reflexivity.

        layer_link_split_tac.
        - apply set_nps_correct; code_correct_tac. 
        - apply get_nps_correct; code_correct_tac. 
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
  Require Import CommonTactic.
  Require Import LayerCalculusLemma.
  Require Import Behavior.

  Lemma init_correct:
    forall M, MALInit_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA) (malinit ⊕ L64) M (mboot ⊕ L64).
  Proof.
    Opaque oplus.
    intros.
    pose proof (fun i => module_ok_variable M i (H0 i)) as MOK; clear H0.
    apply cl_init_sim_intro.
    - intros. 
      eapply module_impl_imply in H; destruct H; subst.
      inv_monad' H0.
      generalize (make_program_make_globalenv _ _ _ _ H1).
      intros HP. pose proof HP as HP'.
      eapply make_globalenv_stencil_matches in HP'.
      inv_make_globalenv HP. subst.
      rewrite  (stencil_matches_symbols _ _ HP') in *. inv HP'.
      constructor.
      + constructor; simpl; trivial. apply FlatMem.flatmem_empty_inj.
      + econstructor; eauto.
        * econstructor; eauto.
          specialize (Genv.init_mem_characterization _ _ Hbvi H2); eauto.
          unfold Genv.perm_globvar; simpl; intros [Hperm _].
          intros. 
          assert(HVALID: Mem.valid_access m2 Mint32 b (ofs * 12) Writable).
          {
            intros; split; simpl.
            change (Z.max 12582912 0) with 12582912 in Hperm.
            unfold Mem.range_perm in *.
            intros. apply Hperm. omega.
            apply Zdivide_mult_r. exists 3. reflexivity.
          }
           assert(HVALID': Mem.valid_access m2 Mint32 b (ofs * 12 + 4) Writable).
          {
            intros; split; simpl.
            change (Z.max 12582912 0) with 12582912 in Hperm.
            unfold Mem.range_perm in *.
            intros. apply Hperm. omega.
            apply Zdivide_plus_r.
            - apply Zdivide_mult_r. exists 3. reflexivity.
            - reflexivity.
          }
          assert(HVALID'': Mem.valid_access m2 Mint32 b (ofs * 12 + 8) Writable).
          {
            intros; split; simpl.
            change (Z.max 12582912 0) with 12582912 in Hperm.
            unfold Mem.range_perm in *.
            intros. apply Hperm. omega.
            apply Zdivide_plus_r.
            - apply Zdivide_mult_r. exists 3. reflexivity.
            - change 8 with (4 + 4).
              apply Zdivide_plus_r; reflexivity.
          }
          assert(HEX1: exists v, Mem.load Mint32 m2 b (ofs * 12) = Some v).
          {
            intros; apply (Mem.valid_access_load).
            apply Mem.valid_access_implies with Writable.
            apply HVALID; trivial.
            constructor.
          }
          assert(HEX2: exists v, Mem.load Mint32 m2 b (ofs * 12 + 4) = Some v).
          {
            intros; apply (Mem.valid_access_load).
            apply Mem.valid_access_implies with Writable.
            apply HVALID'; trivial.
            constructor.
          }
          assert(HEX3: exists v, Mem.load Mint32 m2 b (ofs * 12 + 8) = Some v).
          {
            intros; apply (Mem.valid_access_load).
            apply Mem.valid_access_implies with Writable.
            apply HVALID''; trivial.
            constructor.
          }
          destruct HEX1, HEX2, HEX3.
          refine_split'; eauto.
          rewrite ZMap.gi.
          constructor.
        * specialize (Genv.init_mem_characterization _ _ Hb0vi H2); eauto.
          unfold Genv.perm_globvar; simpl. intros [Hperm[_ Hinit]].
          split. eapply Hinit; trivial.
          split; trivial.
          apply Zdivide_0.
        * reflexivity.
    - intros. destruct H0 as [HF|[HF|HF]]; inv HF; reflexivity.
    - intros. destruct H0 as [HF|[HF|HF]]; inv HF; reflexivity.
    - intros.
      eapply module_impl_imply in H; destruct H; subst.
      transf_none i. specialize (MOK i).

      destruct H0 as [HF|[HF|HF]]; inv HF; econstructor.
      + get_module_variable_relfexivity.
      + get_module_variable_relfexivity.

    - intros.
      eapply module_impl_imply in H; destruct H; subst.
      transf_none i. specialize (MOK i).

      destruct (peq i AT_LOC); subst.
      + eapply (get_module_varible_OK_Some_left at_loc_type) in H0; subst.
        reflexivity.
        destruct (get_module_variable_isOK _ _ _ MOK) as [HT1 _].
        get_module_variable_relfexivity.
      + destruct (peq i NPS_LOC); subst.
        * eapply (get_module_varible_OK_Some_left nps_loc_type) in H0; subst.
          reflexivity.
          destruct (get_module_variable_isOK _ _ _ MOK) as [HT1 _].
          get_module_variable_relfexivity.
        * assert (get_module_variable
                    i ((((MALINIT_at_get
                            ⊕ MALINIT_is_norm ⊕ MALINIT_at_get_c ⊕
                            MALINIT_at_set ⊕ MALINIT_set_norm ⊕ MALINIT_at_set_c)
                           ⊕ AT_LOC ↦ at_loc_type)
                          ⊕ (MALINIT_set_nps ⊕ MALINIT_get_nps) ⊕ NPS_LOC ↦ nps_loc_type)
                         ⊕ ∅) = OK None).
          {
            get_module_variable_relfexivity.
          }
          congruence.
    - decision.
  Qed.

  Theorem cl_simulation:
    forall p (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      MALInit_impl = OK M ->
      make_program s CTXT (malinit ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (mboot ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (malinit ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (mboot ⊕ L64)) pl)
        (observe_lasm _ p) (observe_lasm _ p).
  Proof.
    intros. pose proof H as HM.
    eapply module_impl_imply in HM.
    eapply (soundness_simulation (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.
    eapply MALINIT_Mok; assumption.
  Qed.

  Theorem cl_forward_simulation:
    forall (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      MALInit_impl = OK M ->
      make_program s CTXT (malinit ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (mboot ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (malinit ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (mboot ⊕ L64)) pl).
  Proof.
    intros. pose proof H as HM.
    eapply module_impl_imply in HM.
    eapply (soundness_forward (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.
    eapply MALINIT_Mok; assumption.
  Qed.

  Theorem cl_backward_simulation:
    forall (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      MALInit_impl = OK M ->
      make_program s CTXT (malinit ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (mboot ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (malinit ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (mboot ⊕ L64)) pl).
  Proof.
    intros. pose proof H as HM.
    eapply module_impl_imply in HM.
    eapply (soundness (crel HDATA LDATA)); try eassumption; try decision.

    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.
    eapply MALINIT_Mok; assumption.
  Qed.

  Require Import LAsmModuleSemMakeProgram.

  Theorem make_program_exists:
    forall (s: stencil) (CTXT M: module) pl,
      MALInit_impl = OK M ->
      make_program s (CTXT ⊕ M) (mboot ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (malinit ⊕ L64) = OK ph.
  Proof.
    intros.
    exploit link_correct_aux; eauto.
    eapply make_program_vertical' in H0; try eassumption.
    destruct H0 as [p' Hmake].
    intros Hle.
    eapply make_program_sim_monotonic_exists.
    2: eapply Hle.
    reflexivity.
    eassumption.
    eapply module_impl_imply in H.
    eapply MALINIT_Mok; assumption.
  Qed.

End WITHCOMPCERTIKOS.
