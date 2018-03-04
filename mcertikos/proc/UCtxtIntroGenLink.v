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
Require Import PIPC.
Require Import PUCtxtIntro.
Require Import PIPCCSource.
Require Import PIPCCode.
Require Import UCtxtIntroGen.
Require Import UCtxtIntroGenSpec.
Require Import UCtxtIntroGenLinkSource.
Require Import UCtxtIntroGenAsmSource.
Require Import UCtxtIntroGenAsm.
Require Import LAsmModuleSemSpec.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Lemma elf_load_correct:
      cl_sim _ _
             (crel HDATA LDATA)
             (elf_load ↦ elf_load_compatsem)
             (〚 elf_load ↦ elfload_function 〛 pipc).
  Proof.
    intros.
    eapply asm_spec_compose_inl; eauto.
    pose proof layer_sim_intro as Hlsi.
    eapply Hlsi.
    eapply elf_load_spec_ref.
    eapply elf_load_code_correct.
  Qed.

  Lemma uctx_get_correct :
    forall COMPILABLE: LayerCompilable ((UCTX_LOC ↦ uctx_loc_type ⊕ pipc) ⊕ L64),
    forall MOK: ModuleOK (uctx_get ↦ f_uctx_get),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (uctx_get ↦ f_uctx_get) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (uctx_get ↦ gensem uctx_get_spec)
             (〚 M2 〛((UCTX_LOC ↦ uctx_loc_type ⊕ pipc) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply uctx_get_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PIPCCODE.uctx_get_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma uctx_set_correct :
    forall COMPILABLE: LayerCompilable ((UCTX_LOC ↦ uctx_loc_type ⊕ pipc) ⊕ L64),
    forall MOK: ModuleOK (uctx_set ↦ f_uctx_set),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (uctx_set ↦ f_uctx_set) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (uctx_set ↦ gensem uctx_set_spec)
             (〚 M2 〛((UCTX_LOC ↦ uctx_loc_type ⊕ pipc) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply uctx_set_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PIPCCODE.uctx_set_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma uctx_set_eip_correct :
    forall COMPILABLE: LayerCompilable ((UCTX_LOC ↦ uctx_loc_type ⊕ pipc) ⊕ L64),
    forall MOK: ModuleOK (uctx_set_eip ↦ f_uctx_set_eip),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (uctx_set_eip ↦ f_uctx_set_eip) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (uctx_set_eip ↦ (uctx_set_eip_compatsem _))
             (〚 M2 〛((UCTX_LOC ↦ uctx_loc_type ⊕ pipc) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply uctx_set_eip_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PIPCCODE.uctx_set_eip_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma save_uctx_correct :
    forall COMPILABLE: LayerCompilable ((UCTX_LOC ↦ uctx_loc_type ⊕ pipc) ⊕ L64),
    forall MOK: ModuleOK (save_uctx ↦ f_save_uctx),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (save_uctx ↦ f_save_uctx) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (save_uctx ↦ (save_uctx_compatsem _))
             (〚 M2 〛((UCTX_LOC ↦ uctx_loc_type ⊕ pipc) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply save_uctx_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PIPCCODE.save_uctx_code_correct.
    - apply oplus_monotonic; [ reflexivity |].
      repeat (apply left_upper_bound || apply le_right).
  Qed.

  Lemma restore_uctx_correct:
      cl_sim _ _
             (crel HDATA LDATA)
             (restore_uctx ↦ primcall_restoreuctx_compatsem restore_uctx_spec cid)
             (〚 restore_uctx ↦ restoreuctx_function 〛 pipc).
  Proof.
    intros.
    eapply link_assembly; eauto.
    - eapply restore_uctx_spec_ref.
    - eapply restore_uctx_code_correct.
  Qed.

  (** XXX: added **)
  Record PUCtxtIntro_impl_inverted (M: module) : Prop:=
    {
      PUCTXTINTRO_uctx_get: module;
      PUCTXTINTRO_uctx_set: module;
      PUCTXTINTRO_uctx_set_eip: module;
      PUCTXTINTRO_save_uctx: module;
      PUCTXTINTRO_uctx_get_transf: CompCertiKOS.transf_module (uctx_get ↦ f_uctx_get) = ret PUCTXTINTRO_uctx_get;
      PUCTXTINTRO_uctx_set_transf: CompCertiKOS.transf_module (uctx_set ↦ f_uctx_set) = ret PUCTXTINTRO_uctx_set;
      PUCTXTINTRO_uctx_set_eip_transf: CompCertiKOS.transf_module (uctx_set_eip ↦ f_uctx_set_eip) = ret PUCTXTINTRO_uctx_set_eip;
      PUCTXTINTRO_save_uctx_transf: CompCertiKOS.transf_module (save_uctx ↦ f_save_uctx) = ret PUCTXTINTRO_save_uctx;

      PUCTXTINTRO_M: M = ((((PUCTXTINTRO_uctx_get ⊕ PUCTXTINTRO_uctx_set ⊕ PUCTXTINTRO_uctx_set_eip 
                                                  ⊕ PUCTXTINTRO_save_uctx)
                              ⊕ UCTX_LOC ↦ uctx_loc_type)
                             ⊕ (restore_uctx ↦ restoreuctx_function ⊕ elf_load ↦ elfload_function))
                            ⊕ ∅);
      PUCTXTINTRO_Mok: LayerOK (〚M 〛 (pipc ⊕ L64) ⊕ pipc ⊕ L64);
      PUCTXTINTRO_Lok: LayerOK
                     (〚PUCTXTINTRO_uctx_get ⊕ PUCTXTINTRO_uctx_set ⊕ PUCTXTINTRO_uctx_set_eip 
                                                  ⊕ PUCTXTINTRO_save_uctx〛
                        ((pipc ⊕ L64) ⊕ UCTX_LOC ↦ uctx_loc_type)
                        ⊕ (pipc ⊕ L64) ⊕ UCTX_LOC ↦ uctx_loc_type)
    }.

  (** XXX: added **)
  Lemma module_impl_imply:
    forall M, PUCtxtIntro_impl = OK M -> PUCtxtIntro_impl_inverted M.
  Proof.
    unfold PUCtxtIntro_impl. intros M HM.
    inv_monad' HM.
    inv_monad' HM0. 
    econstructor.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    inv HM1. reflexivity.
    apply x1.
    apply x5.
  Qed.

  Lemma link_correct_aux:
    forall M, PUCtxtIntro_impl = OK M ->
              pipc ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), M)
              : puctxtintro ⊕ L64.
  Proof.
    (** XXX: added **)
    intros M HM.
    eapply module_impl_imply in HM; destruct HM; subst.

    unfold puctxtintro, puctxtintro_fresh_c, puctxtintro_fresh_asm.
    eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      hcomp_tac.
      {
        apply transfer_variable.

        (** XXX: added **)
        apply PUCTXTINTRO_Lok.
        eapply (LayerOK_impl_subst PUCTXTINTRO_Mok0).
        apply module_le_left.
        apply module_le_left.
        reflexivity.

        layer_link_split_tac.
        - apply uctx_get_correct; code_correct_tac.
        - apply uctx_set_correct; code_correct_tac.
        - apply uctx_set_eip_correct; code_correct_tac.
        - apply save_uctx_correct; code_correct_tac.
      }
      {
        apply Language.conseq_le_left with pipc; [| apply left_upper_bound ].
        layer_link_split_tac.
        - apply restore_uctx_correct.
        - apply elf_load_correct.
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
  Require Import AuxLemma.
  Require Import Behavior.

  Lemma init_correct:
    forall M, PUCtxtIntro_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA)
                          (puctxtintro ⊕ L64) M (pipc ⊕ L64).
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
          Opaque Val.load_result.
          specialize (Genv.init_mem_characterization _ _ Hbvi H2); eauto.
          unfold Genv.perm_globvar; simpl; intros [Hperm _].
          assert(HVALID: forall i n,
                           0<= i < num_proc ->
                           0<= n < UCTXT_SIZE ->
                           Mem.valid_access m2 Mint32 b (i * UCTXT_SIZE * 4 + n * 4) Writable).
          {
            intros; split; simpl.
            change (Z.max 4352 0) with 4352 in Hperm.
            unfold Mem.range_perm in *.
            intros. apply Hperm. omega.
            unfold Z.divide.
            exists (i * 17 + n).
            omega.
          }
          assert(HEX: forall i n,
                        0<= i < num_proc ->
                        0<= n < UCTXT_SIZE ->
                        (exists v, Mem.load Mint32 m2 b (i * UCTXT_SIZE * 4 + n * 4) = Some v)).
          {
            intros; apply (Mem.valid_access_load).
            apply Mem.valid_access_implies with Writable.
            apply HVALID; trivial. constructor.
          }
          intros.
          destruct (HEX _ _ H H0) as [v1 HEX1].
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

      destruct (peq i UCTX_LOC); subst.
      + eapply (get_module_varible_OK_Some_left uctx_loc_type) in H0; subst.
        reflexivity.
        destruct (get_module_variable_isOK _ _ _ MOK) as [HT1 _].
        get_module_variable_relfexivity.
      + assert (get_module_variable
                  i ((((PUCTXTINTRO_uctx_get
                          ⊕ PUCTXTINTRO_uctx_set
                          ⊕ PUCTXTINTRO_uctx_set_eip ⊕ PUCTXTINTRO_save_uctx)
                         ⊕ UCTX_LOC ↦ uctx_loc_type) ⊕ MCode_Asm) ⊕ ∅) = OK None).
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
      PUCtxtIntro_impl = OK M ->
      make_program s CTXT (puctxtintro ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pipc ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (puctxtintro ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pipc ⊕ L64)) pl)
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
      PUCtxtIntro_impl = OK M ->
      make_program s CTXT (puctxtintro ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pipc ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (puctxtintro ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pipc ⊕ L64)) pl).
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
      PUCtxtIntro_impl = OK M ->
      make_program s CTXT (puctxtintro ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pipc ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (puctxtintro ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pipc ⊕ L64)) pl).
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
      PUCtxtIntro_impl = OK M ->
      make_program s (CTXT ⊕ M) (pipc ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (puctxtintro ⊕ L64) = OK ph.
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
