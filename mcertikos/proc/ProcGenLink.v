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
Require Import PUCtxtIntro.
Require Import PProc.
Require Import PUCtxtIntroCSource.
Require Import PUCtxtIntroCode.
Require Import ProcGen.
Require Import ProcGenSpec.
Require Import ProcGenLinkSource.
Require Import ProcGenAsmSource.
Require Import ProcGenAsm.
Require Import ProcGenAsm1.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Notation HDATA := AbstractDataType.RData.
  Notation LDATA := AbstractDataType.RData.

  Notation HDATAOps := (cdata (cdata_ops := pproc_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := pipc_data_ops) LDATA).

  Definition left_upper_bound := Structures.left_upper_bound
    (A := compatlayer LDATAOps).

  (** FIXME: doesn't really belong here. Try to generalize
    [proc_create_inv] instead? *)
  Require Import CommonTactic.
  Require Import INVLemmaThread.
  Require Import INVLemmaProc.
  Require Import INVLemmaContainer.
  Global Instance proc_create_inv': PCreateInvariants (data_ops := PIPC.pipc_data_ops) proc_create_spec.
  Proof.
    constructor; intros; inv H0;
    unfold proc_create_spec in *;
    subdestruct; inv H; simpl; auto.

    - (* low level invariant *)
      constructor; trivial; intros; simpl in *.
      + eapply kctxt_inject_neutral_gss_flatinj'; eauto.
        eapply kctxt_inject_neutral_gss_flatinj; eauto.
      + eapply uctxt_inject_neutral_gss; eauto.
        repeat eapply uctxt_inject_neutral0_gss;
        try eapply uctxt_inject_neutral0_Vint.
        * eapply uctxt_inject_neutral_impl; eauto.
        * eapply uctxt_inject_neutral0_Vptr_flat; eauto.
    - (* high_level_invariant *)
      destruct (correct_curid eq_refl) as [Hused _]; auto.
      constructor; simpl; eauto 2; try congruence; intros.
      + exploit split_container_valid; eauto.
        eapply container_split_some; eauto.
        auto.
      + unfold update_cusage, update_cchildren; zmap_solve.
      + eapply AbTCBStrong_range_gss_READY; eauto. 
      + eapply AbQCorrect_range_gss_enqueue; eauto.
      + unfold update_cusage, update_cchildren; apply NotInQ_gso_ac_true; eauto.
        zmap_simpl; repeat apply NotInQ_gso_true; auto.
      + eapply QCount_gss_spawn; eauto. 
        eapply AbTCBStrong_range_impl; eauto.
        split; [|split; [|eauto]].
        assert (Hpos:= cvalid_child_id_pos _ valid_container _ Hused 0); omega.
        apply cvalid_unused_next_child; auto.
      + eapply InQ_gss_spawn; eauto.
        eapply AbTCBStrong_range_impl; eauto.
        split; [|split; [|eauto]].
        assert (Hpos:= cvalid_child_id_pos _ valid_container _ Hused 0); omega.
        apply cvalid_unused_next_child; auto.
      + unfold update_cusage, update_cchildren; apply CurIDValid_gso_neq_true; auto.
        zmap_simpl; repeat apply CurIDValid_gss_ac; auto.
        assert (Hneq:= cvalid_child_id_neq _ valid_container _ Hused); zmap_simpl.
        apply cvalid_unused_next_child; auto.
      + eapply SingleRun_gso_state_READY; eauto.
  Qed.

  Lemma proc_create_correct :
    forall COMPILABLE: LayerCompilable (puctxtintro ⊕ L64),
    forall MOK: ModuleOK (proc_create ↦ f_proc_create),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (proc_create ↦ f_proc_create) = OK M2 ->
      cl_sim HDATAOps LDATAOps
             (crel HDATA LDATA)
             (proc_create ↦ proc_create_compatsem proc_create_spec)
             (〚 M2 〛(puctxtintro ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply ProcGen.proc_create_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PUCTXTINTROCODE.proc_create_code_correct.
    - LayerCalculusLemma.le_oplus.
  Qed.

  Lemma proc_start_user_correct:
      cl_sim _ _
             (crel HDATA LDATA)
             (proc_start_user ↦ primcall_start_user_compatsem proc_start_user_spec)
             (〚 proc_start_user ↦ proc_start_user_function 〛 puctxtintro).
  Proof.
    intros.
    eapply link_assembly; eauto.
    - eapply proc_start_user_spec_ref.
    - eapply proc_start_user_code_correct.
  Qed.

  Lemma proc_exit_user_correct:
      cl_sim _ _
             (crel HDATA LDATA)
             (proc_exit_user ↦ primcall_exit_user_compatsem proc_exit_user_spec)
             (〚 proc_exit_user ↦ proc_exit_user_function 〛 puctxtintro).
  Proof.
    intros.
    eapply link_assembly; eauto.
    - eapply proc_exit_user_spec_ref.
    - eapply proc_exit_user_code_correct.
  Qed.
 
  Record PProc_impl_inverted (M: module) : Prop :=
    {
      PProc_proc_create: module;
      PProc_proc_create_transf: CompCertiKOS.transf_module (proc_create ↦ f_proc_create) = ret PProc_proc_create;
      PProc_M: M = (
        (
          PProc_proc_create
          ⊕ ((proc_start_user ↦ proc_start_user_function) ⊕ (proc_exit_user ↦ proc_exit_user_function))
        ) ⊕ ∅);
      PProc_Mok: LayerOK (〚M 〛 (puctxtintro ⊕ L64) ⊕ puctxtintro ⊕ L64)
    }.

  Lemma module_impl_imply:
    forall M, PProc_impl = OK M -> PProc_impl_inverted M.
  Proof.
    unfold PProc_impl. intros M HM.
    inv_monad' HM.
    econstructor.
    eassumption.
    inv HM1. reflexivity.
    apply x1.
  Qed.

  Lemma link_correct_aux:
    forall M, PProc_impl = OK M ->
              puctxtintro ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), M)
              : pproc ⊕ L64.
  Proof.
    unfold PProc_impl. intros M HM.
    eapply module_impl_imply in HM; destruct HM; subst.

    unfold pproc, pproc_fresh_c, pproc_fresh_asm.
    eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      hcomp_tac.
      {
        layer_link_split_tac.
        apply proc_create_correct; code_correct_tac.
      }
      {
        apply Language.conseq_le_left with puctxtintro; [| apply left_upper_bound ].
        layer_link_split_tac.
        - apply proc_start_user_correct.
        - apply proc_exit_user_correct.
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
  Require Import AuxLemma.
  Require Import Behavior.

  Lemma init_correct:
    forall M, PProc_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA) (pproc ⊕ L64) M (puctxtintro ⊕ L64).
  Proof.
    intros.
    pose proof (fun i => module_ok_variable M i (H0 i)) as MOK; clear H0.
    apply cl_init_sim_intro.
    - constructor; simpl; trivial.
      constructor; simpl; trivial. apply FlatMem.flatmem_empty_inj.
      apply kctxt_inj_empty.
      apply uctxt_inj_empty.
      constructor.
    - intros; inv H0.
    - intros; inv H0.
    - intros; inv H0.
    - intros.
      eapply module_impl_imply in H; destruct H; subst.

      transf_none i. specialize (MOK i).
      assert (get_module_variable i ((PProc_proc_create
         ⊕ proc_start_user ↦ proc_start_user_function
           ⊕ proc_exit_user ↦ proc_exit_user_function) ⊕ ∅) = OK None).
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
      PProc_impl = OK M ->
      make_program s CTXT (pproc ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (puctxtintro ⊕ L64) = OK pl ->
      simulation
        (LAsm.semantics (lcfg_ops := LC (pproc ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (puctxtintro ⊕ L64)) pl)
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
      PProc_impl = OK M ->
      make_program s CTXT (pproc ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (puctxtintro ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (pproc ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (puctxtintro ⊕ L64)) pl).
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
      PProc_impl = OK M ->
      make_program s CTXT (pproc ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (puctxtintro ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (pproc ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (puctxtintro ⊕ L64)) pl).
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
      PProc_impl = OK M ->
      make_program s (CTXT ⊕ M) (puctxtintro ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (pproc ⊕ L64) = OK ph.
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
    eapply PProc_Mok; assumption.
  Qed.

End WITHCOMPCERTIKOS.
