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
Require Import PAbQueue.
Require Import PCurID.
Require Import PAbQueueCSource.
Require Import PAbQueueCode.
Require Import CurIDGen.
Require Import CurIDGenSpec.
Require Import CurIDGenLinkSource.

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Notation HDATA := AbstractDataType.RData.
  Notation LDATA := AbstractDataType.RData.

  Notation HDATAOps := (cdata (cdata_ops := pcurid_data_ops) HDATA).
  Notation LDATAOps := (cdata (cdata_ops := pabqueue_data_ops) LDATA).

  Lemma get_curid_correct :
    forall COMPILABLE: LayerCompilable ((CURID_LOC ↦ curid_loc_type ⊕ pabqueue) ⊕ L64),
    forall MOK: ModuleOK (get_curid ↦ f_get_curid),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (get_curid ↦ f_get_curid) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (get_curid ↦ gensem get_curid_spec)
             (〚 M2 〛((CURID_LOC ↦ curid_loc_type ⊕ pabqueue) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply get_curid_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PABQUEUECODE.get_curid_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma set_curid_correct :
    forall COMPILABLE: LayerCompilable ((CURID_LOC ↦ curid_loc_type ⊕ pabqueue) ⊕ L64),
    forall MOK: ModuleOK (set_curid ↦ f_set_curid),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (set_curid ↦ f_set_curid) = OK M2 ->
      cl_sim _ _
             (crel HDATA LDATA)
             (set_curid ↦ gensem set_curid_spec)
             (〚 M2 〛((CURID_LOC ↦ curid_loc_type ⊕ pabqueue) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply set_curid_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - eapply PABQUEUECODE.set_curid_code_correct.
    - apply left_upper_bound.
  Qed.

  (** XXX: added **)
  Record PCurID_impl_inverted (M: module) : Prop:=
    {
      PCURID_get_curid: module;
      PCURID_set_curid: module;
      PCURID_get_curid_transf: CompCertiKOS.transf_module (get_curid ↦ f_get_curid) = ret PCURID_get_curid;
      PCURID_set_curid_transf: CompCertiKOS.transf_module (set_curid ↦ f_set_curid) = ret PCURID_set_curid;

      PCURID_M: M = (((PCURID_get_curid ⊕ PCURID_set_curid)
                        ⊕ CURID_LOC ↦ curid_loc_type)
                       ⊕ ∅);
      PCURID_Mok: LayerOK (〚M 〛 (pabqueue ⊕ L64) ⊕ pabqueue ⊕ L64);
      PCURID_Lok: LayerOK
                    (〚PCURID_get_curid ⊕ PCURID_set_curid〛
                       ((pabqueue ⊕ L64) ⊕ CURID_LOC ↦ curid_loc_type)
                       ⊕ (pabqueue ⊕ L64) ⊕ CURID_LOC ↦ curid_loc_type)
    }.

  (** XXX: added **)
  Lemma module_impl_imply:
    forall M, PCurID_impl = OK M -> PCurID_impl_inverted M.
  Proof.
    unfold PCurID_impl. intros M HM.
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
    forall M, PCurID_impl = OK M ->
              pabqueue ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), M)
              : pcurid ⊕ L64.
  Proof.
    (** XXX: added **)
    intros M HM.
    eapply module_impl_imply in HM; destruct HM; subst.

    unfold pcurid, pcurid_fresh.
    eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      apply transfer_variable.

      (** XXX: added **)
      apply PCURID_Lok.
      eapply (LayerOK_impl_subst PCURID_Mok0).
      apply module_le_left.
      reflexivity.

      layer_link_split_tac.
      - apply get_curid_correct; code_correct_tac.
      - apply set_curid_correct; code_correct_tac.
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
    forall M, PCurID_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA) (pcurid ⊕ L64) M (pabqueue ⊕ L64).
  Proof.
    intros.
    pose proof (fun i => module_ok_variable M i (H0 i)) as MOK; clear H0.
    apply cl_init_sim_intro.
    - intros. 

      (** XXX: added **)
      eapply module_impl_imply in H; destruct H; subst.

      inv_monad' H0.
      assert (HP := make_program_make_globalenv _ _ _ _ H1).
      assert (HP' := make_globalenv_stencil_matches _ _ _ _ HP).
      (* unfold MVar in HP. *)
      inv_make_globalenv HP.
      rewrite  (stencil_matches_symbols _ _ HP') in *.
      inv HP'.
      constructor.
      + constructor; simpl; trivial;
          [ apply FlatMem.flatmem_empty_inj | apply kctxt_inj_empty ].
      + (* match_RData & match_CurID *)
        econstructor; eauto.
        destruct (Genv.init_mem_characterization _ _ Hbvi H2)
          as (Hperm & _ & Hinit).
        unfold Genv.perm_globvar in Hperm; simpl in Hperm, Hinit.
        assert (load_init := proj1 (Hinit eq_refl)).
        assert(HVALID: Mem.valid_access m2 Mint32 b 0 Writable).
        { change (Z.max 4 0) with 4 in Hperm.
          split; simpl; [ apply Hperm | apply Z.divide_0_r ].
        }
        econstructor; eauto.
    - intros i [ <- | [] ].
      reflexivity.
    - intros i [ <- | [] ].
      reflexivity.
    - intros i [ <- | [] ].

      (** XXX: added **)
      eapply module_impl_imply in H; destruct H; subst.
      transf_none CURID_LOC. specialize (MOK CURID_LOC).
      econstructor.
      get_module_variable_relfexivity.
    - intros. 
      (** XXX: added **)
      eapply module_impl_imply in H; destruct H; subst.
      transf_none i. specialize (MOK i).

      destruct (peq i CURID_LOC); subst.
      + eapply (get_module_varible_OK_Some_left curid_loc_type) in H0; subst;
          try reflexivity.
        destruct (get_module_variable_isOK _ _ _ MOK) as [HT1 _].
        get_module_variable_relfexivity.
      + assert (get_module_variable
                  i (((PCURID_get_curid ⊕ PCURID_set_curid) ⊕ CURID_LOC ↦ curid_loc_type) ⊕ ∅) = OK None).
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
      PCurID_impl = OK M ->
      make_program s CTXT (pcurid ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pabqueue ⊕ L64) = OK pl ->
      simulation 
        (LAsm.semantics (lcfg_ops := LC (pcurid ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pabqueue ⊕ L64)) pl)
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
      PCurID_impl = OK M ->
      make_program s CTXT (pcurid ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pabqueue ⊕ L64) = OK pl ->
      forward_simulation
        (LAsm.semantics (lcfg_ops := LC (pcurid ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pabqueue ⊕ L64)) pl).
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
      PCurID_impl = OK M ->
      make_program s CTXT (pcurid ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (pabqueue ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (pcurid ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (pabqueue ⊕ L64)) pl).
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
      PCurID_impl = OK M ->
      make_program s (CTXT ⊕ M) (pabqueue ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (pcurid ⊕ L64) = OK ph.
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
