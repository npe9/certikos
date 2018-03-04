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

Require Import MBoot.
Require Import PreInit.
Require Import PreInitCode.
Require Import PreInitCSource.
Require Import BootGen.
Require Import BootGenLinkSource.
Require Import LinkTemplate.

(** Remove*)
(*Require Import MBootCSource.*)

Section WITHCOMPCERTIKOS.

  Context `{compcertikos_prf: CompCertiKOS}.

  Context `{real_params_prf : RealParams}.

  Notation HDATA := AbstractDataType.RData.
  Notation LDATA := AbstractDataType.RData.

  (** Fix Me *)
  Lemma fstore_correct:
    forall COMPILABLE: LayerCompilable ((FlatMem_LOC ↦ flatmem_loc_type ⊕ preinit) ⊕ L64),
    forall MOK: ModuleOK (fstore ↦ f_fstore),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (fstore ↦ f_fstore) = OK M2 ->
      cl_sim HDATAOps LDATAOps
             (crel HDATA LDATA)
             (fstore ↦ gensem fstore'_spec)
             (〚 M2 〛((FlatMem_LOC ↦ flatmem_loc_type ⊕ preinit) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply fstore_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - apply PREINITCODE.fstore_correct.
    - apply left_upper_bound.
  Qed.

  Lemma fload_correct:
    forall COMPILABLE: LayerCompilable ((FlatMem_LOC ↦ flatmem_loc_type ⊕ preinit) ⊕ L64),
    forall MOK: ModuleOK (fload ↦ f_fload),
    forall M2: LAsm.module,
      CompCertiKOS.transf_module (fload ↦ f_fload) = OK M2 ->
      cl_sim HDATAOps LDATAOps
             (crel HDATA LDATA)
             (fload ↦ gensem fload'_spec)
             (〚 M2 〛((FlatMem_LOC ↦ flatmem_loc_type ⊕ preinit) ⊕ L64)).
  Proof.
    intros.
    eapply link_compiler; eauto.
    - eapply fload_spec_ref.
    - link_nextblock.
    - link_kernel_mode.
    - apply PREINITCODE.fload_code_correct.
    - apply left_upper_bound.
  Qed.

  Lemma link_correct_aux:
    forall M, MBoot_impl = OK M ->
              preinit ⊕ L64
                    ⊢ (path_inj (crel HDATA LDATA), M)
              : mboot ⊕ L64.
  Proof.
    intros M HM.
    inv_link_impl HM; subst.
    unfold mboot.
    eapply conseq_le_assoc_comm.
    hcomp_tac.
    {
      transfer_variables.
      unfold mboot_fresh.
      layer_link_split_tac.
      - apply fload_correct; code_correct_tac.
      - apply fstore_correct; code_correct_tac.
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

  Lemma empty_flatmem_inject f m b n bs :
      Mem.loadbytes m b 0 n = Some bs ->
      list_forall2 (memval_inject f)
        (FlatMem.loadbytes FlatMem.empty_flatmem 0 n) bs.
  Proof.
    intros HLD.
    apply Mem.loadbytes_length in HLD.
    destruct n; try (destruct bs; try discriminate HLD; constructor).
    generalize 0.
    generalize dependent bs.
    generalize dependent p.
    refine (Pos.peano_ind _ _ _).
    - destruct bs; try discriminate.
      destruct bs; try discriminate.
      unfold FlatMem.loadbytes, FlatMem.empty_flatmem; simpl; intros _ ?.
      rewrite ZMap.gi.
      repeat constructor.
    - intros p IHp.
      unfold FlatMem.loadbytes, FlatMem.empty_flatmem.
      rewrite Pos2Z.inj_succ, Z2Nat.inj_succ; [| discriminate ].
      destruct bs; try discriminate; simpl.
      injection 1 as bs_length.
      intros; constructor.
      + rewrite ZMap.gi.
        repeat constructor.
      + apply IHp; assumption.
  Qed.

  Lemma init_correct:
    forall M, MBoot_impl = OK M ->
              ModuleOK M ->
              cl_init_sim HDATAOps LDATAOps (crel HDATA LDATA) (mboot ⊕ L64) M (preinit ⊕ L64).
  Proof.
    Opaque oplus.
    intros.
    pose proof (fun i => module_ok_variable M i (H0 i)) as MOK.
    clear H0.
    apply cl_init_sim_intro.
    - intros. 
      inv_link_impl H; subst.
      inv_monad' H0.
      generalize (make_program_make_globalenv _ _ _ _ H1).
      intros HP. pose proof HP as HP'.
      eapply make_globalenv_stencil_matches in HP'.
      inv_make_globalenv HP. subst.
      rewrite  (stencil_matches_symbols _ _ HP') in *. inv HP'.
      constructor.
      + constructor; simpl; trivial. 
      + econstructor; eauto.
        econstructor; eauto.
        specialize (Genv.init_mem_characterization _ _ Hbvi H2); eauto.
        unfold Genv.perm_globvar; simpl; intros [Hperm _].
        change (Z.max 4294967296 0) with 4294967296 in Hperm.
        assert (Hperm': Mem.range_perm m2 b 0 (0 + 4294967296) Cur Readable).
        {
          simpl. eapply Mem.range_perm_implies; eauto.
          constructor.
        }
        exploit Mem.range_perm_loadbytes; try eassumption.
        intros [bs HLD].
        refine_split'; eauto.
	eapply empty_flatmem_inject; eassumption.
    - intros. destruct H0 as [HF|HF]; inv HF; reflexivity.
    - intros. destruct H0 as [HF|HF]; inv HF; reflexivity.
    - intros.
      inv_link_impl H; subst.
      transf_none i. specialize (MOK i).

      destruct H0 as [HF|HF]; inv HF; econstructor.
      + get_module_variable_relfexivity.

    - intros.
      inv_link_impl H; subst.
      transf_none i. specialize (MOK i).

      destruct (peq i FlatMem_LOC); subst.
      + eapply (get_module_varible_OK_Some_left flatmem_loc_type) in H0; subst.
        reflexivity.
        destruct (get_module_variable_isOK _ _ _ MOK) as [HT1 _].
        get_module_variable_relfexivity.
      + assert (get_module_variable
                  i ((((M1 ⊕ M0 ⊕ ∅) ⊕ ∅) ⊕ FlatMem_LOC ↦ flatmem_loc_type) ⊕ ∅) = OK None).
          {
            get_module_variable_relfexivity.
          }
          setoid_rewrite H0 in H.
          congruence.
    - decision.
  Qed.

  Theorem cl_backward_simulation:
    forall (s: stencil) (CTXT M: module) pl ph
           (builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet),
      MBoot_impl = OK M ->
      make_program s CTXT (mboot ⊕ L64) = OK ph ->
      make_program s (CTXT ⊕ M) (preinit ⊕ L64) = OK pl ->
      backward_simulation
        (LAsm.semantics (lcfg_ops := LC (mboot ⊕ L64)) ph)
        (LAsm.semantics (lcfg_ops := LC (preinit ⊕ L64)) pl).
  Proof.
    intros. pose proof H as HM.
    inv_link_impl HM; subst.
    eapply (soundness (crel HDATA LDATA)); try eassumption; try decision.
    eapply link_correct_aux; eauto.
    eapply init_correct; eauto.
    eapply make_program_oplus_right; eassumption.
  Qed.

  Require Import LAsmModuleSemMakeProgram.

  Theorem make_program_exists:
    forall (s: stencil) (CTXT M: module) pl,
      MBoot_impl = OK M ->
      make_program s (CTXT ⊕ M) (preinit ⊕ L64) = OK pl ->
      exists ph, make_program s CTXT (mboot ⊕ L64) = OK ph.
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
    inv_link_impl H.
    assumption.
  Qed.

End WITHCOMPCERTIKOS.
