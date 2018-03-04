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
(** This file provide the semantics for the [Asm] instructions. Since we introduce paging mechanisms, the semantics of memory load and store are different from [Compcert Asm]*)
Require Import Coqlib.
Require Import Maps.
Require Import ASTExtra.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import AsmX.
Require Import Conventions.
Require Import Machregs.
Require Import AuxLemma.
Require Import CommonTactic.
Require Import liblayers.logic.PTreeModules.
Require Import liblayers.logic.PTreeSemantics.
Require Import liblayers.compcertx.MemWithData.
Require Import liblayers.compcertx.Stencil.
Require Import liblayers.compcertx.MakeProgram.
Require Import liblayers.compat.CompatData.
Require Import liblayers.compat.CompatPrimSem.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatExternalCalls.
Require Import CompCertBuiltins.
Require Import LAsm.
Require Import MemoryExtra.
Require Import LAsmModuleSemDef.
Require Import Observation.
(** ** Asm Invariants preserved by LAsm modules *)

Section ModuleSemantics_Asm_Invariant.

  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
  Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

(** [asm_invariant] *)

Section ASM_INVARIANT.

  Context {D: compatdata}.

  Variable (L: compatlayer D).

  Context `{acc_def_prf: !AccessorsDefined L}.

  Existing Instance compatlayer_mem_accessors.

  Instance compatlayer_mem_accessors_prf:
    MemAccessorsInvariant (LAsm.acc_exec_load _) (LAsm.acc_exec_store _).
  Proof.
    constructor.
    * unfold acc_exec_load.
      destruct (acc_exec_load_strong L).
      destruct x.
      destruct exec_load_spec.
      eauto.
    * unfold acc_exec_store.
      destruct (acc_exec_store_strong L).
      destruct x.
      destruct exec_store_spec.
      eauto.
  Qed.

  Lemma asm_invariant_nextinstr `{memory_model_x: !Mem.MemoryModelX mem}:
    forall {F V} (ge: Genv.t F V) rs (m: mwd D) rs' m',
      AsmX.asm_invariant ge rs m ->
      Next (nextinstr rs) m = Next rs' m' -> 
      AsmX.asm_invariant ge rs' m'.
  Proof.
    inversion 1; subst; intros. inv H0.
    inversion inv_inject_neutral; subst.
    constructor.
    + split; auto.
      apply AsmX.nextinstr_inject. eauto.
    + apply AsmX.nextinstr_wt; eauto.
  Qed.

  Lemma asm_invariant_nextinstr_Vint `{memory_model_x: !Mem.MemoryModelX mem}:
    forall {F V} (ge: Genv.t F V) rs (m: mwd D) rs' m' (rd: ireg) i,
      AsmX.asm_invariant ge rs m ->
      Next (nextinstr rs # rd <- (Vint i))  m = Next rs' m' -> 
      AsmX.asm_invariant ge rs' m'.
  Proof.
    inversion 1; subst; intros. inv H0.
    inversion inv_inject_neutral; subst.
    constructor.
    + split; auto.
      apply AsmX.nextinstr_inject.
      apply AsmX.set_reg_inject; auto.
    + apply AsmX.nextinstr_wt; eauto.
      apply AsmX.set_reg_wt; auto.
      simpl. trivial.
  Qed.

  Lemma asm_invariant_Vint `{memory_model_x: !Mem.MemoryModelX mem}:
    forall {F V} (ge: Genv.t F V) rs (m: mwd D) rs' m' (rd: ireg) i,
      AsmX.asm_invariant ge rs m ->
      Next (rs # rd <- (Vint i) )  m = Next rs' m' -> 
      AsmX.asm_invariant ge rs' m'.
  Proof.
    inversion 1; subst; intros. inv H0.
    inversion inv_inject_neutral; subst.
    constructor.
    + split; auto.
      apply AsmX.set_reg_inject; auto.
    + apply AsmX.set_reg_wt; auto.
      simpl. trivial.
  Qed.

  Lemma exec_instr_asm_invariant `{memory_model_x: !Mem.MemoryModelX mem}:
    forall ge rs (m: mwd D),
      AsmX.asm_invariant ge rs m ->
      forall c rs' m' i,
        LAsm.exec_instr (lcfg_ops := LC L) ge c i rs m = Next rs' m' ->
        AsmX.asm_invariant ge rs' m'
    .
  Proof.
    destruct i; eauto using AsmX.exec_instr_invariant;
    simpl; eauto using AsmX.exec_load_invariant, AsmX.exec_store_invariant.
    * inversion 1; subst.
      inversion H; subst.
      inversion inv_inject_neutral; subst.
      constructor.
      + split; auto.
        apply AsmX.nextinstr_nf_inject.
        apply AsmX.set_reg_inject; auto.
        apply AsmX.symbol_offset_inject_neutral; auto.
      + apply AsmX.nextinstr_nf_wt.
        apply AsmX.set_reg_wt; auto.
        unfold symbol_offset. destruct (Genv.find_symbol ge id); simpl; auto. 
    * inversion 1; subst.
      inversion H; subst.
      inversion inv_inject_neutral; subst.
      constructor.
      + split; auto.
        apply AsmX.nextinstr_inject.
        apply AsmX.set_reg_inject; auto.
      + apply AsmX.nextinstr_wt.
        apply AsmX.set_reg_wt; auto.
        simpl. apply inv_reg_wt.
    * inversion 1; subst.
      inversion H; subst.
      inversion inv_inject_neutral; subst.
      constructor.
      + split; auto.
        apply AsmX.nextinstr_inject.
        apply AsmX.set_reg_inject; auto.
      + apply AsmX.nextinstr_wt.
        apply AsmX.set_reg_wt; auto.
        simpl; apply inv_reg_wt.
    * inversion 1; subst.
      inversion H; subst.
      inversion inv_inject_neutral.
      split.
      + constructor; auto.
        apply AsmX.set_reg_inject; auto.
        apply AsmX.undef_reg_inject; auto.
      + apply AsmX.set_reg_wt.
        - simpl; apply inv_reg_wt.
        - apply AsmX.undef_reg_wt; auto.
    * eapply asm_invariant_nextinstr; eauto.
    * eapply asm_invariant_nextinstr; eauto.
    * eapply asm_invariant_nextinstr; eauto.
    * intros.
      eapply asm_invariant_nextinstr_Vint.
      eapply asm_invariant_Vint; eauto.
      eassumption.
    * eapply asm_invariant_nextinstr; eauto. 
    * eapply asm_invariant_nextinstr_Vint; eauto.
    * eapply asm_invariant_nextinstr_Vint; eauto.
    * eapply asm_invariant_nextinstr_Vint; eauto.
    * eapply asm_invariant_nextinstr; eauto.
    * eapply asm_invariant_nextinstr; eauto.
  Qed.

  Context `{extcall_invariants_available_prf: !ExtcallInvariantsAvailable L}.

  Lemma external_call_inject_neutral
        `{memory_model_x: !Mem.MemoryModelX mem}
        ef (ge: LAsm.genv) args (m: mwd D) t res m':
    external_call (external_calls_ops := compatlayer_extcall_ops L)
                  ef (fun _ : block => True) ge args m t res m' ->
    val_list_inject (Mem.flat_inj (Mem.nextblock m)) args args ->
    Mem.inject_neutral (Mem.nextblock m) m ->
    Ple (Genv.genv_next ge) (Mem.nextblock m) ->
    (val_inject (Mem.flat_inj (Mem.nextblock m')) res res /\
     Mem.inject_neutral (Mem.nextblock m') m').
  Proof.
    destruct ef.
    * destruct 1 as (σ & Hσ & Hextcall).
      destruct Hextcall as (s & σ' & Hs & Hσ' & ? & ? & ?); subst.
      destruct m. destruct m'.
      intros.
      pose proof (extcall_invariants_available name _ Hσ).
      eapply external_call_inject_neutral in Hσ'; eauto.
      erewrite <- stencil_matches_genv_next; eauto.
    * inversion 1; subst; split; auto.
      + destruct x; constructor.
      + destruct x; destruct y; constructor.
      + destruct x; destruct y; constructor.
      + destruct x; destruct y; constructor.
    * inversion 1; subst; split; auto.
      inv H0; subst.
      + inv H6; destruct chunk; try (simpl; constructor; fail).
        econstructor.
        unfold Mem.flat_inj. destruct (plt b0 (Mem.nextblock m')); try reflexivity.
        exfalso. exploit Genv.genv_symb_range; eauto. xomega.
        rewrite Int.add_zero. reflexivity.
      + eapply Mem.load_inject_neutral; eauto.
    * inversion 1; subst; split; auto.
      inversion H0; subst; auto.
      erewrite Mem.nextblock_store; eauto.
      inv H1. inv H11.
      inversion H9. clear H13. subst.
      unfold Mem.flat_inj in H10. destruct (plt b (Mem.nextblock m)); try discriminate.
      eapply Mem.store_inject_neutral; eauto.
    * inversion 1; subst; split; auto.
      inv H1; subst.
      + inv H7; destruct chunk; try (simpl; constructor; fail).
        econstructor.
        unfold Mem.flat_inj. destruct (plt b0 (Mem.nextblock m')); try reflexivity.
        exfalso. exploit Genv.genv_symb_range; eauto. xomega.
        rewrite Int.add_zero. reflexivity.
      + eapply Mem.load_inject_neutral; eauto.
    * inversion 1; subst; split; auto.
      inversion H1; subst; auto.
      erewrite Mem.nextblock_store; eauto.
      inv H2.            
      eapply Mem.store_inject_neutral; eauto.
      eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies. eapply Mem.store_valid_access_3; eauto. constructor.
    * inversion 1; subst.
      intros.
      generalize (Mem.inject_neutral_incr _ _ H3 _ (Plt_Ple _ _ (Plt_succ _))).
      intro NEUTRAL.
      generalize H0. intro HALLOC.
      eapply Mem.alloc_inject_neutral in HALLOC; eauto using Plt_succ.
      erewrite Mem.nextblock_store; eauto.
      erewrite Mem.nextblock_alloc; eauto.
      assert (Plt b (Pos.succ (Mem.nextblock m))).
      { 
        erewrite <- Mem.nextblock_alloc; eauto. 
        eapply Mem.valid_access_valid_block. 
        eapply Mem.valid_access_implies. 
        + eapply Mem.store_valid_access_3; eauto. 
        + constructor.
      }
      split.
      + econstructor. unfold Mem.flat_inj. destruct (plt b (Pos.succ (Mem.nextblock m))); try reflexivity. contradiction.
      rewrite Int.add_zero. reflexivity.
      + eapply Mem.store_inject_neutral; eauto.
    * inversion 1; subst.
      split; auto.
      erewrite Mem.nextblock_free; eauto.
      eapply Mem.free_inject_neutral; eauto.
      inv H3. inversion H9. unfold Mem.flat_inj in H8. destruct (plt b (Mem.nextblock m)); auto; discriminate.
    * inversion 1; subst.
      split; auto.
      erewrite Mem.nextblock_storebytes; eauto.
      eapply Mem.storebytes_inject_neutral; eauto.
      + eapply Mem.loadbytes_inject_neutral; eauto.
        inv H8. inv H16. inversion H13. clear H18. subst.
        unfold Mem.flat_inj in H15. destruct (plt bsrc (Mem.nextblock m)); try discriminate. assumption.
      + inv H8. inversion H14. clear H17. subst.
        unfold Mem.flat_inj in H13. destruct (plt bdst (Mem.nextblock m)); try discriminate. assumption.
    * inversion 1; subst; auto.
    * inversion 1; subst; split; auto.
      inv H1; auto.
    * inversion 1.
  Qed.

  Lemma external_call_inject_neutral'
        `{memory_model_x: !Mem.MemoryModelX mem}
        ef (ge: LAsm.genv) args (m: mwd D) t res m':
    external_call' (external_calls_ops := compatlayer_extcall_ops L)
                   (fun _ => True) ef ge args m t res m' ->
    val_list_inject (Mem.flat_inj (Mem.nextblock m)) args args ->
    Mem.inject_neutral (Mem.nextblock m) m ->
    Ple (Genv.genv_next ge) (Mem.nextblock m) ->
    (val_list_inject (Mem.flat_inj (Mem.nextblock m')) res res /\
     Mem.inject_neutral (Mem.nextblock m') m').
  Proof.
    inversion 1; subst.
    intros.
    eapply external_call_inject_neutral in H0; eauto using decode_longs_inject.
    destruct H0.
    eauto using encode_long_inject.
  Qed.

  Context `{primcall_inv_available_prf: !PrimcallInvariantsAvailable L}.

  Context `{builtin_idents_norepet_prf: CompCertBuiltins.BuiltinIdentsNorepet}.

  Global Existing Instance compatlayer_extcall_strong.

  Lemma nextinstr_asm_invariant `{memory_model_x: !Mem.MemoryModelX mem}:
    forall (ge: genv) rs (m: mwd D),
      AsmX.asm_invariant ge rs m ->
      AsmX.asm_invariant ge (nextinstr rs) m.
  Proof.
    inversion 1. split; auto.
    - inv inv_inject_neutral.
      econstructor; eauto.
      apply nextinstr_inject'; eauto.
    - apply AsmX.nextinstr_wt; trivial.
  Qed.

  Lemma nextinstr_nf_asm_invariant `{memory_model_x: !Mem.MemoryModelX mem}:
    forall (ge: genv) rs (m: mwd D),
      AsmX.asm_invariant ge rs m ->
      AsmX.asm_invariant ge (nextinstr_nf rs) m.
  Proof.
    inversion 1. split; auto.
    - inv inv_inject_neutral.
      econstructor; eauto.
      apply nextinstr_nf_inject'; eauto.
    - apply AsmX.nextinstr_nf_wt; trivial.
  Qed.

  Lemma asm_invariant_equiv:
    forall {F V} (ge: Genv.t F V) s rs (m: mwd D),
      stencil_matches s ge ->
      (asm_invariant s rs m <-> AsmX.asm_invariant ge rs m).
  Proof.                    
    split; inversion 1; split; auto;
    inv inv_inject_neutral; split; auto;
    inv H; congruence.
  Qed.

  Section EMPTYEXT.
    Local Instance empty_extcall_ops_x:
      ExternalCallsOpsX (mwd D) :=
      {|
        external_functions_sem i sg WB F V ge vargs m t vres m' :=
          False
      |}.

    Local Instance empty_extcall_ops:
      ExternalCallsOps (mwd D) :=
      external_calls_ops_x_to_external_calls_ops (mwd D) (external_calls_ops_x := empty_extcall_ops_x).

    Local Instance empty_compiler_config_ops:
      CompilerConfigOps _
                        (external_calls_ops := empty_extcall_ops)
      :=
        {|
          (** We want to follow the calling conventions when calling an
    external function which will be replaced later with code. This is
    not possible if EF_extcall are enabled at builtin call sites. *)
          cc_enable_external_as_builtin := false
        |}.

    Local Instance empty_extcall_x_strong:
        ExternalCallsX _
                       (external_calls_ops_x := empty_extcall_ops_x).
    Proof.
      intros.
      constructor.
      constructor; try (inversion 1; fail); try (inversion 2; fail); inversion 4.
    Qed.

    Local Instance empty_extcall_strong :
      forall `{builtin_norepet: BuiltinIdentsNorepet},
        ExternalCalls _
                      (external_calls_ops := empty_extcall_ops)
      := _.

    Local Instance empty_compiler_config :
      forall `{builtin_norepet: BuiltinIdentsNorepet},
        CompilerConfiguration _
                              (external_calls_ops := empty_extcall_ops).
    Proof.
      constructor.
      typeclasses eauto.
      apply empty_extcall_strong.
    Qed.

    Lemma builtin_enabled_empty ef
          (BUILTIN_ENABLED: builtin_enabled (compiler_config_ops := compatlayer_compiler_config_ops L) ef)
          WB {F V} (ge: _ F V) args m t res m'
          (EC: external_call (external_calls_ops := compatlayer_extcall_ops L) ef WB ge args m t res m'):
    external_call (external_calls_ops := empty_extcall_ops) ef WB ge args m t res m'.
    Proof.
      destruct ef; try contradiction; tauto.
    Qed.

    Lemma builtin_enabled_empty' ef
          (BUILTIN_ENABLED: builtin_enabled (compiler_config_ops := compatlayer_compiler_config_ops L) ef)
          WB {F V} (ge: _ F V) args m t res m'
          (EC: external_call' (external_calls_ops := compatlayer_extcall_ops L) WB ef ge args m t res m'):
    external_call' (external_calls_ops := empty_extcall_ops) WB ef ge args m t res m'.
    Proof.
      inversion EC; subst.
      econstructor; eauto using builtin_enabled_empty.
    Qed.

  Theorem step_asm_invariant `{memory_model_x: !Mem.MemoryModelX mem}:
    forall ge
           (Hge_external: forall b ef, Genv.find_funct_ptr ge b = Some (External ef) ->
                                       exists i sg, ef = EF_external i sg)
           rs m t rs' m',
      LAsm.step (lcfg_ops := LC L) ge (State rs m) t (State rs' m') ->
      AsmX.asm_invariant ge rs m ->
      AsmX.asm_invariant ge rs' m'.
  Proof.
    inversion 2; subst.
    - intros; eapply exec_instr_asm_invariant; eauto.
    - inversion 1; subst. apply nextinstr_nf_asm_invariant.
      inversion inv_inject_neutral; subst. 
      generalize H8. intro H8'.
      eapply external_call_inject_neutral' in H8'; eauto.
      destruct H8' as [HT1 HT2].
      split.
      split; auto.
      + etransitivity. eassumption.
        eapply external_call_nextblock'; eauto using builtin_enabled_empty'.
      + eapply set_regs_inject; eauto.
        eapply undef_regs_inject; eauto.
        intros; eapply (val_inject_incr (Mem.flat_inj (Mem.nextblock m))); eauto.
        apply flat_inj_inject_incr.
        eapply external_call_nextblock'; eauto using builtin_enabled_empty'.
      + inversion H8; subst.
        eapply set_regs_wt'. eapply encode_long_has_type.
        eapply Events.external_call_well_typed; eauto using builtin_enabled_empty.
        eapply undef_regs_wt; auto.
        assumption.
      + eapply val_list_inject_args; eauto.
    - intros. apply nextinstr_asm_invariant. 
      destruct H0. split; auto.
      inv inv_inject_neutral.
      split; eauto.
      + etransitivity. eassumption. eapply external_call_nextblock'; eauto using builtin_enabled_empty'.
      + eapply external_call_inject_neutral' in H9; eauto. eapply H9.
        eapply annot_args_inject_neutral in H8; eauto.
        apply list_forall2_val_list_inject; auto.
      + intros; eapply (val_inject_incr (Mem.flat_inj (Mem.nextblock m))); eauto.
        apply flat_inj_inject_incr. eapply external_call_nextblock'; eauto using builtin_enabled_empty'.
    - destruct (Hge_external _ _ H5) as [?[? Hef]].
      subst.
      pose proof H8 as Hext'.
      inv H8. pose proof H0 as Hext. inv H0. destruct H1 as [Hprim Hsem].
      inv Hsem. destruct H0 as [?[Hstencl[Hsigma[Hx1[Hx0 Ht]]]]]; subst. 
      pose proof (extcall_invariants_available x x3 Hprim) as Hinv.
      repeat (rewrite <- asm_invariant_equiv; eauto).
      pose proof I as H0.
      intros H1.
      inv H1.
      split.
      inv inv_inject_neutral. split; auto.
      + etransitivity. eassumption.
        destruct m, m'.
        lift_unfold.
        eapply external_call_inv_nextblock; eauto.
      + eapply external_call_inject_neutral; eauto. 
        eapply decode_longs_inject.
        eapply list_forall2_val_list_inject.
        eapply extcall_args_inject_neutral'; eauto.
        inv Hstencl. congruence.
      + assert(Hinject': forall r,
                           val_inject (Mem.flat_inj (Mem.nextblock m')) (rs r) (rs r)).
        {
          intros; eapply (val_inject_incr (Mem.flat_inj (Mem.nextblock m))); eauto.
          apply flat_inj_inject_incr. 
          destruct m, m'.
          lift_unfold.
          eapply external_call_inv_nextblock; eauto.
        }        
        intros. eapply undef_reg_inject. eapply set_reg_inject; eauto.
        eapply set_regs_inject; eauto. eapply undef_regs_inject; eauto.
        eapply undef_regs_inject; eauto.
        eapply encode_long_inject; eauto.
        eapply external_call_inject_neutral; eauto.
        eapply decode_longs_inject.
        eapply list_forall2_val_list_inject.
        eapply extcall_args_inject_neutral'; eauto.
        inv Hstencl. congruence.
      + eapply undef_reg_wt. eapply set_reg_wt.
        simpl; apply inv_reg_wt. 
        eapply set_regs_wt. eapply encode_long_has_type.
        eapply external_call_inv_well_typed in Hsigma.        
        unfold sextcall_sig, sextcall_res, csig_sig, proj_sig_res in *.
        destruct (sextcall_csig x3); destruct csig_res; simpl in *; auto.
        destruct f; auto.
        eapply undef_regs_wt; auto.
        eapply undef_regs_wt; auto.
    - inv H7. destruct H0 as [?[?[Hef[Hprim Hsem]]]].
      inv Hsem. pose proof (primcall_invariants_available _ _ Hprim) as Hinv.
      simpl in *.
      repeat (rewrite <- asm_invariant_equiv; eauto).
      eapply primitive_call_invariant; eauto.
  Qed.

  End EMPTYEXT.
    
End ASM_INVARIANT.

End ModuleSemantics_Asm_Invariant.
