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

(** ** Properties of LAsm modules *)

Section ModuleSemantics_Prop.

  Context `{Hobs: Observation}.
  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModel}.
  Context `{Hmwd: UseMemWithData mem}.

  Context `{make_program_ops: !MakeProgramOps function Ctypes.type fundef unit}.
  Context `{make_program_prf: !MakeProgram function Ctypes.type fundef unit}.

(** Monotonicity lemmas *)

(** Monotonicity wrt. modules *)

Section WITHLAYER.

  Context `{BUILTIN_IDENTS_NOREPET: CompCertBuiltins.BuiltinIdentsNorepet}.

  Context {D: compatdata}.
  Variable (L: compatlayer D).

  Lemma external_call_spec:
    forall ef,
      builtin_enabled (compiler_config_ops := compatlayer_compiler_config_ops L) ef ->
      extcall_properties (external_call (external_calls_ops := compatlayer_extcall_ops L) ef) (ef_sig ef).
  Proof.
    destruct ef; simpl; intros; try contradiction.
    * apply CompCertBuiltins.builtin_functions_properties.
    * apply volatile_load_ok.
    * apply volatile_store_ok.
    * apply volatile_load_global_ok.
    * apply volatile_store_global_ok.
    * apply extcall_malloc_ok.
    * apply extcall_free_ok.
    * apply extcall_memcpy_ok.
    * apply extcall_annot_ok.
    * apply extcall_annot_val_ok.
    * split; contradiction.
  Qed.

  Definition builtin_is_enabled (ef: external_function) : 
    {builtin_enabled (compiler_config_ops := compatlayer_compiler_config_ops L) ef} + {~ builtin_enabled (compiler_config_ops := compatlayer_compiler_config_ops L) ef}.
  Proof.
    unfold builtin_enabled.
    destruct ef; try (left; exact I).
    simpl.
    right. clear. tauto.
  Defined.

  Variables (ge1 ge2: LAsm.genv).
  Hypothesis (Hgele: ge1 ≤ ge2).

  (** We need to amend CompcertStructures.genv_le with the following. *)
  Hypothesis SYMB: forall i, Genv.find_symbol ge2 i = Genv.find_symbol ge1 i.
  Hypothesis GENV_NEXT: Genv.genv_next ge2 = Genv.genv_next ge1.
  Hypothesis VOLATILE: forall b, Events.block_is_volatile ge2 b = Events.block_is_volatile ge1 b.

  Lemma compatsem_extcall_symbols_preserved:
    forall x sg WB args m t v0 m',
      compatsem_extcall (D := D) x sg WB _ _ ge1 args m t v0 m' ->
      compatsem_extcall x sg WB fundef unit ge2 args m t v0 m'.
  Proof.
    inversion 1; subst.
    inversion H0.
    inversion H1.
    econstructor; eauto.
    esplit.
    split.
    eapply stencil_matches_preserves_symbols. 4: eassumption.
    auto.
    auto.
    auto.
    eauto.
  Qed.

  Theorem external_call_symbols_preserved':
    forall ef args m t v m',
      external_call' (external_calls_ops := compatlayer_extcall_ops L) (fun _ : block => True) ef ge1 args m t
                     v m' ->
      external_call' (external_calls_ops := compatlayer_extcall_ops L) (fun _ : block => True) ef ge2 args m t
                     v m'.
  Proof.
    intros.
    inversion H; subst.
    destruct (builtin_is_enabled ef).
    * (* enabled *)
      econstructor; eauto.
      eapply ec_symbols_preserved; eauto using external_call_spec.
    * (* external *)
      destruct ef; simpl in n; revert n; try (clear; tauto).
      intros _.
      inversion H0; subst.
      destruct H1.
      simpl in H2.
      econstructor; eauto.
      econstructor; eauto using compatsem_extcall_symbols_preserved.
  Qed.

  Context `{acc_def_prf: !AccessorsDefined L}.

  Global Existing Instance exec_load_spec.
  Global Existing Instance exec_store_spec.

  Theorem exec_instr_symbols_preserved:
    forall
      rs m      
      f i,
      LAsm.exec_instr (lcfg_ops := LC L) ge2 f i rs m = LAsm.exec_instr (lcfg_ops := LC L) ge1 f i rs m.
  Proof.
    destruct i; try reflexivity; simpl; intros;
    eauto using AsmX.exec_instr_symbols_preserved,
    exec_load_symbols_preserved,
    exec_store_symbols_preserved.
    erewrite AsmX.symbol_offset_symbols_preserved; eauto.
  Qed.
      
  Theorem module_le_step:
    forall s t s',
      LAsm.step (lcfg_ops := LC L) ge1 s t s' ->
      LAsm.step (lcfg_ops := LC L) ge2 s t s'.
  Proof.
    inversion 1; subst.
    * (* internal *)
      erewrite <- exec_instr_symbols_preserved in H3; eauto.
      econstructor; eauto.
      eapply CompcertStructures.genv_le_find_funct_ptr_some; eauto.
    * (* builtin *)
      eapply exec_step_builtin; eauto using CompcertStructures.genv_le_find_funct_ptr_some,
                                external_call_symbols_preserved'.
    * (* annot *)
      eapply exec_step_annot; eauto using CompcertStructures.genv_le_find_funct_ptr_some,
                                external_call_symbols_preserved'.
    * (* external *)
      eapply exec_step_external; eauto using CompcertStructures.genv_le_find_funct_ptr_some,
                                external_call_symbols_preserved'.
      rewrite GENV_NEXT; eauto.
    * (* primitive *)
      simpl in H2.
      destruct H2 as [? [? [? [? [? ?]]]]].
      eapply exec_step_prim_call; eauto using CompcertStructures.genv_le_find_funct_ptr_some.
      econstructor. esplit. esplit.
      split; eauto.
      split; eauto.
      inversion H4; subst.
      econstructor; eauto.
      eapply stencil_matches_preserves_symbols. 4: eassumption.
      auto.
      auto.
      auto.
  Qed.

End WITHLAYER.

(** Vertical composition *)

Section WITH2LAYERS.

  Context `{BUILTIN_IDENTS_NOREPET: CompCertBuiltins.BuiltinIdentsNorepet}.

  Context {D: compatdata}.
  Variables (L1 L2: compatlayer D).

  Variables (ge1 ge2: LAsm.genv).

  Hypothesis SYMB: forall i, Genv.find_symbol ge2 i = Genv.find_symbol ge1 i.
  Hypothesis GENV_NEXT: Genv.genv_next ge2 = Genv.genv_next ge1.
  Hypothesis VOLATILE: forall b, Events.block_is_volatile ge2 b = Events.block_is_volatile ge1 b.

  Context `{acc_def_prf1: !AccessorsDefined L1}.
  Context `{acc_def_prf2: !AccessorsDefined L2}.

  Hypothesis exec_load_preserved:
    forall chunk m a rs r rs' m',
    acc_exec_load L1 _ _ ge1 chunk m a rs r = Next rs' m' ->
    acc_exec_load L2 _ _ ge2 chunk m a rs r = Next rs' m'.

  Hypothesis exec_store_preserved:
    forall chunk m a rs r rl rs' m',
    acc_exec_store L1 _ _ ge1 chunk m a rs r rl = Next rs' m' ->
    acc_exec_store L2 _ _ ge2 chunk m a rs r rl = Next rs' m'.

  Theorem exec_instr_replaced:
    forall
      rs m      
      f i
      rs' m',
      LAsm.exec_instr (lcfg_ops := LC L1) ge1 f i rs m = Asm.Next rs' m' ->
      LAsm.exec_instr (lcfg_ops := LC L2) ge2 f i rs m = Asm.Next rs' m'.
  Proof.
    destruct i; try tauto; simpl; intros; eauto.
    * destruct i; try tauto; simpl; intros; eauto.
      + erewrite AsmX.symbol_offset_symbols_preserved; eauto.
      + erewrite AsmX.eval_addrmode_symbols_preserved; eauto.
      + erewrite AsmX.symbol_offset_symbols_preserved; eauto.
      + erewrite AsmX.symbol_offset_symbols_preserved; eauto.
    * erewrite AsmX.symbol_offset_symbols_preserved; eauto.
  Qed.

  Hypothesis internal_functions_preserved:
    forall b f,
      Genv.find_funct_ptr ge1 b = Some (Internal f) ->
      Genv.find_funct_ptr ge2 b = Some (Internal f).

  Hypothesis builtin_functions_preserved:
    forall b ef,
      Genv.find_funct_ptr ge1 b = Some (External ef) ->
      match ef with
        | EF_external _ _ => False
        | _ => True
      end ->
      Genv.find_funct_ptr ge2 b = Some (External ef).

  Hypothesis external_functions_replaced:
    forall b i sg,
      Genv.find_funct_ptr ge1 b = Some (External (EF_external i sg)) ->
      forall σ,
        get_layer_primitive i L1 = Errors.OK (Some (compatsem_inl σ)) ->
        Genv.find_funct_ptr ge2 b = Some (External (EF_external i sg)) /\
        get_layer_primitive i L2 = Errors.OK (Some (compatsem_inl σ)).

  Hypothesis primcall_replaced:
    forall b i sg,
      Genv.find_funct_ptr ge1 b = Some (External (EF_external i sg)) ->
      forall σ,
        get_layer_primitive i L1 = Errors.OK (Some (compatsem_inr σ)) ->
        forall s,
          stencil_matches s ge1 ->
          forall rs,
            rs PC = Vptr b Int.zero ->
            forall m rs' m',
              sprimcall_step σ s rs m rs' m' ->
              plus (LAsm.step (lcfg_ops := LC L2)) ge2 (Asm.State rs m) E0 (Asm.State rs' m').

  Theorem vcomp_step:
    forall s t s',
      LAsm.step (lcfg_ops := LC L1) ge1 s t s' ->
      plus (LAsm.step (lcfg_ops := LC L2)) ge2 s t s'.
  Proof.
    inversion 1; subst.
    * (* internal *)
      apply plus_one.
      econstructor; eauto using exec_instr_replaced.
    * (* builtin *)
      inversion H3; subst.
      apply plus_one.
      eapply exec_step_builtin; eauto.
      econstructor; eauto.
      eapply ec_symbols_preserved.
      eapply external_call_spec; eauto.
      eassumption.
      assumption.
      assumption.
      destruct ef; try contradiction; assumption.
    * (* annot *)
      inversion H4; subst.
      apply plus_one.
      eapply exec_step_annot; eauto.
      econstructor; eauto.
      eapply ec_symbols_preserved.
      eapply external_call_spec; eauto.
      eassumption.
      assumption.
      assumption.
      destruct ef; try contradiction; eassumption.
    * (* external *)
      inversion H3; subst.
      destruct (builtin_is_enabled L1 ef).
      + (* builtin *)
        apply plus_one.
        eapply exec_step_external; eauto.
        econstructor; eauto.
        eapply ec_symbols_preserved.
        eapply external_call_spec; eauto.
        eassumption.
        assumption.
        assumption.
        destruct ef; try contradiction; eassumption.
        rewrite GENV_NEXT; assumption.
      + (* external *)
        destruct ef; try (exfalso; revert n; clear; simpl; tauto).
        inversion H4; subst.
        destruct H5 as [H5 H6].
        inversion H6; subst.
        destruct H7 as [? [? [? [? [? ?]]]]]; subst.
        exploit external_functions_replaced; eauto.
        destruct 1.
        apply plus_one.
        eapply exec_step_external; eauto.
        - econstructor; eauto.
          simpl.
          esplit. split; eauto.
          econstructor.
          esplit. split; eauto using stencil_matches_preserves_symbols.
        - rewrite GENV_NEXT; assumption.
    * inversion H2; subst.
      destruct H3 as [? [? [? [? SEM]]]].
      subst.
      inversion SEM; subst.
      eauto.
  Qed.

End WITH2LAYERS.

(** Monotonicity wrt. layers for "syntactic" order *)

Section WITH2LAYERS2.

  Context `{BUILTIN_IDENTS_NOREPET: CompCertBuiltins.BuiltinIdentsNorepet}.

  Context {D: compatdata}.
  Variables (L1 L2: compatlayer D).

  Context `{acc_def_prf1: !AccessorsDefined L1}.
  Context `{acc_def_prf2: !AccessorsDefined L2}.

  Variable (ge: LAsm.genv).

  Hypothesis exec_load_preserved:
    forall chunk m a rs r rs' m',
    acc_exec_load L1 _ _ ge chunk m a rs r = Next rs' m' ->
    acc_exec_load L2 _ _ ge chunk m a rs r = Next rs' m'.

  Hypothesis exec_store_preserved:
    forall chunk m a rs r rl rs' m',
    acc_exec_store L1 _ _ ge chunk m a rs r rl = Next rs' m' ->
    acc_exec_store L2 _ _ ge chunk m a rs r rl = Next rs' m'.

  Hypothesis layer_valid:
    forall s, stencil_matches s ge -> get_layer_prim_valid L2 s.

  Hypothesis get_layer_primitive_le:
    forall i σ,
      get_layer_primitive i L1 = Errors.OK (Some σ) ->
      exists σ', get_layer_primitive i L2 = Errors.OK (Some σ')
                 /\ compatsem_le D σ σ'.

  Theorem layer_le_step:
    forall s t s',
      LAsm.step (lcfg_ops := LC L1) ge s t s' ->
      LAsm.step (lcfg_ops := LC L2) ge s t s'.
  Proof.
    inversion 1; subst.
    * (* internal *)
      econstructor; eauto.
      eapply (exec_instr_replaced L1 L2); eauto.
    * (* builtin *)
      inversion H3; subst.
      eapply exec_step_builtin; eauto.
      econstructor; eauto.
      destruct ef; try contradiction; assumption.
    * (* annot *)
      inversion H4; subst.
      eapply exec_step_annot; eauto.
      econstructor; eauto.
      destruct ef; try contradiction; eassumption.
    * (* external *)
      inversion H3; subst.
      destruct (builtin_is_enabled L1 ef).
      + (* builtin *)
        eapply exec_step_external; eauto.
        econstructor; eauto.
        destruct ef; try contradiction; eassumption.
      + (* external *)
        destruct ef; try (exfalso; revert n; clear; simpl; tauto).
        inversion H4; subst.
        destruct H5 as [H5 H6].
        inversion H6; subst.
        destruct H7 as [? [? [? [? [? ?]]]]]; subst.
        eapply exec_step_external; eauto.
        econstructor; eauto.
        eapply get_layer_primitive_le in H5.
        destruct H5 as [?[Hlayer Hle]].
        esplit. split; eauto.
        eapply compatsem_extcall_le; eauto.
        inv Hle. simpl. 
        intros.
        specialize (layer_valid _ H5).
        unfold get_layer_prim_valid in *.
        specialize (layer_valid _ _ Hlayer).
        apply layer_valid.
    * (* primitive *)
      inversion_clear H2; subst.
      destruct H3 as [? [? [? [? SEM]]]].
      subst.
      inversion SEM; subst.
      eapply exec_step_prim_call; eauto.
      eapply get_layer_primitive_le in H3.
      destruct H3 as [?[Hlayer Hle]].
      econstructor. refine_split'; eauto.
      eapply compatsem_primcall_le; eauto 1.
      intros.
      specialize (layer_valid _ H3).
      unfold get_layer_prim_valid in *.
      specialize (layer_valid _ _ Hlayer).
      inv Hle.
      apply layer_valid.
  Qed.

End WITH2LAYERS2.

End ModuleSemantics_Prop.
