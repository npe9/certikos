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
Require Import Errors.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import SmallstepX.
Require SeparateCompilerproof.
Require Import Decision.
Require Import MemWithData.
Require Import liblayers.compat.CompatData.
Require Import Stencil.
Require Import MakeProgram.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatExternalCalls.
Require Import liblayers.compat.I64Layer.
Require Import liblayers.logic.PTreeSemantics.
Require Import liblayers.compat.CompatClightSem.
Require LAsmgenproof.
Require Import LAsmModuleSem.
Require Import CompCertiKOS.
Require Import LiftValueAnalysis.
Require Import LiftDeadcodeproof.
Require Import CompCertiKOSproof.

Require StencilImpl.
Require MakeProgramImpl.

Opaque fmap.

Local Existing Instance StencilImpl.ptree_stencil_ops.
Local Existing Instance StencilImpl.ptree_stencil_prf.

Local Instance clight_make_program_ops:
  forall
         mem (memory_model_ops: Mem.MemoryModelOps mem)
         (Hmwd: UseMemWithData mem),
  MakeProgram.MakeProgramOps Clight.function
                             Ctypes.type Clight.fundef Ctypes.type.
Proof.
  intros; eapply MakeProgramImpl.make_program_ops.
Defined.

Local Instance lasm_make_program_ops:
  forall
         mem (memory_model_ops: Mem.MemoryModelOps mem)
         (Hmwd: UseMemWithData mem),
 MakeProgramOps LAsm.function Ctypes.type LAsm.fundef unit.
Proof.
  intros; eapply MakeProgramImpl.make_program_ops.
Defined.

Local Instance clight_make_program_prf:
  forall
         mem (memory_model_ops: Mem.MemoryModelOps mem)
         (Hmwd: UseMemWithData mem)
         (memory_model_x_prf: Mem.MemoryModelX mem),
  MakeProgram Clight.function Ctypes.type Clight.fundef Ctypes.type.
Proof.
  intros; eapply MakeProgramImpl.make_program_prf.
Qed.

Local Instance lasm_make_program_prf:
  forall
         mem (memory_model_ops: Mem.MemoryModelOps mem)
         (Hmwd: UseMemWithData mem)
         (memory_model_x_prf: Mem.MemoryModelX mem),
 MakeProgram LAsm.function Ctypes.type LAsm.fundef unit.
Proof.
  intros; eapply MakeProgramImpl.make_program_prf.
Qed.

Lemma get_module_function_transf_some_strong:
  forall M1 M2,
    transf_module M1 = OK M2 ->
    forall (i: ident) f1,
      get_module_function i M1 = OK (Some f1) ->
      exists f2,
        get_module_function i M2 = OK (Some f2) /\
        exists fenv,
          fenv_of_clight M1 = OK fenv /\
          transf_clight_function' fenv f1 = OK f2.
Proof.
  intros until M2. intros TRANSF.
  apply  transf_module_eq_module'_ok in TRANSF.
  unfold transf_module' in TRANSF.
  destruct (fenv_of_clight M1); try discriminate.
  intro i.
  unfold transf_module_with_fenv in TRANSF.
  inv_monad TRANSF; subst.
  generalize (PTrees.PTree.gmap_error_ok _ _ _ i _ _ H0).
  Transparent PTreeModules.ptree_module_ops. simpl.
  unfold PTreeModules.ptree_module_function.
  destruct (Maps.PTree.get i (fst M1)); try discriminate.
  destruct r as [|]; try discriminate; simpl.
  destruct 1 as [? [? HM2]].
  rewrite HM2.
  inversion 1; subst.
  simpl in *; monad_norm; simpl in *.
  unfold transf_nzdef in H.
  inv_monad H; subst.
  exists x2.
  simpl.
  eauto.
Qed.

   (** Additional properties needed by [make_program] *)

Section WITHMEM.

Context {mem} {memory_model_ops: Mem.MemoryModelOps mem}
        {Hmwd: UseMemWithData mem}.

Lemma transf_fundef_internal_complete:
  forall f: Inlining.funenv,
  forall (f1 : Clight.function) (f2 : LAsm.function),
    transf_clight_function' f f1 = OK f2 ->
    forall fp1 : Clight.fundef,
      make_internal f1 = OK fp1 ->
      exists fp2 : LAsm.fundef,
        make_internal f2 = OK fp2 /\ transf_clight_fundef' f fp1 = OK fp2.
Proof.
  inversion 2; subst; simpl;
  eauto using transf_clight_fundef_internal.
Qed.

Lemma transf_module_functions:
  forall M1 M2,
    transf_module M1 = OK M2 ->
    forall f, fenv_of_clight M1 = OK f ->
  forall (i : ident) (f1 : Clight.function),
   get_module_function i M1 = OK (Some f1) ->
   exists f2 : LAsm.function,
     transf_clight_function' f f1 = OK f2 /\
     get_module_function i M2 = OK (Some f2).
Proof.
  intros. exploit get_module_function_transf_some_strong; eauto.
  destruct 1 as (? & ? & fenv & ? & ?).
  replace fenv with f in * by congruence.
  eauto.
Qed.

Lemma make_program_transf_module_recip:
      forall M1 M2,
        transf_module M1 = OK M2 ->
        forall s D L,
          isOK (make_program (D := D) s M2 L) ->
          isOK (make_program s M1 L)
    .
Proof.
  intros until L.
  generalize (transf_module_eq_module'_ok _ _ H).
  unfold transf_module'.
  destruct (fenv_of_clight M1) eqn:?; try discriminate.
  intro.
  eapply MakeProgramImpl.make_program_transf_partial2_ok_recip.
  * eapply transf_fundef_internal_complete with (f := f).
  * apply transf_module_functions; auto.
  * eapply get_module_function_transf_none; eauto.
  * eapply get_module_variable_transf; eauto.
  * simpl. unfold isOK. eauto.
  * destruct 1. exploit get_module_function_transf_error; eauto.
    simpl. intro ERR. rewrite ERR. unfold isError; eauto.
  * simpl. destruct 3. discriminate.
Qed.

Lemma make_program_transf_module:
      forall M1 M2,
        transf_module M1 = OK M2 ->
        forall s D L x,
          make_program (D := D) s M1 L = ret x ->
          exists x_rtl,
            SeparateCompiler.transf_clight_program_to_rtl x = OK x_rtl /\
            exists fenv,
              Inliningspec.fenv_compat (Genv.globalenv x_rtl) fenv /\
              exists x_lasm,
                CompCertiKOS.transf_rtl_program fenv x_rtl = OK x_lasm /\
                make_program s M2 L = ret x_lasm.
Proof.
  intros.
  generalize (transf_module_eq_module'_ok _ _ H).
  unfold transf_module'.
  destruct (fenv_of_clight M1) eqn:?; try discriminate.
  intro.
  exploit (MakeProgramImpl.make_program_transf_partial2 (transf_clight_function' f)).
  * eapply transf_fundef_internal_complete with (f := f).
  * instantiate (1 := Cshmgen.transl_globvar). reflexivity.
  * instantiate (1 := D). instantiate (1 := L).
    simpl. inversion 2; subst.
    esplit. split. reflexivity.
    destruct s0;
      eapply transf_clight_fundef_external;
      symmetry;
      eauto using signature_of_type_correct.
  * eapply transf_module_functions; eauto.
  * apply get_module_function_transf_none; auto.
  * apply get_module_variable_transf; auto.
  * simpl in H0. eassumption.
  * {
      destruct 1 as (p2 & TRANSF & MAKE2).
      apply transf_clight_fundef_to_program' in TRANSF.
      unfold transf_clight_program' in TRANSF.
      unfold ComposePasses.apply_total, ComposePasses.apply_partial in TRANSF.
      unfold SeparateCompiler.transf_clight_program' in TRANSF.
      unfold ComposePasses.apply_total, ComposePasses.apply_partial in TRANSF.
      destruct (SeparateCompiler.transf_clight_program_to_rtl x) eqn:TRANSFC; try discriminate.
      destruct (SeparateCompiler.transf_rtl_program f p) eqn:TRANSFR; try discriminate.
      inv TRANSF.
      esplit. split; try reflexivity.
      unfold transf_rtl_program. simpl.
      unfold ComposePasses.apply_total, ComposePasses.apply_partial.
      exists f.
      rewrite TRANSFR.
      split; eauto.
      unfold Inliningspec.fenv_compat. intros.
      unfold fenv_of_clight in Heqr. 
      destruct (PTrees.PTree.map_error _ _) eqn:TRANSFCF; try discriminate.
      inv_monad Heqr; subst.
      unfold fenv in H2.
      generalize TRANSFC.
      intro TRANSFC'.
      apply SeparateCompiler.transf_clight_program_to_rtl_fundef in TRANSFC'.
      destruct (Maps.PTree.get id x0) eqn:GET.
      {
        generalize GET.
        intro GET'.
        apply (PTrees.PTree.gmap_option_some _ _ select_to_inline) in GET'.
        rewrite H2 in GET'.
        unfold select_to_inline in GET'.
        destruct r as [|]; try discriminate.
        simpl in GET'; monad_norm.
        destruct (Inlining.should_inline id f); try discriminate.
        inv GET'.
        clear H2.
        apply PTrees.PTree.gmap_error_ok with (i := id) in TRANSFCF.
        destruct (Maps.PTree.get id (fst M1)) eqn:GETM.
        {
          destruct TRANSFCF as (? & TRANSFCF & GET2).
          rewrite GET2 in GET.
          inv GET.
          unfold transf_nzdef in TRANSFCF.
          inv_monad TRANSFCF; subst.
          inv TRANSFCF.
          apply SeparateCompiler.transf_clight_function_to_rtl_internal in H4.
          exploit (MakeProgramImpl.make_globalenv_module_function s M1 L x id x1); auto.
          {
            unfold get_module_function. simpl.
            unfold PTreeModules.ptree_module_function.
            rewrite GETM.
            reflexivity.
          }
          destruct 1 as (? & HMAKE1 & b0 & SYMB & FUNC).
          inv HMAKE1.
          assert (b0 = b).
          {
            unfold SeparateCompiler.transf_clight_program_to_rtl in TRANSFC.
            unfold ComposePasses.apply_total, ComposePasses.apply_partial in TRANSFC.
            destruct (Cshmgen.transl_program x) eqn:?; try discriminate.
            destruct (Cminorgen.transl_program p1) eqn:?; try discriminate.
            destruct (RTLgen.transl_program (SelectionX.sel_program p2)) eqn:RTLGEN; try discriminate.
            inv TRANSFC.
            revert SYMB.
            erewrite <- Cshmgenproof.symbols_preserved; eauto.
            erewrite <- Cminorgenproof.symbols_preserved; eauto.
            erewrite <- Selectionproof.symbols_preserved.
            instantiate (1 := I64helpers.hf).
            instantiate (1 := fun _ => None).
            erewrite <- RTLgenproof.symbols_preserved; eauto.
            rewrite <- Tailcallproof.symbols_preserved.
            congruence.
          }
          subst.
          exploit Genv.find_funct_ptr_transf_partial2; eauto.
          destruct 1 as (? & ? & TRANSF).
          rewrite H4 in TRANSF.
          inv TRANSF.
          assumption.
        }
        exfalso.
        congruence.
      }
      exfalso.
      apply (PTrees.PTree.gmap_option_none _ _ select_to_inline) in GET.
      congruence.
    }
Qed.

End WITHMEM.

Require MemimplX.
Require ValueDomainImplX.
Require ValueAnalysisImplX.
Require DeadcodeproofImplX.

Global Instance compcertikos_ops: CompCertiKOSOps.
Proof.
  esplit.
  eapply clight_make_program_ops.
  eapply lasm_make_program_ops.
  eapply ValueDomainImpl.mmatch_ops.
  eapply DeadcodeproofImplX.magree_ops.
  Grab Existential Variables.
  constructor.
Defined.

Global Instance compcertikos_prf:
  CompCertiKOS.
Proof.
  intros.
  constructor.
  eapply StencilImpl.ptree_stencil_prf.
  eapply MemimplX.memory_model_x.
  eapply clight_make_program_prf.
  eapply MemimplX.memory_model_x.
  eapply lasm_make_program_prf.
  eapply MemimplX.memory_model_x.
  eapply ValueAnalysisImpl.mmatch_constructions.
  eapply DeadcodeproofImplX.magree_prf.
  constructor. match goal with |- list_norepet ?l => destruct (list_norepet_dec peq l) eqn:?; auto; discriminate end.
  eapply make_program_transf_module_recip.
  eapply make_program_transf_module.
Qed.
