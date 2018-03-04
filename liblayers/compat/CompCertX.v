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
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Errors.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcertx.driver.SeparateCompiler.
(* We should split this file into two parts, to separate the
   module compiler from its proof of correctness. *)
Require Import compcertx.driver.SeparateCompilerproof.
Require Import liblayers.compcertx.PTreeStencil.
Require Import liblayers.compcertx.MemWithData.
Require Import liblayers.lib.OptionMonad.
Require Import liblayers.logic.PTree.
Require Import liblayers.compat.CompatLayers.
Require Import liblayers.compat.CompatClightSem.
Require Import liblayers.compat.CompatAsmSem.

(** How to use CompCertX to compile modules from Clight to Asm. *)

  Definition transf_nzdef
             {A B}
             (transf_function: A -> res B)
  (z: nzdef (fundef := A) (vardef := AST.globvar Ctypes.type))
  :
    res (nzdef (fundef := B) (vardef := AST.globvar Ctypes.type))
    :=
      match z with
        | PTreeModules.function f =>
          match transf_function f with
            | OK f' => OK (PTreeModules.function f')
            | Error msg => Error msg
          end
        | variable v => OK (variable v)
        | magic => OK magic
      end.

(** We first construct the [fenv] function map for function
inlining, from an RTL "module" (PTree of RTL internal function
definitions).

The following definition selects a function for inlining.
 *)

Definition select_to_inline
           (i: ident)
           (z: nzdef (fundef := RTL.function) (vardef := AST.globvar Ctypes.type))
: option RTL.function :=
  match z with
    | PTreeModules.function f =>
      if Inlining.should_inline i f
      then Some f
      else None
    | _ => None
  end.

(** Thanks to this definition, we can now build the inlining environment. *)

Definition fenv
           (M: PTree.t (nzdef (fundef := RTL.function) (vardef := AST.globvar Ctypes.type)))
: Inlining.funenv :=
  PTree.map_option select_to_inline M.

(** Finally, we can define the CompCertX compiler on Clight modules. *)

Definition transf_module (M: ptree_module Clight.function (AST.globvar Ctypes.type)):
  res (ptree_module Asm.function (AST.globvar Ctypes.type)) :=
  let (Mt, X) := M in
  match PTree.map_error (fun _ => transf_nzdef transf_clight_function_to_rtl) Mt with
    | OK Mt1 =>
      match PTree.map_error (fun _ => transf_nzdef (transf_rtl_function (fenv Mt1))) Mt1 with
        | OK Mt' => OK (Mt', X)
        | Error msg => Error msg
      end
    | Error msg => Error msg
  end.

(** For the purpose of the proof, we can rewrite our compiler as follows: *)

Definition fenv_of_clight (M: ptree_module Clight.function (AST.globvar Ctypes.type)):
  res Inlining.funenv
  :=
    let (Mt, _) := M in
    match PTree.map_error (fun _ => transf_nzdef transf_clight_function_to_rtl) Mt with
      | OK Mt1 => OK (fenv Mt1)
      | Error msg => Error msg
    end.

Definition transf_module_with_fenv
           (fenv: Inlining.funenv)
           (M: ptree_module Clight.function (AST.globvar Ctypes.type))
  :=
  let (Mt, X) := M in
  match PTree.map_error (fun _ => transf_nzdef (transf_clight_function' fenv)) Mt with
    | OK Mt' => OK (Mt', X)
    | Error msg => Error msg
  end.

Definition transf_module'
           (M: ptree_module Clight.function (AST.globvar Ctypes.type)) :=
  match fenv_of_clight M with
    | OK fenv => transf_module_with_fenv fenv M
    | Error msg => Error msg
  end.

Lemma transf_module_eq_module'_ok:
  forall M M',
    transf_module M = OK M' ->
    transf_module' M = OK M'.
Proof.
  unfold transf_module, transf_module'.
  destruct M.
  intros.
  unfold transf_module_with_fenv.
  unfold fenv_of_clight.
  destruct (PTree.map_error (fun _ => transf_nzdef transf_clight_function_to_rtl) t) eqn:?; try discriminate.
  destruct (PTree.map_error (fun _ => transf_nzdef (transf_rtl_function (fenv t0))) t0) eqn:?; try discriminate.
  inv H.
  exploit PTree.map_compose_ok.
   eexact Heqr.
   eassumption.
   instantiate (1 := (fun _ => transf_nzdef (transf_clight_function' (fenv t0)))).
   simpl.
   destruct a; simpl.
   {
    intros.
    unfold transf_clight_function'.
    unfold ComposePasses.compose_partial, ComposePasses.apply_partial.
    destruct (transf_clight_function_to_rtl f) eqn:?; try discriminate.
    inv H0.
    assumption.
   }
   {
    inversion 2; subst.
    simpl. tauto.
   }
   {
     inversion 2; subst.
     simpl. tauto.
   }
   intro.
   rewrite H.
   reflexivity.
Qed.

Section WITH_FENV.

  Variable fenv: Inlining.funenv.

  Let transf_function := transf_clight_function' fenv.

  Let transf_fundef   := transf_clight_fundef' fenv.

  Let transf_varinfo := Cshmgen.transl_globvar.

  Variables (M1: ptree_module Clight.function (AST.globvar Ctypes.type))
            (M2: ptree_module Asm.function (AST.globvar Ctypes.type)).

  Hypothesis (compile_succeeds:
                transf_module_with_fenv fenv M1 = OK M2).

  Section WITHMEM.

  Context `{Hmem: Mem.MemoryModel} `{Hmem': !UseMemWithData mem}.

  Let transf_fundef_internal_complete:
    forall (f1: Clight.function)
           (f2: Asm.function),
      transf_function f1 = OK f2 ->
      transf_fundef (make_internal f1) = OK (make_internal f2).
  Proof.
    apply transf_clight_fundef_internal.
  Qed.

  Let transf_make_varinfo:
    forall lv,
      transf_varinfo (make_varinfo lv) = OK (make_varinfo lv).
  Proof.
    reflexivity.
  Qed.
  
  Context {D: compatdata}.

  Variable (L: compatlayer D).

  Let transf_layer_primitives:
               forall i σ,
                 ptree_layer_get L i = Some (primitive σ) ->
                 transf_fundef (CompatClightSem.make_external i σ) = OK (make_external i σ).
  Proof.
    intros.
    unfold make_external.
    unfold CompatClightSem.make_external.
    destruct σ as [σe | σp]; simpl;
    apply transf_clight_fundef_external; 
    reflexivity.
  Qed.

  Let transf_module_functions:
    forall i f1,
      ptree_module_get M1 i = Some (PTreeModules.function f1) ->
      exists f2, transf_function f1 = OK f2 /\
                 ptree_module_get M2 i = Some (PTreeModules.function f2).
  Proof.
    unfold transf_function.
    unfold transf_module_with_fenv in compile_succeeds.
    unfold ptree_module_get.
    destruct M1.
    destruct (PTree.map_error (fun _ => transf_nzdef (transf_clight_function' fenv)) t) eqn:?; try discriminate.
    intros.
    generalize (PTree.gmap_error_ok _ _ _ i _ _ Heqr).
    rewrite H.
    simpl.    
    destruct 1 as [? [FUN GET]].
    destruct (transf_clight_function' fenv f1); try discriminate.
    inv FUN.
    inv compile_succeeds.
    eauto.
  Qed.

  Let transf_module_variables:
       forall i v,
         ptree_module_get M1 i = Some (variable v) ->
         ptree_module_get M2 i = Some (variable v).
  Proof.
    unfold transf_module_with_fenv in compile_succeeds.
    unfold ptree_module_get.
    destruct M1.
    destruct (PTree.map_error (fun _ => transf_nzdef (transf_clight_function' fenv)) t) eqn:?; try discriminate.
    intros.
    generalize (PTree.gmap_error_ok _ _ _ i _ _ Heqr).
    rewrite H.
    simpl.
    destruct 1 as [? [VAR GET]].
    inv VAR.
    inv compile_succeeds.
    eauto.
  Qed.

  Let transf_module_none:
       forall i,
         ptree_module_get M1 i = None ->
         ptree_module_get M2 i = None.
  Proof.    
    unfold transf_module_with_fenv in compile_succeeds.
    unfold ptree_module_get.
    destruct M1.
    destruct (PTree.map_error (fun _ => transf_nzdef (transf_clight_function' fenv)) t) eqn:?; try discriminate.
    intros.
    generalize (PTree.gmap_error_ok _ _ _ i _ _ Heqr).
    rewrite H.
    simpl.
    intros.
    inv compile_succeeds.
    eauto.
  Qed.

  Lemma compcertx_syntax_correct_with_fenv:
    forall s p1
           (MAKE: make_program s M1 L = ret p1),
      exists p2,
        AST.transform_partial_program2
          transf_fundef transf_varinfo
          p1 = OK p2 /\
        make_program s M2 L = ret p2.
  Proof.
    eapply make_program_transform_partial2; eauto.
  Qed.

  End WITHMEM.

End WITH_FENV.

Theorem compcertx_syntax_correct_aux:
  forall
    (M1 : ptree_module Clight.function (globvar Ctypes.type))
    (M2 : ptree_module function (globvar Ctypes.type)),
    transf_module M1 = OK M2 ->
    forall {mem : Type} {memory_model_ops : Mem.MemoryModelOps mem}
           {Hmem' : UseMemWithData mem} {D : compatdata}
           (L : compatlayer D) (s : stencil)
           (p1 : AST.program Clight.fundef Ctypes.type),
      make_program s M1 L = ret p1 ->
      exists fenv,
        fenv_of_clight M1 = OK fenv /\
        exists p2 : AST.program fundef unit,
          transf_clight_program' fenv p1 = OK p2 /\ make_program s M2 L = ret p2.
Proof.
  intros.
  exploit transf_module_eq_module'_ok; eauto.
  unfold transf_module'.
  destruct (fenv_of_clight M1) eqn:?; try discriminate.
  intros.
  exploit compcertx_syntax_correct_with_fenv; eauto.
  destruct 1 as [? [? ?]].
  esplit.
  split.
  reflexivity.
  esplit.
  split.
  eapply transf_clight_fundef_to_program'.
  eassumption.
  assumption.
Qed.

Theorem compcertx_syntax_correct:
  forall
    (M1 : ptree_module Clight.function (globvar Ctypes.type))
    (M2 : ptree_module function (globvar Ctypes.type)),
    forall (TRANSF_MODULE: transf_module M1 = OK M2),
    forall {mem : Type} {memory_model_ops : Mem.MemoryModelOps mem}
           {Hmem' : UseMemWithData mem} {D : compatdata}
           (L : compatlayer D) (s : stencil)
           (p1 : AST.program Clight.fundef Ctypes.type),
      forall (MAKE_PROGRAM1: make_program s M1 L = ret p1),
      exists p_rtl fenv p2,
             transf_clight_program_to_rtl p1 = OK p_rtl /\            
             fenv_of_clight M1 = OK fenv /\             
             Inliningspec.fenv_compat (Genv.globalenv p_rtl) fenv /\
             transf_rtl_program fenv p_rtl = OK p2 /\
             transf_clight_program' fenv p1 = OK p2 /\
             make_program s M2 L = ret p2.
Proof.
  intros.
  exploit compcertx_syntax_correct_aux; eauto.
  destruct 1 as [var_x [K1 [var_x0 [K2 K3]]]].
  generalize K1. (* fenv_of_clight *)
  intro K4.
  unfold fenv_of_clight in K4.
  destruct M1 as [var_t var_b].
  destruct (PTree.map_error (fun _ => transf_nzdef transf_clight_function_to_rtl) var_t) as [ var_t0 | ] eqn:Keqr; try discriminate.
  inv K4.
  unfold transf_clight_program' in *.
  unfold ComposePasses.apply_partial in *.
  destruct (transf_clight_program_to_rtl p1) as [ var_p | ] eqn:Keqr0; try discriminate.
  esplit. esplit. esplit.
  split. reflexivity.
  split. eassumption.
  split.
  2: split.
  2: eassumption.
  2: split.
  2: assumption.
  2: assumption.
  intro var_id. intros var_b0 var_f K4.
  unfold fenv in K4.
  unfold make_program in MAKE_PROGRAM1.
  inv_monad MAKE_PROGRAM1.
  subst.
  exploit transf_clight_program_to_rtl_fundef; eauto.
  intro K0.
  destruct (var_t0 ! var_id) as [ var_n | ] eqn:Keqo.
  {
    exploit PTree.gmap_option_some; eauto.
    instantiate (1 := select_to_inline). rewrite K4. unfold select_to_inline.    
    destruct var_n as [ var_f0 | ? | ] ; try discriminate.
    destruct (Inlining.should_inline var_id var_f0); try discriminate.
    inversion 1; subst.
    exploit PTree.gmap_error_ok; eauto.
    instantiate (1 := var_id).
    rewrite Keqo.
    destruct (var_t ! var_id) as [ var_n | ] eqn:Keqo0; try discriminate.
    destruct 1 as [var_x7 [K14 K15]].
    inv K15.
    destruct var_n as [ var_f | | ]; try discriminate.
    simpl in K14.
    destruct (transf_clight_function_to_rtl var_f) as [ var_f1 | ] eqn:Keqr1; try discriminate.
    inv K14.
    simpl in *.
    match goal with
      | [ x2: ptree_forall (fun i _ => In i (stencil_ids s)) var_t
        |- _ ] =>
        assert (K14: In var_id (stencil_ids s)) by (eapply x2; eauto)
    end.
    generalize (in_map (ptree_get_globdef L (var_t, var_b)) _ _ K14).
    unfold ptree_get_globdef at 1.
    unfold ptree_layer_get_globdef.
    destruct (ptree_layer_get L var_id) as [ var_n | ] eqn:Keqo1.
    {
     exfalso.
     match goal with
       | [ x: ptree_disjoint L var_t |- _ ] =>
         generalize (x _ _ Keqo1);
           congruence
     end.
    }
    unfold ptree_module_get_globdef.
    unfold ptree_module_get.
    rewrite Keqo0.
    intros K13 K15.
    exploit Genv.find_funct_ptr_exists.
    instantiate (1 := unsafe_make_program s L (var_t, var_b)).
    rewrite unsafe_make_prog_defs_names.
    apply stencil_ids_norepet.
    eassumption.
    destruct 1 as [var_x7 [K16 K17]].
    erewrite <- Genv.find_symbol_transf_partial2 in K16; eauto.
    replace var_x7 with var_b0 in * by congruence.
    exploit Genv.find_funct_ptr_transf_partial2; eauto.
    simpl.
    destruct 1 as [var_x8 [K18 K19]].
    exploit transf_clight_function_to_rtl_internal; eauto.
    intro K20.
    rewrite K19 in K20; inv K20.
    assumption.
  }
  generalize (PTree.gmap_option_none _ _ select_to_inline _ _ Keqo).
  intro; congruence.
Qed.  
  
