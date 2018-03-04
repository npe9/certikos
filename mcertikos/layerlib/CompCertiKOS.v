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
(** The CompCertiKOS verified compiler, from CompCertX ClightX to per-function/module CertiKOS LAsm. *)

Require SeparateCompiler.
Require LAsmgen.

Import Errors.
Import AST.
Import ComposePasses.

Definition transf_rtl_program
           (fenv: Inlining.funenv)
           (p: RTL.program): res LAsm.program := 
  OK p
     @@@ (SeparateCompiler.transf_rtl_program fenv)
     @@ LAsmgen.transf_program.

(** Now, let's prove that our compiler is a per-function compiler 
    (given an inlining parameter, which we do not care about how
    it is computed). *)

Definition transf_rtl_fundef (fenv: Inlining.funenv): 
  forall (f: RTL.fundef), res LAsm.fundef :=
  (SeparateCompiler.transf_rtl_fundef fenv)
    ;> LAsmgen.transf_fundef.

(** Auxiliary functions. These functions should be used only in proofs, and should not be extracted,
    because if the computation of [fenv] is based on [transf_clight_fundef_to_rtl], then
    using [transf_clight_fundef_to_lasm'] will call [transf_clight_fundef_to_rtl] twice. *)

Definition transf_clight_fundef' (fenv: Inlining.funenv):
  forall (f: Clight.fundef), res LAsm.fundef :=
  (SeparateCompiler.transf_clight_fundef' fenv)
    ;> LAsmgen.transf_fundef.

Definition transf_clight_program' (fenv: Inlining.funenv)
           (p: Clight.program): res LAsm.program :=
  OK p 
     @@@ (SeparateCompiler.transf_clight_program' fenv)
     @@ LAsmgen.transf_program.

Lemma transf_rtl_fundef_to_program:
  forall fenv p tp,
    transform_partial_program (transf_rtl_fundef fenv) p = OK tp ->
    transf_rtl_program fenv p = OK tp.
Proof.
  unfold transf_rtl_fundef, transf_rtl_program.
  intros.
  repeat SeparateCompiler.compose_elim.
  eapply apply_partial_intro; eauto using SeparateCompiler.transf_rtl_fundef_to_program.
Qed.

Lemma transf_clight_fundef_to_program':
  forall fenv p tp,
    transform_partial_program2 (transf_clight_fundef' fenv) Cshmgen.transl_globvar p = OK tp ->
    transf_clight_program' fenv p = OK tp.
Proof.
  unfold transf_clight_program', transf_clight_fundef'. intros.  
  replace (Cshmgen.transl_globvar) with (Cshmgen.transl_globvar ;;; (fun v => OK v)) in H by reflexivity.
  eapply transform_partial_program2_compose_in_out in H. SeparateCompiler.compose_elim.
  match type of Hbc with
    | transform_partial_program2 ?tf ?tv ?b = _ =>
      change (transform_partial_program2 tf tv b) with (transform_partial_program tf b) in Hbc
  end.
  simpl.
  unfold apply_partial.
  erewrite SeparateCompiler.transf_clight_fundef_to_program'; eauto.
  simpl. f_equal.
  rewrite transform_program_partial_program in Hbc.
  inversion Hbc; subst.
  reflexivity.
Qed.

Lemma transf_rtl_program_to_fundef:
  forall fenv p tp,
    transf_rtl_program fenv p = OK tp ->
    transform_partial_program (transf_rtl_fundef fenv) p = OK tp.
Proof.
  unfold transf_rtl_program, transf_rtl_fundef.
  intros.
  repeat SeparateCompiler.apply_elim.
  repeat SeparateCompiler.compose_intro.
  eauto using SeparateCompiler.transf_rtl_program_to_fundef.
Qed.

Lemma transf_clight_program_to_fundef':
  forall fenv p tp,
    transf_clight_program' fenv p = OK tp ->
    transform_partial_program2 (transf_clight_fundef' fenv) Cshmgen.transl_globvar p = OK tp.
Proof.
  unfold transf_clight_program', transf_clight_fundef'.
  intros.
  repeat SeparateCompiler.apply_elim.
  replace (Cshmgen.transl_globvar) with (Cshmgen.transl_globvar ;;; (fun v => OK v)) by reflexivity.
  eapply transform_partial_program2_compose_out_in.
  eapply compose_partial_intro.
  eapply SeparateCompiler.transf_clight_program_to_fundef'; eauto.
  eapply transform_program_partial_program.
Qed.

(** Now, let's prove that our compiler does not change well-typed external functions *)

Theorem transf_clight_fundef_external:
  forall fenv ef tl ty cc,
    ef_sig ef = Ctypes.signature_of_type tl ty cc ->
    transf_clight_fundef' fenv (Clight.External ef tl ty cc) = OK (AST.External ef).
Proof.  
  unfold transf_clight_fundef'.
  unfold compose_total_right, apply_total.
  simpl.
  intros.
  erewrite SeparateCompiler.transf_clight_fundef_external; eauto.
Qed.

(** Now, let's prove that our compiler is a per-function compiler for internal functions. *)

Definition transf_rtl_function fenv: forall (p: RTL.function), res LAsm.function :=
  (SeparateCompiler.transf_rtl_function fenv)
    ;> LAsmgen.transf_function.

Definition transf_clight_function' fenv: forall (p: Clight.function), res LAsm.function :=
  (SeparateCompiler.transf_clight_function' fenv)
    ;> LAsmgen.transf_function.

Theorem transf_clight_fundef_internal:
  forall fenv f tf,
    transf_clight_function' fenv f = OK tf ->
    transf_clight_fundef' fenv (Clight.Internal f) = OK (AST.Internal tf).
Proof.
  intros.
  unfold transf_clight_function' in H.
  repeat SeparateCompiler.compose_elim.
  unfold transf_clight_fundef'.
  unfold compose_total_right.
  unfold apply_total.
  simpl.
  erewrite SeparateCompiler.transf_clight_fundef_internal; eauto.
  reflexivity.
Qed.

(** Per-module compiler (uses the concrete implementation of modules) *)

Require Import Coqlib.
Require Import Functor.
Require Import Monad.
Require Import OptionMonad.
Require Import ErrorMonad.
Require Import PTrees.
Require Import PTreeModules.

(** How to use CompCertX to compile modules from Clight to Asm. *)

Definition transf_nzdef {A B} (transf_function: A -> res B):
  res A -> res (res B) :=
    fun z =>
      a <- z;
      b <- transf_function a;
      OK (OK b).
  
(** We first construct the [fenv] function map for function
inlining, from an RTL "module" (PTree of RTL internal function
definitions).

The following definition selects a function for inlining.
 *)

Definition select_to_inline i (z: res RTL.function): option RTL.function :=
  fallback None
    (f <- z;
     OK (if Inlining.should_inline i f then Some f else None)).

(** Thanks to this definition, we can now build the inlining environment. *)

Definition fenv (M: PTree.t (res RTL.function)): Inlining.funenv :=
  PTree.map_option select_to_inline M.

(** Finally, we can define the CompCertX compiler on Clight modules. *)

Definition transf_module (M: ptree_module Clight.function (globvar Ctypes.type)):
  res (ptree_module LAsm.function (AST.globvar Ctypes.type)) :=
  Mt1 <- PTree.map_error
           (fun _ => transf_nzdef SeparateCompiler.transf_clight_function_to_rtl)
           (fst M);
  Mt2 <- PTree.map_error
           (fun _ => transf_nzdef (transf_rtl_function (fenv Mt1)))
           Mt1;
  ret (Mt2, snd M).

(** For the purpose of the proof, we can rewrite our compiler as follows: *)

Definition fenv_of_clight (M:ptree_module Clight.function (globvar Ctypes.type)):
  res Inlining.funenv := 
  Mt1 <- PTree.map_error
           (fun _ => transf_nzdef SeparateCompiler.transf_clight_function_to_rtl)
           (fst M);
  OK (fenv Mt1).

Definition transf_module_with_fenv
           (fenv: Inlining.funenv)
           (M: ptree_module Clight.function (AST.globvar Ctypes.type))
  :=
    Mt <- PTree.map_error
            (fun _ => transf_nzdef (transf_clight_function' fenv))
            (fst M);
    OK (Mt, snd M).

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
  intros.
  unfold transf_module_with_fenv.
  unfold fenv_of_clight.
  destruct (PTree.map_error _ _) eqn:?; try discriminate; monad_norm.
  inv_monad H; subst.
  generalize (PTree.map_compose_ok).
  generalize (PTree.map_compose_ok _ _ _ _ _ (fun _ => transf_nzdef (transf_clight_function' (fenv t))) _ _ _ Heqr H2).
  intro Z.
  exploit Z.
  destruct a as [|]; simpl.
   {
    intros.
    unfold transf_clight_function'.
    unfold SeparateCompiler.transf_clight_function'.
    unfold ComposePasses.compose_partial, ComposePasses.compose_total_right, ComposePasses.apply_partial.
    unfold transf_nzdef, transf_rtl_function in *.
    monad_norm.
    destruct (SeparateCompiler.transf_clight_function_to_rtl f); try discriminate.
    monad_norm.
    inv H0.
    assumption.
   }
   {
    inversion 2; subst.
   }
   intro.
   rewrite H.
   reflexivity.
Qed.

Local Existing Instance ptree_module_ops.
Local Existing Instance ptree_module_prf.

Lemma get_module_function_transf_some_strong:
  forall M1 M2,
    transf_module M1 = OK M2 ->
    forall (i: ident) f1,
      get_module_function i M1 = OK (Some f1) ->
      exists f2,
        get_module_function i M2 = OK (Some f2) /\
        exists fenv,
          transf_clight_function' fenv f1 = OK f2.
Proof.
  intros until M2. intros TRANSF.
  apply  transf_module_eq_module'_ok in TRANSF.
  unfold transf_module' in TRANSF.
  destruct (fenv_of_clight M1); try discriminate.
  intros i f1.
  unfold transf_module_with_fenv in TRANSF.
  inv_monad TRANSF; subst.
  generalize (PTree.gmap_error_ok _ _ _ i _ _ H0).
  Transparent ptree_module_ops. simpl.
  unfold ptree_module_function.
  destruct ((fst M1) ! i) as [[|]|]; try discriminate.
  simpl. 
  unfold transf_nzdef.
  intros (f' & Hf'1 & Hf'2).
  inv_monad Hf'1; subst.
  inversion 1; subst.
  eexists.
  split.
  * rewrite Hf'2.
    reflexivity.
  * exists f.
    assumption.
Qed.

Lemma get_module_function_transf_some:
  forall M1 M2,
    transf_module M1 = OK M2 ->
    forall (i: ident) f1,
      get_module_function i M1 = OK (Some f1) ->
      exists f2,
        get_module_function i M2 = OK (Some f2).
Proof.
  intros. exploit get_module_function_transf_some_strong; eauto.
  destruct 1 as (? & ? & ?) .
  eauto.
Qed.

Lemma get_module_function_transf_none:
  forall M1 M2,
    transf_module M1 = OK M2 ->
    forall (i: ident),
      get_module_function i M1 = OK None ->
      get_module_function i M2 = OK None.
Proof.
  intros until M2. intros TRANSF.
  apply  transf_module_eq_module'_ok in TRANSF.
  unfold transf_module' in TRANSF.
  destruct (fenv_of_clight M1); try discriminate.
  intro i.
  unfold transf_module_with_fenv in TRANSF.
  inv_monad TRANSF; subst.
  generalize (PTree.gmap_error_ok _ _ _ i _ _ H0).
  Transparent ptree_module_ops. simpl.
  unfold ptree_module_function.
  destruct ((fst M1) ! i) as [[|]|]; try discriminate.
  simpl.
  intros H _.
  rewrite H.
  reflexivity.
Qed.

Lemma get_module_function_transf_error:
  forall M1 M2,
    transf_module M1 = OK M2 ->
    forall (i: ident) msg,
      get_module_function i M1 = Error msg ->
      get_module_function i M2 = Error msg.
Proof.
  intros until M2. intros TRANSF.
  apply  transf_module_eq_module'_ok in TRANSF.
  unfold transf_module' in TRANSF.
  destruct (fenv_of_clight M1); try discriminate.
  intro i.
  unfold transf_module_with_fenv in TRANSF.
  inv_monad TRANSF; subst.
  generalize (PTree.gmap_error_ok _ _ _ i _ _ H0).
  Transparent ptree_module_ops. simpl.
  unfold ptree_module_function.
  destruct ((fst M1) ! i); try discriminate.
  destruct r as [|]; try discriminate.
  destruct 1 as [? [? HM2]].
  discriminate.
Qed.

Lemma get_module_variable_transf:
  forall M1 M2,
    transf_module M1 = OK M2 ->
    forall (i: ident),
      get_module_variable i M2 =
      get_module_variable i M1.
Proof.
  intros until M2. intros TRANSF.
  apply  transf_module_eq_module'_ok in TRANSF.
  unfold transf_module' in TRANSF.
  destruct (fenv_of_clight M1); try discriminate.
  intro i.
  unfold transf_module_with_fenv in TRANSF.
  inv_monad TRANSF; subst.
  generalize (PTree.gmap_error_ok _ _ _ i _ _ H0).
  Transparent ptree_module_ops. simpl.
  unfold ptree_module_variable.
  reflexivity.
Qed.
