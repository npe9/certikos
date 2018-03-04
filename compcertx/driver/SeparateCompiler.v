
(** We do NOT import compcert.driver.Compiler, because we do NOT want
to depend on passes that are unsupported (e.g. CompCert C) *)

(** Also, we separate code generation from proofs. In this file, we
define the compiler without any proof, so it depends on no proof of
any compiler pass. *)

(** I can list the passes of CompCert backwards by heart! *)

Require compcert.ia32.Asmgen.
Require compcert.backend.Stacking.
Require compcert.backend.CleanupLabels.
Require compcert.backend.Linearize.
Require compcert.backend.Tunneling.
Require compcert.backend.Allocation.
Require DeadcodeX.
Require ConstpropX.
Require CSEX.
Require compcert.backend.Renumber.
Require InliningX.
Require compcert.backend.Tailcall.
Require compcert.backend.RTLgen.
Require SelectionX.
Require compcert.cfrontend.Cminorgen.
Require compcert.cfrontend.Cshmgen.
Require ComposePasses.

Import Coqlib.
Import String.
Import Errors.
Import AST.
Import ComposePasses.

Open Local Scope string_scope.

(** * Composing the translation passes *)

Definition transf_clight_program_to_rtl (p: Clight.program) : res RTL.program :=
  OK p 
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program
   @@ SelectionX.sel_program
  @@@ RTLgen.transl_program
   @@ Tailcall.transf_program.

Definition transf_rtl_program (fenv: Inlining.funenv) (p: RTL.program): res Asm.program :=
  OK p
  @@@ (InliningX.transf_program fenv)
   @@ Renumber.transf_program
   @@ ConstpropX.transf_program
   @@ Renumber.transf_program
  @@@ CSEX.transf_program
  @@@ DeadcodeX.transf_program
  @@@ Allocation.transf_program
   @@ Tunneling.tunnel_program
  @@@ Linearize.transf_program
   @@ CleanupLabels.transf_program
  @@@ Stacking.transf_program
  @@@ Asmgen.transf_program.

Opaque SelectionX.sel_program.

(** Now, let's prove that our compiler is a per-function compiler 
    (given an inlining parameter, which we do not care about how
    it is computed). *)

Definition transf_clight_fundef_to_rtl: forall (p: Clight.fundef), res RTL.fundef :=
  Cshmgen.transl_fundef
  ;;; (
    Cminorgen.transl_fundef
      ;> SelectionX.sel_fundef
      ;;; RTLgen.transl_fundef
      ;> Tailcall.transf_fundef
  ).

Definition transf_rtl_fundef (fenv: Inlining.funenv): forall (p: RTL.fundef), res Asm.fundef :=
  (Inlining.transf_fundef fenv)
    ;> Renumber.transf_fundef
    ;> ConstpropX.transf_fundef
    ;> Renumber.transf_fundef
  ;;; CSEX.transf_fundef
  ;;; DeadcodeX.transf_fundef
  ;;; Allocation.transf_fundef
  ;> Tunneling.tunnel_fundef
  ;;; Linearize.transf_fundef
  ;> CleanupLabels.transf_fundef
  ;;; Stacking.transf_fundef
  ;;; Asmgen.transf_fundef
.

(** Auxiliary functions. These functions should be used only in proofs, and should not be extracted,
    because if the computation of [fenv] is based on [transf_clight_fundef_to_rtl], then
    using [transf_clight_fundef'] will call [transf_clight_fundef_to_rtl] twice. *)

Definition transf_clight_fundef' (fenv: Inlining.funenv): forall (p: Clight.fundef), res Asm.fundef :=
  transf_clight_fundef_to_rtl
    ;;; (transf_rtl_fundef fenv).

Definition transf_clight_program' (fenv: Inlining.funenv) (p: Clight.program): res Asm.program :=
  OK p
     @@@ transf_clight_program_to_rtl
     @@@ (transf_rtl_program fenv)
.

Ltac apply_elim :=
  ComposePasses.apply_elim idtac.

Ltac compose_elim :=
  match goal with
    | [ H : transform_partial_program
              (?f1 ;;; ?f2) _ = OK _ |- _ ] =>
      apply transform_partial_program_compose_in_out in H;
        ComposePasses.compose_elim idtac
    | [ H : transform_partial_program
              (?f1 ;> ?f2) _ = OK _ |- _ ] =>
      apply transform_partial_program_compose_right_in_out in H;
        ComposePasses.compose_elim idtac
    | _ => ComposePasses.compose_elim idtac
  end.

Lemma transf_clight_fundef_to_rtl_program:
  forall p tp,
    transform_partial_program2 transf_clight_fundef_to_rtl Cshmgen.transl_globvar p = OK tp ->
    transf_clight_program_to_rtl p = OK tp.
Proof.
  unfold transf_clight_program_to_rtl, transf_clight_fundef_to_rtl. intros.  
  replace (Cshmgen.transl_globvar) with (Cshmgen.transl_globvar ;;; (fun v => OK v)) in H by reflexivity.
  eapply transform_partial_program2_compose_in_out in H.
  compose_elim.
  match type of Hbc with
    | transform_partial_program2 ?tf ?tv ?b = _ =>
      change (transform_partial_program2 tf tv b) with (transform_partial_program tf b) in Hbc
  end.
  repeat compose_elim.
  repeat (eapply apply_partial_intro; eauto).
Qed.

Lemma transf_rtl_fundef_to_program:
  forall fenv p tp,
    transform_partial_program (transf_rtl_fundef fenv) p = OK tp ->
    transf_rtl_program fenv p = OK tp.
Proof.
  unfold transf_rtl_program, transf_rtl_fundef. intros.  
  repeat compose_elim.
  repeat (eapply apply_partial_intro; eauto).
Qed.

Lemma transf_clight_fundef_to_program':
  forall fenv p tp,
    transform_partial_program2 (transf_clight_fundef' fenv) Cshmgen.transl_globvar p = OK tp ->
    transf_clight_program' fenv p = OK tp.
Proof.
  unfold transf_clight_program', transf_clight_fundef'. intros.  
  replace (Cshmgen.transl_globvar) with (Cshmgen.transl_globvar ;;; (fun v => OK v)) in H by reflexivity.
  eapply transform_partial_program2_compose_in_out in H.  compose_elim.
  match type of Hbc with
    | transform_partial_program2 ?tf ?tv ?b = _ =>
      change (transform_partial_program2 tf tv b) with (transform_partial_program tf b) in Hbc
  end.
  simpl.
  unfold apply_partial.
  erewrite transf_clight_fundef_to_rtl_program; eauto.
  eapply transf_rtl_fundef_to_program; eauto.
Qed.

Ltac compose_intro :=
  match goal with
    | [ |- transform_partial_program (?f1 ;> ?f2) _ = OK _ ] =>
      eapply transform_partial_program_compose_right_out_in; eapply compose_partial_intro; eauto
    | [ |- transform_partial_program (?f1 ;;; ?f2) _ = OK _ ] =>
      eapply transform_partial_program_compose_out_in; eapply compose_partial_intro; eauto
  end.

Lemma transf_clight_program_to_rtl_fundef:
  forall p tp,
    transf_clight_program_to_rtl p = OK tp ->
    transform_partial_program2 transf_clight_fundef_to_rtl Cshmgen.transl_globvar p = OK tp.
Proof.
  unfold transf_clight_program_to_rtl, transf_clight_fundef_to_rtl.
  intros.
  repeat apply_elim.
  replace (Cshmgen.transl_globvar) with (Cshmgen.transl_globvar ;;; (fun v => OK v)) by reflexivity.
  eapply transform_partial_program2_compose_out_in.
  eapply compose_partial_intro; eauto.
  eapply transform_partial_program_compose_right_out_in.
  eapply compose_partial_intro; eauto.
  repeat compose_intro.
Qed.

Lemma transf_rtl_program_to_fundef:
  forall fenv p tp,
    transf_rtl_program fenv p = OK tp ->
    transform_partial_program (transf_rtl_fundef fenv) p = OK tp.
Proof.
  unfold transf_rtl_program, transf_rtl_fundef.
  intros.
  repeat apply_elim.
  repeat compose_intro.
Qed.

Lemma transf_clight_program_to_fundef':
  forall fenv p tp,
    transf_clight_program' fenv p = OK tp ->
    transform_partial_program2 (transf_clight_fundef' fenv) Cshmgen.transl_globvar p = OK tp.
Proof.
  unfold transf_clight_program', transf_clight_fundef'.
  intros.
  repeat apply_elim.
  replace (Cshmgen.transl_globvar) with (Cshmgen.transl_globvar ;;; (fun v => OK v)) by reflexivity.
  eapply transform_partial_program2_compose_out_in.
  eapply compose_partial_intro.
  eapply transf_clight_program_to_rtl_fundef; eauto.
  eapply transf_rtl_program_to_fundef; eauto.
Qed.

(** Now, let's prove that our compiler does not change well-typed external functions *)

Theorem transf_clight_fundef_external:
  forall fenv ef tl ty cc,
    ef_sig ef = Ctypes.signature_of_type tl ty cc ->
    transf_clight_fundef' fenv (Clight.External ef tl ty cc) = OK (AST.External ef).
Proof.  
  unfold transf_clight_fundef'. unfold transf_clight_fundef_to_rtl, transf_rtl_fundef.
  unfold compose_partial, apply_partial.
  simpl.
  intros.
  destruct (signature_eq (ef_sig ef) (Ctypes.signature_of_type tl ty cc)); try contradiction.
  reflexivity.
Qed.

(** Now, let's prove that our compiler is a per-function compiler for internal functions. *)

Definition transf_clight_function_to_rtl: forall (p: Clight.function), res RTL.function :=
  Cshmgen.transl_function
  ;;;
    Cminorgen.transl_function
      ;> SelectionX.sel_function
      ;;; RTLgen.transl_function
      ;> Tailcall.transf_function.

Definition transf_rtl_function fenv: forall (p: RTL.function), res Asm.function :=
(Inlining.transf_function fenv)
  ;> Renumber.transf_function
  ;> ConstpropX.transf_function
  ;> Renumber.transf_function
  ;;; CSEX.transf_function
  ;;; DeadcodeX.transf_function
      ;;; Allocation.transf_function
      ;> Tunneling.tunnel_function
      ;;; Linearize.transf_function
      ;> CleanupLabels.transf_function
      ;;; Stacking.transf_function
      ;;; Asmgen.transf_function
.

Definition transf_clight_function' fenv: forall (p: Clight.function), res Asm.function :=
  transf_clight_function_to_rtl
    ;;; (transf_rtl_function fenv).

Ltac rewrite_step :=
  match goal with
    | [ H : ?x = OK ?y |- context [ bind ?x _ ] ] =>
      rewrite H; simpl
  end.

Theorem transf_clight_fundef_internal:
  forall fenv f tf,
    transf_clight_function' fenv f = OK tf ->
    transf_clight_fundef' fenv (Clight.Internal f) = OK (AST.Internal tf).
Proof.
  intros.
  unfold transf_clight_function', transf_clight_function_to_rtl, transf_rtl_function in H.
  repeat compose_elim.
  unfold transf_clight_fundef', transf_clight_fundef_to_rtl, transf_rtl_fundef.
  unfold compose_partial, apply_partial, compose_total_right, apply_total.
  unfold SelectionX.sel_function in *.
  unfold CSEX.transf_function in *.
  unfold ConstpropX.transf_function in *.
  unfold DeadcodeX.transf_function in *.
  simpl.
  repeat rewrite_step.
  reflexivity.
Qed.

Theorem transf_clight_function_to_rtl_internal:
  forall f tf,
    transf_clight_function_to_rtl f = OK tf ->
    transf_clight_fundef_to_rtl (Clight.Internal f) = OK (Internal tf).
Proof.
  unfold transf_clight_function_to_rtl, transf_clight_fundef_to_rtl.
  intros.
  repeat compose_elim.
  unfold compose_partial, apply_partial, compose_total_right, apply_total.
  simpl.
  unfold SelectionX.sel_function in *.
  repeat rewrite_step.
  reflexivity.
Qed.
