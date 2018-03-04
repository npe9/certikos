Require compcert.cfrontend.Cshmgenproof.
Require ClightI64helpers.
Require ClightX.
Require CsharpminorX.
Require SmallstepX.

Import Coqlib.
Import Errors.
Import Integers.
Import Values.
Import Globalenvs.
Import Events.
Import SmallstepX.
Import Cshmgen.
Export Cshmgenproof.

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

Variable prog: Clight.program.
Variable tprog: Csharpminor.program.
Hypothesis TRANSL: transl_program prog = OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma transl_initial_states:
  forall i init_m sg args,
  forall S, ClightX.initial_state prog i init_m sg args S ->
  exists R, CsharpminorX.initial_state tprog i init_m sg args R /\ match_states S R.
Proof.
  inversion 1; subst.
  exploit functions_translated; eauto.
  instantiate (1 := f).
  instantiate (1 := Vptr b Int.zero).
  assumption.
  change (
      Genv.find_funct (Genv.globalenv tprog) (Vptr b Int.zero)
    ) with (
    Genv.find_funct_ptr (Genv.globalenv tprog) b
  ).
  destruct 1 as [? [? ?]].
  esplit.
  split.
  econstructor.
  erewrite symbols_preserved; eauto.
  eassumption.
  symmetry. eapply transl_fundef_sig2; eauto.
  econstructor; eauto.
  constructor.
  constructor.
Qed.

Lemma transl_final_states:
  forall sg,
  forall S R r,
  match_states S R -> ClightX.final_state sg S r -> CsharpminorX.final_state sg R r.
Proof.
  inversion 2; subst. inv H. inv MK. constructor.
Qed.

Theorem transl_program_correct:
  forall i init_m sg args,
    forward_simulation
      (semantics_as_c (ClightX.csemantics prog i init_m) sg args)
      (semantics_as_c (CsharpminorX.csemantics tprog i init_m) sg args)
.
Proof.
  intros.
  eapply forward_simulation_plus.
  apply symbols_preserved; auto.
  apply transl_initial_states.
  apply transl_final_states.
  apply transl_step; auto.
  typeclasses eauto.
Qed.

(** We also need to prove that I64 helpers present in Clight are correctly translated to Csharpminor. *)

Theorem genv_contains_helpers_correct:
  forall h,
    ClightI64helpers.genv_contains_helpers h ge ->
    SelectLongproofX.genv_contains_helpers h tge.
Proof.
  unfold ClightI64helpers.genv_contains_helpers, 
  SelectLongproofX.genv_contains_helpers.
  intros.
  exploit H; eauto.
  destruct 1 as [? [? [? [? [? [? ?]]]]]].
  subst.
  unfold ge, tge in *.
  erewrite symbols_preserved; eauto.
  exploit function_ptr_translated; eauto.
  simpl.
  destruct (AST.signature_eq (Ctypes.signature_of_type x0 x1 x2) (Ctypes.signature_of_type x0 x1 x2)); try congruence.
  destruct 1 as [? [? ?]].
  inv H4.
  eauto.
Qed.

End WITHCONFIG.
