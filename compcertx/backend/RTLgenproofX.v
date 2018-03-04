Require compcert.backend.RTLgenproof.
Require CminorSelX.
Require RTLX.

Import Coqlib.
Import Memory.
Import SmallstepX.
Import Globalenvs.
Import Events.
Import RTLgen.
Export RTLgenproof.

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

Variable prog: CminorSel.program.
Variable tprog: RTL.program.
Hypothesis TRANSL: transl_program prog = Errors.OK tprog.

Let ge : CminorSel.genv := Genv.globalenv prog.
Let tge : RTL.genv := Genv.globalenv tprog.

Lemma transl_initial_states:
  forall i m sg args,
  forall S, CminorSelX.initial_state prog i m sg args S ->
  exists R, RTLX.initial_state tprog i m sg args R /\ match_states S R.
Proof.
  inversion 1; subst.
  exploit function_ptr_translated; eauto.
  destruct 1 as [? [? ?]].
  esplit.
  split.
  econstructor.
  erewrite symbols_preserved; eauto.
  eassumption.
  symmetry. eapply sig_transl_function; eauto.
  constructor; auto.
  constructor.
  refine (val_lessdef_refl _).
  apply Mem.extends_refl.
Qed.

Lemma transl_final_states:
  forall sg,
  forall S R r,
  match_states S R -> CminorSelX.final_state sg S r -> final_state_with_extends (RTLX.final_state sg) R r.
Proof.
  inversion 2; subst.
  inv H.
  inv MS.
  econstructor.
  econstructor.
  assumption.
  assumption.
Qed.

Theorem transf_program_correct:
  forall i m sg args,
  forward_simulation
    (semantics_as_c (CminorSelX.csemantics prog i m) sg args)
    (semantics_with_extends (semantics_as_c (RTLX.csemantics tprog i m) sg args))
.
Proof.
  intros.
  eapply forward_simulation_star_wf with (order := lt_state).
  apply symbols_preserved; auto.
  apply transl_initial_states.
  apply transl_final_states.
  apply lt_state_wf. 
  apply transl_step_correct; auto.
  typeclasses eauto.
Qed.

End WITHCONFIG.
