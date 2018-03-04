Require compcert.backend.Renumberproof.
Require RTLX.

Import Coqlib.
Import Globalenvs.
Import Events.
Import SmallstepX.
Import RTLX.
Import Renumber.
Export Renumberproof.

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

Variable prog: program.
Let tprog := transf_program prog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma transf_initial_states:
  forall i sg args m,
  forall st1, initial_state prog i sg args m st1 ->
  exists st2, initial_state tprog i sg args m st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  esplit. split.
  econstructor.
  unfold tprog. rewrite symbols_preserved; eauto.
  unfold tprog. apply function_ptr_translated; eauto.
  rewrite sig_preserved; auto.
  constructor; auto. constructor.
Qed.

Lemma transf_final_states:
  forall sg,
  forall st1 st2 r, 
  match_states st1 st2 -> final_state sg st1 r -> final_state sg st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. econstructor; eauto.
Qed.

Theorem transf_program_correct:
  forall i sg args m,
  forward_simulation (semantics_as_c (RTLX.csemantics prog i m) sg args) (semantics_as_c (RTLX.csemantics tprog i m) sg args).
Proof.
  intros.
  eapply forward_simulation_step.
  apply symbols_preserved.
  apply transf_initial_states.
  apply transf_final_states.
  apply step_simulation. 
  typeclasses eauto.
Qed.

End WITHCONFIG.
