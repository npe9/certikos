Require compcert.backend.Linearizeproof.
Require LinearX.
Require LTLX.

Import Coqlib.
Import Errors.
Import Globalenvs.
Import Events.
Import Smallstep.
Import LTLX.
Import LinearX.
Import Linearize.
Export Linearizeproof.

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

Variable prog: LTL.program.
Variable tprog: Linear.program.

Hypothesis TRANSF: transf_program prog = OK tprog.

Lemma transf_initial_states:
  forall init_ls i sg args m,
  forall st1, LTLX.initial_state init_ls prog i sg args m st1 ->
  exists st2, LinearX.initial_state init_ls tprog i sg args m st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto.
  destruct 1 as [? [? ?]].
  econstructor; split.
  econstructor; eauto.
  erewrite symbols_preserved; eauto.
  symmetry; eapply sig_preserved; eauto.
  constructor; auto. constructor.
Qed.

Lemma transf_final_states:
  forall init_ls,
  forall sg,
  forall st1 st2 r, 
  match_states st1 st2 -> LTLX.final_state init_ls sg st1 r -> LinearX.final_state init_ls sg st2 r.
Proof.
  intros. inv H0. inv H. inv H4. econstructor; eauto.
Qed.

Theorem transf_program_correct:
  forall init_ls i sg args m,
  forward_simulation (LTLX.semantics init_ls prog i sg args m) (LinearX.semantics init_ls tprog i sg args m).
Proof.
  intros.
  eapply forward_simulation_star.
  apply symbols_preserved; eauto.
  apply transf_initial_states.
  apply transf_final_states.
  apply transf_step_correct; eauto with typeclass_instances.
Qed.

End WITHCONFIG.
