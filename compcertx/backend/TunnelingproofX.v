Require compcert.backend.Tunnelingproof.
Require LTLX.

Import Coqlib.
Import Globalenvs.
Import Events.
Import Smallstep.
Import LTLX.
Import Tunneling.
Export Tunnelingproof.

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

Variable prog: program.
Let tprog := tunnel_program prog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma transf_initial_states:
  forall init_ls i sg args m,
  forall st1, initial_state init_ls prog i sg args m st1 ->
  exists st2, initial_state init_ls tprog i sg args m st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  econstructor; split.
  econstructor.
  unfold tprog. rewrite symbols_preserved; eauto.
  unfold tprog. erewrite function_ptr_translated; eauto.
  subst. symmetry; eauto using sig_preserved.
  assumption.
  constructor; auto. constructor.
Qed.

Lemma transf_final_states:
  forall init_ls,
  forall sg,
  forall st1 st2 r, 
  match_states st1 st2 -> final_state init_ls sg st1 r -> final_state init_ls sg st2 r.
Proof.
  intros. inv H0. inv H. inv H4. econstructor; eauto.
Qed.

Theorem transf_program_correct:
  forall init_ls i sg args m,
  forward_simulation (semantics init_ls prog i sg args m) (semantics init_ls tprog i sg args m).
Proof.
  intros.
  eapply forward_simulation_opt.
  apply symbols_preserved.
  apply transf_initial_states.
  apply transf_final_states.
  apply tunnel_step_correct.
  typeclasses eauto.
Qed.

End WITHCONFIG.
