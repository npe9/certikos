Require compcert.backend.Inliningproof.
Require InliningX.
Require RTLX.
Require SmallstepX.

Import Coqlib.
Import Errors.
Import AST.
Import Values.
Import Memory.
Import Events.
Import SmallstepX.
Import Globalenvs.
Import InliningX.
Import Inliningspec.
Export Inliningproof.

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

Variable prog: RTL.program.
Variable tprog: RTL.program.

Variable fenv: funenv.
Hypothesis funenv_program_compat: fenv_compat (Genv.globalenv prog) fenv.

Hypothesis TRANSL: transf_program fenv prog = OK tprog.
Let ge : RTL.genv := Genv.globalenv prog.
Let tge: RTL.genv := Genv.globalenv tprog.

Variable init_m: mem.
Hypothesis init_m_inject_neutral: Mem.inject_neutral (Mem.nextblock init_m) init_m.
Hypothesis genv_next_init_m: Ple (Genv.genv_next ge) (Mem.nextblock init_m).

Variable args: list val.
Hypothesis args_inj: val_list_inject (Mem.flat_inj (Mem.nextblock init_m)) args args.

Lemma transf_initial_states:
  forall i sg,
  forall S, RTLX.initial_state prog i init_m sg args S ->
  exists R, RTLX.initial_state tprog i init_m sg args R /\ match_states prog fenv init_m S R.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  exists (RTL.Callstate nil tf args init_m); split.
  econstructor; eauto.
  erewrite symbols_preserved; eauto.
  symmetry. eapply sig_function_translated; eauto.
  econstructor.
  econstructor.
  econstructor.
  eapply Ple_refl.
  9: eapply Mem.neutral_inject; eauto.
  unfold Mem.flat_inj. intros. rewrite pred_dec_true. reflexivity. assumption.
  unfold Mem.flat_inj. intros. destruct (plt b1 (Mem.nextblock init_m)); congruence.
  unfold ge in *. intros. exploit Genv.genv_symb_range; eauto. xomega.
  unfold ge in *. intros. exploit Genv.genv_funs_range; eauto. xomega.
  unfold ge in *. intros. exploit Genv.genv_vars_range; eauto. xomega.
  apply Ple_refl. 
  assumption.
  assumption.
Qed.

Lemma transf_final_states:
  forall sg,
  forall st1 st2 r, 
  match_states prog fenv init_m st1 st2 -> RTLX.final_state sg st1 r ->
  final_state_with_inject (RTLX.final_state sg) init_m st2 r.
Proof.
  intros. inv H0. inv H.
  exploit match_stacks_empty; eauto. intros EQ; subst.
  inv MS.
  econstructor.
   econstructor.
    eapply match_globalenvs_inject_incr; eauto.
    eapply match_globalenvs_inject_separated; eauto.
    assumption.
    assumption.   
  exploit match_stacks_inside_empty; eauto. intros [A B]. congruence. 
Qed.

Theorem transf_program_correct:
  forall i sg,
  forward_simulation 
    (semantics_as_c (RTLX.csemantics prog i init_m) sg args)
    (semantics_with_inject (semantics_as_c (RTLX.csemantics tprog i init_m) sg args) init_m).
Proof.
  intros.
  eapply forward_simulation_star.
  eapply symbols_preserved; eauto.
  simpl; intros.
  instantiate (1 := match_states prog fenv init_m).
  eapply transf_initial_states; eauto.
  eapply transf_final_states.
  instantiate (1 := measure). intros.
  eapply step_simulation; eauto with typeclass_instances.
Qed.

End WITHCONFIG.
