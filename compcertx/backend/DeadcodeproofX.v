Require compcert.backend.Deadcodeproof.
Require DeadcodeX.
Require ValueAnalysisX.
Require SmallstepX.

Import Coqlib.
Import Errors.
Import AST.
Import Values.
Import Memory.
Import Events.
Import SmallstepX.
Import Globalenvs.
Import DeadcodeX.
Import ValueDomainX.
Import ValueAnalysisX.
Export Deadcodeproof.

Section WITHCONFIG.
Context `{compiler_config: CompilerConfiguration}.

(** The following [magree] relation on memory states is required by
    [Deadcodeproof]. It is a stronger version of [Mem.extends] which
    is parameterized on a predicate over which equality of contents
    (rather than [Val.lessdef]) is required. *)

Context `{magree_ops: !MAgreeOps mem}.
Context `{magree_prf: !MAgree mem}.

Variable prog: RTL.program.
Variable tprog: RTL.program.

Hypothesis TRANSF: transf_program prog = OK tprog.

Let ge : RTL.genv := Genv.globalenv prog.
Let tge: RTL.genv := Genv.globalenv tprog.

Lemma genv_next_preserved:
  Genv.genv_next tge = Genv.genv_next ge.
Proof.
  unfold transf_program, transf_fundef in TRANSF.
  eapply Deadcodeproof.genv_next_preserved; eauto.
Qed.

Lemma transf_initial_states:
  forall i init_m sg args,
  forall S, RTLX.initial_state prog i init_m sg args S ->
  exists R, RTLX.initial_state tprog i init_m sg args R /\ match_states prog rmtop S R.
Proof.
  unfold transf_program, transf_fundef in TRANSF.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros [f' [? ?]].
  exists (RTL.Callstate nil f' args init_m); split.
  econstructor; eauto.
  erewrite symbols_preserved; eauto.
  symmetry. eapply sig_function_translated; eauto.
  econstructor.
  econstructor.
  assumption.
  exact (val_lessdef_refl _).
  apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall sg,
  forall st1 st2 r, 
  match_states prog rmtop st1 st2 -> RTLX.final_state sg st1 r ->
  final_state_with_extends (RTLX.final_state sg) st2 r.
Proof.
  intros. inv H0. inv H.
  inv STACKS.
  econstructor; eauto.
  constructor.
Qed.

(** The following further hypothesis on the memory model is needed by
    value analysis. *)

Context `{mmatch_ops: !ValueDomain.MMatchOps mem}.
Context `{mmatch_constructions_prf: !ValueAnalysis.MMatchConstructions mem}.

(** To prove that the initial per-function state is sound with respect
    to value analysis, we need the following hypotheses, which
    actually hold thanks to the properties on the caller in assembly
    code (see [AsmX.asm_invariant] for the invariant on the assembly
    state, and [Asm.exec_step_external] for the conditions local to
    the function call site.)
*)
 
Variable init_m: mem.
Variable args: list val.

Hypotheses
  (INJECT_NEUTRAL: Mem.inject_neutral (Mem.nextblock init_m) init_m)
  (GENV_NEXT: Ple (Genv.genv_next ge) (Mem.nextblock init_m))
  (ARGS_INJECT_NEUTRAL: val_list_inject (Mem.flat_inj (Mem.nextblock init_m)) args args).

Theorem transf_program_correct:
  forall i sg,
  forward_simulation 
    (semantics_as_c (RTLX.csemantics prog i init_m) sg args)
    (semantics_with_extends (semantics_as_c (RTLX.csemantics tprog i init_m) sg args)).
Proof.
  unfold transf_program, transf_fundef in TRANSF.
  intros.
  apply forward_simulation_step with
     (match_states := fun s1 s2 => sound_state prog rmtop s1 /\ match_states prog rmtop s1 s2);
    simpl.
  - intros; eapply symbols_preserved; eauto.
  - intros. exploit transf_initial_states; eauto. intros [st2 [A B]].
    exists st2; intuition. eapply sound_initial; eauto. 
    typeclasses eauto.
  - simpl; intros. destruct H. eapply transf_final_states; eauto. 
  - simpl; intros. destruct H0.
    generalize H. intro STEP.
    eapply sound_step in H; eauto.
    eapply step_simulation in STEP; eauto.
    destruct STEP as [st2' [A B]].
    exists st2'; auto. 
    typeclasses eauto.
Qed.

End WITHCONFIG.
